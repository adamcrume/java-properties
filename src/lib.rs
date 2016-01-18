//! Utilities for reading and writing Java properties files
//!
//! The specification is taken from https://docs.oracle.com/javase/7/docs/api/java/util/Properties.html.
//! Where the documentation is ambiguous or incomplete, behavior is based on the behavior of java.util.Properties.
//!
//! # Examples
//!
//! ```
//! use java_properties::PropertiesIter;
//! use java_properties::PropertiesWriter;
//! use std::collections::HashMap;
//! use std::env::temp_dir;
//! use std::fs::File;
//! use std::io::prelude::*;
//!
//! # fn main() {
//! # fn foo() -> std::result::Result<(), java_properties::PropertiesError> {
//! let mut file_name = temp_dir();
//! file_name.push("java-properties-test.properties");
//!
//! // Writing
//! let mut map1 = HashMap::new();
//! map1.insert("a".to_string(), "b".to_string());
//! let mut f = try!(File::create(&file_name));
//! let mut writer = PropertiesWriter::new(f);
//! for (k, v) in map1.iter() {
//!   try!(writer.write(&k, &v));
//! }
//!
//! // Reading
//! let mut f = try!(File::open(&file_name));
//! let mut map2 = HashMap::new();
//! try!(PropertiesIter::new(f).read_into(|k, v| {
//!   map2.insert(k, v);
//! }));
//! assert_eq!(map1, map2);
//! # Ok(())
//! # }
//! # foo().unwrap();
//! # }
//! ```

extern crate encoding;
extern crate regex;

use encoding::ByteWriter;
use encoding::EncoderTrap;
use encoding::Encoding;
use encoding::DecoderTrap;
use encoding::RawEncoder;
use encoding::all::ISO_8859_1;
use regex::Regex;
use std::convert::From;
use std::error::Error;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::io;
use std::io::BufRead;
use std::io::Bytes;
use std::io::Read;
use std::io::Write;
use std::iter::Peekable;
use std::ops::Deref;

/////////////////////

#[derive(Debug)]
pub struct PropertiesError {
  description: String,
  cause: Option<Box<Error>>,
  line_number: Option<usize>,
}

impl PropertiesError {
  fn new(description: &str, cause: Option<Box<Error>>, line_number: Option<usize>) -> Self {
    PropertiesError {
      description: description.to_string(),
      cause: cause,
      line_number: line_number,
    }
  }

  pub fn line_number(&self) -> Option<usize> {
    self.line_number
  }
}

impl Error for PropertiesError {
  fn description(&self) -> &str {
    &self.description
  }

  fn cause(&self) -> Option<&Error> {
    match self.cause {
      Some(ref c) => Some(c.deref()),
      None => None,
    }
  }
}

impl From<io::Error> for PropertiesError {
  fn from(e: io::Error) -> Self {
    PropertiesError::new("I/O error", Some(Box::new(e)), None)
  }
}

impl Display for PropertiesError {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    Display::fmt(&self.description, f)
  }
}

/////////////////////

#[derive(PartialEq,Eq,Debug)]
struct NaturalLine(usize, String);

// We can't use BufRead.lines() because it doesn't use the proper line endings
struct NaturalLines<R: Read> {
  bytes: Peekable<Bytes<R>>,
  eof: bool,
  line_count: usize,
}

impl<R: Read> NaturalLines<R> {
  fn new(reader: R) -> Self {
    NaturalLines {
      bytes: reader.bytes().peekable(),
      eof: false,
      line_count: 0,
    }
  }
}

const LF: u8 = 10;
const CR: u8 = 13;

impl< R: Read> Iterator for NaturalLines<R> {
  type Item = Result<NaturalLine, PropertiesError>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.eof {
      return None;
    }
    let mut buf = String::new();
    loop {
      match self.bytes.next() {
        Some(r) => match r {
          Ok(b) => {
            match b {
              CR => {
                match self.bytes.peek() {
                  Some(&Ok(LF)) => { self.bytes.next(); },
                  _ => (),
                }
                self.line_count += 1;
                return Some(Ok(NaturalLine(self.line_count, buf)));
              },
              LF => {
                self.line_count += 1;
                return Some(Ok(NaturalLine(self.line_count, buf)));
              },
              _ => match ISO_8859_1.decode(&[b], DecoderTrap::Strict) {
                Ok(s) => buf.push_str(&s),
                Err(_) => return Some(Err(PropertiesError::new("Error reading ISO-8859-1 encoding", None, Some(self.line_count)))),
              },
            };
          },
          Err(e) => return Some(Err(PropertiesError::new("I/O error", Some(Box::new(e)), Some(self.line_count + 1)))),
        },
        None => {
          self.eof = true;
          self.line_count += 1;
          return Some(Ok(NaturalLine(self.line_count, buf)));
        },
      }
    }
  }
}

/////////////////////

#[derive(PartialEq,Eq,Debug)]
struct LogicalLine(usize, String);

struct LogicalLines<I: Iterator<Item=Result<NaturalLine, PropertiesError>>> {
  physical_lines: I,
  eof: bool,
  comment_re: Regex,
}

impl<I: Iterator<Item=Result<NaturalLine, PropertiesError>>> LogicalLines<I> {
  fn new(physical_lines: I) -> Self {
    LogicalLines {
      physical_lines: physical_lines,
      eof: false,
      comment_re: Regex::new("^[ \t\r\n\x0c]*[#!]").unwrap(),
    }
  }
}

fn count_ending_backslashes(s: &str) -> usize {
  let chars: Vec<char> = s.chars().collect();
  let n = chars.len();
  let mut i = n;
  while i > 0 {
    i -= 1;
    if chars[i] != '\\' {
      return n - 1 - i;
    }
  }
  n
}

impl<I: Iterator<Item=Result<NaturalLine, PropertiesError>>> Iterator for LogicalLines<I> {
  type Item = Result<LogicalLine, PropertiesError>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.eof {
      return None;
    }
    let mut buf = String::new();
    let mut first = true;
    let mut line_number = 0;
    loop {
      match self.physical_lines.next() {
        Some(Err(e)) => return Some(Err(e)),
        Some(Ok(NaturalLine(line_no, line))) => {
          if first {
            line_number = line_no;
          }
          buf.push_str(
            if first {
              &line
            } else {
              line.trim_left()
            }
          );
          if first && self.comment_re.is_match(&line) {
            // This format is terrible.  We can't throw out comment lines before joining natural lines, because "a\\\n#b" should be joined into "a#b".
            // On the other hand, we can't join natural lines before processing comments, because "#a\\\nb" should stay as two lines, "#a\\" and "b".
            // Processing line joins and comments are inextricably linked.
            assert!(line_number != 0);
            return Some(Ok(LogicalLine(line_number, buf)));
          }
          if count_ending_backslashes(&line) % 2 == 1 {
            buf.pop();
          } else {
            assert!(line_number != 0);
            return Some(Ok(LogicalLine(line_number, buf)));
          }
        },
        None => {
          self.eof = true;
          return None;
        },
      }
      first = false;
    }
  }
}

/////////////////////

#[derive(PartialEq,Eq,PartialOrd,Ord,Debug)]
enum ParsedLine<'a> {
  Comment(&'a str),
  KVPair(&'a str, &'a str),
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct Line {
  line_number: usize,
  data: LineContent,
}

impl Line {
  pub fn line_number(&self) -> usize {
    self.line_number
  }

  pub fn content(&self) -> &LineContent {
    &self.data
  }

  pub fn consume_content(self) -> LineContent {
    self.data
  }

  fn mk_pair(line_no: usize, key: String, value: String) -> Line {
    Line {
      line_number: line_no,
      data: LineContent::KVPair(key, value),
    }
  }

  fn mk_comment(line_no: usize, text: String) -> Line {
    Line {
      line_number: line_no,
      data: LineContent::Comment(text),
    }
  }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Debug)]
pub enum LineContent {
  Comment(String),
  KVPair(String, String),
}

/////////////////////

fn unescape(s: &str, line_number: usize) -> Result<String, PropertiesError> {
  let mut buf = String::new();
  let mut iter = s.chars();
  loop {
    match iter.next() {
      None => break,
      Some(c) => {
        if c == '\\' {
          match iter.next() {
            Some(c) => match c {
              // \b is specifically blacklisted by the documentation.  Why?  Who knows.
              't' => buf.push('\t'),
              'n' => buf.push('\n'),
              'f' => buf.push('\x0c'),
              'r' => buf.push('\r'),
              'u' => {
                let mut tmp = String::new();
                for _ in 0..4 {
                  match iter.next() {
                    Some(c) => tmp.push(c),
                    None => return Err(PropertiesError::new("Malformed \\uxxxx encoding: not enough digits.", None, Some(line_number))),
                  }
                }
                let val = match u16::from_str_radix(&tmp, 16) {
                  Ok(x) => x,
                  Err(e) => return Err(PropertiesError::new("Malformed \\uxxxx encoding: not hex.", Some(Box::new(e)), Some(line_number))),
                };
                match std::char::from_u32(val as u32) {
                  Some(c) => buf.push(c),
                  None => return Err(PropertiesError::new("Malformed \\uxxxx encoding: invalid character.", None, Some(line_number))),
                }
              },
              _ => buf.push(c),
            },
            None => {
              // The Java implementation replaces a dangling backslash with a NUL byte (\0).
              // Is this "correct"?  Probably not.
              // It's never documented, so assume it's undefined behavior.
              // Let's do what Java does, though.
              buf.push('\x00');
              break;
            }
          }
        } else {
          buf.push(c);
        }
      },
    }
  }
  Ok(buf)
}

struct LineParser {
  re: Regex,
}

impl LineParser {
  fn new() -> Self {
    // Note that we have to use \x20 to match a space and \x23 to match a pound character since we're ignoring whitespace and comments
    let re_str = r"(?x) # allow whitespace and comments
      ^
      [\x20\t\r\n\x0c]* # ignorable whitespace
      (?:
        [\x23!] # start of comment (# or !)
        [\x20\t\r\n\x0c]* # ignorable whitespace
        (.*?) # comment text
      |
        (
          (?:[^\\:=\x20\t\r\n\x0c]|\\.)* # key
          (?:\\$)? # end of line backslash, can't show up in real input because it's caught by LogicalLines
        )
        (?:
          (?:
            [\x20\t\r\n\x0c]*[:=][\x20\t\r\n\x0c]* # try matching an actual separator (: or =)
          |
            [\x20\t\r\n\x0c]+ # try matching whitespace only
          )
          (
            (?:[^\\]|\\.)*? # value
            (?:\\$)? # end of line backslash, can't show up in real input because it's caught by LogicalLines
          )
        )?
      )
      [\x20\t\r\n\x0c]* # ignorable whitespace
      $
    ";
    LineParser {
      re: Regex::new(re_str).unwrap(),
    }
  }

  fn parse_line<'a>(&self, line: &'a str) -> Option<ParsedLine<'a>> {
    if let Some(c) = self.re.captures(line) {
      if let Some((start, end)) = c.pos(1) {
        Some(ParsedLine::Comment(&line[start..end]))
      } else if let Some((kstart, kend)) = c.pos(2) {
        let key = &line[kstart..kend];
        if let Some((vstart, vend)) = c.pos(3) {
          Some(ParsedLine::KVPair(key, &line[vstart..vend]))
        } else if key != "" {
          Some(ParsedLine::KVPair(key, ""))
        } else {
          None
        }
      } else {
        panic!("Failed to get any groups out of the regular expression.")
      }
    } else {
      // This should never happen.  The pattern should match all strings.
      panic!("Failed to match on {:?}", line);
    }
  }
}

pub struct PropertiesIter<R: Read> {
  lines: LogicalLines<NaturalLines<R>>,
  parser: LineParser,
}

impl<R: Read> PropertiesIter<R> {
  pub fn new(input: R) -> Self {
    PropertiesIter {
      lines: LogicalLines::new(NaturalLines::new(input)),
      parser: LineParser::new(),
    }
  }

  pub fn read_into<F: FnMut(String, String)>(&mut self, mut f: F) -> Result<(), PropertiesError> {
    for line in self {
      match try!(line).data {
        LineContent::KVPair(key, value) => {
           f(key, value);
        },
        LineContent::Comment(_) => (),
      }
    }
    Ok(())
  }

  fn parsed_line_to_line(&self, parsed_line: ParsedLine, line_number: usize) -> Result<Line, PropertiesError> {
    Ok(match parsed_line {
      ParsedLine::Comment(c) => {
        let comment = try!(unescape(c, line_number));
        Line::mk_comment(line_number, comment)
      },
      ParsedLine::KVPair(k, v) => {
        let key = try!(unescape(k, line_number));
        let value = try!(unescape(v, line_number));
        Line::mk_pair(line_number, key, value)
      },
    })
  }
}

impl<R: Read> Iterator for PropertiesIter<R> {
  type Item = Result<Line, PropertiesError>;

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      match self.lines.next() {
        Some(maybe_line) => match maybe_line {
          Ok(LogicalLine(line_no, line)) => match self.parser.parse_line(&line) {
            Some(parsed_line) => {return Some(self.parsed_line_to_line(parsed_line, line_no));},
            None => (), // empty line, continue
          },
          Err(e) => return Some(Err(e)),
        },
        None => return None,
      }
    }
  }
}

/////////////////////

fn unicode_escape(_encoder: &mut RawEncoder, input: &str, output: &mut ByteWriter) -> bool {
  let escapes: Vec<String> = input.chars().map(|ch| format!("\\u{:x}", ch as isize)).collect();
  let escapes = escapes.concat();
  output.write_bytes(escapes.as_bytes());
  true
}

static UNICODE_ESCAPE: EncoderTrap = EncoderTrap::Call(unicode_escape);

pub struct PropertiesWriter<W: Write> {
  writer: W,
  lines_written: usize,
}

impl<W: Write> PropertiesWriter<W> {
  pub fn new(writer: W) -> Self {
    PropertiesWriter {
      writer: writer,
      lines_written: 0,
    }
  }

  pub fn write_comment(&mut self, comment: &str) -> Result<(), PropertiesError> {
    self.lines_written += 1;
    try!(self.writer.write_all(&['#' as u8, ' ' as u8]));
    let data = ISO_8859_1.encode(comment, UNICODE_ESCAPE);
    match data {
      Ok(d) => try!(self.writer.write_all(&d)),
      Err(_) => return Err(PropertiesError::new("Encoding error", None, Some(self.lines_written))),
    };
    try!(self.writer.write_all(&['\n' as u8]));
    Ok(())
  }

  fn write_escaped(&mut self, s: &str) -> Result<(), PropertiesError> {
    self.lines_written += 1;
    let mut escaped = String::new();
    for c in s.chars() {
      match c {
        '\\' => escaped.push_str("\\\\"),
        ' ' => escaped.push_str("\\ "),
        '\t' => escaped.push_str("\\t"),
        '\r' => escaped.push_str("\\r"),
        '\n' => escaped.push_str("\\n"),
        '\x0c' => escaped.push_str("\\f"),
        ':' => escaped.push_str("\\:"),
        '=' => escaped.push_str("\\="),
        _ if c < ' ' => escaped.push_str(&format!("\\u{:x}", c as u16)),
        _ => escaped.push(c), // We don't worry about other characters, since they're taken care of below.
      }
    }
    match ISO_8859_1.encode(&escaped, UNICODE_ESCAPE) {
      Ok(d) => try!(self.writer.write_all(&d)),
      Err(_) => return Err(PropertiesError::new("Encoding error", None, Some(self.lines_written))),
    };
    Ok(())
  }

  pub fn write(&mut self, key: &str, value: &str) -> Result<(), PropertiesError> {
    try!(self.write_escaped(key));
    try!(self.writer.write_all(&['=' as u8]));
    try!(self.write_escaped(value));
    try!(self.writer.write_all(&['\n' as u8]));
    Ok(())
  }

  pub fn flush(&mut self) -> Result<(), PropertiesError> {
    try!(self.writer.flush());
    Ok(())
  }
}

/////////////////////

#[cfg(test)]
mod tests {
  use encoding::all::ISO_8859_1;
  use encoding::DecoderTrap;
  use encoding::Encoding;
  use std::io;
  use std::io::ErrorKind;
  use std::io::Read;
  use super::CR;
  use super::LF;
  use super::Line;
  use super::LogicalLine;
  use super::LogicalLines;
  use super::NaturalLine;
  use super::NaturalLines;
  use super::ParsedLine;
  use super::PropertiesIter;
  use super::PropertiesWriter;

  const SP: u8 = 32; // space

  #[test]
  fn natural_lines() {
    let data = [
      (vec![], vec![""]),
      (vec![SP], vec![" "]),
      (vec![SP, CR], vec![" ", ""]),
      (vec![SP, LF], vec![" ", ""]),
      (vec![SP, CR, LF], vec![" ", ""]),
      (vec![SP, CR, SP], vec![" ", " "]),
      (vec![SP, LF, SP], vec![" ", " "]),
      (vec![SP, CR, LF, SP], vec![" ", " "]),
      (vec![CR], vec!["", ""]),
      (vec![LF], vec!["", ""]),
      (vec![CR, LF], vec!["", ""]),
      (vec![CR, SP], vec!["", " "]),
      (vec![LF, SP], vec!["", " "]),
      (vec![CR, LF, SP], vec!["", " "]),
    ];
    for &(ref bytes, ref lines) in data.iter() {
      let reader = &bytes as &[u8];
      let mut iter = NaturalLines::new(reader);
      let mut count = 1;
      for line in lines {
        match (line.to_string(), iter.next()) {
          (ref e, Some(Ok(NaturalLine(a_ln, ref a)))) => if (count, e) != (a_ln, a) {
            panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", bytes, (count, e), (a_ln, a));
          },
          (e, a) => panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", bytes, (count, e), a),
        }
        count += 1;
      }
      match iter.next() {
        None => (),
        a => panic!("Failure while processing {:?}.  Expected None, but was {:?}", bytes, a),
      }
    }
  }

  #[test]
  fn logical_lines() {
    let data = [
      (vec![], vec![]),
      (vec!["foo"], vec!["foo"]),
      (vec!["foo", "bar"], vec!["foo", "bar"]),
      (vec!["foo\\", "bar"], vec!["foobar"]),
      (vec!["foo\\\\", "bar"], vec!["foo\\\\", "bar"]),
      (vec!["foo\\\\\\", "bar"], vec!["foo\\\\bar"]),
      (vec!["foo\\", " bar"], vec!["foobar"]),
      (vec!["#foo\\", " bar"], vec!["#foo\\", " bar"]),
      (vec!["foo\\", "# bar"], vec!["foo# bar"]),
      (vec!["\u{1F41E}\\", "\u{1F41E}"], vec!["\u{1F41E}\u{1F41E}"]),
      (vec!["\u{1F41E}\\", " \u{1F41E}"], vec!["\u{1F41E}\u{1F41E}"]),
    ];
    for &(ref input_lines, ref lines) in data.iter() {
      let mut count = 0;
      let mut iter = LogicalLines::new(input_lines.iter().map(|x| {
          count += 1;
          Ok(NaturalLine(count, x.to_string()))
      }));
      let mut e_ln = 0;
      for line in lines {
        e_ln += 1;
        match (line.to_string(), iter.next()) {
          (ref e, Some(Ok(LogicalLine(a_ln, ref a)))) => if (e_ln, e) != (a_ln, a) {
            panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", input_lines, (e_ln, e), (a_ln, a));
          },
          (e, a) => panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", input_lines, (e_ln, e), a),
        }
      }
      match iter.next() {
        None => (),
        a => panic!("Failure while processing {:?}.  Expected None, but was {:?}", input_lines, a),
      }
    }
  }

  #[test]
  fn count_ending_backslashes() {
    assert_eq!(0, super::count_ending_backslashes(""));

    assert_eq!(0, super::count_ending_backslashes("x"));
    assert_eq!(1, super::count_ending_backslashes("\\"));

    assert_eq!(0, super::count_ending_backslashes("xx"));
    assert_eq!(0, super::count_ending_backslashes("\\x"));
    assert_eq!(1, super::count_ending_backslashes("x\\"));
    assert_eq!(2, super::count_ending_backslashes("\\\\"));

    assert_eq!(0, super::count_ending_backslashes("xxx"));
    assert_eq!(0, super::count_ending_backslashes("\\xx"));
    assert_eq!(0, super::count_ending_backslashes("x\\x"));
    assert_eq!(0, super::count_ending_backslashes("\\\\x"));
    assert_eq!(1, super::count_ending_backslashes("xx\\"));
    assert_eq!(1, super::count_ending_backslashes("\\x\\"));
    assert_eq!(2, super::count_ending_backslashes("x\\\\"));
    assert_eq!(3, super::count_ending_backslashes("\\\\\\"));

    assert_eq!(0, super::count_ending_backslashes("x\u{1F41E}"));
    assert_eq!(0, super::count_ending_backslashes("\\\u{1F41E}"));
    assert_eq!(0, super::count_ending_backslashes("\u{1F41E}x"));
    assert_eq!(1, super::count_ending_backslashes("\u{1F41E}\\"));
  }

  #[test]
  fn parse_line() {
    let data = [
      ("", None),
      (" ", None),
      ("\\", Some(ParsedLine::KVPair("\\", ""))),
      ("a=\\", Some(ParsedLine::KVPair("a", "\\"))),
      ("\\ ", Some(ParsedLine::KVPair("\\ ", ""))),
      ("# foo", Some(ParsedLine::Comment("foo"))),
      (" # foo", Some(ParsedLine::Comment("foo"))),
      ("a # foo", Some(ParsedLine::KVPair("a", "# foo"))),
      ("a", Some(ParsedLine::KVPair("a", ""))),
      ("a = b", Some(ParsedLine::KVPair("a", "b"))),
      ("a : b", Some(ParsedLine::KVPair("a", "b"))),
      ("a b", Some(ParsedLine::KVPair("a", "b"))),
      (" a = b", Some(ParsedLine::KVPair("a", "b"))),
      (" a : b", Some(ParsedLine::KVPair("a", "b"))),
      (" a b", Some(ParsedLine::KVPair("a", "b"))),
      ("a:=b", Some(ParsedLine::KVPair("a", "=b"))),
      ("a=:b", Some(ParsedLine::KVPair("a", ":b"))),
      ("a b:c", Some(ParsedLine::KVPair("a", "b:c"))),
      ("a\\ \\:\\=b c", Some(ParsedLine::KVPair("a\\ \\:\\=b", "c"))),
      ("a\\ \\:\\=b=c", Some(ParsedLine::KVPair("a\\ \\:\\=b", "c"))),
      ("a\\\\ \\\\:\\\\=b c", Some(ParsedLine::KVPair("a\\\\", "\\\\:\\\\=b c"))),
      ("\\  b", Some(ParsedLine::KVPair("\\ ", "b"))),
      ("=", Some(ParsedLine::KVPair("", ""))),
      ("\u{1F41E}=\u{1F41E}", Some(ParsedLine::KVPair("\u{1F41E}", "\u{1F41E}"))),
    ];
    let splitter = super::LineParser::new();
    for &(line, ref expected) in data.iter() {
      let actual = splitter.parse_line(line);
      if expected != &actual {
        panic!("Failed when splitting {:?}.  Expected {:?} but got {:?}", line, expected, actual);
      }
    }
  }

  #[test]
  fn unescape() {
    let data = [
      (r"", Some("")),
      (r"x", Some("x")),
      (r"\\", Some("\\")),
      (r"\\\n\r\t\f\u0001\b", Some("\\\n\r\t\x0c\u{0001}b")),
      (r"\", Some("\x00")),
      (r"\u", None),
      (r"\uasfd", None),
    ];
    for &(input, expected) in data.iter() {
      let actual = &super::unescape(input, 1);
      let is_match = match (expected, actual) {
        (Some(e), &Ok(ref a)) => e == a,
        (None, &Err(_)) => true,
        _ => false,
      };
      if !is_match {
        panic!("Failed when unescaping {:?}.  Expected {:?} but got {:?}", input, expected, actual);
      }
    }
  }

  #[test]
  fn properties_iter() {
    fn mk_comment(line_no: usize, text: &str) -> Line {
      Line::mk_comment(line_no, text.to_string())
    }
    fn mk_pair(line_no: usize, key: &str, value: &str) -> Line {
      Line::mk_pair(line_no, key.to_string(), value.to_string())
    }
    let data = [
      ("", vec![]),
      ("a=b", vec![mk_pair(1, "a", "b")]),
      ("a=b\nc=d\\\ne=f\ng=h\r#comment1\r\n#comment2\\\ni=j\\\n#comment3\n \n#comment4", vec![
        mk_pair(1, "a", "b"),
        mk_pair(2, "c", "de=f"),
        mk_pair(4, "g", "h"),
        mk_comment(5, "comment1"),
        mk_comment(6, "comment2\u{0}"),
        mk_pair(7, "i", "j#comment3"),
        mk_comment(10, "comment4"),
      ]),
      ("a = b\\\n  c, d ", vec![mk_pair(1, "a", "bc, d")]),
    ];
    for &(input, ref lines) in data.iter() {
      let mut iter = PropertiesIter::new(input.as_bytes());
      for line in lines {
        match (line, iter.next()) {
          (ref e, Some(Ok(ref a))) => if e != &a {
            panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", input, e, a);
          },
          (e, a) => panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", input, e, a),
        }
      }
      match iter.next() {
        None => (),
        a => panic!("Failure while processing {:?}.  Expected None, but was {:?}", input, a),
      }
    }
  }

  #[test]
  fn properties_writer_kv() {
    let data = [
      ("", "", "=\n"),
      ("a", "b", "a=b\n"),
      (" :=", " :=", "\\ \\:\\==\\ \\:\\=\n"),
      ("\u{1F41E}", "\u{1F41E}", "\\u1f41e=\\u1f41e\n"),
    ];
    for &(key, value, expected) in data.iter() {
      let mut buf = Vec::new();
      {
        let mut writer = PropertiesWriter::new(&mut buf);
        writer.write(key, value).unwrap();
      }
      match ISO_8859_1.decode(&buf, DecoderTrap::Strict) {
        Ok(actual) => {
          if expected != actual {
            panic!("Failure while processing key {:?} and value {:?}.  Expected {:?}, but was {:?}", key, value, expected, actual);
          }
        },
        Err(_) => panic!("Error decoding test output"),
      }
    }
  }

  #[test]
  fn properties_writer_comment() {
    let data = [
      ("", "# \n"),
      ("a", "# a\n"),
      (" :=", "#  :=\n"),
      ("\u{1F41E}", "# \\u1f41e\n"),
    ];
    for &(comment, expected) in data.iter() {
      let mut buf = Vec::new();
      {
        let mut writer = PropertiesWriter::new(&mut buf);
        writer.write_comment(comment).unwrap();
      }
      match ISO_8859_1.decode(&buf, DecoderTrap::Strict) {
        Ok(actual) => {
          if expected != actual {
            panic!("Failure while processing {:?}.  Expected {:?}, but was {:?}", comment, expected, actual);
          }
        },
        Err(_) => panic!("Error decoding test output"),
      }
    }
  }

  struct ErrorReader;

  impl Read for ErrorReader {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
      Err(io::Error::new(ErrorKind::InvalidData, "dummy error"))
    }
  }

  #[test]
  fn properties_error_line_number() {
    let data = [
      ("", 1),
      ("\n", 2),
      ("\r", 2),
      ("\r\n", 2),
      ("\\uxxxx", 1),
      ("\n\\uxxxx", 2),
      ("a\\\nb\n\\uxxxx", 3),
    ];
    for &(input, line_number) in data.iter() {
      let iter = PropertiesIter::new(input.as_bytes().chain(ErrorReader));
      let mut got_error = false;
      for line in iter {
        if let Err(e) = line {
          assert_eq!(e.line_number(), Some(line_number));
          got_error = true;
          break;
        }
      }
      assert!(got_error);
    }
  }
}
