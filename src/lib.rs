//! This is all based on https://docs.oracle.com/javase/7/docs/api/java/util/Properties.html.

extern crate encoding;
extern crate regex;

use encoding::Encoding;
use encoding::DecoderTrap;
use encoding::all::ISO_8859_1;
use regex::Regex;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::io;
use std::io::BufRead;
use std::io::Bytes;
use std::io::ErrorKind;
use std::io::Read;
use std::iter::Peekable;

/////////////////////

#[derive(Debug)]
pub struct PropertiesError {
  description: String,
  cause: Option<Box<Error+Send+Sync>>,
}

impl PropertiesError {
  fn new(description: &str, cause: Option<Box<Error+Send+Sync>>) -> Self {
    PropertiesError {
      description: description.to_string(),
      cause: cause,
    }
  }
}

impl Error for PropertiesError {
  fn description(&self) -> &str {
    &self.description
  }
}

impl Display for PropertiesError {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    Display::fmt(&self.description, f)
  }
}

/////////////////////

#[derive(PartialEq,Eq,Debug)]
struct NaturalLine(String);

// We can't use BufRead.lines() because it doesn't use the proper line endings
struct NaturalLines<R: Read> {
  bytes: Peekable<Bytes<R>>,
  eof: bool,
}

impl<R: Read> NaturalLines<R> {
  fn new(reader: R) -> Self {
    NaturalLines {
      bytes: reader.bytes().peekable(),
      eof: false,
    }
  }
}

const LF: u8 = 10;
const CR: u8 = 13;

impl< R: Read> Iterator for NaturalLines<R> {
  type Item = io::Result<NaturalLine>;

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
                return Some(Ok(NaturalLine(buf)));
              },
              LF => return Some(Ok(NaturalLine(buf))),
              _ => match ISO_8859_1.decode(&[b], DecoderTrap::Strict) {
                Ok(s) => buf.push_str(&s),
                Err(_) => return Some(Err(io::Error::new(ErrorKind::InvalidData, "Error reading ISO-8859-1 encoding"))),
              },
            };
          },
          Err(e) => return Some(Err(e)),
        },
        None => {
          self.eof = true;
          return Some(Ok(NaturalLine(buf)));
        },
      }
    }
  }
}

/////////////////////

#[derive(PartialEq,Eq,Debug)]
struct LogicalLine(String);

struct LogicalLines<I: Iterator<Item=io::Result<NaturalLine>>> {
  physical_lines: I,
  eof: bool,
  comment_re: Regex,
}

impl<I: Iterator<Item=io::Result<NaturalLine>>> LogicalLines<I> {
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

impl<I: Iterator<Item=io::Result<NaturalLine>>> Iterator for LogicalLines<I> {
  type Item = io::Result<LogicalLine>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.eof {
      return None;
    }
    let mut buf = String::new();
    let mut first = true;
    loop {
      match self.physical_lines.next() {
        Some(Err(e)) => return Some(Err(e)),
        Some(Ok(NaturalLine(line))) => {
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
            return Some(Ok(LogicalLine(buf)));
          }
          if count_ending_backslashes(&line) % 2 == 1 {
            buf.pop();
          } else {
            return Some(Ok(LogicalLine(buf)));
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

/////////////////////

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

pub fn load(reader: &mut BufRead) -> Result<HashMap<String, String>, PropertiesError> {
  let map = HashMap::new();
  let mut lines = LogicalLines::new(NaturalLines::new(reader));
  loop {
    match lines.next() {
      Some(line) => (), // TODO
      None => break,
    }
  }
  Ok(map)
}

/////////////////////

#[cfg(test)]
mod tests {
  use super::CR;
  use super::LF;
  use super::LogicalLine;
  use super::LogicalLines;
  use super::NaturalLine;
  use super::NaturalLines;
  use super::ParsedLine;

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
      for line in lines {
        match (line.to_string(), iter.next()) {
          (e, Some(Ok(NaturalLine(a)))) => if e != a {
            panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", bytes, e, a);
          },
          (e, a) => panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", bytes, e, a),
        }
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
      let mut iter = LogicalLines::new(input_lines.iter().map(|x| Ok(NaturalLine(x.to_string()))));
      for line in lines {
        match (line.to_string(), iter.next()) {
          (e, Some(Ok(LogicalLine(a)))) => if e != a {
            panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", input_lines, e, a);
          },
          (e, a) => panic!("Failure while processing {:?}.  Expected Some(Ok({:?})), but was {:?}", input_lines, e, a),
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
}
