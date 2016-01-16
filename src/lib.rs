extern crate encoding;

use encoding::Encoding;
use encoding::DecoderTrap;
use encoding::all::ISO_8859_1;
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
}

impl<I: Iterator<Item=io::Result<NaturalLine>>> LogicalLines<I> {
  fn new(physical_lines: I) -> Self {
    LogicalLines {
      physical_lines: physical_lines,
      eof: false,
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

// Note that this is not the same as char.is_whitespace.  This is correct.
fn is_whitespace(c: char) -> bool {
  match c {
    ' ' | '\t' | '\x0C' | '\n' | '\r' => true,
    _ => false,
  }
}

// This only splits the line and does not trim whitespace or evaluate escape sequences.
fn split_line(line: &str) -> (&str, &str) {
  // This code is complicated because the format is ridiculously and unnecessarily complicated.
  // We can't just split on the first colon, equal sign, or whitespace because we don't want to split "a = b" into "a" and "= b".
  // Therefore, we first try splitting by ":" or "=", then by whitespace.

  // Try splitting by ":" or "="
  let mut escaped = false;
  for (i, c) in line.char_indices() {
    if escaped {
      escaped = false;
    } else if c == '\\' {
      escaped = true;
    } else if c == ':' || c == '=' {
      return (&line[..i], &line[(i + 1)..]);
    }
  }

  // Try splitting by whitespace
  let mut escaped = false;
  let mut found_non_whitespace = false;
  for (i, c) in line.char_indices() {
    if escaped {
      escaped = false;
    } else if c == '\\' {
      escaped = true;
      found_non_whitespace = true;
    } else if is_whitespace(c) {
      if found_non_whitespace {
        return (&line[..i], &line[(i + 1)..]);
      }
    } else {
      found_non_whitespace = true;
    }
  }

  // If there is no separator, the whole line is the key, and the empty string is the value.
  (line, "")
}

fn trim_unescaped_whitespace(s: &str) -> &str {
  fn ltrim(s: &str) -> &str {
    for (i, c) in s.char_indices() {
      if !is_whitespace(c) {
        return &s[i..];
      }
    }
    "" // all whitespace
  }

  fn rtrim(s: &str) -> &str {
    let mut ix = 0; // index of first whitespace character after last non-whitespace character
    let mut escaped = false;
    let mut last_was_non_whitespace = true;
    for (i, c) in s.char_indices() {
      if escaped {
        escaped = false;
        last_was_non_whitespace = true;
      } else if c == '\\' {
        escaped = true;
      } else if is_whitespace(c) {
        if last_was_non_whitespace {
          ix = i;
        }
        last_was_non_whitespace = false;
      } else {
        last_was_non_whitespace = true;
      }
    }
    if last_was_non_whitespace {
      s
    } else {
      &s[..ix]
    }
  }

  ltrim(rtrim(s))
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
  }

  #[test]
  fn split_line() {
    let data = [
      ("a", "a", ""),
      ("a = b", "a ", " b"),
      ("a : b", "a ", " b"),
      ("a b", "a", "b"),
      (" a = b", " a ", " b"),
      (" a : b", " a ", " b"),
      (" a b", " a", "b"),
      ("a:=b", "a", "=b"),
      ("a=:b", "a", ":b"),
      ("a\\ \\:\\=b c", "a\\ \\:\\=b", "c"),
      ("a\\ \\:\\=b=c", "a\\ \\:\\=b", "c"),
      ("\\  b", "\\ ", "b"),
    ];
    for &(line, key, value) in data.iter() {
      let (k, v) = super::split_line(line);
      if (key, value) != (k, v) {
        panic!("Failed when splitting {:?}.  Expected {:?} and {:?}, but got {:?} and {:?}", line, key, value, k, v);
      }
    }
  }

  #[test]
  fn trim_unescaped_whitespace() {
    let data = [
      ("", ""),
      (" ", ""),
      ("x", "x"),
      (" x x ", "x x"),
      ("  xx  xx  ", "xx  xx"),
      (" \\  ", "\\ "),
      (" \u{1F41E} \u{1F41E} ", "\u{1F41E} \u{1F41E}"),
    ];
    for &(raw, trimmed) in data.iter() {
      let t = super::trim_unescaped_whitespace(raw);
      if trimmed != t {
        panic!("Failed when trimming {:?}.  Expected {:?} but got {:?}", raw, trimmed, t);
      }
    }
  }
}
