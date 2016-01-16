extern crate encoding;

use encoding::Encoding;
use encoding::DecoderTrap;
use encoding::all::ISO_8859_1;
use encoding::types::RawDecoder;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::io;
use std::io::BufRead;
use std::io::Bytes;
use std::io::ErrorKind;
use std::io::Lines;
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
                Err(e) => return Some(Err(io::Error::new(ErrorKind::InvalidData, "Error reading ISO-8859-1 encoding"))),
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

// We can't use BufRead.lines() because it doesn't use the proper line endings
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
    loop {
      match self.physical_lines.next() {
        Some(Err(e)) => return Some(Err(e)),
        Some(Ok(NaturalLine(mut line))) => {
          buf.push_str(&line);
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
    }
  }
}

/////////////////////

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
  use std::io;
  use std::io::BufRead;
  use std::io::BufReader;
  use std::io::Read;
  use super::CR;
  use super::LF;
  use super::LogicalLine;
  use super::LogicalLines;
  use super::NaturalLine;
  use super::NaturalLines;

  const BS: u8 = 92; // backslash
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
    ];
    for &(ref input_lines, ref lines) in data.iter() {
      let input_natural_lines: Vec<io::Result<NaturalLine>> =
            input_lines.iter().map(|x| Ok(NaturalLine(x.to_string()))).collect();
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
}
