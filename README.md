# Java properties for Rust

This is a library for reading and writing Java properties files in Rust.
The specification is taken from the [Properties](https://docs.oracle.com/javase/7/docs/api/java/util/Properties.html) documentation.
Where the documentation is ambiguous or incomplete, behavior is based on the behavior of `java.util.Properties`.

## Example
```rust
use java_properties::PropertiesIter;
use java_properties::PropertiesWriter;
use std::collections::HashMap;
use std::env::temp_dir;
use std::fs::File;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::prelude::*;

let mut file_name = temp_dir();
file_name.push("java-properties-test.properties");

// Writing
let mut map1 = HashMap::new();
map1.insert("a".to_string(), "b".to_string());
let mut f = try!(File::create(&file_name));
let mut writer = PropertiesWriter::new(BufWriter::new(f));
for (k, v) in map1.iter() {
  try!(writer.write(&k, &v));
}
writer.flush();

// Reading
let mut f = try!(File::open(&file_name));
let mut map2 = HashMap::new();
try!(PropertiesIter::new(BufReader::new(f)).read_into(|k, v| {
  map2.insert(k, v);
}));
assert_eq!(map1, map2);
```
