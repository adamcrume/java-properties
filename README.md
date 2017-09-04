# Java properties for Rust

This is a library for reading and writing Java properties files in Rust.
The specification is taken from the [Properties](https://docs.oracle.com/javase/7/docs/api/java/util/Properties.html) documentation.
Where the documentation is ambiguous or incomplete, behavior is based on the behavior of `java.util.Properties`.

## Example
```rust
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
let mut f = File::create(&file_name)?;
write(BufWriter::new(f), &map1)?;

// Reading
let mut f = File::open(&file_name)?;
let map2 = read(BufReader::new(f))?;
assert_eq!(src_map1, dst_map1);
```
