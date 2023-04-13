# Java properties for Rust

This is a library for reading and writing Java properties files in Rust.
The specification is taken from the [Properties](https://docs.oracle.com/javase/7/docs/api/java/util/Properties.html) documentation.
Where the documentation is ambiguous or incomplete, behavior is based on the behavior of `java.util.Properties`.

## Example
```rust
#![allow(unused)]

use java_properties::read;
use java_properties::write;
use java_properties::PropertiesIter;
use java_properties::PropertiesWriter;
use std::collections::HashMap;
use std::env::temp_dir;
use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;
use std::io::BufWriter;

fn main() -> std::result::Result<(), java_properties::PropertiesError> {
    let mut file_name = temp_dir();
    file_name.push("java-properties-test.properties");

    // Writing simple
    let mut src_map1 = HashMap::new();
    src_map1.insert("a".to_string(), "b".to_string());
    let mut f = File::create(&file_name)?;
    write(BufWriter::new(f), &src_map1)?;

    // Reading simple
    let mut f2 = File::open(&file_name)?;
    let dst_map1 = read(BufReader::new(f2))?;
    assert_eq!(src_map1, dst_map1);

    // Writing advanced
    let mut src_map2 = HashMap::new();
    src_map2.insert("c".to_string(), "d".to_string());
    let mut f = File::create(&file_name)?;
    let mut writer = PropertiesWriter::new(BufWriter::new(f));
    for (k, v) in &src_map2 {
        writer.write(&k, &v)?;
    }
    writer.flush();

    // Reading advanced
    let mut f = File::open(&file_name)?;
    let mut dst_map2 = HashMap::new();
    PropertiesIter::new(BufReader::new(f)).read_into(|k, v| {
        dst_map2.insert(k, v);
    })?;
    assert_eq!(src_map2, dst_map2);

    println!("file: {:#?}", file_name.as_path());

    Ok(())
}
```
