#![allow(dead_code,unused_imports)]


#[macro_use] extern crate lazy_static;

use std::path::Path;
use std::fs::File;
use std::io::Read;

mod util;

mod name;
mod beta;
mod read;
mod ast;
mod parse;
mod core_forms;

mod form;
mod ty;



fn main() {
    let mut raw_input = String::new();
    File::open(&Path::new(&std::env::args().next()
               .expect("Expected first argument to be a file name")))
        .expect("Error opening file")
        .read_to_string(&mut raw_input)
        .expect("Error reading file");
        
}

#[test]
fn test() {
    assert!(true);
}
