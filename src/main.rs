#![allow(dead_code,non_snake_case,unused_imports)]
// dead_code is a hopefully temporary allowance
// non_snake_case is stylistic, unused_imports is inaccurate because of macros

// unstable; only for testing
// #![feature(log_syntax,trace_macros)]
// trace_macros!(true);

// unstable; only for testing
// #[macro_use] extern crate log;
#[macro_use] extern crate lazy_static;
extern crate num;
#[macro_use] extern crate custom_derive;

use std::path::Path;
use std::fs::File;
use std::io::Read;

mod macros;

mod name; // should maybe be moved to `util`; `mbe` needs it

mod util;

mod beta;
mod read;
mod ast;

mod earley;
mod parse;

mod form;

mod ast_walk;
mod ty;

mod runtime;

mod core_type_forms;
mod core_forms;


use runtime::reify::Reifiable;

fn main() {
    let mut raw_input = String::new();
    File::open(&Path::new(&std::env::args().next()
               .expect("Expected first argument to be a file name")))
        .expect("Error opening file")
        .read_to_string(&mut raw_input)
        .expect("Error reading file");
}

