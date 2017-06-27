// Unseemly is a "core" typed language with (typed!) macros.
// You shouldn't write code in Unseemly.
// Instead, you should implement your programming language as Unseemly macros.


#![allow(dead_code,non_snake_case,unused_imports,non_upper_case_globals, unused_macros)]
// dead_code and unused_macros are hopefully temporary allowances
// non_snake_case is stylistic, unused_imports is inaccurate because of macros
// non_upper_case_globals is stylistic; I like my thread_local!s lowercase.

// unstable; only for testing
// #![feature(log_syntax,trace_macros)]
// trace_macros!(true);

// unstable; only for testing
// #[macro_use] extern crate log;
#[macro_use] extern crate lazy_static;
extern crate num;
#[macro_use] extern crate custom_derive;
#[macro_use] extern crate mac;
#[macro_use] extern crate quote;
extern crate rustyline;

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
mod ty_compare;

mod runtime;

mod core_type_forms;
mod core_forms;


use runtime::reify::Reifiable;

fn main() {
    let arguments : Vec<String> = std::env::args().collect();

    if arguments.len() == 1 {
        let mut rl = rustyline::Editor::<()>::new();

        let _ = rl.load_history("/tmp/unseemly_interp_history");
        while let Ok(line) = rl.readline("≫ ") {
            // TODO: count delimiters, and allow line continuation!
            rl.add_history_entry(&line);
            print!("≉ {}\n", eval_unseemly_program(&line));
        }
        let _ = rl.save_history("/tmp/unseemly_interp_history").unwrap();
    } else {
        let ref filename = arguments[1];

        let mut raw_input = String::new();
        File::open(&Path::new(filename))
            .expect("Error opening file")
            .read_to_string(&mut raw_input)
            .expect("Error reading file");

        let result = eval_unseemly_program(&raw_input);

        print!("{:?}\n", result);
    }
}

fn eval_unseemly_program(program: &str) -> runtime::eval::Value {
    let tokens = read::read_tokens(program);

    let ast = core_forms::core_forms.with(|cse| {
        parse::parse(&core_forms::outermost_form(), &cse, &tokens).unwrap()
    });

    let _type = ty::synth_type(&ast, runtime::core_values::core_types()).unwrap();

    runtime::eval::eval(&ast, runtime::core_values::core_values()).unwrap()
}

#[test]
fn end_to_end_eval() {
    assert_eq!(eval_unseemly_program("(zero? zero)"), val!(b true));

    assert_eq!(eval_unseemly_program("(plus one one)"), val!(i 2));

    assert_eq!(eval_unseemly_program("(.[x : int  y : int . (plus x y)]. one one)"),
               val!(i 2));
}
