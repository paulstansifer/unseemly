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
extern crate regex;


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

use runtime::core_values;
use std::cell::RefCell;
use util::assoc::Assoc;
use name::{Name, n};
use ty::Ty;
use ast::Ast;
use runtime::eval::{eval, Value};

thread_local! {
    pub static ty_env : RefCell<Assoc<Name, Ty>> = RefCell::new(core_values::core_types());
    pub static val_env : RefCell<Assoc<Name, Value>> = RefCell::new(core_values::core_values());
}

struct ValueCompleter {}

impl rustyline::completion::Completer for ValueCompleter {
    fn complete(&self, line: &str, pos: usize)
            -> Result<(usize, Vec<String>), rustyline::error::ReadlineError> {
        let mut break_chars = std::collections::BTreeSet::new();
        break_chars.extend(vec!['[', '(', '{', ' ', '}', ')',  ']'].iter());
        let mut res = vec![];
        let (start, word_so_far) = rustyline::completion::extract_word(line, pos, &break_chars);
        val_env.with(|vals| {
            let vals = vals.borrow();
            for k in vals.iter_keys() {
                if k.sp().starts_with(word_so_far) { res.push(k.sp()); }
            }
        });
        Ok((start, res))
    }
}

fn main() {
    let arguments : Vec<String> = std::env::args().collect();

    if arguments.len() == 1 {
        let mut rl = rustyline::Editor::<ValueCompleter>::new();
        rl.set_completer(Some(ValueCompleter{}));

        let just_type = regex::Regex::new("^:t (.*)$").unwrap();
        let assign_value = regex::Regex::new("^(\\w+)\\s*:=(.*)$").unwrap();

        print!("\n");
        print!("                 \x1b[1;32mUnseemly\x1b[0m\n");
        print!("   `:t <expr>` to synthesize the type of <expr>.\n");
        print!("   `<name> := <expr>` to bind a name for this session.\n");
        print!("   Tab-completion works on variables, and many Bash-isms work.\n");

        let _ = rl.load_history("/tmp/unseemly_interp_history");
        while let Ok(line) = rl.readline("\x1b[1;36m≫\x1b[0m ") {
            // TODO: count delimiters, and allow line continuation!
            rl.add_history_entry(&line);

            let result_display = if let Some(caps) = just_type.captures(&line) {
                type_unseemly_program(caps.at(1).unwrap()).map(|x| format!("{}", x))
            } else if let Some(caps) = assign_value.captures(&line) {
                let expr = caps.at(2).unwrap();
                let res = eval_unseemly_program(expr);

                if let Ok(ref v) = res {
                    let var = n(caps.at(1).unwrap());
                    let ty = type_unseemly_program(expr).unwrap();
                    ty_env.with(|tys| {
                        val_env.with(|vals| {
                            let new_tys = tys.borrow().set(var, ty).clone();
                            let new_vals = vals.borrow().set(var, v.clone());
                            *tys.borrow_mut() = new_tys;
                            *vals.borrow_mut() = new_vals;
                        })
                    })
                }

                res.map(|x| format!("{}", x))
            } else {
                eval_unseemly_program(&line).map(|x| format!("{}", x))
            };


            match result_display {
                Ok(v) => print!("\x1b[1;32m≉\x1b[0m {}\n", v),
                Err(s) => print!("\x1b[1;31m✘\x1b[0m {}\n", s)
            }
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

fn type_unseemly_program(program: &str) -> Result<ty::Ty, String> {
    let tokens = read::read_tokens(program);


    let ast = try!(
        parse::parse(&core_forms::outermost_form(), &core_forms::get_core_forms(), &tokens)
            .map_err(|e| e.msg));

    ty_env.with(|types| {
        ty::synth_type(&ast, types.borrow().clone()).map_err(|e| format!("{:?}", e))
    })
}

fn eval_unseemly_program(program: &str) -> Result<runtime::eval::Value, String> {
    let tokens = read::read_tokens(program);

    let ast : ::ast::Ast = try!(
        parse::parse(&core_forms::outermost_form(), &core_forms::get_core_forms(), &tokens)
            .map_err(|e| e.msg));

    let _type = try!(ty_env.with(|types| {
        ty::synth_type(&ast, types.borrow().clone()).map_err(|e| format!("{:?}", e))
    }));

    val_env.with(|vals| {
        runtime::eval::eval(&ast, vals.borrow().clone()).map_err(|_| "???".to_string())
    })
}

#[test]
fn end_to_end_eval() {
    assert_eq!(eval_unseemly_program("(zero? zero)"), Ok(val!(b true)));

    assert_eq!(eval_unseemly_program("(plus one one)"), Ok(val!(i 2)));

    assert_eq!(eval_unseemly_program("(.[x : int  y : int . (plus x y)]. one one)"),
               Ok(val!(i 2)));
}
