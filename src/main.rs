// Unseemly is a "core" typed language with (typed!) macros.
// You shouldn't write code in Unseemly.
// Instead, you should implement your programming language as Unseemly macros.

#![allow(dead_code,non_snake_case,unused_imports,non_upper_case_globals,unused_macros)]
// dead_code and unused_macros are hopefully temporary allowances
// non_snake_case is stylistic, unused_imports is inaccurate for `cargo check`
// non_upper_case_globals is stylistic; I like my thread_local!s lowercase.

// unstable; only for testing
// #![feature(log_syntax,trace_macros)]
// trace_macros!(true);

// unstable; only for testing
// #[macro_use] extern crate log;
#[macro_use] extern crate lazy_static;
extern crate num;
#[macro_use] extern crate custom_derive;
#[macro_use] extern crate quote;
extern crate rustyline;
extern crate regex;


use std::path::Path;
use std::fs::File;
use std::io::Read;

mod macros;

mod name; // should maybe be moved to `util`; `mbe` needs it

mod util;

mod alpha;
mod beta;
mod read;
mod ast;

mod earley;
mod parse;
mod unparse;

mod form;

mod ast_walk;
mod walk_mode;
mod ty;
mod ty_compare;

mod runtime;

mod core_forms;
mod core_type_forms;
mod core_syntax_forms;

use runtime::core_values;
use std::cell::RefCell;
use util::assoc::Assoc;
use name::{Name, n};
use ty::Ty;
use runtime::eval::{eval, Value};
use std::io::BufRead;

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
    let prelude_filename = format!("{}/.unseemly_prelude",
                                   std::env::home_dir().unwrap().display());
    let history_filename = format!("{}/.unseemly_history",
                                   std::env::home_dir().unwrap().display());

    if arguments.len() == 1 {
        let mut rl = rustyline::Editor::<ValueCompleter>::new();
        rl.set_completer(Some(ValueCompleter{}));

        let just_type = regex::Regex::new("^:t (.*)$").unwrap();
        let just_eval = regex::Regex::new("^:e (.*)$").unwrap();
        let canon_type = regex::Regex::new("^:tt (.*)$").unwrap();
        let assign_value = regex::Regex::new("^(\\w+)\\s*:=(.*)$").unwrap();
        let save_value = regex::Regex::new("^:s +((\\w+)\\s*:=(.*))$").unwrap();
        let assign_type = regex::Regex::new("^(\\w+)\\s*t=(.*)$").unwrap();
        let save_type = regex::Regex::new("^:s +((\\w+)\\s*t=(.*))$").unwrap();
        let comment = regex::Regex::new("^#").unwrap();

        println!("");
        println!("                  \x1b[1;38mUnseemly\x1b[0m");
        println!("    `<expr>` to (typecheck and) evaluate `<expr>`.");
        println!("    `:e <expr>` to evaluate `<expr>` without typechecking.");
        println!("    `<name> := <expr>` to bind a name for this session.");
        println!("    `:t <expr>` to synthesize the type of <expr>.");
        println!("    `:tt <type>` to canonicalize <type>.");
        println!("    `<name> t= <type>` to bind a type for this session.");
        println!("    `:s <name> := <expr>` to save a binding to the prelude for the future.");
        println!("    `:s <name> t= <expr>` to save a type binding to the prelude.");
        println!("    Command history is saved over sessions.");
        println!("    Tab-completion works on variables, and many Bash-isms work.");
        println!("");

        if let Ok(prelude_file) = File::open(&Path::new(&prelude_filename)) {
            let prelude = std::io::BufReader::new(prelude_file);
            for line in prelude.lines() {
                let line = line.unwrap();
                if comment.captures(&line).is_some() { /*comment*/
                } else if let Some(caps) = assign_value.captures(&line) {
                    if let Err(e) = assign_variable(caps.at(1).unwrap(), caps.at(2).unwrap()) {
                        println!("    Error in prelude line: {}\n    {}", line, e);
                    }
                } else if let Some(caps) = assign_type.captures(&line) {
                    if let Err(e) = assign_t_var(caps.at(1).unwrap(), caps.at(2).unwrap()) {
                        println!("    Error in prelude line: {}\n    {}", line, e);
                    }
                }
            }
            println!("    [prelude loaded from {}]", prelude_filename);
        }


        let _ = rl.load_history(&history_filename);
        while let Ok(line) = rl.readline("\x1b[1;36m≫\x1b[0m ") {
            // TODO: count delimiters, and allow line continuation!
            rl.add_history_entry(&line);

            let result_display = if let Some(caps) = just_type.captures(&line) {
                type_unseemly_program(caps.at(1).unwrap()).map(|x| format!("{}", x))
            } else if let Some(caps) = just_eval.captures(&line) {
                eval_unseemly_program_without_typechecking(caps.at(1).unwrap())
                    .map(|x| format!("{}", x))
            } else if let Some(caps) = canon_type.captures(&line) {
                canonicalize_type(caps.at(1).unwrap()).map(|x| format!("{}", x))
            } else if let Some(caps) = assign_value.captures(&line) {
                assign_variable(caps.at(1).unwrap(), caps.at(2).unwrap()).map(|x| format!("{}", x))
            } else if let Some(caps) = save_value.captures(&line) {
                match assign_variable(caps.at(2).unwrap(), caps.at(3).unwrap()) {
                    Ok(_) => {
                        use std::io::Write;
                        let mut prel_file = ::std::fs::OpenOptions::new().create(true).append(true)
                            .open(&prelude_filename).unwrap();
                        writeln!(prel_file, "{}", caps.at(1).unwrap()).unwrap();
                        Ok(format!("[saved to {}]", &prelude_filename))
                    }
                    Err(e) => Err(e)
                }
            } else if let Some(caps) = assign_type.captures(&line) {
                assign_t_var(caps.at(1).unwrap(), caps.at(2).unwrap()).map(|x| format!("{}", x))
            } else if let Some(caps) = save_type.captures(&line) {
                match assign_t_var(caps.at(2).unwrap(), caps.at(3).unwrap()) {
                    Ok(_) => {
                        use std::io::Write;
                        let mut prel_file = ::std::fs::OpenOptions::new().create(true).append(true)
                            .open(&prelude_filename).unwrap();
                        writeln!(prel_file, "{}", caps.at(1).unwrap()).unwrap();
                        Ok(format!("[saved to {}]", &prelude_filename))
                    }
                    Err(e) => Err(e)
                }
            } else {
                eval_unseemly_program(&line).map(|x| format!("{}", x))
            };


            match result_display {
                Ok(v) => println!("\x1b[1;32m≉\x1b[0m {}", v),
                Err(s) => println!("\x1b[1;31m✘\x1b[0m {}", s)
            }
        }
        rl.save_history(&history_filename).unwrap();
    } else {
        let filename = &arguments[1];

        let mut raw_input = String::new();
        File::open(&Path::new(filename))
            .expect("Error opening file")
            .read_to_string(&mut raw_input)
            .expect("Error reading file");

        let result = eval_unseemly_program(&raw_input);

        match result {
            Ok(v) => println!("{}", v),
            Err(e) => println!("\x1b[1;31m✘\x1b[0m {:?}", e)
        }
    }
}

fn assign_variable(name: &str, expr: &str) -> Result<Value, String> {
    let res = eval_unseemly_program(expr);

    if let Ok(ref v) = res {
        let ty = type_unseemly_program(expr).unwrap();
        ty_env.with(|tys| {
            val_env.with(|vals| {
                let new_tys = tys.borrow().set(n(name), ty).clone();
                let new_vals = vals.borrow().set(n(name), v.clone());
                *tys.borrow_mut() = new_tys;
                *vals.borrow_mut() = new_vals;
            })
        })
    }
    res
}

fn assign_t_var(name: &str, t: &str) -> Result<ty::Ty, String> {
    let tokens = try!(read::read_tokens(t));

    let ast = try!(parse::parse(&parse::FormPat::Call(n("Type")),
                                &core_forms::get_core_forms(), &tokens).map_err(|e| e.msg));

    let res = ty_env.with(|tys| {
        ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:?}", e))
    });

    if let Ok(ref t) = res {
        ty_env.with(|tys| {
            let new_tys = tys.borrow().set(n(name), t.clone());
            *tys.borrow_mut() = new_tys;
        })
    }

    res
}

fn canonicalize_type(t: &str) -> Result<ty::Ty, String> {
    let tokens = try!(read::read_tokens(t));

    let ast = try!(parse::parse(&parse::FormPat::Call(n("Type")),
                                &core_forms::get_core_forms(), &tokens).map_err(|e| e.msg));

    ty_env.with(|tys| {
        ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:?}", e))
    })
}

fn type_unseemly_program(program: &str) -> Result<ty::Ty, String> {
    let tokens = try!(read::read_tokens(program));


    let ast = try!(
        parse::parse(&core_forms::outermost_form(), &core_forms::get_core_forms(), &tokens)
            .map_err(|e| e.msg));

    ty_env.with(|tys| {
        ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:?}", e))
    })
}

fn eval_unseemly_program_without_typechecking(program: &str) -> Result<Value, String> {
    let tokens = try!(read::read_tokens(program));

    let ast : ::ast::Ast = try!(
        parse::parse(&core_forms::outermost_form(), &core_forms::get_core_forms(), &tokens)
            .map_err(|e| e.msg));

    val_env.with(|vals| {
        eval(&ast, vals.borrow().clone()).map_err(|_| "???".to_string())
    })
}


fn eval_unseemly_program(program: &str) -> Result<Value, String> {
    let tokens = try!(read::read_tokens(program));

    let ast : ::ast::Ast = try!(
        parse::parse(&core_forms::outermost_form(), &core_forms::get_core_forms(), &tokens)
            .map_err(|e| e.msg));

    let _type = try!(ty_env.with(|tys| {
        ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:?}", e))
    }));


    val_env.with(|vals| {
        eval(&ast, vals.borrow().clone()).map_err(|_| "???".to_string())
    })
}

#[test]
fn simple_end_to_end_eval() {
    assert_eq!(eval_unseemly_program("(zero? zero)"), Ok(val!(b true)));

    assert_eq!(eval_unseemly_program("(plus one one)"), Ok(val!(i 2)));

    assert_eq!(eval_unseemly_program("(.[x : Int  y : Int . (plus x y)]. one one)"),
               Ok(val!(i 2)));

    assert_eq!(eval_unseemly_program(
        "((fix .[ again : [ -> [ Int -> Int ]] .
            .[ n : Int .
                match (zero? n) {
                    +[True]+ => one
                    +[False]+ => (times n ((again) (minus n one))) } ]. ].) five)"),
        Ok(val!(i 120)));
}


#[test]
fn end_to_end_int_list_tools() {

    assert_m!(assign_t_var("IntList", "mu_type IntList . enum { Nil () Cons (Int IntList) }"),
        Ok(_));

    assert_m!(assign_t_var("IntListUF", "enum { Nil () Cons (Int IntList) }"),
        Ok(_));

    assert_m!(assign_variable(
        "mt_ilist", "fold +[Nil]+ : enum { Nil () Cons (Int IntList) } : IntList"),
        Ok(_));

    assert_m!(assign_variable("3_ilist", "fold +[Cons three mt_ilist]+ : IntListUF : IntList"),
        Ok(_));

    assert_m!(assign_variable("23_ilist", "fold +[Cons two 3_ilist]+ : IntListUF : IntList"),
        Ok(_));

    assert_m!(assign_variable("123_ilist", "fold +[Cons one 23_ilist]+ : IntListUF : IntList"),
        Ok(_));

    assert_m!(assign_variable("sum_int_list",
        "(fix .[again : [-> [IntList -> Int]] .
             .[ lst : IntList .
                 match unfold lst {
                     +[Nil]+ => zero +[Cons hd tl]+ => (plus hd ((again) tl))} ]. ]. )"),
        Ok(_));

    assert_eq!(eval_unseemly_program("(sum_int_list 123_ilist)"), Ok(val!(i 6)));

    assert_m!(assign_variable("int_list_len",
        "(fix .[again : [-> [IntList -> Int]] .
             .[ lst : IntList .
                 match unfold lst {
                     +[Nil]+ => zero +[Cons hd tl]+ => (plus one ((again) tl))} ]. ].)"),
        Ok(_));

    assert_eq!(eval_unseemly_program("(int_list_len 123_ilist)"), Ok(val!(i 3)));

}

#[test]
fn end_to_end_list_tools() {
    assert_m!(
        assign_t_var("List", "forall T . mu_type List . enum { Nil () Cons (T List <[T]<) }"),
        Ok(_));

    assert_m!(
        assign_t_var("ListUF", "forall T . enum { Nil () Cons (T List <[T]<) }"),
        Ok(_));

    assert_m!(assign_variable(
        "mt_list", "fold +[Nil]+ : enum { Nil () Cons (Int List <[Int]<) } : List <[Int]<"),
        Ok(_));

    assert_m!(
        assign_variable("3_list", "fold +[Cons three mt_list]+ : ListUF <[Int]< : List <[Int]<"),
        Ok(_));

    assert_m!(
        assign_variable("23_list", "fold +[Cons two 3_list]+ : ListUF <[Int]< : List <[Int]<"),
        Ok(_));

    assert_m!(
        assign_variable("123_list", "fold +[Cons one 23_list]+ : ListUF <[Int]< : List <[Int]<"),
        Ok(_));

    assert_m!(assign_variable("list_len",
        "forall S . (fix .[again : [-> [List <[S]< -> Int]] .
            .[ lst : List <[S]< .
                match unfold lst {
                    +[Nil]+ => zero
                    +[Cons hd tl]+ => (plus one ((again) tl))} ]. ].)"),
        Ok(_));

    assert_eq!(eval_unseemly_program("(list_len 123_list)"), Ok(val!(i 3)));

    assert_m!(assign_variable("map",
        "forall T S . (fix  .[again : [-> [List <[T]<  [T -> S] -> List <[S]< ]] .
            .[ lst : List <[T]<   f : [T -> S] .
                match unfold lst {
                    +[Nil]+ => fold +[Nil]+ : ListUF <[S]< : List <[S]<
                    +[Cons hd tl]+ =>
                      fold +[Cons (f hd) ((again) tl f)]+ : ListUF <[S]< : List <[S]< } ]. ].)"),
        Ok(_));
    // TODO: what should even happen if you have `forall` not on the "outside"?
    // It should probably be an error to have a value typed with an underdetermined type.


    // TODO: it's way too much of a pain to define each different expected result list.
    assert_m!(eval_unseemly_program("(map 123_list .[x : Int . (plus x one)]. )"), Ok(_));

    assert_m!(eval_unseemly_program("(map 123_list .[x : Int . (equal? x two)]. )"), Ok(_));
}

#[test]
fn end_to_end_quotation() {
    assert_m!(
        eval_unseemly_program("'[Expr | .[ x : Int . x ]. ]'"),
        Ok(_)
    );

    assert_m!(
        eval_unseemly_program("'[Expr | (plus five five) ]'"),
        Ok(_)
    );


    assert_m!(
        eval_unseemly_program("'[Expr | '[Expr | (plus five five) ]' ]'"),
        Ok(_)
    );
//≫ .[s : Expr <[Int]< . '[Expr | ( ,[Expr | s], '[Expr | ,[Expr | s], ]')]' ].

}
