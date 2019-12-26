// Unseemly is a "core" typed language with (typed!) macros.
// You shouldn't write code in Unseemly.
// Instead, you should implement your programming language as Unseemly macros.

#![allow(dead_code, unused_macros, non_snake_case, unused_imports, non_upper_case_globals)]
// dead_code and unused_macros are hopefully temporary allowances
// non_snake_case is stylistic, unused_imports is inaccurate for `cargo check`
// non_upper_case_globals is stylistic; I like my thread_local!s lowercase.
#![recursion_limit = "128"] // Yikes.

// for testing; requires `cargo +nightly`
// #![feature(log_syntax, trace_macros)]
// trace_macros!(true);

// TODO: turn these into `use` statements in the appropriate places
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate custom_derive;
#[macro_use]
extern crate quote;


use std::{fs::File, io::Read, path::Path};

mod macros;

mod name; // should maybe be moved to `util`; `mbe` needs it

mod util;

mod alpha;
mod ast;
mod beta;
mod read;

mod earley;
mod grammar;
mod unparse;

mod form;

mod ast_walk;
mod expand;
mod ty;
mod ty_compare;
mod walk_mode;

mod runtime;

mod core_forms;
mod core_macro_forms;
mod core_qq_forms;
mod core_type_forms;

use crate::{
    ast::Ast,
    name::{n, Name},
    runtime::{
        core_values,
        eval::{eval, Value},
    },
    ty::Ty,
    util::assoc::Assoc,
};
use std::{borrow::Cow, cell::RefCell, io::BufRead};

thread_local! {
    pub static ty_env : RefCell<Assoc<Name, Ty>> = RefCell::new(core_values::core_types());
    pub static val_env : RefCell<Assoc<Name, Value>> = RefCell::new(core_values::core_values());
}

struct LineHelper {
    highlighter: rustyline::highlight::MatchingBracketHighlighter,
}

impl LineHelper {
    fn new() -> LineHelper {
        LineHelper { highlighter: rustyline::highlight::MatchingBracketHighlighter::new() }
    }
}

impl rustyline::completion::Completer for LineHelper {
    type Candidate = String;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctxt: &rustyline::Context,
    ) -> Result<(usize, Vec<String>), rustyline::error::ReadlineError>
    {
        let mut res = vec![];
        let (start, word_so_far) = rustyline::completion::extract_word(line, pos, None, b"[({ })]");
        val_env.with(|vals| {
            let vals = vals.borrow();
            for k in vals.iter_keys() {
                if k.sp().starts_with(word_so_far) {
                    res.push(k.sp());
                }
            }
        });
        Ok((start, res))
    }
}

impl rustyline::hint::Hinter for LineHelper {
    fn hint(&self, _line: &str, _pos: usize, _ctxt: &rustyline::Context) -> Option<String> { None }
}

impl rustyline::highlight::Highlighter for LineHelper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }
    fn highlight_prompt<'p>(&self, prompt: &'p str) -> Cow<'p, str> {
        self.highlighter.highlight_prompt(prompt)
    }
    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        self.highlighter.highlight_hint(hint)
    }
    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: rustyline::config::CompletionType,
    ) -> Cow<'c, str>
    {
        self.highlighter.highlight_candidate(candidate, completion)
    }
    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl rustyline::Helper for LineHelper {}

#[cfg_attr(tarpaulin, skip)]
fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let prelude_filename = format!("{}/.unseemly_prelude", dirs::home_dir().unwrap().display());
    let history_filename = format!("{}/.unseemly_history", dirs::home_dir().unwrap().display());

    if arguments.len() == 1 {
        let mut rl = rustyline::Editor::<LineHelper>::new();
        rl.set_helper(Some(LineHelper::new()));

        let just_parse = regex::Regex::new("^:p (.*)$").unwrap();

        let just_type = regex::Regex::new("^:t (.*)$").unwrap();
        let just_eval = regex::Regex::new("^:e (.*)$").unwrap();
        let type_and_expand = regex::Regex::new("^:x (.*)$").unwrap();
        let canon_type = regex::Regex::new("^:tt (.*)$").unwrap();
        let assign_value = regex::Regex::new("^(\\w+)\\s*:=(.*)$").unwrap();
        let save_value = regex::Regex::new("^:s +((\\w+)\\s*:=(.*))$").unwrap();
        let assign_type = regex::Regex::new("^(\\w+)\\s*t=(.*)$").unwrap();
        let save_type = regex::Regex::new("^:s +((\\w+)\\s*t=(.*))$").unwrap();
        let comment = regex::Regex::new("^#").unwrap();

        println!();
        println!("                  \x1b[1;38mUnseemly\x1b[0m");
        println!("    `<expr>` to (typecheck and expand and) evaluate `<expr>`.");
        println!("    `:x <expr>` to (typecheck and) expand `<expr>`.");
        println!("    `:e <expr>` to (expand and) evaluate `<expr>` without typechecking.");
        println!("    `<name> := <expr>` to bind a name for this session.");
        println!("    `:t <expr>` to synthesize the type of <expr>.");
        println!("    `:tt <type>` to canonicalize <type>.");
        println!("    `<name> t= <type>` to bind a type for this session.");
        println!("    `:s <name> := <expr>` to save a binding to the prelude for the future.");
        println!("    `:s <name> t= <expr>` to save a type binding to the prelude.");
        println!("    `:p <expr>` to parse `<expr>` and print its debug AST output.");
        println!("    Command history is saved over sessions.");
        println!("    Tab-completion works on variables, and lots of Bash-isms work.");
        println!();

        if let Ok(prelude_file) = File::open(&Path::new(&prelude_filename)) {
            let prelude = std::io::BufReader::new(prelude_file);
            for line in prelude.lines() {
                let line = line.unwrap();
                if comment.captures(&line).is_some() {
                    // comment
                } else if let Some(caps) = assign_value.captures(&line) {
                    if let Err(e) = assign_variable(&caps[1], &caps[2]) {
                        println!("    Error in prelude line: {}\n    {}", line, e);
                    }
                } else if let Some(caps) = assign_type.captures(&line) {
                    if let Err(e) = assign_t_var(&caps[1], &caps[2]) {
                        println!("    Error in prelude line: {}\n    {}", line, e);
                    }
                }
            }
            println!("    [prelude loaded from {}]", prelude_filename);
        }

        let _ = rl.load_history(&history_filename);
        while let Ok(line) = rl.readline("\x1b[1;36m≫\x1b[0m ") {
            // TODO: count delimiters, and allow line continuation!
            rl.add_history_entry(line.clone());

            let result_display = if let Some(caps) = just_parse.captures(&line) {
                parse_unseemly_program(&caps[1])
            } else if let Some(caps) = just_type.captures(&line) {
                type_unseemly_program(&caps[1]).map(|x| format!("{}", x))
            } else if let Some(caps) = just_eval.captures(&line) {
                eval_unseemly_program_without_typechecking(&caps[1]).map(|x| format!("{}", x))
            } else if let Some(caps) = type_and_expand.captures(&line) {
                type_and_expand_unseemly_program(&caps[1]).map(|x| format!("{}", x))
            } else if let Some(caps) = canon_type.captures(&line) {
                canonicalize_type(&caps[1]).map(|x| format!("{}", x))
            } else if let Some(caps) = assign_value.captures(&line) {
                assign_variable(&caps[1], &caps[2]).map(|x| format!("{}", x))
            } else if let Some(caps) = save_value.captures(&line) {
                match assign_variable(&caps[2], &caps[3]) {
                    Ok(_) => {
                        use std::io::Write;
                        let mut prel_file = std::fs::OpenOptions::new()
                            .create(true)
                            .append(true)
                            .open(&prelude_filename)
                            .unwrap();
                        writeln!(prel_file, "{}", &caps[1]).unwrap();
                        Ok(format!("[saved to {}]", &prelude_filename))
                    }
                    Err(e) => Err(e),
                }
            } else if let Some(caps) = assign_type.captures(&line) {
                assign_t_var(&caps[1], &caps[2]).map(|x| format!("{}", x))
            } else if let Some(caps) = save_type.captures(&line) {
                match assign_t_var(&caps[2], &caps[3]) {
                    Ok(_) => {
                        use std::io::Write;
                        let mut prel_file = std::fs::OpenOptions::new()
                            .create(true)
                            .append(true)
                            .open(&prelude_filename)
                            .unwrap();
                        writeln!(prel_file, "{}", &caps[1]).unwrap();
                        Ok(format!("[saved to {}]", &prelude_filename))
                    }
                    Err(e) => Err(e),
                }
            } else {
                eval_unseemly_program(&line).map(|x| format!("{}", x))
            };

            match result_display {
                Ok(v) => println!("\x1b[1;32m≉\x1b[0m {}", v),
                Err(s) => println!("\x1b[1;31m✘\x1b[0m {}", s),
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
            Err(e) => println!("\x1b[1;31m✘\x1b[0m {:#?}", e),
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
    let ast = grammar::parse(
        &grammar::FormPat::Call(n("Type")),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        t,
    )
    .map_err(|e| e.msg)?;

    let res = ty_env
        .with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:#?}", e)));

    if let Ok(ref t) = res {
        ty_env.with(|tys| {
            let new_tys = tys.borrow().set(n(name), t.clone());
            *tys.borrow_mut() = new_tys;
        })
    }

    res
}

fn canonicalize_type(t: &str) -> Result<ty::Ty, String> {
    let ast = grammar::parse(
        &grammar::FormPat::Call(n("Type")),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        t,
    )
    .map_err(|e| e.msg)?;

    ty_env.with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:#?}", e)))
}

fn parse_unseemly_program(program: &str) -> Result<String, String> {
    let ast = grammar::parse(
        &core_forms::outermost_form(),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        program,
    )
    .map_err(|e| e.msg)?;

    Ok(format!("▵ {:#?}\n∴ {}\n", ast, ast))
}

fn type_unseemly_program(program: &str) -> Result<ty::Ty, String> {
    let ast = grammar::parse(
        &core_forms::outermost_form(),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        program,
    )
    .map_err(|e| e.msg)?;

    ty_env.with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:#?}", e)))
}

fn eval_unseemly_program_without_typechecking(program: &str) -> Result<Value, String> {
    let ast: Ast = grammar::parse(
        &core_forms::outermost_form(),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        program,
    )
    .map_err(|e| e.msg)?;

    let core_ast = crate::expand::expand(&ast).map_err(|e| format!("{:#?}", e))?;

    val_env.with(|vals| eval(&core_ast, vals.borrow().clone()).map_err(|_| "???".to_string()))
}

fn eval_unseemly_program(program: &str) -> Result<Value, String> {
    let ast: Ast = grammar::parse(
        &core_forms::outermost_form(),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        program,
    )
    .map_err(|e| e.msg)?;

    let _type = ty_env
        .with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:#?}", e)))?;

    let core_ast = crate::expand::expand(&ast).map_err(|e| format!("{:#?}", e))?;

    val_env.with(|vals| eval(&core_ast, vals.borrow().clone()).map_err(|_| "???".to_string()))
}

fn type_and_expand_unseemly_program(program: &str) -> Result<ast::Ast, String> {
    let ast: Ast = grammar::parse(
        &core_forms::outermost_form(),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        program,
    )
    .map_err(|e| e.msg)?;

    let _type = ty_env
        .with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{:#?}", e)))?;

    crate::expand::expand(&ast).map_err(|e| format!("{:#?}", e))
}

#[test]
fn simple_end_to_end_eval() {
    assert_eq!(eval_unseemly_program("(zero? zero)"), Ok(val!(b true)));

    assert_eq!(eval_unseemly_program("(plus one one)"), Ok(val!(i 2)));

    assert_eq!(eval_unseemly_program("(.[x : Int  y : Int . (plus x y)]. one one)"), Ok(val!(i 2)));

    assert_eq!(
        eval_unseemly_program(
            "((fix .[ again : [ -> [ Int -> Int ]] .
            .[ n : Int .
                match (zero? n) {
                    +[True]+ => one
                    +[False]+ => (times n ((again) (minus n one))) } ]. ].) five)"
        ),
        Ok(val!(i 120))
    );
}

#[test]
fn end_to_end_int_list_tools() {
    assert_m!(
        assign_t_var("IntList", "mu_type IntList . enum { Nil () Cons (Int IntList) }"),
        Ok(_)
    );

    assert_m!(assign_t_var("IntListUF", "enum { Nil () Cons (Int IntList) }"), Ok(_));

    assert_m!(
        assign_variable("mt_ilist", "fold +[Nil]+ : enum { Nil () Cons (Int IntList) } : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable("3_ilist", "fold +[Cons three mt_ilist]+ : IntListUF : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable("23_ilist", "fold +[Cons two 3_ilist]+ : IntListUF : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable("123_ilist", "fold +[Cons one 23_ilist]+ : IntListUF : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable(
            "sum_int_list",
            "(fix .[again : [-> [IntList -> Int]] .
             .[ lst : IntList .
                 match unfold lst {
                     +[Nil]+ => zero +[Cons hd tl]+ => (plus hd ((again) tl))} ]. ]. )"
        ),
        Ok(_)
    );

    assert_eq!(eval_unseemly_program("(sum_int_list 123_ilist)"), Ok(val!(i 6)));

    assert_m!(
        assign_variable(
            "int_list_len",
            "(fix .[again : [-> [IntList -> Int]] .
             .[ lst : IntList .
                 match unfold lst {
                     +[Nil]+ => zero +[Cons hd tl]+ => (plus one ((again) tl))} ]. ].)"
        ),
        Ok(_)
    );

    assert_eq!(eval_unseemly_program("(int_list_len 123_ilist)"), Ok(val!(i 3)));
}

#[test]
fn end_to_end_list_tools() {
    assert_m!(
        assign_t_var("List", "forall T . mu_type List . enum { Nil () Cons (T List <[T]<) }"),
        Ok(_)
    );

    assert_m!(assign_t_var("ListUF", "forall T . enum { Nil () Cons (T List <[T]<) }"), Ok(_));

    assert_m!(
        assign_variable(
            "mt_list",
            "fold +[Nil]+ : enum { Nil () Cons (Int List <[Int]<) } : List <[Int]<"
        ),
        Ok(_)
    );

    assert_m!(
        assign_variable("3_list", "fold +[Cons three mt_list]+ : ListUF <[Int]< : List <[Int]<"),
        Ok(_)
    );

    assert_m!(
        assign_variable("23_list", "fold +[Cons two 3_list]+ : ListUF <[Int]< : List <[Int]<"),
        Ok(_)
    );

    assert_m!(
        assign_variable("123_list", "fold +[Cons one 23_list]+ : ListUF <[Int]< : List <[Int]<"),
        Ok(_)
    );

    assert_m!(
        assign_variable(
            "list_len",
            "forall S . (fix .[again : [-> [List <[S]< -> Int]] .
            .[ lst : List <[S]< .
                match unfold lst {
                    +[Nil]+ => zero
                    +[Cons hd tl]+ => (plus one ((again) tl))} ]. ].)"
        ),
        Ok(_)
    );

    assert_eq!(eval_unseemly_program("(list_len 123_list)"), Ok(val!(i 3)));

    assert_m!(
        assign_variable(
            "map",
            "forall T S . (fix  .[again : [-> [List <[T]<  [T -> S] -> List <[S]< ]] .
            .[ lst : List <[T]<   f : [T -> S] .
                match unfold lst {
                    +[Nil]+ => fold +[Nil]+ : ListUF <[S]< : List <[S]<
                    +[Cons hd tl]+ =>
                      fold +[Cons (f hd) ((again) tl f)]+ : ListUF <[S]< : List <[S]< } ]. ].)"
        ),
        Ok(_)
    );
    // TODO: what should even happen if you have `forall` not on the "outside"?
    // It should probably be an error to have a value typed with an underdetermined type.

    // TODO: it's way too much of a pain to define each different expected result list.
    assert_m!(eval_unseemly_program("(map 123_list .[x : Int . (plus x one)]. )"), Ok(_));

    assert_m!(eval_unseemly_program("(map 123_list .[x : Int . (equal? x two)]. )"), Ok(_));
}

#[test]
fn end_to_end_quotation_basic() {
    assert_m!(eval_unseemly_program("'[Expr | .[ x : Int . x ]. ]'"), Ok(_));

    assert_m!(eval_unseemly_program("'[Expr | (plus five five) ]'"), Ok(_));

    assert_m!(eval_unseemly_program("'[Expr | '[Expr | (plus five five) ]' ]'"), Ok(_));

    //≫ .[s : Expr <[Int]< . '[Expr | ( ,[Expr | s], '[Expr | ,[Expr | s], ]')]' ].
}
#[test]
fn subtyping_direction() {
    // Let's check to make sure that "supertype" and "subtype" never got mixed up:

    assert_m!(assign_variable("ident", "forall T . .[ a : T . a ]."), Ok(_));

    assert_eq!(eval_unseemly_program("(ident five)"), Ok(val!(i 5)));

    assert_m!(eval_unseemly_program("( .[ a : [Int -> Int] . a]. ident)"), Ok(_));

    assert_m!(eval_unseemly_program("( .[ a : forall T . [T -> T] . a]. .[a : Int . a].)"), Err(_));

    assert_m!(eval_unseemly_program(".[ a : struct {} . a]."), Ok(_));

    assert_m!(
        eval_unseemly_program("( .[ a : struct {normal : Int extra : Int} . a]. *[normal : one]*)"),
        Err(_)
    );

    assert_m!(
        eval_unseemly_program(
            "( .[ a : struct {normal : Int} . a]. *[normal : one extra : five]*)"
        ),
        Ok(_)
    );
}

#[test]
fn end_to_end_quotation_advanced() {
    assert_eq!(
        eval_unseemly_program(
            "(.[five_e : Expr <[Int]< .
                '[Expr | (plus five ,[five_e],) ]' ].
                '[Expr | five]')"
        ),
        eval_unseemly_program("'[Expr | (plus five five) ]'")
    );

    // Pass the wrong type (not really a test of quotation)
    assert_m!(
        type_unseemly_program(
            "(.[five_e : Expr <[Int]< .
                '[Expr | (plus five ,[five_e],) ]' ].
                '[Expr | true]')"
        ),
        Err(_)
    );

    // Interpolate the wrong type
    assert_m!(
        type_unseemly_program(
            "(.[five_e : Expr <[Bool]< .
                '[Expr | (plus five ,[five_e],) ]' ].
                '[Expr | true]')"
        ),
        Err(_)
    );

    // Interpolate the wrong type (no application needed to find the error)
    assert_m!(
        type_unseemly_program(".[five_e : Expr <[Bool]< . '[Expr | (plus five ,[five_e],) ]' ]."),
        Err(_)
    );

    assert_m!(
        eval_unseemly_program(
            "forall T . .[type : Type <[T]<   rhs : Expr <[T]<
                . '[Expr | (.[x : ,[Type <[T]< | type], . eight].  ,[rhs], )]' ]."
        ),
        Ok(_)
    );

    assert_m!(eval_unseemly_program("'[Pat <[Nat]< | x]'"), Ok(_));

    // Actually import a pattern of quoted syntax:
    assert_eq!(
        eval_unseemly_program(
            "match '[Expr | (plus one two) ]' {
                 '[Expr <[Int]< | (plus ,[Expr <[Int]< | e], two) ]' => e }"
        ),
        Ok(val!(ast (vr "one")))
    );

    // In order to have "traditional", non-type-annotated `let`, we want to ... reify T, I guess?
    // But the whole language has parametricity kinda baked in, and that seems to make it hard?
    // I think the solution is to build `let` into the language;
    //  if a macro wants to have non-annotated binding, it's probably expandable to `let` anyways.
    assert_m!(
        assign_variable(
            "let",
            "forall T S . .[binder : Pat <[T]<
                        type : Type <[T]<
                        rhs : Expr <[T]<
                        body : Expr <[S]< .
             '[ Expr | (.[x : ,[type],
                     . match x { ,[Pat <[T]< | binder], => ,[body], } ].
                 ,[rhs],)]' ]."
        ),
        Ok(_)
    );

    without_freshening! {
        assert_eq!(
            eval_unseemly_program(
                "(let  '[Pat <[Int]< | y]'
                       '[Type <[Int]< | Int]'
                       '[Expr <[Int]< | eight]'
                       '[Expr <[Int]< | five]')"),
            eval_unseemly_program("'[Expr <[Int]< | (.[x : Int . match x {y => five}].  eight)]'"));
    }

    //  // We need tuple literals before we can test this:
    //  assert_m!(assign_variable("let-multi",
    //      "forall T . .[ binder : **[ :::[T >> Ident <[T]< ]::: ]**
    //                     type : **[ :::[T >> Type <[T]< ]::: ]**
    //                     rhs : **[ :::[T >> Expr <[T]< ]::: ]**
    //                     body : Expr <[S]< .
    //          '[Expr | (.[ ...[, binder , >> ,[Ident | binder],]...
    //                       : ...[, type , >> ,[Type | type], ]... .
    //                    ,[body], ].
    //                      ...[, Expr , | ,[rhs], ]... ) ]'
    //                       "),
    //       Ok(_));

    //  without_freshening! {
    //      assert_eq!(
    //          eval_unseemly_program(
    //              "(let-multi  '[Ident <[Int]< | y]'
    //                     '[Type <[Int]< | Int]'
    //                     '[Expr <[Int]< | eight]'
    //                     '[Expr <[Int]< | five]')"),
    //          eval_unseemly_program("'[Expr <[Int]< | (.[x : Int . match x {y => five}].  eight)]'"));
    //  }
}

#[test]
fn language_building() {
    assert_eq!(
        eval_unseemly_program(
            r"extend_syntax
                DefaultToken ::= /(?:\s|#[^\n]*)*(\S+)/ ;
            in
                # Now we have comments! (just not after the last token)
            five"
        ),
        Ok(val!(i 5))
    );

    let bound_wrong_prog = "extend_syntax
            Expr ::=also forall T S . '{
                [
                    lit ,{ DefaultToken }, = 'let'
                    [
                        pat := ( ,{ Pat <[ S ]< }, )
                        lit ,{ DefaultToken }, = '='
                        value := ( ,{ Expr <[ S ]< }, )
                        lit ,{ DefaultToken }, = ';'
                    ] *
                    lit ,{ DefaultToken }, = 'in'
                    body := ( ,{ Expr <[ T ]< }, <-- ...[pat = value]... )
                ]
            }' let_macro -> .{
                '[Expr |
                    match ...[, value , >> ,[value], ]...
                        { ...[, pat , >> ,[pat],]... => ,[body], } ]'
            }. ;
        in
        let x = eight ;
            y = times ;
        in (plus x y)";
    let bound_wrong_ast = grammar::parse(
        &core_forms::outermost_form(),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        bound_wrong_prog,
    )
    .unwrap();

    assert_m!(
        ty::synth_type(&bound_wrong_ast, crate::runtime::core_values::core_types()),
        ty_err_p!(Mismatch(x, y)) => {
            assert_eq!(x, uty!({Int :}));
            assert_eq!(y, uty!({fn : [{Int :}; {Int :}] {Int :}}));
        }
    );

    let inner_expr_wrong_prog = "extend_syntax
            Expr ::=also forall T S . '{
                [
                    lit ,{ DefaultToken }, = 'let'
                    [
                        pat := ( ,{ Pat <[ S ]< }, )
                        lit ,{ DefaultToken }, = '='
                        value := ( ,{ Expr <[ S ]< }, )
                        lit ,{ DefaultToken }, = ';'
                    ] *
                    lit ,{ DefaultToken }, = 'in'
                    body := ( ,{ Expr <[ T ]< }, <-- ...[pat = value]... )
                ]
            }' let_macro -> .{
                '[Expr |
                    match ...[, value , >> ,[value], ]...
                        { ...[, pat , >> ,[pat],]... => ,[body], } ]'
            }. ;
        in
        let x = eight ;
            y = four ;
        in (plus x times)";
    let inner_expr_wrong_ast = grammar::parse(
        &core_forms::outermost_form(),
        &core_forms::get_core_forms(),
        runtime::core_values::get_core_envs(),
        inner_expr_wrong_prog,
    )
    .unwrap();

    assert_m!(
        ty::synth_type(&inner_expr_wrong_ast, crate::runtime::core_values::core_types()),
        ty_err_p!(Mismatch(x, times)) => {
            assert_eq!(x, uty!({Int :}));
            assert_eq!(times, uty!({fn : [{Int :}; {Int :}] {Int :}}));
        }
    );

    // TODO: leaving out the `**[ ]**` results in an ICP; it should be a static error.

    let let_macro_prog = "extend_syntax
            Expr ::=also forall T S . '{
                [
                    lit ,{ DefaultToken }, = 'let'
                    [
                        pat := ( ,{ Pat <[ S ]< }, )
                        lit ,{ DefaultToken }, = '='
                        value := ( ,{ Expr <[ S ]< }, )
                        lit ,{ DefaultToken }, = ';'
                    ] *
                    lit ,{ DefaultToken }, = 'in'
                    body := ( ,{ Expr <[ T ]< }, <-- ...[pat = value]... )
                ]
            }' let_macro -> .{
                '[Expr |
                    match **[...[, value , >> ,[value], ]... ]**
                        { **[...[, pat , >> ,[pat],]... ]** => ,[body], } ]'
            }. ;
        in
        let x = eight ;
            y = four ;
        in (plus y (plus x y))";
    assert_eq!(eval_unseemly_program(let_macro_prog), Ok(val!(i 16)));
}
