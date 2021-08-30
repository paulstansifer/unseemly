// Unseemly is a "core" typed language with (typed!) macros.
// You shouldn't write code in Unseemly.
// Instead, you should implement your programming language as Unseemly macros.

#![allow(dead_code, unused_macros, non_snake_case, non_upper_case_globals, deprecated)]
// dead_code and unused_macros are hopefully temporary allowances
// non_snake_case is stylistic, so we can write `non__snake_case`.
// non_upper_case_globals is stylistic ... but maybe thread_locals really ought to be upper case.
// deprecated is temporary, until `Sky` replaces `EnvMBE` (and the deprecated calls are cleaned up)
#![recursion_limit = "128"] // Yikes.

// for testing; requires `cargo +nightly`
// #![feature(log_syntax, trace_macros)]
// trace_macros!(true);

// TODO: turn these into `use` statements in the appropriate places
#[macro_use]
extern crate custom_derive;

pub mod macros;

pub mod name; // should maybe be moved to `util`; `mbe` needs it

pub mod util;

pub mod alpha;
pub mod ast;
pub mod beta;
pub mod read;

pub mod earley;
pub mod grammar;
pub mod unparse;

pub mod form;

pub mod ast_walk;
pub mod expand;
pub mod ty;
pub mod ty_compare;
pub mod walk_mode;

pub mod runtime;

pub mod core_extra_forms;
pub mod core_forms;
pub mod core_macro_forms;
pub mod core_qq_forms;
pub mod core_type_forms;

mod end_to_end__tests;

use crate::{
    ast::Ast,
    name::Name,
    runtime::eval::{eval, Value},
    util::assoc::Assoc,
};

use wasm_bindgen::prelude::*;

/// Run the file (which hopefully evaluates to `capture_language`), and get the language it defines.
/// Returns the parse context, the type environment, the phaseless version of the type environment,
///  and the value environment.
/// This doesn't take a language 4-tuple -- it assumes that the language is in Unseemly
///  (but of course it may do `include /[some_language.unseemly]/` itself).
/// TODO: we only need the phaselessness for macros, and maybe we can get rid of it there?
pub fn language_from_file(
    path: &std::path::Path,
) -> (crate::earley::ParseContext, Assoc<Name, Ast>, Assoc<Name, Ast>, Assoc<Name, Value>) {
    let mut raw_lib = String::new();

    use std::io::Read;
    let orig_dir = std::env::current_dir().unwrap();
    std::fs::File::open(path)
        .expect("Error opening file")
        .read_to_string(&mut raw_lib)
        .expect("Error reading file");
    // Evaluate the file in its own directory:
    if let Some(dir) = path.parent() {
        // Might be empty:
        if dir.is_dir() {
            std::env::set_current_dir(dir).unwrap();
        }
    }

    let orig_pc = crate::core_forms::outermost__parse_context();

    // TODO: I guess syntax extensions ought to return `Result`, too...
    let lib_ast =
        crate::grammar::parse(&core_forms::outermost_form(), orig_pc.clone(), &raw_lib).unwrap();
    // TODO: This gets roundtripped (LazyWalkReses -> Assoc -> LazyWalkReses). Just call `walk`?
    let lib_typed = crate::ty::synth_type(&lib_ast, orig_pc.type_ctxt.env).unwrap();
    let lib_expanded = crate::expand::expand(&lib_ast).unwrap();
    let lib_evaled = crate::runtime::eval::eval(&lib_expanded, orig_pc.eval_ctxt.env).unwrap();
    let (new_pc, new__value_env) = if let Value::Sequence(mut lang_and_env) = lib_evaled {
        let env_value = lang_and_env.pop().unwrap();
        let lang_value = lang_and_env.pop().unwrap();
        let new_pc = match &*lang_value {
            Value::Language(boxed_pc) => (**boxed_pc).clone(),
            _ => icp!("[type error] not a language"),
        };
        let new__value_env = if let Value::Struct(ref env) = *env_value {
            let mut new__value_env = Assoc::new();
            // We need to un-freshen the names that we're importing
            //  so they can actually be referred to.
            for (k, v) in env.iter_pairs() {
                new__value_env = new__value_env.set(k.unhygienic_orig(), v.clone())
            }
            new__value_env
        } else {
            icp!("[type error] Unexpected lib syntax structure: {:#?}", env_value)
        };
        (new_pc, new__value_env)
    } else {
        icp!("[type error] Unexpected lib syntax strucutre: {:#?}", lib_evaled);
    };

    node_let!(lib_typed => {Type tuple}
        lang_and_types *= component);
    node_let!(lang_and_types[1] => {Type struct}
        keys *= component_name, values *= component);

    let mut new__type_env = Assoc::<Name, Ast>::new();
    for (k, v) in keys.into_iter().zip(values.into_iter()) {
        // As above, unfreshen:
        new__type_env = new__type_env.set(k.to_name().unhygienic_orig(), v.clone());
    }

    // Do it again, to unpack the phaseless type environment:
    node_let!(lang_and_types[2] => {Type struct}
        pl_keys *= component_name, pl_values *= component);

    let mut new__type_env__phaseless = Assoc::<Name, Ast>::new();
    for (k, v) in pl_keys.into_iter().zip(pl_values.into_iter()) {
        // As above, unfreshen:
        new__type_env__phaseless =
            new__type_env__phaseless.set(k.to_name().unhygienic_orig(), v.clone());
    }

    // Go back to the original directory:
    std::env::set_current_dir(orig_dir).unwrap();

    (new_pc, new__type_env, new__type_env__phaseless, new__value_env)
}

/// Evaluate a program written in some language.
/// The last four arguments match the values returned by `language_from_file`.
pub fn eval_program(
    program: &str,
    pc: crate::earley::ParseContext,
    type_env: Assoc<Name, Ast>,
    type_env__phaseless: Assoc<Name, Ast>,
    value_env: Assoc<Name, Value>,
) -> Result<Value, String> {
    let ast: Ast =
        crate::grammar::parse(&core_forms::outermost_form(), pc, program).map_err(|e| e.msg)?;

    let _type = ast_walk::walk::<ty::SynthTy>(
        &ast,
        &ast_walk::LazyWalkReses::new(type_env, type_env__phaseless, ast.clone()),
    )
    .map_err(|e| format!("{}", e))?;

    let core_ast = crate::expand::expand(&ast).map_err(|_| "???".to_string())?;

    eval(&core_ast, value_env).map_err(|_| "???".to_string())
}

/// Evaluate a program written in Unseemly.
/// Of course, it may immediately do `include /[something]/` to switch languages.
pub fn eval_unseemly_program_top(program: &str) -> Result<Value, String> {
    eval_program(
        program,
        crate::core_forms::outermost__parse_context(),
        crate::runtime::core_values::core_types(),
        crate::runtime::core_values::core_types(),
        crate::runtime::core_values::core_values(),
    )
}

/// Type program written in Unseemly.
/// Of course, it may immediately do `include /[something]/` to switch languages.
pub fn type_unseemly_program_top(program: &str) -> Result<Ast, String> {
    let pc = crate::core_forms::outermost__parse_context();
    let type_env = crate::runtime::core_values::core_types();

    let ast: Ast =
        crate::grammar::parse(&core_forms::outermost_form(), pc, program).map_err(|e| e.msg)?;

    ast_walk::walk::<ty::SynthTy>(
        &ast,
        &ast_walk::LazyWalkReses::new(type_env.clone(), type_env, ast.clone()),
    )
    .map_err(|e| format!("{}", e))
}

/// Displays `res` on a color terminal.
pub fn terminal_display(res: Result<Value, String>) {
    match res {
        Ok(v) => println!("\x1b[1;32m≉\x1b[0m {}", v),
        Err(s) => println!("\x1b[1;31m✘\x1b[0m {}", s),
    }
}

fn html_render(res: Result<Value, String>) -> String {
    match res {
        Ok(v) => format!("<b>{}</b>", v),
        // HACK: codespan_reporting uses terminal escapes
        Err(s) => format!("<pre>{}</pre>", ansi_to_html::convert_escaped(&s).unwrap()),
    }
}

#[wasm_bindgen]
pub fn html__eval_program(program: &str) -> String {
    html_render(eval_unseemly_program_top(program))
}
