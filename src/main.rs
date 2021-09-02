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

/// Everything you need to turn text into behavior.
#[derive(Clone)]
pub struct Language {
    pub pc: crate::earley::ParseContext,
    // TODO: how do these differ from the corresponding elements of `ParseContext`?
    //  Should we get rid of `Language` in favor of it???
    pub type_env: Assoc<Name, Ast>,
    pub type_env__phaseless: Assoc<Name, Ast>,
    pub value_env: Assoc<Name, Value>,
}

/// Generate Unseemly.
/// (This is the core language.)
pub fn unseemly() -> Language {
    Language {
        pc: crate::core_forms::outermost__parse_context(),
        type_env: crate::runtime::core_values::core_types(),
        type_env__phaseless: crate::runtime::core_values::core_types(),
        value_env: crate::runtime::core_values::core_values(),
    }
}

/// Run the file (which hopefully evaluates to `capture_language`), and get the language it defines.
/// Returns the parse context, the type environment, the phaseless version of the type environment,
///  and the value environment.
/// This doesn't take a language 4-tuple -- it assumes that the language is in Unseemly
///  (but of course it may do `include /[some_language.unseemly]/` itself).
/// TODO: we only need the phaselessness for macros, and maybe we can get rid of it there?
pub fn language_from_file(path: &std::path::Path) -> Language {
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

    let lang = get_language(&raw_lib, unseemly());

    // Go back to the original directory:
    std::env::set_current_dir(orig_dir).unwrap();

    return lang;
}

pub fn get_language(program: &str, lang: Language) -> Language {
    // TODO: I guess syntax extensions ought to return `Result`, too...
    let lib_ast = crate::grammar::parse(&core_forms::outermost_form(), lang.pc, &program).unwrap();
    let lib_typed = ast_walk::walk::<ty::SynthTy>(
        &lib_ast,
        &ast_walk::LazyWalkReses::new(lang.type_env, lang.type_env__phaseless, lib_ast.clone()),
    )
    .unwrap();
    let lib_expanded = crate::expand::expand(&lib_ast).unwrap();
    let lib_evaled = crate::runtime::eval::eval(&lib_expanded, lang.value_env).unwrap();
    let (new_pc, new__value_env) = if let Value::Sequence(mut lang_and_env) = lib_evaled {
        let env_value = lang_and_env.pop().unwrap();
        let lang_value = lang_and_env.pop().unwrap();
        let new_pc = match &*lang_value {
            Value::ParseContext(boxed_pc) => (**boxed_pc).clone(),
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

    let mut new___type_env__phaseless = Assoc::<Name, Ast>::new();
    for (k, v) in pl_keys.into_iter().zip(pl_values.into_iter()) {
        // As above, unfreshen:
        new___type_env__phaseless =
            new___type_env__phaseless.set(k.to_name().unhygienic_orig(), v.clone());
    }

    Language {
        pc: new_pc,
        type_env: new__type_env,
        type_env__phaseless: new___type_env__phaseless,
        value_env: new__value_env,
    }
}

/// Evaluate a program written in some language.
/// The last four arguments match the values returned by `language_from_file`.
pub fn eval_program(program: &str, lang: Language) -> Result<Value, String> {
    // TODO: looks like `outermost_form` ought to be a property of `ParseContext`
    let ast: Ast = crate::grammar::parse(&core_forms::outermost_form(), lang.pc, program)
        .map_err(|e| e.msg)?;

    let _type = ast_walk::walk::<ty::SynthTy>(
        &ast,
        &ast_walk::LazyWalkReses::new(lang.type_env, lang.type_env__phaseless, ast.clone()),
    )
    .map_err(|e| format!("{}", e))?;

    let core_ast = crate::expand::expand(&ast).map_err(|_| "???".to_string())?;

    eval(&core_ast, lang.value_env).map_err(|_| "???".to_string())
}

/// Evaluate a program written in Unseemly.
/// Of course, it may immediately do `include /[something]/` to switch languages.
pub fn eval_unseemly_program_top(program: &str) -> Result<Value, String> {
    eval_program(program, unseemly())
}

/// Type program written in Unseemly.
/// Of course, it may immediately do `include /[something]/` to switch languages.
pub fn type_unseemly_program_top(program: &str) -> Result<Ast, String> {
    let unseemly = unseemly();
    let ast: Ast = crate::grammar::parse(&core_forms::outermost_form(), unseemly.pc, program)
        .map_err(|e| e.msg)?;

    ast_walk::walk::<ty::SynthTy>(
        &ast,
        &ast_walk::LazyWalkReses::new(unseemly.type_env, unseemly.type_env__phaseless, ast.clone()),
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
pub fn wasm_init() {
    #[cfg(target_arch = "wasm32")]
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
}

use std::iter::FromIterator;

thread_local! {
    static language_stash: std::cell::RefCell<std::collections::HashMap<String, Language>>
        = std::cell::RefCell::new(std::collections::HashMap::from_iter(
            vec![("unseemly".to_string(), unseemly())].into_iter()));
}

#[wasm_bindgen]
pub fn html__eval_program(program: &str, stashed_lang: &str) -> String {
    let lang: Language =
        language_stash.with(|ls| (*ls.borrow()).get(stashed_lang).unwrap().clone());
    html_render(eval_program(program, lang))
}

#[wasm_bindgen]
pub fn stash_lang(result_name: &str, program: &str, orig_stashed: &str) {
    let orig_lang = language_stash.with(|ls| (*ls.borrow()).get(orig_stashed).unwrap().clone());
    let new_lang = get_language(program, orig_lang);
    language_stash.with(|ls| ls.borrow_mut().insert(result_name.to_string(), new_lang));
}

#[wasm_bindgen]
pub fn generate__ace_rules(stashed_lang: &str) -> String {
    language_stash.with(|ls|
        grammar::ace_rules__for(&(*ls.borrow()).get(stashed_lang).unwrap().pc.grammar))
}