use crate::{
    ast::{Ast, Ast::*},
    ast_walk::{LazyWalkReses, WalkRule::*},
    core_forms::{get_core_forms, outermost_form},
    core_type_forms::get__primitive_type,
    form::Form,
    grammar::FormPat,
    name::*,
    runtime::eval::Value,
    util::assoc::Assoc,
};
use std::rc::Rc;

fn extend__capture_language(
    pc: crate::earley::ParseContext,
    _starter_info: Ast,
) -> crate::earley::ParseContext {
    use crate::runtime::reify::Reifiable;
    let reified_language = pc.reify();
    crate::earley::ParseContext {
        grammar: assoc_n!("OnlyNt" =>
            Rc::new(FormPat::Named(n("body"), Rc::new(FormPat::Anyways(Node(
                basic_typed_form!(
                    [], // No syntax
                    cust_rc_box!(|parts| {
                        // Reify the current type environment:
                        let mut struct_body = vec![];

                        for (k, v) in parts.env.iter_pairs() {
                            struct_body.push(crate::util::mbe::EnvMBE::new_from_leaves(assoc_n!(
                                "component_name" => Atom(*k),
                                "component" => v.clone()
                            )))
                        }

                        Ok(ast!({"Type" "tuple" :
                            "component" => [
                                (, get__primitive_type(n("LanguageSyntax"))),
                                (, Node(crate::core_forms::find("Type", "struct"),
                                     crate::util::mbe::EnvMBE::new_from_anon_repeat(struct_body),
                                     crate::beta::ExportBeta::Nothing))]
                    }))}),
                    cust_rc_box!(move |parts| {
                        Ok(Value::Sequence(vec![
                            // The captured reified language syntax:
                            Rc::new(reified_language.clone()),
                            // Reifying the value environment is easy:
                            Rc::new(Value::Struct(parts.env))
                        ]))})
                ),
            crate::util::mbe::EnvMBE::<Ast>::new(),
            crate::beta::ExportBeta::Nothing
        )))))),
        // We can't just squirrel `reified_language` here:
        //  these only affect earlier phases, and we need the language in phase 0
        eval_ctxt: LazyWalkReses::<crate::runtime::eval::Eval>::new_empty(),
        type_ctxt: LazyWalkReses::<crate::ty::SynthTy>::new_empty(),
    }
}

// Shift the parser into the language specified in "filename".
// TODO: This is probably unhygenic in some sense. Perhaps this needs to be a new kind of `Beta`?
fn extend_import(
    _pc: crate::earley::ParseContext,
    starter_info: Ast,
) -> crate::earley::ParseContext {
    let filename = match starter_info {
        // Skip "import" and the separator:
        Shape(ref parts) => match parts[2] {
            IncompleteNode(ref parts) => {
                parts.get_leaf_or_panic(&n("filename")).to_name().orig_sp()
            }
            _ => icp!("Unexpected structure {:#?}", parts),
        },
        _ => icp!("Unexpected structure {:#?}", starter_info),
    };
    let mut raw_lib = String::new();

    use std::io::Read;
    std::fs::File::open(std::path::Path::new(&filename))
        .expect("Error opening file")
        .read_to_string(&mut raw_lib)
        .expect("Error reading file");

    let core_envs = crate::runtime::core_values::get_core_envs();
    // TODO: I guess syntax extensions ought to return `Result`, too...
    let lib_ast =
        crate::grammar::parse(&outermost_form(), &get_core_forms(), core_envs.clone(), &raw_lib)
            .unwrap();
    // TODO: This gets roundtripped (LazyWalkReses -> Assoc -> LazyWalkReses). Fix `get_core_envs`?
    let lib_typed = crate::ty::synth_type(&lib_ast, core_envs.0.env).unwrap();
    let lib_evaled = crate::runtime::eval::eval(&lib_ast, core_envs.1.env).unwrap();
    let (new_pc, new__value_env) = if let Value::Sequence(ref lang_and_env) = lib_evaled {
        use crate::runtime::reify::Reifiable;
        let new_pc = crate::earley::ParseContext::reflect(&(*lang_and_env[0]));
        let new__value_env = if let Value::Struct(ref env) = *lang_and_env[1] {
            let mut new__value_env = Assoc::new();
            // We need to un-freshen the names that we're importing
            //  so they can actually be referred to.
            for (k, v) in env.iter_pairs() {
                new__value_env = new__value_env.set(k.unhygienic_orig(), v.clone())
            }
            new__value_env
        } else {
            icp!("[type error] Unexpected lib syntax structure: {:#?}", *lang_and_env[1])
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

    crate::earley::ParseContext {
        grammar: new_pc.grammar.set(
            n("ImportStarter"),
            Rc::new(FormPat::Scope(
                basic_typed_form!(
                    (named "body", (call "Expr")),
                    cust_rc_box!(move |parts| {
                        parts.with_environment(
                            parts.env.set_assoc(&new__type_env)).get_res(n("body"))
                    }),
                    cust_rc_box!(move |parts| {
                        parts.with_environment(
                            parts.env.set_assoc(&new__value_env)).get_res(n("body"))
                    })
                ),
                crate::beta::ExportBeta::Nothing,
            )),
        ),
        ..new_pc
    }
}

/// Some of these forms are theoretically implementable as macros from other forms,
///  but for performance and debugability reasons, they are a part of Unseemly.
/// Other of these forms are just not central to the design of Unseemly and have ad-hoc designs.
///
/// Stored as a `FormPat` instead of a `SynEnv`
///  because we need to merge this with the rest of the "Expr"s.
pub fn make_core_extra_forms() -> FormPat {
    // I think we want to have "Stmt" separate from "Expr", once #4 is complete.
    // Should "Item"s be valid "Stmt"s? Let's do whatever Rust does.

    forms_to_form_pat![
        typed_form!("block",
            (delim "-{", "{", [(star [(named "effect", (call "Expr")), (lit ";")]),
                            (named "result", (call "Expr"))]),
            /* type */
            Body(n("result")),
            /* evaluation */
            cust_rc_box!( move | part_values | {
                for effect_values in part_values.march_all(&[n("effect")]) {
                    let _ = effect_values.get_res(n("effect"))?;
                }
                part_values.get_res(n("result"))
        })),
        typed_form!("capture_language",
            // Immediately descend into a grammar with one NT pointing to one form,
            //  which has captured the whole parse context.
            (extend_nt [(lit "capture_language")], "OnlyNt", extend__capture_language),
            Body(n("body")),
            Body(n("body"))),
        typed_form!("import_language_from_file",
            (extend
                [(lit "import"), (call "DefaultSeparator"),
                    (named "filename", (scan r"/\[(.*)]/"))],
                (named "body", (call "ImportStarter")),
                extend_import),
            Body(n("body")),
            Body(n("body"))),
        typed_form!("string_literal",
            (named "body", (scan r#"\s*"((?:[^"\\]|\\")*)""#)),
            cust_rc_box!(|_| {
                Ok(ast!({"Type" "String" :}))
            }),
            cust_rc_box!(|parts| {
                // Undo the escaping:
                Ok(Value::Text(parts.get_term(n("body")).to_name().orig_sp()
                    .replace(r#"\""#, r#"""#)))
            })
        )
    ]
}
