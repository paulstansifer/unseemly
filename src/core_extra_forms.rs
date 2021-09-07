use crate::{
    ast::{Ast, AstContents::*},
    ast_walk::{LazyWalkReses, WalkRule::*},
    core_type_forms::get__primitive_type,
    grammar::FormPat,
    name::*,
    runtime::eval::Value,
    util::mbe::EnvMBE,
};
use std::rc::Rc;

pub fn extend__capture_language(
    pc: crate::earley::ParseContext,
    _starter_info: Ast,
) -> crate::earley::ParseContext {
    crate::earley::ParseContext {
        grammar: assoc_n!("OnlyNt" =>
            Rc::new(FormPat::Named(n("body"), Rc::new(FormPat::Anyways(raw_ast!(Node(
                basic_typed_form!(
                    [], // No syntax
                    cust_rc_box!(|parts| {
                        // Reify the current type environment:
                        let mut struct_body = vec![];

                        for (k, v) in parts.env.iter_pairs() {
                            struct_body.push(EnvMBE::new_from_leaves(assoc_n!(
                                "component_name" => ast!((at *k)),
                                "component" => v.clone()
                            )))
                        }

                        // HACK: Anything that was added to the prelude is phaseless.
                        let phaseless_env = parts.prelude_env.cut_common(
                            &crate::runtime::core_values::core_types());

                        let mut struct_body__phaseless = vec![];

                        for (k, v) in phaseless_env.iter_pairs() {
                            struct_body__phaseless.push(EnvMBE::new_from_leaves(assoc_n!(
                                "component_name" => ast!((at *k)),
                                "component" => v.clone()
                            )))
                        }

                        Ok(ast!({"Type" "tuple" :
                            "component" => [
                                (, get__primitive_type(n("LanguageSyntax"))),
                                (, raw_ast!(Node(crate::core_forms::find("Type", "struct"),
                                     EnvMBE::new_from_anon_repeat(struct_body),
                                     crate::beta::ExportBeta::Nothing))),
                                (, raw_ast!(Node(crate::core_forms::find("Type", "struct"),
                                     EnvMBE::new_from_anon_repeat(struct_body__phaseless),
                                     crate::beta::ExportBeta::Nothing)))]
                        }))}),
                    cust_rc_box!(move |parts| {
                        Ok(Value::Sequence(vec![
                            // The captured language syntax:
                            Rc::new(Value::ParseContext(Box::new(pc.clone()))),
                            // Reifying the value environment is easy:
                            Rc::new(Value::Struct(parts.env))
                        ]))})
                ),
            EnvMBE::<Ast>::new(),
            crate::beta::ExportBeta::Nothing
        ))))))),
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
    let filename = match starter_info.c() {
        // Skip "import" and the separator:
        Shape(ref parts) => match parts[2].c() {
            IncompleteNode(ref parts) => {
                parts.get_leaf_or_panic(&n("filename")).to_name().orig_sp()
            }
            _ => icp!("Unexpected structure {:#?}", parts),
        },
        _ => icp!("Unexpected structure {:#?}", starter_info),
    };

    let crate::Language { pc, type_env, type_env__phaseless, value_env } =
        crate::language_from_file(&std::path::Path::new(&filename));

    crate::earley::ParseContext {
        grammar: pc.grammar.set(
            n("ImportStarter"),
            Rc::new(FormPat::Scope(
                basic_typed_form!(
                    (named "body", (call "Expr")),
                    cust_rc_box!(move |parts| {
                        // HACK: Copied from `ExtendEnvPhaseless`
                        LazyWalkReses {
                            env: parts.env.set_assoc(&type_env)
                                .set_assoc(&type_env__phaseless),
                            prelude_env: parts.prelude_env.set_assoc(&type_env__phaseless),
                            more_quoted_env: parts.more_quoted_env.iter().map(
                                |e| e.set_assoc(&type_env__phaseless)).collect(),
                            less_quoted_env: parts.less_quoted_env.iter().map(
                                |e| e.set_assoc(&type_env__phaseless)).collect(),
                            .. parts.clone()
                        }.get_res(n("body"))
                    }),
                    cust_rc_box!(move |parts| {
                        parts.with_environment(
                            parts.env.set_assoc(&value_env)).get_res(n("body"))
                    })
                ),
                crate::beta::ExportBeta::Nothing,
            )),
        ),
        ..pc
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
        typed_form!("prefab_type",
            [(lit "prefab_type"), (named "ty", (call "Type"))],
            /* type */
            cust_rc_box!(move |part_types| {
                Ok(ast!({"Type" "type_apply" :
                    "type_rator" => (, (get__primitive_type(n("Type")))),
                    "arg" => [(, part_types.get_res(n("ty"))?)]
                }))
            }),
            /* evaluation */
            // HACK: at evaluation time, nobody cares
            cust_rc_box!(move |_| {
                Ok(Value::AbstractSyntax(ast!((trivial))))
            })
        ),
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
            (named "body", (scan_cat r#"\s*"((?:[^"\\]|\\"|\\\\)*)""#, "string.quoted.double")),
            cust_rc_box!(|_| {
                Ok(ast!({"Type" "String" :}))
            }),
            cust_rc_box!(|parts| {
                // Undo the escaping:
                Ok(Value::Text(parts.get_term(n("body")).to_name().orig_sp()
                    .replace(r#"\""#, r#"""#)
                    .replace(r#"\\"#, r#"\"#)))
            })
        ),
        // Sequence literals. These actually can't be implemented as a macro
        //  until we get recursive macro invocations:
        //  there's no other way to go from a tuple to a sequence.
        typed_form!("seq_literal",
        (delim "s[", "[", (star (named "elt", (call "Expr")))),
            cust_rc_box!(|parts| {
                let mut elts = parts.get_rep_res(n("elt"))?;
                match elts.pop() {
                    None => Ok(ast!({"Type" "forall_type" :
                        "param" => ["T"],
                        "body" => (import [* [forall "param"]] { "Type" "type_apply" :
                        "type_rator" => (vr "Sequence"), "arg" => [(vr "T")]})})),
                    Some(ref t) => {
                        for ref other_elt in elts {
                            crate::ty_compare::must_equal(t, other_elt, &parts).map_err(
                                |e| crate::util::err::sp(e, parts.this_ast.clone())
                            )?;
                        }
                        Ok(ast!({ "Type" "type_apply" :
                            "type_rator" => (vr "Sequence"),
                            "arg" => [(, t.clone())]}))
                    }
                }
            }),
            cust_rc_box!(|parts| {
                Ok(Value::Sequence(
                    parts.get_rep_res(n("elt"))?.into_iter().map(|elt| Rc::new(elt)).collect()))
            })
        )
    ]
}
