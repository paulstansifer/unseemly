use ast_walk::LazyWalkReses;
use grammar::FormPat::*;
use grammar::FormPat;
use grammar::SynEnv;
use std::rc::Rc;
use name::*;
use form::Form;
use form::EitherPN::{Both};
use ast::{Ast, Node, Atom};
use ast_walk::WalkRule::{NotWalked, LiteralLike, Custom};
use runtime::reify::Reifiable;
use runtime::eval::Closure;
use util::assoc::Assoc;
use ty::{Ty, SynthTy};
use walk_mode::{WalkElt, WalkMode};
use core_type_forms::{more_quoted_ty, less_quoted_ty};
use core_forms::ast_to_name;

// Macros!
//
// Macro expansion happens after typechecking. Macro expansion happens after typechecking.
// You'd think I'd remember that better, what with that being the whole point of Unseemly, but nope.
// Here's how macros work:
// The programmer writes a macro definition, e.g.:
// forall T . '{ (lit if) ,{Expr <[Bool]< | cond},
//               (lit then) ,{Expr <[T]< | then_e},
//               (lit else) ,{Expr <[T]< | else_e}, }'
//  conditional -> .{ '[Expr | match ,[Expr | cond], {
//                                 +[True]+ => ,[Expr | then_e],
//                                 +[False]+ => ,[Expr | else_e], } ]' }.
// ...which can be added to the `SynEnv` in order to make the following valid:
//   if (zero? five) then three else eight
//
// The parser parses the `if` as a macro invocation, but doesn't lose the '{…}'!
//  It spits out an `Ast` in which the `extend` binds `conditional` and `if ⋯` references it.
//   Under the hood, `conditional` has the type
//    `∀ T . [ *[ cond : Expr <[Bool]<  then : Expr <[T]<  else : Expr <[T]<   -> Expr <[T]< ]* ]
//   ... even though it's a macro, not a function. (A kind-checker is needed here!)
//
// Everything is typechecked (including the `.{ ⋯ }.` implementation and the invocation).
//  The macro name (`conditional`) is a bit of a hack
// The syntax extension is typechecked, much like a function definition is.
//  (`cond`, `then_e`, and `else_e` are assumed to be their respective types,
//    and the macro is shown to produce an `Expr <[T]<`.)
// So is the invocation, which subtypes away the `T`, checks its arguments, and produces `T`.
//
// Macro expansion evaluates the macro with its arguments, `(zero? five)`, `three`, and `eight`,
//  producing a match statement.
//
// Finally, phase-0 evaluation produces a result of `8`!

// It's best to read this file in the voice of the /Pushing Daisies/ narrator.
// This macro is a helper for generating `FormPat`-generating syntactic forms.
macro_rules! syntax_syntax {
    // atomic FormPat
    (( $($gram:tt)* )  $syntax_name:ident  ) => {
        Rc::new(Form {
            name: n(&stringify!($syntax_name).to_lowercase()),
            grammar: Rc::new(form_pat!( $($gram)* )),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            // Binds nothing
            synth_type: ::form::Both(NotWalked, cust_rc_box!(|_parts| { Ok(Assoc::new())}) ),
            eval: ::form::Positive(cust_rc_box!(|_parts| {
                Ok(::grammar::FormPat::$syntax_name.reify())}
            )),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        })
    };

    // FormPat with arguments
    (( $($gram:tt)* )  $syntax_name:ident ( $($arg:ident => $e:expr),* ) ) => {
        Rc::new(Form {
            name: n(&stringify!($syntax_name).to_lowercase()),
            grammar: Rc::new(form_pat!( $($gram)* )),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            synth_type: ::form::Negative(cust_rc_box!(|parts| {
                let mut out = ::util::assoc::Assoc::<Name, ::ty::Ty>::new();
                $(
                    out = out.set_assoc(&parts.get_res(n(&stringify!($arg)))?);
                )*
                Ok(out)
            })),
            eval: ::form::Positive(cust_rc_box!(|parts| {
                Ok(::grammar::FormPat::$syntax_name(
                    $( { let $arg = parts.get_res(n(&stringify!($arg)))?; $e } ),*
                ).reify())}
            )),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        })
    };
    // FormPat with arguments, and just doing `get_res` on everything doesn't work:
    (( $($gram:tt)* )  $syntax_name:ident { $type:expr } { $eval:expr }) => {
        Rc::new(Form {
            name: n(&stringify!($syntax_name).to_lowercase()),
            grammar: Rc::new(form_pat!( $($gram)* )),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            synth_type: ::form::Negative(cust_rc_box!( $type )), // Produces a typed value
            eval: ::form::Positive(cust_rc_box!( $eval )),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        })
    };
}

// Macros have types!
// ...but they're not higher-order (i.e., you can't do anything with a macro other than invoke it).
// This means that we can just generate a type for them at the location of invocation.
fn macro_type(forall_ty_vars: &[Name], arguments: Assoc<Name, Ty>, output: Ty) -> Ty {
    let mut components = vec![];
    for (k,v) in arguments.iter_pairs() {
        components.push(mbe!("component_name" => (, Atom(*k)), "component" => (, v.to_ast())));
    }
    let argument_struct = Node(::core_forms::find_core_form("Type", "struct"),
        ::util::mbe::EnvMBE::new_from_anon_repeat(components), ::beta::ExportBeta::Nothing);
    let mac_fn = ast!({"Type" "fn" :
        "param" => [(, argument_struct)],
        "ret" => (, output.to_ast())
    });

    if forall_ty_vars.is_empty() {
        Ty(mac_fn)
    } else {
        ty!({"Type" "forall_type" :
            "body" => (import [* [forall "param"]] (, mac_fn)),
            "param" => (,seq forall_ty_vars.iter().map(|n| { Atom(*n) }).collect::<Vec<_>>())
        })
    }
}

fn type_macro_invocation(macro_name: Name, parts: &LazyWalkReses<::ty::SynthTy>,
                         expected_return: Ty, grammar: &FormPat)
        -> Result<Assoc<Name, Ty>, ::ty::TypeError> {
    // Typecheck the subterms, and then quote them:
    let mut q_arguments = Assoc::new();

    for (binder, depth) in grammar.binders() {
        if let Some(nt) = grammar.find_named_call(binder).unwrap() {
            let term_ty = if ::core_type_forms::nt_is_positive(nt) {
                parts.flatten_res_at_depth(binder, depth, &|ty_vec: Vec<Ty>| {
                    ty!({"Type" "tuple" :
                        "component" => (,seq ty_vec.iter().map(|ty| ty.concrete()))
                    })
                })?
            } else {
                ::ty_compare::Subtype::underspecified(binder)
            };
            q_arguments = q_arguments.set(binder, more_quoted_ty(&term_ty, nt));
        } // Otherwise, it's not a call (should we treat this more like `Pat`?)
    }

    // This is lifted almost verbatim from "Expr" "apply". Maybe they should be unified?
    use walk_mode::WalkMode;

    let _ = ::ty_compare::must_subtype(
        &macro_type(&[], q_arguments.clone(), expected_return),
        &SynthTy::walk_var(macro_name, &parts)?,
        parts.env.clone()).map_err(|e| ::util::err::sp(e, parts.this_ast.clone()))?;

    Ok(q_arguments)
}

// This will be called at parse-time to generate the `Ast` for a macro invocation.
// The form it emits is analogous to the "Expr" "apply" form.
fn macro_invocation(grammar: FormPat, macro_name: Name, export_names: Vec<Name>) -> Rc<Form> {
    use walk_mode::WalkMode;

    let grammar1 = grammar.clone();
    let grammar2 = grammar.clone();
    Rc::new(Form {
        name: n("macro_invocation"), // TODO: maybe generate a fresh name?
        grammar: Rc::new(grammar.clone()), // For pretty-printing
        type_compare: ::form::Both(NotWalked, NotWalked),
        // Invoked at typechecking time.
        // `macro_name` will be bound to a type of the form
        //     ∀ T . [*[x : Nt <[T]< ⋯ ]* -> Nt <[T]<]
        // ... which you can imagine is the type of the implementation of the macro
        synth_type: ::form::Both(
            cust_rc_box!( move |parts| {
                let return_type = ::ty_compare::Subtype::underspecified(n("<return_type>"));
                let _ = type_macro_invocation(macro_name, &parts, return_type.clone(), &grammar1)?;

                // What return type made that work?
                let q_result = ::ty_compare::unification.with(|unif| {
                    let resolved = ::ty_compare::resolve(
                        ::ast_walk::Clo{ it: return_type, env: parts.env.clone()},
                        &unif.borrow());

                    // Canonicalize the type in its environment:
                    let resolved = ::ty_compare::canonicalize(&resolved.it, resolved.env);
                    resolved.map_err(|e| ::util::err::sp(e, parts.this_ast.clone()))
                })?;

                less_quoted_ty(&q_result, Some(n("Expr")), &parts.this_ast)
            }),
            cust_rc_box!( move |parts| {
                // From the macro's point of view, its parts are all positive;
                // they all produce (well, expand to), rather than consume, syntax.
                let parts_positive = parts.switch_mode::<SynthTy>();
                let expected_return_type = more_quoted_ty(parts.context_elt(), n("Pat"));

                let arguments = type_macro_invocation(macro_name, &parts_positive,
                                                      expected_return_type, &grammar2)?;

                // What argument types made that work?
                let mut res : Assoc<Name, Ty> = Assoc::new();
                ::ty_compare::unification.with(|unif| {
                    for binder in &export_names {
                        let ty = arguments.find_or_panic(binder);
                        let binder_clo = ::ty_compare::resolve(
                                ::ast_walk::Clo{
                                    it: ty.clone(),
                                    env: parts.env.clone()
                                },
                            &unif.borrow());
                        let binder_ty = ::ty_compare::canonicalize(&binder_clo.it, binder_clo.env)
                            .map_err(|e| ::util::err::sp(e, parts.this_ast.clone()))?;

                        for (ty_n, ty)
                                in parts.with_context(binder_ty).get_res(*binder)?.iter_pairs() {
                            res = res.set(*ty_n,
                                          less_quoted_ty(ty, Some(n("Pat")), &parts.this_ast)?);
                        }
                    }

                    Ok(res)
                })
            })
        ),
        eval: ::form::Both(NotWalked, NotWalked), // Macros should be expanded first!
        quasiquote: ::form::Both(LiteralLike, LiteralLike)
    })
}

pub fn make_core_macro_forms() -> SynEnv {
    let trivial_type_form = ::core_type_forms::type_defn("unused", form_pat!((impossible)));

    // Most of "Syntax" is a negative walk (because it produces an environment),
    //  but lacking a `negative_ret_val`.
    let grammar_grammar = forms_to_form_pat_export![
        syntax_syntax!( ( (delim "anyways,{", "{", (named "body", (call "Expr"))) ) Anyways (
            body => ::ast::Ast::reflect(&body)
        )) => ["body"],
        syntax_syntax!( ((lit "impossible")) Impossible ) => [],
        syntax_syntax!( ((delim "{", "{", [(lit "lit"), (named "body", aat)]) ) Literal (
            body => ::name::Name::reflect(&body)
        )) => ["body"],
        syntax_syntax!( ((lit "any_token")) AnyToken ) => [],
        syntax_syntax!( ((lit "atom")) AnyToken ) => [],
        syntax_syntax!( ((lit "vr")) VarRef ) => [],
        syntax_syntax!( ([(lit "delim"), (named "name", aat), (named "br", (anyways "[")),
                          (delim "[", "[", (named "body", (call "Syntax"))) ]  ) Delimited (
            name => n(&format!("{}[", ::name::Name::reflect(&name))),
            br => ::read::delim(&::name::Name::reflect(&br).sp()),
            body => Rc::new(FormPat::reflect(&body))
        )) => ["body"],
        syntax_syntax!( ([(lit "delim"), (named "name", aat), (named "br", (anyways "(")),
                          (delim "(", "(", (named "body", (call "Syntax"))) ]  ) Delimited (
            name => n(&format!("{}(", ::name::Name::reflect(&name))),
            br => ::read::delim(&::name::Name::reflect(&br).sp()),
            body => Rc::new(FormPat::reflect(&body))
        )) => ["body"],
        syntax_syntax!( ([(lit "delim"), (named "name", aat), (named "br", (anyways "{")),
                          (delim "{", "{", (named "body", (call "Syntax"))) ]  ) Delimited (
            name => n(&format!("{}{{", ::name::Name::reflect(&name))),
            br => ::read::delim(&::name::Name::reflect(&br).sp()),
            body => Rc::new(FormPat::reflect(&body))
        )) => ["body"],
        // TODO: split out a separate SyntaxSeq, so that we can get rid of the [ ] delimiters
        syntax_syntax!( ( (delim "[", "[", (star (named "elt", (call "Syntax"))))) Seq {
            |parts| {
                let mut out = Assoc::<Name, Ty>::new();
                for sub in &parts.get_rep_res(n("elt"))? {
                    out = out.set_assoc(sub);
                }
                Ok(out)
            }
        } {
            |parts| {
                Ok(Seq(parts.get_rep_res(n("elt"))?.iter().map(|val| {
                    Rc::new(FormPat::reflect(val))
                }).collect()).reify())
            }
        }) => [* ["elt"]],
        syntax_syntax!( ([(named "body", (call "Syntax")), (lit "*")]) Star {
            |parts| {
                let body : Assoc<Name, Ty> = parts.get_res(n("body"))?;
                let seq_body = body.map(::runtime::reify::sequence_type__of);
                Ok(seq_body)
            }
        } {
            |parts| {
                Ok(Star(Rc::new(FormPat::reflect(&parts.get_res(n("body"))?))).reify())
            }
        }) => ["body"],
        syntax_syntax!( ([(named "body", (call "Syntax")), (lit "+")]) Plus {
            |parts| {
                let body : Assoc<Name, Ty> = parts.get_res(n("body"))?;
                let seq_body = body.map(::runtime::reify::sequence_type__of);
                Ok(seq_body)
            }
        } {
            |parts| {
                Ok(Plus(Rc::new(FormPat::reflect(&parts.get_res(n("body"))?))).reify())
            }
        }) => ["body"],
        syntax_syntax!( ( (delim "alt[", "[", (star (named "elt", (call "Syntax"))))) Alt {
            |parts| {
                let mut out = Assoc::<Name, Ty>::new();
                for sub in &parts.get_rep_res(n("elt"))? {
                    out = out.set_assoc(sub);
                }
                Ok(out)
            }
        } {
            |parts| {
                Ok(Alt(parts.get_rep_res(n("elt"))?.iter().map(|val| {
                    Rc::new(FormPat::reflect(val))
                }).collect()).reify())
            }
        }) => [* ["elt"]],
        syntax_syntax!( ([(named "plan_a", (call "Syntax")),
                          (delim "or{", "{", (named "plan_b", (call "Syntax")))  ]) Biased (
            plan_a => Rc::new(FormPat::reflect(&plan_a)),
            plan_b => Rc::new(FormPat::reflect(&plan_b))
        )) => ["plan_a" "plan_b"],
        // `Named` switches to a positive mode for typechecking its body.
        // TODO: I don't think this makes sense, now that `Named` and `Call` are split apart:
        //   TODO: replace `binder` with a `Pat`, and make the following true:
        //     This has to have the same named parts as `unquote`, because it reuses its typechecker
        //     But the type walk (as an overall quotation and locally) is always negative.
        syntax_syntax!( ([(named "part_name", aat), (lit "="), (named "body", (call "Syntax"))])
        Named {
            |parts| {
                let binder = ast_to_name(&parts.get_term(n("part_name")));
                Ok(Assoc::new().set(binder, parts.switch_mode::<SynthTy>().get_res(n("body"))?))
            }
        } {
            |parts| {
                Ok(Named(
                    ::name::Name::reflect(&parts.get_res(n("part_name"))?),
                    Rc::new(FormPat::reflect(&parts.get_res(n("body"))?))).reify())
            }
        }) => ["part_name"],
        // `Call` is positive (has to be under a `Named`)
        Rc::new(Form {
            name: n("call"),
            grammar: Rc::new(form_pat!(
                (delim ",{", "{",
                    [(named "nt", aat), (delim "<[", "[", (named "ty_annot", (call "Type")))]))),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            synth_type: Both(cust_rc_box!(|parts| {
                let expected_type = parts.get_res(n("ty_annot"))?;
                let nt = ast_to_name(&parts.get_term(n("nt")));

                Ok(more_quoted_ty(&expected_type, nt))
            }), NotWalked),
            eval: ::form::Positive(cust_rc_box!(|parts| {
                Ok(Rc::new(Call(::name::Name::reflect(&parts.get_res(n("nt"))?))).reify())
            })),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        }) => [],
        // `Import` is positive (has to be under a `Named`)
        Rc::new(Form {
            name: n("import"),
            grammar: Rc::new(form_pat!(
                (delim ",{", "{",
                    [(named "nt", aat), (delim "<[", "[", (named "ty_annot", (call "Type")))]))),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            synth_type: Both(cust_rc_box!(|parts| {
                let expected_type = parts.get_res(n("ty_annot"))?;
                let nt = ast_to_name(&parts.get_term(n("nt")));

                Ok(more_quoted_ty(&expected_type, nt))
            }), NotWalked),
            eval: ::form::Positive(cust_rc_box!(|parts| {
                Ok(Rc::new(Call(::name::Name::reflect(&parts.get_res(n("nt"))?))).reify())
            })),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        }) => [],
        // TODO: implement syntax for ComputeSyntax
        // Not sure if `Scope` syntax should be positive or negative.
        syntax_syntax!( ([(lit "forall"), (star (named "param", aat)), (lit "."),
                          (delim "'{", "{",
                              (import [* [forall "param"]], (named "syntax", (call "Syntax")))),
                          // We need an arbitrary negative_ret_val:
                          (named "unused_type", (anyways {trivial_type_form ; } )),
                          (named "macro_name", aat), (lit "->"),
                          (delim ".{", "{", (named "implementation",
                              // TODO `beta!` needs `Shadow` so we can combine these `import`s:
                              (import [* [forall "param"]],
                                  (import ["syntax" = "unused_type"], (call "Expr"))))),
                          (alt [], // TODO: needs proper `beta` structure, not just a name list:
                               [(lit "=>"), (star (named "export", aat))])])
        Scope {
            |parts| {
                let return_ty = parts.switch_mode::<::ty::SynthTy>().get_res(n("implementation"))?;
                let arguments = parts.get_res(n("syntax"))?;
                let ty_params = &parts.get_rep_term(n("param")).iter().map(
                            |p| ast_to_name(p)).collect::<Vec<_>>();
                Ok(Assoc::new().set(ast_to_name(&parts.get_term(n("macro_name"))),
                                    macro_type(&ty_params, arguments, return_ty)))
            }
        } {
            |parts| {
                // TODO: I think this is to check that `get_res` will work, but it might be
                // a leftover mistake:
                let _macro_params = ::beta::bound_from_export_beta(
                    &ebeta!(["syntax"]), &parts.this_ast.node_parts(), 0);

                let mut export = ::beta::ExportBeta::Nothing;
                let export_names = parts.get_rep_term(n("export")).iter()
                    .map(ast_to_name).collect::<Vec<Name>>();
                for name in &export_names {
                    export = ::beta::ExportBeta::Shadow(
                        Box::new(::beta::ExportBeta::Use(*name)),
                        Box::new(export));
                }

                // This macro invocation (will replace `syntax`)
                Ok(Scope(macro_invocation(
                        FormPat::reflect(&parts.get_res(n("syntax"))?),
                        ast_to_name(&parts.get_term(n("macro_name"))),
                        export_names),
                    export).reify())
            }
        }) => ["macro_name"] // This exports a macro, not syntax (like `binders` does)!

    ];

    assoc_n!("Syntax" => Rc::new(grammar_grammar))
}

custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct ExpandMacros {}
}
custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct UnusedNegativeExpandMacros {}
}

fn expand_macro(parts: ::ast_walk::LazyWalkReses<ExpandMacros>) -> Result<Ast, ()> {
    let mut env = Assoc::new(); // TODO: there should probably be something in scope here...

    let macro_form: &Form = parts.this_ast.node_form();

    // Turn the subterms into values
    for (binder, _depth) in macro_form.grammar.binders() {
        if let Some(_nt) = macro_form.grammar.find_named_call(binder).unwrap() {
            env = env.set(binder, ::runtime::eval::Value::from_ast(&parts.get_term(binder)));
        } // Otherwise, it's not a call (presumably a binder)
    }

    let expanded = ::runtime::eval::eval(&parts.get_term(n("implementation")), env)?.to_ast();

    expand(&expanded, parts.env)
}

impl WalkMode for ExpandMacros {
    fn name() -> &'static str { "MExpand" }
    type Elt = Ast;
    type Negated = UnusedNegativeExpandMacros;
    type Err = ();  // TODO: should be the same as runtime errors
    type D = ::walk_mode::Positive<ExpandMacros>;
    type ExtraInfo = ();

    fn get_walk_rule(f: &Form) -> ::ast_walk::WalkRule<ExpandMacros> {
        if f.name == n("macro_invocation") {
            cust_rc_box!(expand_macro)
        } else {
            LiteralLike
        }
    }
    fn automatically_extend_env() -> bool { true }
}
impl WalkMode for UnusedNegativeExpandMacros {
    fn name() -> &'static str { "XXXXX" }
    type Elt = Ast;
    type Negated = ExpandMacros;
    type Err = ();
    type D = ::walk_mode::Positive<UnusedNegativeExpandMacros>;
    type ExtraInfo = ();
    fn get_walk_rule(_: &Form) -> ::ast_walk::WalkRule<UnusedNegativeExpandMacros> { panic!("ICE") }
    fn automatically_extend_env() -> bool { panic!("ICE") }
}

pub fn expand(ast: &Ast, env: Assoc<Name, Ast>) -> Result<Ast, ()> {
    ::ast_walk::walk::<ExpandMacros>(ast, &LazyWalkReses::new_wrapper(env))
}


#[test]
fn formpat_reflection() {
    use ::runtime::eval::eval_top;
    use core_forms::find_form;
    let macro_forms = make_core_macro_forms();

    assert_eq!(
        FormPat::reflect(&eval_top(
            &ast!({find_form(&macro_forms, "Syntax", "impossible"); })).unwrap()),
        Impossible);

    assert_eq!(
        FormPat::reflect(&eval_top(
            &ast!({find_form(&macro_forms, "Syntax", "literal"); "body" =>
                {"Expr" "quote_expr" : "nt" => "Expr", "body" => (++ true "<--->")}
             })).unwrap()),
        Literal(n("<--->")));
}

#[test]
fn macro_definitions() {
    let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let pat_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Pat" });
    let int_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Int" :}]
    });
    let env = assoc_n!("ie" => int_expr_type.clone()).set(negative_ret_val(), ty!((trivial)));

    assert_eq!(
        ::ty::neg_synth_type(
            &ast!({"Syntax" "star" => ["body"] :
                "body" => {"Syntax" "named" => ["part_name"] :
                    "part_name" => "x",
                    "body" => {"Syntax" "call" :
                        "nt" => "Expr",
                        "ty_annot" => {"Type" "Int" :}
                    }
                }
            }), env.clone()),
        Ok(assoc_n!("x" => ::runtime::reify::sequence_type__of(
            &int_expr_type))));

    let t_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "T")]
    });
    let s_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "S")]
    });
    let t_pat_type = ty!({"Type" "type_apply" :
        "type_rator" => (,pat_type.clone()), "arg" => [(vr "T")]
    });

    assert_eq!(
    ::ty::neg_synth_type(&ast!(
            {"Syntax" "scope" :
                "param" => ["T", "S"],
                "syntax" => (import [* [forall "param"]] {"Syntax" "seq" => [* ["elt"]] :
                    "elt" => [
                        {"Syntax" "named" => ["part_name"] :
                            "part_name" => "val",
                            "body" => {"Syntax" "call" : "nt" => "Expr", "ty_annot" => (vr "T")}},
                        {"Syntax" "named" => ["part_name"] :
                            "part_name" => "binding",
                            "body" => {"Syntax" "call" : "nt" => "Pat", "ty_annot" => (vr "T")}},
                        {"Syntax" "named" => ["part_name"] :
                            "part_name" => "body",
                            "body" => {"Syntax" "call" : "nt" => "Expr", "ty_annot" => (vr "S")}}]
                }),
                "unused_type" => {"Type" "Nat" :}, // In practice, this is a `trivial_type_form`
                "macro_name" => "some_macro",
                "implementation" => (import [* [forall "param"]] (import ["syntax" = "unused_type"]
                    (vr "ie")))
            }), env.clone()),
        Ok(assoc_n!(
            "some_macro" => macro_type(&vec![n("T"), n("S")],
                                       assoc_n!("body" => s_expr_type.clone(),
                                                "binding" => t_pat_type.clone(),
                                                "val" => t_expr_type.clone()),
                                       int_expr_type.clone()))));

}

#[test]
fn macro_types() {
    let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let int_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Int" :}]
    });
    let t_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "T")]
    });
    assert_eq!(macro_type(&vec![], assoc_n!("a" => int_expr_type.clone()), int_expr_type.clone()),
               ty!({"Type" "fn" :
                    "param" => [{"Type" "struct" :
                        "component" => [@"c" (, int_expr_type.concrete())],
                        "component_name" => [@"c" "a"]
                    }],
                    "ret" => (, int_expr_type.concrete() )}));
    assert_eq!(
        macro_type(&vec![n("T")], assoc_n!("a" => t_expr_type.clone()), t_expr_type.clone()),
            ty!({"Type" "forall_type" :
                "param" => ["T"],
                "body" => (import [* [forall "param"]] {"Type" "fn" :
                    "param" => [{"Type" "struct" :
                        "component" => [@"c" (, t_expr_type.concrete())],
                        "component_name" => [@"c" "a"]
                    }],
                    "ret" => (, t_expr_type.concrete() )})}));
}

#[test]
fn type_basic_macro_invocation() {
    let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let pat_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Pat" });
    let type_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Type" });
    let int_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Int" :}]
    });
    let t_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "T")]
    });
    let s_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "S")]
    });
    let t_pat_type = ty!({"Type" "type_apply" :
        "type_rator" => (,pat_type.clone()), "arg" => [(vr "T")]
    });
    let t_type_type = ty!({"Type" "type_apply" :
        "type_rator" => (,type_type.clone()), "arg" => [(vr "T")]
    });
    let env = assoc_n!(
        "int_var" => ty!({ "Type" "Int" :}),
        "nat_var" => ty!({ "Type" "Nat" :}),
        "basic_int_macro" =>
            macro_type(&vec![], assoc_n!("a" => int_expr_type.clone()), int_expr_type.clone()),
        "basic_t_macro" =>
            macro_type(&vec![n("T")], assoc_n!("a" => t_expr_type.clone()), t_expr_type.clone()),
        "basic_pattern_macro" =>
            macro_type(&vec![n("T")], assoc_n!("a" => t_pat_type.clone()), t_pat_type.clone()),
        "let_like_macro" =>
            macro_type(&vec![n("T"), n("S")],
                       assoc_n!("val" => t_expr_type.clone(),
                                "binding" => t_pat_type.clone(),
                                "body" => s_expr_type.clone()),
                       s_expr_type.clone()),
        "pattern_cond_like_macro" =>
            macro_type(&vec![n("T"), n("S")],
                       assoc_n!("t" => t_type_type.clone(),
                                "body" => t_pat_type.clone(),
                                "cond_expr" => int_expr_type.clone()), // (would really be a bool)
                       t_pat_type.clone())

    );
    assert_eq!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_int_macro"), (named "a", (call "Expr"))]),
                    n("basic_int_macro"), vec![]) ;
                "a" => (vr "int_var")
            }),
            env.clone()),
        Ok(ty!({ "Type" "Int" :})));

    assert_eq!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_t_macro"), (named "a", (call "Expr"))]),
                    n("basic_t_macro"), vec![]) ;
                "a" => (vr "nat_var")
            }),
            env.clone()),
        Ok(ty!({ "Type" "Nat" :})));

    assert_m!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_int_macro"), (named "a", (call "Expr"))]),
                    n("basic_int_macro"), vec![]) ;
                "a" => (vr "nat_var")
            }),
            env.clone()),
        Err(_));

    assert_eq!(
        ::ty::neg_synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_pattern_macro"), (named "a", (call "Pat"))]),
                    n("basic_pattern_macro"), vec![n("a")]) => ["a"];
                "a" => "should_be_nat"
            }),
            env.clone().set(negative_ret_val(), ty!({"Type" "Nat" :}))),
        Ok(assoc_n!("should_be_nat" => ty!({"Type" "Nat" :}))));

    assert_eq!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke let_like_macro"),
                               (named "val", (call "Expr")),
                               (named "binding", (call "Pat")),
                               (named "body", (import ["binding" = "val"], (call "Expr")))]),
                    n("let_like_macro"), vec![]) ;
                "val" => (vr "nat_var"),
                "binding" => "x",
                "body" => (import ["binding" = "val"] (vr "x"))
            }),
            env.clone()),
        Ok(ty!({ "Type" "Nat" :})));

    assert_eq!(
        ::ty::neg_synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke pattern_cond_like_macro"),
                               (named "t", (call "Type")),
                               (named "body", (call "Pat")),
                               (named "cond_expr", (import ["body" : "t"], (call "Expr")))]),
                    n("pattern_cond_like_macro"), vec![n("body")]) ;
                "t" => {"Type" "Int" :},
                "body" => "x",
                "cond_expr" => (import ["body" : "t"] (vr "x"))
            }),
            env.set(negative_ret_val(), ty!({"Type" "Int" :})).clone()),
        Ok(assoc_n!("x" => ty!({ "Type" "Int" :}))));

}

#[test]
fn type_ddd_macro() {
        let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let pat_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Pat" });
    let t_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "T")]
    });
    let s_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "S")]
    });
    let t_pat_type = ty!({"Type" "type_apply" :
        "type_rator" => (,pat_type.clone()), "arg" => [(vr "T")]
    });
    let env = assoc_n!(
        "int_var" => ty!({ "Type" "Int" :}),
        "nat_var" => ty!({ "Type" "Nat" :}),
        "let_like_macro" =>
            macro_type(&vec![n("T"), n("S")],
                       assoc_n!("val" => t_expr_type.clone(),
                                "binding" => t_pat_type.clone(),
                                "body" => s_expr_type.clone()),
                       s_expr_type.clone()));

    assert_eq!(
    ::ty::synth_type(
        &ast!({
            macro_invocation(
                form_pat!([(lit "invoke let_like_macro"),
                            (star (named "val", (call "Expr"))),
                            (star (named "binding", (call "Pat"))),
                            (named "body", (import [* ["binding" = "val"]], (call "Expr")))]),
                n("let_like_macro"), vec![]) ;
            "val" => [@"arm" (vr "nat_var"), (vr "nat_var")],
            "binding" => [@"arm" "x1", "x2"],
            "body" => (import [* ["binding" = "val"]] (vr "x1"))
        }),
        env.clone()),
    Ok(ty!({ "Type" "Nat" :})));
}


#[test]
fn expand_basic_macros() {

}
