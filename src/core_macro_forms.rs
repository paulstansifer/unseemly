use ast_walk::LazyWalkReses;
use grammar::FormPat::*;
use grammar::FormPat;
use grammar::SynEnv;
use std::rc::Rc;
use name::*;
use form::Form;
use ast::{Ast, Node, Atom};
use ast_walk::WalkRule::{NotWalked, LiteralLike, Custom};
use runtime::reify::Reifiable;
use runtime::eval::Closure;
use util::assoc::Assoc;
use ty::{Ty, SynthTy};
use walk_mode::WalkElt;
use core_type_forms::{more_quoted_ty, less_quoted_ty};
use core_forms::ast_to_name;

// Macros!
// Macro expansion happens after typechecking. Macro expansion happens after typechecking.
// You'd think I'd remember that better, what with that being the whole point of Unseemly, but nope.
// Here's how macros work:
// The programmer writes a syntax extension, e.g.:
//   extend '{ forall T . #{ (lit if) ,{Expr <[Bool]< | cond},
//                           (lit then) ,{Expr <[T]< | then}, (lit else) ,{Expr <[T]< | else}, }#
//              conditional -> .{ '[Expr | match ,[Expr | cond], {
//                                             +[True]+ => ,[Expr | then],
//                                             +[False]+ => ,[Expr | else], } ]' }. }'
//   in if (zero? five) then three else eight
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
//  (`cond`, `then`, and `else` are assumed to be their respective types,
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
        return Ty(mac_fn);
    } else {
        return ty!({"Type" "forall_type" :
            "body" => (import [* [forall "param"]] (, mac_fn)),
            "param" => (,seq forall_ty_vars.iter().map(|n| { Atom(*n) }).collect::<Vec<_>>())
        })
    }
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
        //     ∀ T . [*[x : Nt <[T]<  x: Nt <[T]<]* -> Nt <[T]<]
        // ... which you can imagine is the type of the implementation of the macro
        synth_type: ::form::Both(
            cust_rc_box!( move |parts| {

                // Typecheck the subterms, and then quote them:
                let q_parts = &parts.clone().map_terms(&mut |n: Name, t: &Ast| {
                        Ok(match grammar1.find_named_call(n).unwrap() {
                            Some(nt) => {
                                let term_ty = ::ty::synth_type(t, parts.env.clone())?;
                                more_quoted_ty(&term_ty, nt).concrete()
                            }
                            // Not a call (presumably a binder)
                            None => ast!({"Type" "Int" :}) // TODO: what do we do here??
                        })
                    })?;

                let mut arguments = Assoc::new();
                for binder in grammar1.binders() {
                    arguments = arguments.set(binder, q_parts.get_res(binder)?);
                }

                // This is lifted almost verbatim from "Expr" "apply". Maybe they should be unified?
                use walk_mode::WalkMode;
                let return_type = ::ty_compare::Subtype::underspecified(n("<return_type>"));

                let _ = ::ty_compare::must_subtype(
                    &macro_type(&[], arguments, return_type.clone()),
                    &SynthTy::walk_var(macro_name, &parts)?,
                    q_parts.env.clone()).map_err(|e| ::util::err::sp(e, q_parts.this_ast.clone()))?;

                // What return type made that work?
                let q_result = ::ty_compare::unification.with(|unif| {
                    let resolved = ::ty_compare::resolve(
                        ::ast_walk::Clo{ it: return_type, env: q_parts.env.clone()},
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

                let invoked_macro = &SynthTy::walk_var(macro_name, &parts_positive)?;

                let mut arguments = Assoc::new();
                for binder in grammar2.binders() {
                    match grammar2.find_named_call(binder).unwrap() {
                        Some(nt) => {
                            arguments = arguments.set(
                                binder, 
                                more_quoted_ty(&::ty_compare::Subtype::underspecified(binder), nt));
                        }
                        None => { /* not a call; do nothing, I guess? */ }
                    }
                }
                let expected_return_type = more_quoted_ty(parts.context_elt(), n("Pat"));

                let _ = ::ty_compare::must_subtype(
                    &macro_type(&[], arguments.clone(), expected_return_type),
                    invoked_macro,
                    parts.env.clone()).map_err(|e| ::util::err::sp(e, parts.this_ast.clone()))?;

                // What argument types made that work?
                let mut res : Assoc<Name, Ty> = Assoc::new();
                ::ty_compare::unification.with(|unif| {
                    for binder in &export_names {
                        let binder_clo = ::ty_compare::resolve(
                                ::ast_walk::Clo{
                                    it: arguments.find_or_panic(&binder).clone(), 
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
                for ref sub in parts.get_rep_res(n("elt"))? {
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
        syntax_syntax!( ([(named "body", (call "Syntax")), (lit "*")]) Star (
            body => Rc::new(FormPat::reflect(&body))
        )) => ["body"],
        syntax_syntax!( ([(named "body", (call "Syntax")), (lit "+")]) Plus (
            body => Rc::new(FormPat::reflect(&body))
        )) => ["body"],
        syntax_syntax!( ( (delim "alt[", "[", (star (named "elt", (call "Syntax"))))) Alt {
            |parts| {
                let mut out = Assoc::<Name, Ty>::new();
                for ref sub in parts.get_rep_res(n("elt"))? {
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
        // This has to have the same named parts as `unquote`, because it reuses its typechecker
        syntax_syntax!( ([(named "binder", aat), (lit "="),
                          (delim ",{", "{",
                           [(named "nt", aat),
                            (delim "<[", "[", /*]]*/ (named "ty_annot", (call "Type"))),
                            (lit "|"), (-- 1 (named "body", (call "Pat")))])])
        NamedCall { // We combine `Named` and `Call`
            |parts| {
                // This is a lot like the typechecker for `unquote`.
                // But the type walk (as an overall quotation and locally) is always negative.
                let expected_type = parts.switch_mode::<::ty::SynthTy>().get_res(n("ty_annot"))?;
                let nt = ast_to_name(&parts.get_term(n("nt")));

                let _res = parts.with_context(more_quoted_ty(&expected_type, nt));

                Ok(Assoc::new())
            }
        } {
            |parts| {
                Ok(Named(
                    ::name::Name::reflect(&parts.get_res(n("binder"))?),
                    Rc::new(Call(::name::Name::reflect(&parts.get_res(n("nt"))?)))).reify())
            }
        }) => ["binder"],
        // TODO ComputeSyntax
        syntax_syntax!( ([(lit "forall"), (star (named "param", aat)), (lit "."),
                          (delim "#{", "{",
                              (import [* [forall "param"]], (named "syntax", (call "Syntax")))),
                          (named "fake_type", (anyways (trivial))),
                          (named "macro_name", aat), (lit "->"),
                          (delim ".{", "{", (named "implementation",
                              // TODO `beta!` needs `Shadow` so we can combine these `import`s:
                              (import [* [forall "param"]],
                                  (import ["body" = "fake_type"], (call "Expr"))))),
                          (alt [], // TODO: needs proper `beta` structure, not just a name list:
                               [(lit "=>"), (star (named "export", aat))])])
        Scope {
            |parts| {
                // TODO: this ought to be tested!
                let return_ty = parts.switch_mode::<::ty::SynthTy>().get_res(n("body"))?;
                let arguments = parts.get_res(n("syntax"))?;
                let ty_params = &parts.get_rep_term(n("param")).iter().map(
                            |p| ast_to_name(p)).collect::<Vec<_>>();
                Ok(Assoc::new().set(ast_to_name(&parts.get_term(n("macro_name"))), 
                                    macro_type(&ty_params, arguments, return_ty)))
            }
        } {
            |parts| {
                let _macro_params = ::beta::bound_from_export_beta(
                    &ebeta!(["syntax"]), &parts.this_ast.node_parts());

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
                    // This needs to be used somewhere!
                        /*,*/
                        FormPat::reflect(&parts.get_res(n("syntax"))?),
                        ast_to_name(&parts.get_term(n("macro_name"))),
                        export_names),
                    export).reify())
            }
        }) => ["macro_name"] // This exports a macro, not syntax (like `binders` does)!

    ];

    assoc_n!("Syntax" => Rc::new(grammar_grammar))
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
fn use_basic_macro_invocation() {
    let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let pat_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Pat" });
    let int_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Int" :}]
    });
    let t_expr_type = ty!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [(vr "T")]
    });
    let t_pat_type = ty!({"Type" "type_apply" :
        "type_rator" => (,pat_type.clone()), "arg" => [(vr "T")]
    });
    let env = assoc_n!(
        "int_var" => ty!({ "Type" "Int" :}),
        "nat_var" => ty!({ "Type" "Nat" :}),
        "basic_int_macro" =>
            macro_type(&vec![], assoc_n!("a" => int_expr_type.clone()), int_expr_type.clone()),
        "basic_t_macro" =>
            macro_type(&vec![n("T")], assoc_n!("a" => t_expr_type.clone()), t_expr_type.clone()),
        "basic_pattern_macro" =>
            macro_type(&vec![n("T")], assoc_n!("a" => t_pat_type.clone()), t_pat_type.clone())
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
        ::ty::neg_synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_pattern_macro"), (named "a", (call "Pat"))]),
                    n("basic_pattern_macro"), vec![n("a")]) => ["a"];
                "a" => "should_be_nat"
            }),
            env.clone().set(negative_ret_val(), ty!({"Type" "Nat" :}))),
        Ok(assoc_n!("should_be_nat" => ty!({"Type" "Nat" :}))));

}

