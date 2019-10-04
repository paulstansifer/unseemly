use ast::{Ast, Atom, Node};
use ast_walk::{
    LazyWalkReses,
    WalkRule::{Body, Custom, LiteralLike, NotWalked},
};
use beta::Beta::*;
use core_forms::ast_to_name;
use core_type_forms::{less_quoted_ty, more_quoted_ty};
use form::{EitherPN::Both, Form};
use grammar::{
    FormPat::{self, *},
    SynEnv,
};
use name::*;
use runtime::{eval::Closure, reify::Reifiable};
use std::rc::Rc;
use ty::{SynthTy, Ty};
use util::assoc::Assoc;
use walk_mode::WalkElt;

// Macros!
//
// Macro expansion happens after typechecking. Macro expansion happens after typechecking.
// You'd think I'd remember that better, what with that being the whole point of Unseemly, but nope.
// Here's how macros work:
// The programmer writes a macro definition, e.g.:
//
// extend_syntax macro
//     Expr :+:=
//         forall T . '{ (lit if) ,{Expr <[Bool]< | cond},
//             (lit then) ,{Expr <[T]< | then_e},
//             (lit else) ,{Expr <[T]< | else_e}, }'
//         conditional ->
//         '[Expr | match ,[Expr | cond], {
//             +[True]+ => ,[Expr | then_e],
//             +[False]+ => ,[Expr | else_e], } ]'
//     in
//         if (zero? five) then three else eight
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
                Ok($syntax_name.reify())}
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
                Ok($syntax_name(
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
fn macro_type(forall_ty_vars: &[Name], arguments: Vec<(Name, Ty)>, output: Ty) -> Ty {
    let mut components = vec![];
    for (k, v) in arguments.iter() {
        components.push(mbe!("component_name" => (, Atom(*k)), "component" => (, v.to_ast())));
    }
    let argument_struct = Node(
        ::core_forms::find_core_form("Type", "struct"),
        ::util::mbe::EnvMBE::new_from_anon_repeat(components),
        ::beta::ExportBeta::Nothing,
    );
    let mac_fn = u!({Type fn : [(, argument_struct)] (, output.to_ast())});

    if forall_ty_vars.is_empty() {
        Ty(mac_fn)
    } else {
        ty!({"Type" "forall_type" :
            "body" => (import [* [forall "param"]] (, mac_fn)),
            "param" => (,seq forall_ty_vars.iter().map(|n| { Atom(*n) }).collect::<Vec<_>>())
        })
    }
}

fn type_macro_invocation(
    macro_name: Name,
    parts: &LazyWalkReses<::ty::SynthTy>,
    expected_return: Ty,
    grammar: &FormPat,
) -> Result<Assoc<Name, Ty>, ::ty::TypeError>
{
    // Typecheck the subterms, and then quote them:
    let mut q_arguments = vec![];

    for (binder, depth) in grammar.binders() {
        let nt = grammar.find_named_call(binder).unwrap();
        let term_ty = if ::core_type_forms::nt_is_positive(nt) {
            parts.flatten_res_at_depth(binder, depth, &|ty_vec: Vec<Ty>| {
                ty!({"Type" "tuple" :
                    "component" => (,seq ty_vec.iter().map(|ty| ty.concrete()))
                })
            })?
        } else {
            ::ty_compare::Subtype::underspecified(binder)
        };
        q_arguments.push((binder, more_quoted_ty(&term_ty, nt)));
    }

    // This is lifted almost verbatim from "Expr" "apply". Maybe they should be unified?
    use walk_mode::WalkMode;

    let _ = ::ty_compare::must_subtype(
        &macro_type(&[], q_arguments.clone(), expected_return),
        &SynthTy::walk_var(macro_name, &parts)?,
        parts.env.clone(),
    )
    .map_err(|e| ::util::err::sp(e, parts.this_ast.clone()))?;

    // TODO: I think `Assoc` should implement `From<Vec<(K,V)>>`, maybe?
    let mut res = Assoc::new();
    for (k, v) in q_arguments {
        res = res.set(k, v.clone())
    }

    Ok(res)
}

// This will be called at parse-time to generate the `Ast` for a macro invocation.
// The form it emits is analogous to the "Expr" "apply" form.
// Public for use in `expand.rs` tests.
pub fn macro_invocation(
    grammar: FormPat,
    macro_name: Name,
    implementation: ::runtime::eval::Closure,
    export_names: Vec<Name>,
) -> Rc<Form>
{
    use walk_mode::WalkMode;

    let grammar1 = grammar.clone();
    let grammar2 = grammar.clone();
    Rc::new(Form {
        name: n("macro_invocation"), // TODO: maybe generate a fresh name?
        grammar: Rc::new(grammar.clone()),
        type_compare: ::form::Both(NotWalked, NotWalked),
        // Invoked at typechecking time.
        // `macro_name` will be bound to a type of the form
        //     ∀ T . [*[x : Nt <[T]< ⋯ ]* -> Nt <[T]<]
        // ... which you can imagine is the type of the implementation of the macro
        synth_type: ::form::Both(
            cust_rc_box!(move |parts| {
                let return_type = ::ty_compare::Subtype::underspecified(n("<return_type>"));
                let _ = type_macro_invocation(macro_name, &parts, return_type.clone(), &grammar1)?;

                // What return type made that work?
                let q_result = ::ty_compare::unification.with(|unif| {
                    let resolved = ::ty_compare::resolve(
                        ::ast_walk::Clo { it: return_type, env: parts.env.clone() },
                        &unif.borrow(),
                    );

                    // Canonicalize the type in its environment:
                    let resolved = ::ty_compare::canonicalize(&resolved.it, resolved.env);
                    resolved.map_err(|e| ::util::err::sp(e, parts.this_ast.clone()))
                })?;

                less_quoted_ty(&q_result, Some(n("Expr")), &parts.this_ast)
            }),
            cust_rc_box!(move |parts| {
                // From the macro's point of view, its parts are all positive;
                // they all produce (well, expand to), rather than consume, syntax.
                let parts_positive = parts.switch_mode::<SynthTy>();
                let expected_return_type = more_quoted_ty(parts.context_elt(), n("Pat"));

                let arguments = type_macro_invocation(
                    macro_name,
                    &parts_positive,
                    expected_return_type,
                    &grammar2,
                )?;

                // What argument types made that work?
                let mut res: Assoc<Name, Ty> = Assoc::new();
                ::ty_compare::unification.with(|unif| {
                    for binder in &export_names {
                        let ty = arguments.find_or_panic(binder);
                        let binder_clo = ::ty_compare::resolve(
                            ::ast_walk::Clo { it: ty.clone(), env: parts.env.clone() },
                            &unif.borrow(),
                        );
                        let binder_ty = ::ty_compare::canonicalize(&binder_clo.it, binder_clo.env)
                            .map_err(|e| ::util::err::sp(e, parts.this_ast.clone()))?;

                        for (ty_n, ty) in
                            parts.with_context(binder_ty).get_res(*binder)?.iter_pairs()
                        {
                            res = res
                                .set(*ty_n, less_quoted_ty(ty, Some(n("Pat")), &parts.this_ast)?);
                        }
                    }

                    Ok(res)
                })
            }),
        ),
        // Kind of a HACK, but we re-use `eval` instead of having a separate field.
        eval: ::form::Positive(cust_rc_box!(move |parts| {
            // This code is basically the same as for "apply".
            let mut env = implementation.env.clone();
            for param in &implementation.params {
                let nt = grammar.find_named_call(*param).unwrap();

                if nt != n("DefaultName") && nt != n("Ident") {
                    // TODO: why not?
                    env =
                        env.set(*param, ::runtime::eval::Value::from_ast(&parts.get_term(*param)));
                }
            }
            let expanded = Ast::reflect(&::runtime::eval::eval(&implementation.body, env)?);

            // Expand any macros that were produced by expansion, or were already present in subterms:
            Ok(::expand::expand(&expanded)?.reify())
        })),
        quasiquote: ::form::Both(LiteralLike, LiteralLike),
    })
}

pub fn make_core_macro_forms() -> SynEnv {
    let trivial_type_form = ::core_type_forms::type_defn("unused", form_pat!((impossible)));

    let beta_grammar = forms_to_form_pat_export![
        syntax_syntax!( ((lit "nothing")) Nothing ) => [],
        syntax_syntax!(
            ([(named "name", (call "DefaultName")),
              (lit ":"), (named "type", (call "DefaultName"))]) Basic {
            |_| icp!("Betas are not typed")
        } {
            |parts| {
                Ok(Basic(ast_to_name(&parts.get_term(n("name"))),
                         ast_to_name(&parts.get_term(n("type")))).reify())
            }
        }) => [],
        syntax_syntax!(
            ([(named "name", (call "DefaultName")),
              (lit "="), (named "type", (call "DefaultName"))]) SameAs {
            |_| icp!("Betas are not typed")
        } {
            |parts| {
                Ok(SameAs(ast_to_name(&parts.get_term(n("name"))),
                          ast_to_name(&parts.get_term(n("type")))).reify())
            }
        }) => [],
        syntax_syntax!(
            ([(lit "prot"), (named "name", (call "DefaultName"))]) Protected {
            |_| icp!("Betas are not typed")
        } {
            |parts| {
                Ok(Protected(ast_to_name(&parts.get_term(n("name")))).reify())
            }
        }) => [],
        syntax_syntax!(
            ([(lit "forall"), (named "name", (call "DefaultName"))]) Underspecified {
            |_| icp!("Betas are not typed")
        } {
            |parts| {
                Ok(Underspecified(ast_to_name(&parts.get_term(n("name")))).reify())
            }
        }) => [],
        syntax_syntax!(
            ((delim "...[", "[", (named "sub", (call "Beta")))) ShadowAll {
            |_| icp!("Betas are not typed")
        } {
            |parts| {
                let sub = ::beta::Beta::reflect(&parts.get_res(n("sub"))?);
                let drivers = sub.names_mentioned();
                Ok(ShadowAll(Box::new(sub), drivers).reify())
            }
        }) => [],
        syntax_syntax!(
            ((delim "[", "[",
              [(named "over", (call "Beta")), (lit "o>"), (named "under", (call "Beta"))])) Shadow {
            |_| icp!("Betas are not typed")
        } {
            |parts| {
                Ok(::beta::Beta::Shadow(
                    Box::new(::beta::Beta::reflect(&parts.get_res(n("over"))?)),
                    Box::new(::beta::Beta::reflect(&parts.get_res(n("under"))?))).reify())
            }
        }) => []
    ];

    // Most of "Syntax" is a negative walk (because it produces an environment),
    //  but lacking a `negative_ret_val`.
    let grammar_grammar = forms_to_form_pat_export![
        syntax_syntax!( ( (delim "anyways,{", "{", (named "body", (call "Expr"))) ) Anyways (
            body => ::ast::Ast::reflect(&body)
        )) => ["body"],
        syntax_syntax!( ((lit "impossible")) Impossible ) => [],
        syntax_syntax!( (  // TODO: this might have to be both positive and negative
            [(lit "lit"), (named "body", (call "Syntax")),
             (lit "="), (named "expected", atom)] ) Literal {
            |parts| {
                parts.get_res(n("body"))
            }
        } {
            |parts| {
                Ok(FormPat::Literal(Rc::new(FormPat::reflect(&parts.get_res(n("body"))?)),
                                    ast_to_name(&parts.get_term(n("expected")))).reify())
            }
        }) => [],
        syntax_syntax!( ([(scan r"(\s*/)"), (named "pat", (scan r"([^/]*)")), (scan r"(/)")]) Scan {
            |_| { Ok(Assoc::new()) }
        } {
            |parts| {
                Ok(::grammar::new_scan(
                    &::core_forms::ast_to_name(&parts.get_term(n("pat"))).orig_sp()).reify())
            }
        }) => [],
        syntax_syntax!( ([(lit "vr"), (named "body", (call "Syntax"))]) VarRef (
            body =>  Rc::new(FormPat::reflect(&body))
        )) => [],
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
        // TODO: support seprators, and add a separator here
        syntax_syntax!( ( (delim "alt[", "[", (star [(named "elt", (call "Syntax"))]))) Alt {
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
        syntax_syntax!( ([(named "part_name", atom), (lit ":="),
                          (lit "("), (named "body", (call "Syntax")), (lit ")")])
        Named {
            |parts| {
                let binder = ast_to_name(&parts.get_term(n("part_name")));
                Ok(Assoc::new().set(binder, parts.switch_mode::<SynthTy>().get_res(n("body"))?))
            }
        } {
            |parts| {
                Ok(Named(
                    ::core_forms::ast_to_name(&parts.get_term(n("part_name"))),
                    Rc::new(FormPat::reflect(&parts.get_res(n("body"))?))).reify())
            }
        }) => ["part_name"],
        // `Call` without a type
        syntax_syntax!( ((delim ",{", "{", (named "nt", atom))) Call {
            |_| {
                Ok(Assoc::new()) // We should check that the nt is defined, but we can't here
            }
        } {
            |parts| {
                Ok(Call(::core_forms::ast_to_name(&parts.get_term(n("nt")))).reify())
            }
        }) => [],


        // `Call` with a type is positive (has to be under a `Named`)
        Rc::new(Form {
            name: n("call_with_type"),
            grammar: Rc::new(form_pat!(
                (delim ",{", "{",
                    [(named "nt", atom), (delim "<[", "[", (named "ty_annot", (call "Type")))]))),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            synth_type: Both(cust_rc_box!(|parts| {
                let expected_type = parts.get_res(n("ty_annot"))?;
                let nt = ast_to_name(&parts.get_term(n("nt")));

                Ok(more_quoted_ty(&expected_type, nt))
            }), NotWalked),
            eval: ::form::Positive(cust_rc_box!(|parts| {
                let nt = ast_to_name(&parts.get_term(n("nt")));
                Ok(Rc::new(Call(nt)).reify())
            })),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        }) => [],
        // `Import` is positive (has to be under a `Named`)
        Rc::new(Form {
            name: n("import"),
            grammar: Rc::new(form_pat!(
                // TODO: we need syntax for a full-on beta
                [(named "body", (call "Syntax")), (lit "<--"), (named "imported", (call "Beta"))])),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            synth_type: Both(cust_rc_box!(|parts| {
                parts.get_res(n("body"))
            }), NotWalked),
            eval: ::form::Positive(cust_rc_box!(|parts| {
                Ok(NameImport(Rc::new(FormPat::reflect(&parts.get_res(n("body"))?)),
                              ::beta::Beta::reflect(&parts.get_res(n("imported"))?)).reify())
            })),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        }) => [],
        // TODO: implement syntax for ComputeSyntax
        // Not sure if `Scope` syntax should be positive or negative.
        syntax_syntax!( ([(lit "forall"), (star (named "param", atom)), (lit "."),
                          (delim "'{", "{",
                              (named "syntax", (import [* [forall "param"]],  (call "Syntax")))),
                          // We need an arbitrary negative_ret_val:
                          (named "unused_type", (anyways {trivial_type_form ; } )),
                          (named "macro_name", atom), (lit "->"),
                          (delim ".{", "{", (named "implementation",
                              // TODO `beta!` needs `Shadow` so we can combine these `import`s:
                              (import [* [forall "param"]],
                                  (import ["syntax" = "unused_type"], (call "Expr"))))),
                          (alt [], // TODO: needs proper `beta` structure, not just a name list:
                               [(lit "=>"), (star (named "export", atom))])])
        Scope {
            |parts| {
                let return_ty = parts.switch_mode::<::ty::SynthTy>().get_res(n("implementation"))?;
                let mut arguments : Vec<(Name, Ty)> = parts.get_res(n("syntax"))?
                    .iter_pairs().cloned().collect();
                arguments.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0) ); // Pick a canonical order
                let ty_params = &parts.get_rep_term(n("param")).iter().map(
                            |p| ast_to_name(p)).collect::<Vec<_>>();
                Ok(Assoc::new().set(ast_to_name(&parts.get_term(n("macro_name"))),
                                    macro_type(&ty_params, arguments, return_ty)))
            }
        } {
            |parts| {
                // TODO: This is the right thing to do, right?
                let macro_params = ::beta::bound_from_export_beta(
                    &ebeta!(["syntax"]), &parts.this_ast.node_parts(), 0);

                let mut export = ::beta::ExportBeta::Nothing;
                let export_names = parts.get_rep_term(n("export")).iter()
                    .map(ast_to_name).collect::<Vec<Name>>();
                for name in &export_names {
                    export = ::beta::ExportBeta::Shadow(
                        Box::new(::beta::ExportBeta::Use(*name)),
                        Box::new(export));
                }

                // This macro invocation (will replace `syntax`):
                Ok(Scope(macro_invocation(
                        FormPat::reflect(&parts.get_res(n("syntax"))?),
                        ast_to_name(&parts.get_term(n("macro_name"))),
                        ::runtime::eval::Closure{ body: parts.get_term(n("implementation")),
                            params: macro_params,
                            env: parts.env.clone()
                        },
                        export_names),
                    export).reify())
            }
        }) => ["macro_name"] // This exports a macro, not syntax (like `binders` does)!

    ];

    assoc_n!(
        "Syntax" => Rc::new(grammar_grammar),
        "Beta" => Rc::new(beta_grammar))
}

pub fn extend_syntax() -> Rc<Form> {
    use earley::ParseContext;
    let perform_extension = move |pc: ParseContext, extension_info: Ast| -> ParseContext {
        let bnf_parts =
            // TODO: getting a `Shape` (the second element is the `(lit "in")`) must be a parser bug
            extract!((&extension_info) ::ast::Shape = (ref subs) =>
                extract!((&subs[0]) ::ast::IncompleteNode = (ref parts) => parts));

        let nts: Vec<Name> = bnf_parts
            .get_rep_leaf_or_panic(n("nt"))
            .iter()
            .map(|a| ::core_forms::ast_to_name(*a))
            .collect();
        let ops: Vec<bool> = bnf_parts
            .get_rep_leaf_or_panic(n("operator"))
            .iter()
            .map(|a| a == &&::ast::Atom(n("::=also")))
            .collect();
        let rhses: Vec<&Ast> = bnf_parts.get_rep_leaf_or_panic(n("rhs"));

        // TODO: change signature and thread errors through the parser, instead of doing `unwrap`s.

        // Types pass for the syntax extension:
        let mut new_ty_env = pc.type_ctxt.env.clone();
        for rhs in &rhses {
            // `Syntax` (at least, outside of `Named`s) is type-unpacked, producing macro types.
            new_ty_env = new_ty_env.set_assoc(
                &::ast_walk::walk::<::ty::UnpackTy>(
                    rhs,
                    &pc.type_ctxt.switch_mode::<::ty::UnpackTy>().with_context(Ty(::ast::Trivial)),
                )
                .unwrap(),
            );
        }

        // Evaluation pass for the syntax extension:
        let mut syn_env = pc.grammar;
        for ((nt, extend), rhs) in nts.into_iter().zip(ops.into_iter()).zip(rhses.into_iter()) {
            let rhs_form_pat = FormPat::reflect(&::ast_walk::walk(rhs, &pc.eval_ctxt).unwrap());
            syn_env = syn_env.set(
                nt,
                Rc::new(if extend {
                    form_pat!((alt (, rhs_form_pat), (, (**syn_env.find_or_panic(&nt)).clone())))
                } else {
                    rhs_form_pat
                }),
            )
        }

        ParseContext {
            // Gotta add a `(named "body" ⋯)`, so that `extend_syntax` can use it.
            grammar: syn_env
                .set(n("SyntaxExtensionBody"), Rc::new(form_pat!([(named "body", (call "Expr"))]))),
            type_ctxt: pc.type_ctxt.with_environment(new_ty_env),
            eval_ctxt: pc.eval_ctxt, // no change! (Macro implementations are in `syn_env`.)
        }
    };

    Rc::new(Form {
        name: n("extend_syntax"),
        grammar: Rc::new(form_pat!(
            [(lit "extend_syntax"),
             (extend
                [(star [(named "nt", atom),
                   (named "operator", (alt (lit "::="), (lit "::=also"))),
                   (named "rhs", (call "Syntax")),
                   (lit ";")]),
                 (lit "in")],
                "SyntaxExtensionBody", // just `(named "body", (call "Expr"))`
                perform_extension)])),
        type_compare: ::form::Both(NotWalked, NotWalked),
        synth_type: ::form::Positive(cust_rc_box!(|extend_syntax_parts| {
            // `extension` is typechecked in `perform_extension`
            extend_syntax_parts.get_res(n("body"))
        })),
        eval: ::form::Positive(Body(n("body"))),
        quasiquote: ::form::Both(LiteralLike, LiteralLike),
    })
}

#[test]
fn formpat_reflection() {
    use core_forms::find_form;
    use runtime::eval::eval_top;
    let macro_forms = make_core_macro_forms()
        .set(n("DefaultToken"), Rc::new(::grammar::new_scan(r"\s*(\S+)")))
        .set(n("DefaultName"), Rc::new(FormPat::Call(n("DefaultToken"))))
        .set(n("Type"), Rc::new(FormPat::Call(n("DefaultToken"))));

    fn syntax_to_form_pat(a: Ast) -> FormPat { FormPat::reflect(&eval_top(&a).unwrap()) }

    assert_eq!(
        syntax_to_form_pat(ast!({
            find_form(&macro_forms, "Syntax", "impossible");
        })),
        Impossible
    );
    assert_eq!(
        syntax_to_form_pat(ast!({find_form(&macro_forms, "Syntax", "literal");
            "expected" => "<--->",
            "body" => {find_form(&macro_forms, "Syntax", "call");
                "nt" => "DefaultToken"
        }})),
        Literal(std::rc::Rc::new(Call(n("DefaultToken"))), n("<--->"))
    );

    let string_to_form_pat = |s: &str| -> FormPat {
        syntax_to_form_pat(
            ::earley::parse(
                &form_pat!((call "Syntax")),
                &macro_forms,
                ::earley::empty__code_envs(),
                s,
            )
            .unwrap(),
        )
    };

    assert_eq!(string_to_form_pat(r"/\s*(\S+)/"), ::grammar::new_scan(r"\s*(\S+)"));
    assert_eq!(string_to_form_pat(r"lit /\s*(\S+)/ = x"), form_pat!((lit_aat "x")));
    assert_eq!(
        string_to_form_pat(r"[ lit /\s*(\S+)/ = write_this ,{ Expr <[ Int ]< }, <-- nothing ]"),
        form_pat!([(lit_aat "write_this"), (import [], (call "Expr"))])
    );

    assert_eq!(
        string_to_form_pat(r"[ lit /\s*(\S+)/ = write_this ,{ Expr <[ Int ]< }, <-- a : b ]"),
        form_pat!([(lit_aat "write_this"), (import ["a" : "b"], (call "Expr"))])
    );
    assert_eq!(
        string_to_form_pat(r",{ Expr <[ Int ]< }, <-- [ forall thing o> a = b ]"),
        form_pat!((import [forall "thing" "a" = "b"], (call "Expr")))
    );
}

#[test]
fn macro_definitions() {
    let int_expr_type = uty!({type_apply : (prim Expr) [{Int :}]});
    let env = assoc_n!("ie" => int_expr_type.clone()).set(negative_ret_val(), ty!((trivial)));

    assert_eq!(
        ::ty::neg_synth_type(
            &u!({Syntax star => ["body"] :
                {named => ["part_name"] : x {call_with_type : Expr {Type Int :}}}}),
            env.clone()
        ),
        Ok(assoc_n!("x" => ::runtime::reify::sequence_type__of(
            &int_expr_type)))
    );

    let t_expr_type = uty!({type_apply : (prim Expr) [T]});
    let s_expr_type = uty!({type_apply : (prim Expr) [S]});
    let t_pat_type = uty!({type_apply : (prim Pat) [T]});

    assert_eq!(
        ::ty::neg_synth_type(
            &u!({Syntax scope : [T; S]
                {seq => [* ["elt"]] :
                    [{named => ["part_name"] : body {call_with_type : Expr S}};
                     {named => ["part_name"] : val {call_with_type : Expr T}};
                     {named => ["part_name"] : binding {call_with_type : Pat T}}]
                }
                {Type Nat :} // "unused_type". In practice, this is `trivial_type_form`
                some_macro
                ie
            }),
            env.clone()
        ),
        Ok(assoc_n!(
            "some_macro" => macro_type(&vec![n("T"), n("S")],
                                       vec![(n("binding"), t_pat_type.clone()),
                                            (n("body"), s_expr_type.clone()),
                                            (n("val"), t_expr_type.clone())],
                                       int_expr_type.clone())))
    );
}

#[test]
fn macro_types() {
    let int_expr_type = uty!({type_apply : (prim Expr) [{Int :}]});
    let t_expr_type = uty!({type_apply : (prim Expr) [T]});

    assert_eq!(
        macro_type(&vec![], vec![(n("a"), int_expr_type.clone())], int_expr_type.clone()),
        uty!({fn :
            [{struct : [a {type_apply : (prim Expr) [{Int :}]}]}]
            {type_apply : (prim Expr) [{Int :}]}})
    );
    assert_eq!(
        macro_type(&vec![n("T")], vec![(n("a"), t_expr_type.clone())], t_expr_type.clone()),
        uty!({forall_type : [T]
            {fn : [{struct : [a {type_apply : (prim Expr) [T]}]}]
                {type_apply : (prim Expr) [T]}}})
    );
}

#[test]
fn type_basic_macro_invocation() {
    let int_expr_type = uty!({type_apply : (prim Expr) [{Int :}]});
    let t_expr_type = uty!({type_apply : (prim Expr) [T]});
    let s_expr_type = uty!({type_apply : (prim Expr) [S]});
    let t_pat_type = uty!({type_apply : (prim Pat) [T]});
    let t_type_type = uty!({type_apply : (prim Type) [S]});

    let env = assoc_n!(
        "int_var" => uty!({Int :}),
        "nat_var" => uty!({Nat :}),
        "basic_int_macro" =>
            macro_type(&vec![], vec![(n("a"), int_expr_type.clone())], int_expr_type.clone()),
        "basic_t_macro" =>
            macro_type(&vec![n("T")], vec![(n("a"), t_expr_type.clone())], t_expr_type.clone()),
        "basic_pattern_macro" =>
            macro_type(&vec![n("T")], vec![(n("a"), t_pat_type.clone())], t_pat_type.clone()),
        "let_like_macro" =>
            macro_type(&vec![n("T"), n("S")],
                       vec![(n("val"), t_expr_type.clone()),
                            (n("binding"), t_pat_type.clone()),
                            (n("body"), s_expr_type.clone())],
                       s_expr_type.clone()),
        "pattern_cond_like_macro" =>
            macro_type(&vec![n("T"), n("S")],
                       vec![(n("t"), t_type_type.clone()),
                            (n("body"), t_pat_type.clone()),
                            (n("cond_expr"), int_expr_type.clone())], // (would really be a bool)
                       t_pat_type.clone())

    );

    let impl_clo =
        ::runtime::eval::Closure { body: ast!((trivial)), params: vec![], env: Assoc::new() };
    assert_eq!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_int_macro"), (named "a", (call "Expr"))]),
                    n("basic_int_macro"), impl_clo.clone(), vec![]) ;
                "a" => (vr "int_var")
            }),
            env.clone()
        ),
        Ok(ty!({ "Type" "Int" :}))
    );

    assert_eq!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_t_macro"), (named "a", (call "Expr"))]),
                    n("basic_t_macro"), impl_clo.clone(), vec![]) ;
                "a" => (vr "nat_var")
            }),
            env.clone()
        ),
        Ok(ty!({ "Type" "Nat" :}))
    );

    assert_m!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_int_macro"), (named "a", (call "Expr"))]),
                    n("basic_int_macro"), impl_clo.clone(), vec![]) ;
                "a" => (vr "nat_var")
            }),
            env.clone()
        ),
        Err(_)
    );

    assert_eq!(
        ::ty::neg_synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke basic_pattern_macro"), (named "a", (call "Pat"))]),
                    n("basic_pattern_macro"), impl_clo.clone(), vec![n("a")]) => ["a"];
                "a" => "should_be_nat"
            }),
            env.clone().set(negative_ret_val(), ty!({"Type" "Nat" :}))
        ),
        Ok(assoc_n!("should_be_nat" => ty!({"Type" "Nat" :})))
    );

    assert_eq!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke let_like_macro"),
                               (named "val", (call "Expr")),
                               (named "binding", (call "Pat")),
                               (named "body", (import ["binding" = "val"], (call "Expr")))]),
                    n("let_like_macro"), impl_clo.clone(), vec![]) ;
                "val" => (vr "nat_var"),
                "binding" => "x",
                "body" => (import ["binding" = "val"] (vr "x"))
            }),
            env.clone()
        ),
        Ok(ty!({ "Type" "Nat" :}))
    );

    assert_eq!(
        ::ty::neg_synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke pattern_cond_like_macro"),
                               (named "t", (call "Type")),
                               (named "body", (call "Pat")),
                               (named "cond_expr", (import ["body" : "t"], (call "Expr")))]),
                    n("pattern_cond_like_macro"), impl_clo.clone(), vec![n("body")]) ;
                "t" => {"Type" "Int" :},
                "body" => "x",
                "cond_expr" => (import ["body" : "t"] (vr "x"))
            }),
            env.set(negative_ret_val(), ty!({"Type" "Int" :})).clone()
        ),
        Ok(assoc_n!("x" => ty!({ "Type" "Int" :})))
    );
}

#[test]
fn type_ddd_macro() {
    let t_expr_type = uty!({type_apply : (prim Expr) [T]});
    let s_expr_type = uty!({type_apply : (prim Expr) [S]});
    let t_pat_type = uty!({type_apply : (prim Pat) [T]});

    let impl_clo =
        ::runtime::eval::Closure { body: ast!((trivial)), params: vec![], env: Assoc::new() };

    let env = assoc_n!(
        "int_var" => uty!({Int :}),
        "nat_var" => uty!({Nat :}),
        "let_like_macro" =>
            macro_type(&vec![n("T"), n("S")],
                       vec![(n("val"), t_expr_type.clone()),
                            (n("binding"), t_pat_type.clone()),
                            (n("body"), s_expr_type.clone())],
                       s_expr_type.clone()));

    assert_eq!(
        ::ty::synth_type(
            &ast!({
                macro_invocation(
                    form_pat!([(lit "invoke let_like_macro"),
                                (star (named "val", (call "Expr"))),
                                (star (named "binding", (call "Pat"))),
                                (named "body", (import [* ["binding" = "val"]], (call "Expr")))]),
                    n("let_like_macro"), impl_clo, vec![]) ;
                "val" => [@"arm" (vr "nat_var"), (vr "nat_var")],
                "binding" => [@"arm" "x1", "x2"],
                "body" => (import [* ["binding" = "val"]] (vr "x1"))
            }),
            env.clone()
        ),
        Ok(uty!({Nat :}))
    );
}
#[test]
fn define_and_parse_macros() {
    let ty_ctxt = ::ast_walk::LazyWalkReses::<::ty::SynthTy>::new_wrapper(
        ::runtime::core_values::core_types(),
    );
    let ev_ctxt = ::ast_walk::LazyWalkReses::<::runtime::eval::Eval>::new_wrapper(
        ::runtime::core_values::core_values(),
    );

    ::grammar::parse(
        &form_pat!((scope extend_syntax())),
        &::core_forms::get_core_forms(),
        (ty_ctxt, ev_ctxt),
        "extend_syntax
             Expr ::=also forall T . '{
                 [ lit ,{ DefaultToken }, = [
                     body := ( ,{ Expr <[ Int ]< }, )
                   lit ,{ DefaultToken }, = ]
                 ]
             }' add_one__macro -> .{ '[ Expr | (plus one ,[ Expr | body], ) ]' }. ;
        in [ [ [ one ] ] ]",
    )
    .unwrap();
}
