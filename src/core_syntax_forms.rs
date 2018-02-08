use std::rc::Rc;
use ty::Ty;
use name::*;
use runtime::eval::{Eval, Destructure, QQuote, QQuoteDestr};
use parse::{SynEnv, FormPat};
use form::{Form, Positive, Negative, Both};
use core_forms::ast_to_name;
use core_type_forms::{nt_to_type, nt_is_positive, less_quoted_ty, more_quoted_ty};
use ast_walk::WalkRule::*;
use ast_walk::squirrel_away;
use ast::Ast;
use util::assoc::Assoc;

// A brief digression about types and syntax quotation...
// Expressions are "positive", and are traversed leaf-to-root in an environment, producing a type.
// Patterns are "negative", and are traversed root-to-leave from a type, producing an environment.
// (`match` and `lambda` are examples of interactions between expressions and patterns.)
// Syntax quotation and unquotation embeds expressions/patterns
//  (at a different phase, which matters suprisingly little)
//  inside expressions/patterns.
//
// This looks like:
//                     pattern outside | expression outside      <-- (provides context)
//                   --------------------------------------
// pattern inside    | ok              | needs annotation
// expression inside | bonus check     | ok
//
// Examples of needed annotation:
//
//   optimize_pat '[Pat <[List <[Int]<]< | (cons a b)]'
// In this case, we need to know the type of the syntax quote,
//  but the pattern wants to know its type so that it can tell us its environment.
//
//   match stx { '[Expr | 1 + 5 * ,[Expr <[Nat]< | stx_num], ]' => ... }
// In this case (looking at the expression interpolation),
//  we need to know the type of the interpolated expression syntax (a pattern)
//   in order to type-synthesize the arithmetic.
//
//
// Examples of when we get to do a bonus typecheck:
//
//   match stx { '[Expr | f x]' => ... }
// In this case, we can check that the type of the scrutinee
//  (which is the type of the syntax quotation pattern)
//   equals Expr<[ (whatever `f` returns) ]<.
//
//   optimize_expr '[Expr | match stx { ,[Pat | my_pat], => ... } ]'
// In this case (looking at the Pat interpolation),
//  we can check that the type of the quoted scrutinee is the same as
//   the type of `my_pat` (after peeling off its `Pat <[]<`).
//
// Note that it doesn't matter whether the boundary is a quotation or an unquotation!
// Like I said, the phase doesn't matter much.



// There's a nice-seeming syntax for determining what `unquote` does when quotation is nested.
// However, it would require some weird additional power for the parser:
//   '[Expr | '[Expr | ,[Expr | …], ,,[Expr | …],,]']'
// OTOH, if you are using `,,,,[],,,,`, something has gone terribly wrong.



// Technically, we could have the parser decide whether `unquote` is allowed.
//  (It only makes sense inside a `quote`.)
// However, this would leave us with one `unquote` form available per level of quotation

/// Generate an unquoting form.
/// `pos_quot` is true iff the quotation itself (and thus the interpolation) is positive.
pub fn unquote(nt: Name, pos_quot: bool) -> Rc<FormPat> {
    Rc::new(FormPat::Scope(unquote_form(nt, pos_quot), ::beta::ExportBeta::Nothing))
}

pub fn unquote_form(nt: Name, pos_quot: bool) -> Rc<Form> {
    Rc::new(Form {
        name: n("unquote"),
        grammar:
            // It's a pain to determine whether type annotation is needed at syntax time,
            //  so it's optional
            Rc::new(if pos_quot {
                form_pat!((delim ",[", "[", /*]]*/
                    [(named "nt", (lit_by_name nt)), // TODO: need to muck with case
                     (alt [], (delim "<[", "[", /*]]*/ (named "ty_annot", (call "ty")))),
                     (lit "|"),
                     (named "body", (call "expr"))]))
            } else {
                form_pat!((delim ",[", "[", /*]]*/
                    [(named "nt", (lit_by_name nt)),
                     (alt [], (delim "<[", "[", /*]]*/ (named "ty_annot", (call "ty")))),
                     (lit "|"),
                     (named "body", (call "pat"))]))
            }),
        type_compare: Positive(NotWalked), // this is not a type form
        synth_type:
            // `nt_is_positive` and `pos_quot` have opposite roles from `quote`
            if nt_is_positive(nt) {
                // (without prejudice as to whether this quotation is positive or negative)
                // (nt_is_positive is true in this example, though) For example:
                // ` '[Expr | .[a : Int . ,[Expr <[String]< | body], ]. ]' `
                //                        ^^^^^^^^^^^^^^^^^^^^^^^^^^
                Positive(
                    // `body` has the type `Expr <[String]<` (annotation is superfluous):
                    cust_rc_box!( move | unquote_parts | {
                        // TODO: What the heck is the difference between this and the `nt` that it shadows!!!?!?!?!?!?
                        let nt = ast_to_name(&unquote_parts.get_term(&n("nt")));
                        let ast_for_errors = unquote_parts.get_term(&n("body"));
                        // TODO: check annotation if present

                        if pos_quot {
                            // `String`
                            // `.1` is to drop the `None` on the floor
                            less_quoted_ty(try!(unquote_parts.quote_less().1.get_res(&n("body"))),
                                nt, &ast_for_errors)
                        } else {
                            // need a type annotation
                            let expected_type = try!(unquote_parts.get_res(&n("ty_annot")));

                            let (oeh, lq_parts) =
                                unquote_parts.switch_mode::<::ty::UnpackTy>().quote_less();
                            let res = try!(lq_parts.get_res(&n("body")));

                            squirrel_away::<::ty::UnpackTy>(oeh, res);

                            less_quoted_ty(expected_type, nt, &ast_for_errors)
                        }
                    }))
            } else {
                // For example: ` '[Pat | (x, ,[Pat <[String]< | body], ) ]' `
                //                            ^^^^^^^^^^^^^^^^^^^^^^^^^
                Negative(
                    cust_rc_box!( move | unquote_parts | {
                        let nt = ast_to_name(&unquote_parts.get_term(&n("nt")));

                        if pos_quot {
                            // `String`
                            let (_oeh, lq_parts) = unquote_parts.switch_mode::<::ty::SynthTy>()
                                .quote_less();
                            let res = try!(lq_parts.get_res(&n("body")));

                            // Bonus typecheck
                            ty_exp!(unquote_parts.context_elt(), &res, lq_parts.this_ast);

                            Ok(Assoc::new()) // TODO: this seems like it shouldn't be empty
                        } else {
                            // phase-shift the context_elt:
                            let ctxt = more_quoted_ty(
                                unquote_parts.context_elt().clone(), &nt.sp());
                            let (oeh, lq_parts) = unquote_parts.quote_less();
                            let res = try!(lq_parts.with_context(ctxt).get_res(&n("body")));

                            squirrel_away::<::ty::UnpackTy>(oeh, res);

                            Ok(Assoc::new()) // TODO: does this make sense?
                        }
                    })
                )
            },

            // Also, let's suppose that we have something like:
            //   let some_pattern : pat <[int]< = ...
            //   let s = '[{pat} struct { a: ,[ some_pattern ],  b: b_var} ]'
            // ...what then?
        eval:
            Both(NotWalked, NotWalked), // Outside a quotation? Makes no sense!
        quasiquote: // the only kind of form for which this *isn't* `LiteralLike`:
            Both( // TODO: double-check that `pos` and `neg` don't matter here
                cust_rc_box!( move | unquote_parts | {
                    let (_oeh, lq_parts) = unquote_parts.switch_mode::<Eval>().quote_less();
                    ::ast_walk::walk::<Eval>(lq_parts.get_term_ref(&n("body")), &lq_parts)
                }),
                cust_rc_box!( move | unquote_parts | {
                    let context = unquote_parts.context_elt().clone();

                    let (_oeh, lq_parts) = unquote_parts.switch_mode::<Destructure>().quote_less();
                    ::ast_walk::walk::<Destructure>(lq_parts.get_term_ref(&n("body")),
                        &lq_parts.with_context(context))
                }))
    })
}

// How do we walk quasiquotations?
// During type synthesis, we are checking the internal structure of the quoted syntax,
//  and we walk it just like we walk normal AST; just with a shifted environment.
// This is why we sometimes need type annotations.

// During evaluation, quoted terms are inactive. Everything (except `unquote`!) is LiteralLike.
// Furthermore, the direction of the walk is determined by the direction of the original quotation.

pub fn quote(pos: bool) -> Rc<Form> {
    use ::parse::FormPat;
    use ::parse::FormPat::*;
    let perform_quotation = move |se: SynEnv, starter_nt: Ast| -> SynEnv {
        fn already_has_unquote(fp: &FormPat) -> bool {
            match *fp {
                Alt(ref parts) => { parts.iter().any(|sub_fp| already_has_unquote(&*sub_fp)) },
                Biased(ref plan_a, ref plan_b) => {
                    already_has_unquote(&*plan_a) || already_has_unquote(&*plan_b)
                }
                Scope(ref f, _) => { f.name == n("unquote") }
                _ => false
            }
        }

        se.keyed_map_borrow_f(&mut |nt: &Name, nt_def: &Rc<FormPat>| {
            if already_has_unquote(nt_def) {
                nt_def.clone()
            } else {
                Rc::new(Biased(unquote(*nt, pos), nt_def.clone()))
            }})
            .set(n("starter_nt"),
                Rc::new(form_pat!(
                    [(alt [], (delim "<[", "[", /*]]*/ (named "ty_annot", (call "ty")))),
                     (lit "|"),
                     (named "body", (call_by_name ::core_forms::ast_to_name(&starter_nt)))])))
    };

    // TODO: the following hardcodes positive walks as `Expr` and negative walks as `Pat`.
    // What happens when more NTs are added?
    Rc::new(Form {
        name: if pos { n("quote_expr") } else { n("quote_pat") },
        grammar: Rc::new(form_pat!((delim "'[", "[", /*]]*/
            [(extend (named "nt", aat), "starter_nt", perform_quotation)]))),
        type_compare: ::form::Both(NotWalked, NotWalked), // Not a type
        synth_type:
            if pos {
                ::form::Positive(cust_rc_box!(|quote_parts| {
                    if nt_is_positive(
                            ::core_forms::ast_to_name(&quote_parts.get_term(&n("nt")))) {
                        // TODO: if the user provides an annotation, check it!
                        Ok(ty!({"type" "type_apply" :
                            "type_rator" =>
                                (, nt_to_type(ast_to_name(
                                    &quote_parts.get_term(&n("nt")))).concrete() ),
                            "arg" => [(,
                                try!(quote_parts.quote_more(None).get_res(&n("body"))).concrete())]
                        }))

                    } else {
                        // TODO: if the user accidentally omits the annotation,
                        //  provide a good error message.
                        let expected_type = try!(quote_parts.get_res(&n("ty_annot")));

                        // TODO: do we need this result somewhere?
                        // Note that `Pat <[Point]<` (as opposed to `Pat <:[x: Real, y: Real]<:`)
                        //  is what we want!
                        // In other words, syntax types don't care about positive vs. negative!
                        // I wrote down an argument in the form of code to this effect elsewhere,
                        //  but it boils down to this: environments can always be managed directly,
                        //   by introducing and referencing bindings.
                        let _ = quote_parts.switch_mode::<::ty::UnpackTy>().quote_more(None)
                            .with_context(expected_type.clone())
                            .get_res(&n("body"));

                        Ok(ty!({"type" "type_apply" :
                            "type_rator" =>
                                (, nt_to_type(ast_to_name(
                                    &quote_parts.get_term(&n("nt")))).concrete() ),
                            "arg" => [ (,expected_type.concrete()) ]}))
                    }
                }))
            } else {
                ::form::Negative(cust_rc_box!(|quote_parts| {
                    // There's a weird thing going on here!
                    // We want to type-synthesize the quoted syntax, like normal
                    //  (though I suppose a pattern containing ill-typed syntax could just
                    //    fail to match anything!).
                    // But we're a *pattern* quotation!
                    // Like a normal pattern, we know the overall type already,
                    //  and want to generate a type *environment* from the binders (in `unquote`s).
                    // More importantly, the result of walking the contents are either
                    //  doesn't have any bearing on the "hole"s in this quotation
                    //   (it might not even be an environment, if we're matching `expr` syntax).
                    // So we need to sneak a mutable environment into the `LazyWalkReses`
                    //  that `unquote` can update when we get back to the current quotation level.

                    // Maybe this needs a diagram?
                    // `match e { `[Expr | (add 5 ,[Expr <[Nat]< | a],)]` => ⋯}`
                    //            ^--- `quote_more` here (`get_res` produces `Expr <[Nat]<`),
                    //                 which we already knew.
                    //                            ^--- `quote_less`, and we get {a => Expr <[Nat]<}
                    // We need to smuggle out what we know at the `quote_less`,
                    //  so that `a` winds up bound to `Expr <[Nat]<` on the RHS.

                    let interpolation_accumulator = Rc::new(::std::cell::RefCell::new(
                        Assoc::<Name, Ty>::new()));

                    // There's no need for a type annotation

                    let nt = ast_to_name(&quote_parts.get_term(&n("nt")));

                    if nt_is_positive(nt) {
                        // TODO: check that this matches the type annotation, if provided!
                        let _underlying_type =
                            try!(quote_parts.switch_mode::<::ty::SynthTy>()
                                .quote_more(Some(interpolation_accumulator.clone()))
                                .get_res(&n("body")));
                    } else {
                        let new_context =
                            try!(less_quoted_ty(
                                quote_parts.context_elt().clone(), nt, &quote_parts.this_ast));
                        // TODO: check that this matches the type annotation, if provided!
                        let _underlying_type =
                            try!(quote_parts
                                .quote_more(Some(interpolation_accumulator.clone()))
                                .with_context(new_context)
                                .get_res(&n("body")));
                    }

                    // pull out the squirreled-away environment from unquotes
                    let res : Assoc<Name, Ty> = (*interpolation_accumulator.borrow()).clone();
                    Ok(res)
                }))
            },
        eval:
            if pos {
                Positive(cust_rc_box!(|quote_parts| {
                    let mq_parts = quote_parts.switch_mode::<QQuote>().quote_more(None);
                    ::ast_walk::walk::<QQuote>(mq_parts.get_term_ref(&n("body")), &mq_parts)
                }))
            } else {
                Negative(cust_rc_box!(|quote_parts| {
                    let context = quote_parts.context_elt().clone();

                    let mq_parts = quote_parts.switch_mode::<QQuoteDestr>().quote_more(None)
                        .with_context(context);
                    ::ast_walk::walk::<QQuoteDestr>(mq_parts.get_term_ref(&n("body")), &mq_parts)
                }))
            },
        quasiquote: Both(LiteralLike, LiteralLike)
    })
}

#[test]
fn quote_unquote_eval_basic() {
    use ::runtime::eval::Value;

    let pos = true;
    let neg = false;

    let env = assoc_n!(
        "n" => val!(i 5),
        "en" => val!(ast (vr "qn"))
    );

    let qenv = assoc_n!(
        "qn" => val!(i 6)
    );

    fn eval_two_phased(expr: &Ast, env: Assoc<Name, Value>, qenv: Assoc<Name, Value>)
            -> Result<Value, ()> {
        ::ast_walk::walk::<Eval>(expr, &::ast_walk::LazyWalkReses::new_mq_wrapper(
            env, vec![qenv]))
    }

    fn destr_two_phased(pat: &Ast, env: Assoc<Name, Value>, qenv: Assoc<Name, Value>, ctxt: Value)
            -> Result<Assoc<Name, Value>, ()> {
        ::ast_walk::walk::<Destructure>(pat, &::ast_walk::LazyWalkReses::new_mq_wrapper(
            env, vec![qenv]).with_context(ctxt))
    }

    assert_eq!(eval_two_phased(&ast!({quote(pos) ; "nt" => "Expr", "body" => (vr "qn")}),
            env.clone(), qenv.clone()),
        Ok(val!(ast (vr "qn"))));


    assert_eq!(eval_two_phased(&ast!({quote(pos) ; "nt" => "Expr",
        "body" => {unquote_form(n("Expr"), true) ; "nt" => "Expr",
            "body" => (vr "en")}}),
            env.clone(), qenv.clone()),
        Ok(val!(ast (vr "qn"))));

    assert_eq!(
        destr_two_phased(&ast!({quote(neg) ; "nt" => "Expr", "body" => (vr "qn")}), env, qenv,
                         val!(ast (vr "qn"))),
        Ok(Assoc::<Name, Value>::new()));

}

#[test]
fn quote_type_basic() {
    let pos = true;
    let neg = false;

    let env = assoc_n!(
        "n" => ty!({"type" "Nat" :})
    );

    let qenv = assoc_n!(
        "qn" => ty!({"type" "Nat" :})
    );

    let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let pat_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Pat" });

    fn synth_type_two_phased(expr: &Ast, env: Assoc<Name, Ty>, qenv: Assoc<Name, Ty>)
            -> ::ty::TypeResult {
        ::ast_walk::walk::<::ty::SynthTy>(expr, &::ast_walk::LazyWalkReses::new_mq_wrapper(
            env, vec![qenv]))
    }

    // '[Expr | qn]'
    assert_eq!(synth_type_two_phased(&ast!({quote(pos) ; "nt" => "Expr", "body" => (vr "qn")}),
                                     env.clone(), qenv.clone()),
        Ok(ty!({"type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"type" "Nat" :}]})));
    // '[Expr <[Nat]< | qn]'
    // With type annotation, same result:
    assert_eq!(synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => "Expr", "body" => (vr "qn"),
                "ty_annot" => {"type" "Nat" :}}),
            env.clone(), qenv.clone()),
        Ok(ty!({"type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"type" "Nat" :}]})));

    // '[Expr | n]'
    assert_m!(synth_type_two_phased(&ast!({quote(pos) ; "nt" => "Expr", "body" => (vr "n")}),
                                     env.clone(), qenv.clone()),
        ty_err_p!(UnboundName(_)));

    // '[Expr | { x: qn  y: qn }]'
    assert_eq!(synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => "Expr",
            "body" => {"expr" "struct_expr" :
                "component_name" => [@"c" "x", "y"],
                "component" => [@"c" (vr "qn"), (vr "qn")]
        }}),
        env.clone(), qenv.clone()),
        Ok(ty!({"type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{ "type" "struct" :
                "component_name" => [@"c" "x", "y"],
                "component" => [@"c" {"type" "Nat":}, {"type" "Nat" :}]
            }]})));

    fn unpack_type_two_phased(pat: &Ast, env: Assoc<Name, Ty>, qenv: Assoc<Name, Ty>, ctxt: Ty)
            -> Result<Assoc<Name, Ty>, ::ty::TypeError> {
        ::ast_walk::walk::<::ty::UnpackTy>(pat, &::ast_walk::LazyWalkReses::new_mq_wrapper(
            env, vec![qenv]).with_context(ctxt))
    }

    // A trivial pattern containing an expression
    // '[Expr <[ struct {} ]< | *[]* ]'
    assert_eq!(unpack_type_two_phased(&ast!({quote(neg) ;
                "nt" => "Expr",
                "ty_annot" => {"type" "struct":
                    "component_name" => [@"c"], "component" => [@"c"]},
                "body" => {"expr" "struct_expr":
                    "component_name" => [@"c"], "component" => [@"c"]}}),
            env.clone(), qenv.clone(),
            ty!({"type" "type_apply" :
                "type_rator" => (,expr_type.clone()), "arg" => [{ "type" "struct" :
                    "component_name" => [@"c"], "component" => [@"c"]
                }]})),
        Ok(assoc_n!()));

    // A trivial pattern containing a pattern
    // '[Pat <[ struct {} ]< | *[]* ]'
    assert_eq!(unpack_type_two_phased(&ast!({quote(neg) ;
                "nt" => "Pat",
                "ty_annot" => {"type" "struct":
                    "component_name" => [@"c"], "component" => [@"c"]},
                "body" => {"pat" "struct_pat":
                    "component_name" => [@"c"], "component" => [@"c"]}}),
            env.clone(), qenv.clone(),
            ty!({"type" "type_apply" :
                "type_rator" => (,pat_type.clone()), "arg" => [{ "type" "struct" :
                    "component_name" => [@"c"], "component" => [@"c"]
                }]})),
        Ok(assoc_n!()));

    // A slightly-less trivial pattern containing a pattern (but still no unquotes)
    // '[Pat <[ struct {x: Nat} ]< | *[x: qfoo]* ]'
    assert_eq!(unpack_type_two_phased(&ast!({quote(neg) ;
                "nt" => "Pat",
                "ty_annot" => {"type" "struct":
                    "component_name" => [@"c" "x"], "component" => [@"c" {"type" "Nat" :}]},
                "body" => {"pat" "struct_pat":
                    "component_name" => [@"c" "x"], "component" => [@"c" "qfoo"]}}),
            env.clone(), qenv.clone(),
            ty!({"type" "type_apply" :
                "type_rator" => (,pat_type.clone()), "arg" => [{ "type" "struct" :
                    "component_name" => [@"c" "x"], "component" => [@"c" {"type" "Nat" :}]
                }]})),
        Ok(assoc_n!()));

}



#[test]
fn quote_unquote_type_basic() {
    let pos = true;
    let neg = false;

    let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let pat_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Pat" });

    let env = assoc_n!(
        "n" => ty!({"type" "Nat" :}),
        "en" => ty!({"type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"type" "Nat" :}]}),
        "ef" => ty!({"type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"type" "Float" :}]})
    );

    let qenv = assoc_n!(
        "qn" => ty!({"type" "Nat" :})
    );

    fn synth_type_two_phased(expr: &Ast, env: Assoc<Name, Ty>, qenv: Assoc<Name, Ty>)
            -> ::ty::TypeResult {
        ::ast_walk::walk::<::ty::SynthTy>(expr, &::ast_walk::LazyWalkReses::new_mq_wrapper(
            env, vec![qenv]))
    }
    // An expression containing an expression
    // '[Expr |
    //     *[x: ,[Expr | en], y: ,[Expr | ef], z: baz]* ]'
    assert_eq!(synth_type_two_phased(&ast!({quote(pos) ;
                "nt" => "Expr",
                "body" => {"expr" "struct_expr":
                    "component_name" => [@"c" "x", "y", "z"],
                    "component" => [@"c"
                        {unquote_form(n("Expr"), pos) ; "nt" => "Expr", "body" => (vr "en")},
                        {unquote_form(n("Expr"), pos) ; "nt" => "Expr", "body" => (vr "ef")},
                        (vr "qn")
                    ]}}),
            env.clone(), qenv.clone()),
        Ok(ty!({"type" "type_apply" : "type_rator" => (,expr_type.clone()),
            "arg" => [{"type" "struct":
                "component_name" => [@"c" "x", "y", "z"],
                "component" => [@"c" {"type" "Nat" :}, {"type" "Float" :}, {"type" "Nat" :}]}]})));

    fn unpack_type_two_phased(pat: &Ast, env: Assoc<Name, Ty>, qenv: Assoc<Name, Ty>, ctxt: Ty)
            -> Result<Assoc<Name, Ty>, ::ty::TypeError> {
        ::ast_walk::walk::<::ty::UnpackTy>(pat, &::ast_walk::LazyWalkReses::new_mq_wrapper(
            env, vec![qenv]).with_context(ctxt))
    }

    // A pattern containing a pattern
    // '[Pat <[ struct {x : Nat y : Float z : Nat} ]< |
    //     *[x: ,[Pat | foo], y: ,[Pat | bar], z: baz]* ]'
    assert_eq!(unpack_type_two_phased(&ast!({quote(neg) ;
                "nt" => "Pat",
                "ty_annot" => {"type" "struct":
                    "component_name" => [@"c" "x", "y", "z"],
                    "component" => [@"c" {"type" "Nat" :}, {"type" "Float" :}, {"type" "Nat" :}]},
                "body" => {"pat" "struct_pat":
                    "component_name" => [@"c" "x", "y", "z"],
                    "component" => [@"c"
                        {unquote_form(n("Pat"), neg) ; "nt" => "Pat", "body" => "foo"},
                        {unquote_form(n("Pat"), neg) ; "nt" => "Pat", "body" => "bar"},
                        "baz"
                    ]}}),
            env.clone(), qenv.clone(),
            ty!({"type" "type_apply" :
                "type_rator" => (,pat_type.clone()), "arg" => [{ "type" "struct" :
                    "component_name" => [@"c" "x", "y", "z"],
                    "component" => [@"c" {"type" "Nat" :}, {"type" "Float" :}, {"type" "Nat" :}]
                }]})),
        Ok(assoc_n!(
            "foo" => ty!({"type" "type_apply" :
                "arg" => [{"type" "Nat" :}],
                "type_rator" => (,pat_type.clone())}),
            "bar" => ty!({"type" "type_apply" :
                "arg" => [{"type" "Float" :}],
                "type_rator" => (,pat_type.clone())}))));
}

#[test]
fn unquote_type_basic() {
    use ::ast_walk::{walk, LazyWalkReses, OutEnvHandle};
    let pos = true;
    let _neg = false;

    let expr_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Expr" });
    let _pat_type = ast!({::core_type_forms::get__abstract_parametric_type() ; "name" => "Pat" });


    let env = assoc_n!(
        "n" => ty!({"type" "Nat" :}),
        "en" => ty!({"type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"type" "Nat" :}]})
    );

    let qenv = assoc_n!(
        "qn" => ty!({"type" "Nat" :})
    );

    fn synth_type_two_phased_lq(expr: &Ast, env: Assoc<Name, Ty>, qenv: Assoc<Name, Ty>)
            -> (::ty::TypeResult, OutEnvHandle<::ty::SynthTy>) {
        let oeh = Rc::new(::std::cell::RefCell::new(Assoc::<Name, Ty>::new()));
        let parts = LazyWalkReses::new_wrapper(env);
        let qparts = parts.quote_more(Some(oeh.clone())).with_environment(qenv);

        (::ast_walk::walk::<::ty::SynthTy>(expr, &qparts), oeh)
    }

    // ,[Expr | en ],
    let (res, _) = synth_type_two_phased_lq(
        &ast!({unquote_form(n("Expr"), pos) ; "nt" => "Expr", "body" => (vr "en")}), env, qenv);
    assert_eq!(res, Ok(ty!({"type" "Nat" :})));

}
