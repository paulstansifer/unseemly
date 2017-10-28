use std::rc::Rc;
use ty::Ty;
use name::*;
use parse::{SynEnv, FormPat};
use form::{Form, Positive, Negative};
use ast_walk::WalkRule::*;
use ast::Ast;

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
fn unquote(nt: Name, pos: bool) -> Rc<FormPat> {
    Rc::new(FormPat::Scope(Rc::new(Form {
        name: n("unquote"),
        grammar:
            // It's a pain to determine whether type annotation is needed at syntax time,
            //  so it's optional
            Rc::new(if pos {
                form_pat!((delim ",[", "[", /*]]*/
                    [(lit_by_name nt), // TODO: need to muck with case
                     (alt [], (delim "<[", "[", /*]]*/ (named "ty_annot", (call "ty")))),
                     (lit "|"),
                     (named "body", (call "expr"))]))
            } else {
                form_pat!((delim ",[", "[", /*]]*/
                    [(lit_by_name nt),
                     (alt [], (delim "<[", "[", /*]]*/ (named "ty_annot", (call "ty")))),
                     (lit "|"),
                     (named "body", (call "pat"))]))
            }),
        type_compare: Positive(NotWalked), // this is not a type form
        synth_type:
            // imagine: ` '[Expr | .[a : Int . ,[body], ]. ]' `
            if pos {
                Positive(
                    // suppose that this is an expr, and `body` has the type `Expr <[String]<`:
                    cust_rc_box!( move | unquote_parts | {
                        let interpolate_type = try!(unquote_parts.get_res(&n("body")));
                        expect_ty_node!(
                            (interpolate_type ; ::core_forms::find("type", "type_apply") ;
                                             &unquote_parts.this_ast)
                            apply_parts;
                            {
                                let got_nt = ::core_forms::ast_to_name(
                                    apply_parts.get_leaf_or_panic(&n("type_name")));
                                if  got_nt != nt {
                                    ty_err!(NtInterpMismatch(got_nt, nt) at
                                        unquote_parts.get_term(&n("body")));
                                }
                                let args = apply_parts.get_rep_leaf_or_panic(&n("arg"));
                                if args.len() != 1 {
                                    panic!("Kind error: expected one argument, got {:?}", args)
                                }
                                Ok(Ty::new(args[0].clone()))
                })}))
            } else {
                Negative(
                    // suppose that this is a pat,
                    // and the whole thing has type `Expr <[ [int -> string] ]<`
                    cust_rc_box!( move | _unquote_parts | {
                        unimplemented!("")
                    })
                )
            },

            // Also, let's suppose that we have something like:
            //   let some_pattern : pat <[int]< = ...
            //   let s = '[{pat} struct { a: ,[ some_pattern ],  b: b_var} ]'
            // ...what then?
        eval: // should be both
            Positive(cust_rc_box!( move | _unquote_parts | {
                unimplemented!("");
            })),
        quasiquote: //should be both
            Positive(cust_rc_box!( move | _unquote_parts | {
                unimplemented!("");
            }))
    }), ::beta::ExportBeta::Nothing))
}

fn quote(pos: bool) -> Rc<Form> {
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

    Rc::new(Form {
        name: if pos { n("quote_expr") } else { n("quote_pat") },
        grammar: Rc::new(form_pat!((delim "'[", "[", /*]]*/
            [(extend aat, "starter_nt", perform_quotation)]))),
        type_compare: ::form::Both(NotWalked, NotWalked), // Not a type
        synth_type:
            if pos {
                ::form::Positive(cust_rc_box!(|quote_parts| {
                    if quote_parts.parts.get_leaf(&n("ty_annot")).is_some() { // HACK
                        // TODO: this gives a bad error message if the user accidentally
                        //  uses a type annotation on a positive form.
                        // TODO: do we need this somewhere?
                        let _ = quote_parts.switch_mode::<::ty::UnpackTy>().get_res(&n("body"));

                        quote_parts.get_res(&n("ty_annot"))
                    } else {
                        quote_parts.get_res(&n("body"))
                    }
                }))
            } else {
                ::form::Negative(cust_rc_box!(|_quote_parts| {
                    unimplemented!()
                }))
            },
        eval:
            if pos {
                ::form::Positive(cust_rc_box!(|_quote_parts| {
                    unimplemented!()
                }))
            } else {
                ::form::Negative(cust_rc_box!(|_quote_parts| {
                    unimplemented!()
                }))
            },
        quasiquote: ::form::Both(LiteralLike, LiteralLike)
    })
}
