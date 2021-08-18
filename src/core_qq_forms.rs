use crate::{
    ast::{Ast, Ast::*},
    ast_walk::WalkRule::*,
    core_type_forms::{less_quoted_ty, more_quoted_ty, nt_is_positive, nt_to_type},
    form::{Both, Form, Negative, Positive},
    grammar::FormPat,
    name::*,
    runtime::eval::{Destructure, Eval, QQuote, QQuoteDestr},
    util::assoc::Assoc,
    walk_mode::{NegativeWalkMode, WalkMode},
};
use std::rc::Rc;

// == Types and syntax quotation: when are annotations needed? ==
// Expressions are "positive", and are traversed leaf-to-root in an environment, producing a type.
// Patterns are "negative", and are traversed root-to-leaf from a type, producing an environment.
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
//   (frobnicate_pat '[Pat<List<Int>> | (cons a b)]')
// In this case, we need to know the type of the syntax quote,
//  but the pattern also wants to know its own type so that it can tell us its environment.
//
//   match stx { '[Expr | 1 + 5 * ,[Expr<Nat> | stx_num], ]' => ... }
// In this case (looking at the expression interpolation),
//  we need to know the type of the interpolated expression syntax
//    (a pattern, even though it's a pattern *for* an expression)
//   in order to type-synthesize the arithmetic.
//
//
// Examples of when we get to do a bonus typecheck:
//
//   match stx { '[Expr | f x]' => ... }
// In this case, we can check that the type of the scrutinee
//  (which is the type of the syntax quotation pattern)
//   equals `Expr< (whatever `f` returns) >`.
//
//   optimize_expr '[Expr | match stx { ,[my_pat], => ... } ]'
// In this case (looking at the Pat interpolation),
//  we can check that the type of the quoted scrutinee is the same as
//   the type of `my_pat` (after peeling off its `Pat<>`).
//
// Note that it doesn't matter whether the boundary is a quotation or an unquotation!
// The phase only matters inasmuch as variables don't leave their phase.

// There's a nice-seeming syntax for determining what `unquote` does when quotation is nested.
// However, it would require some weird additional power for the parser:
//   '[Expr | '[Expr | ,[…], ,,[…],, ]']'
// OTOH, if you are using `,,,,[],,,,`, something has gone terribly wrong.

// == Opacity! ==
// Basically, ` ,[Expr<T> | a ], ` dumps an expression with the type `T` into the type checker,
//  but at a different phase from where `T` was defined.
// We don't want to capture the whole environment,
//  so we want the typechecker to treat `T` opaquely (i.e. without looking up),
//   which is what "mu_type" does.
// We just need to write a walk for it (and annotate those `mu_type`s with a depth)

fn adjust_opacity(t: &Ast, env: Assoc<Name, Ast>, delta: i32) -> Ast {
    let ctxt = crate::ast_walk::LazyWalkReses {
        extra_info: delta,
        ..crate::ast_walk::LazyWalkReses::new_wrapper(env)
    };
    crate::ast_walk::walk::<MuProtect>(t, &ctxt).unwrap()
}

fn remove_opacity(t: &Ast, delta: i32) -> Ast {
    if delta > 0 {
        icp!()
    }
    // The environment doesn't matter when removing opacity
    adjust_opacity(t, Assoc::new(), delta)
}

// This walk is for one very simple purpose: to add `mu` around unbound names.
custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct MuProtect {}
}
// Sadly, we have to define a negative version, even though it's never used.
custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct UnusedNegativeMuProtect {}
}

fn change_mu_opacity(parts: crate::ast_walk::LazyWalkReses<MuProtect>) -> Result<Ast, ()> {
    let delta = parts.extra_info;
    let opacity = &parts
        .maybe_get_term(n("opacity_for_different_phase"))
        .map(|a| a.to_name().sp().parse::<i32>().unwrap());

    if let Some(opacity) = opacity {
        if opacity + delta < 0 {
            icp!("unwrapped too far")
        }

        if opacity + delta == 0 {
            return Ok(crate::core_forms::strip_ee(&parts.get_term(n("body"))).clone());
        }
    }
    match parts.this_ast {
        Ast::Node(f, mut mu_parts, export) => {
            if let Some(opacity) = opacity {
                mu_parts.add_leaf(
                    n("opacity_for_different_phase"),
                    Ast::Atom(n(&(opacity + delta).to_string())),
                );
            }
            Ok(Ast::Node(f, mu_parts, export))
        }
        _ => icp!(),
    }
}

impl WalkMode for MuProtect {
    fn name() -> &'static str { "MProt" }
    type Elt = Ast;
    type Negated = UnusedNegativeMuProtect;
    type AsPositive = MuProtect;
    type AsNegative = UnusedNegativeMuProtect;
    type Err = ();
    type D = crate::walk_mode::Positive<MuProtect>;
    type ExtraInfo = i32;

    fn get_walk_rule(f: &Form) -> crate::ast_walk::WalkRule<MuProtect> {
        if f.name == n("mu_type") {
            cust_rc_box!(change_mu_opacity)
        } else {
            LiteralLike
        }
    }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(name: Name, parts: &crate::ast_walk::LazyWalkReses<MuProtect>) -> Result<Ast, ()> {
        if parts.extra_info <= 0 {
            return Ok(VariableReference(name));
        }
        Ok(parts.env.find(&name).map(Clone::clone).unwrap_or_else(|| {
            ast!({"Type" "mu_type" :
                "opacity_for_different_phase" => (, Ast::Atom(n(&parts.extra_info.to_string()))),
                "param" => [(import [prot "param"] (, Ast::VariableReference(name)))],
                "body" => (import [* [prot "param"]] (, Ast::VariableReference(name)))})
        }))
    }

    // TODO: it seems like we always need to define this; think about this more.
    fn underspecified(name: Name) -> Ast { VariableReference(name) }
}

impl WalkMode for UnusedNegativeMuProtect {
    fn name() -> &'static str { "XXXXX" }
    type Elt = Ast;
    type Negated = MuProtect;
    type AsPositive = MuProtect;
    type AsNegative = UnusedNegativeMuProtect;
    type Err = ();
    type D = crate::walk_mode::Negative<UnusedNegativeMuProtect>;
    type ExtraInfo = i32;
    fn get_walk_rule(_: &Form) -> crate::ast_walk::WalkRule<UnusedNegativeMuProtect> { icp!() }
    fn automatically_extend_env() -> bool { icp!() }
}

impl NegativeWalkMode for UnusedNegativeMuProtect {
    fn needs_pre_match() -> bool { panic!() }
}

// Technically, we could have the parser decide whether `unquote` is allowed.
//  (It only makes sense inside a `quote`.)
// However, this would leave us with one `unquote` form available per level of quotation

/// Generate a (depth-1) unquoting form.
/// `pos_quot` is true iff the quotation itself (and thus the interpolation) is positive.
pub fn unquote(nt: Name, pos_quot: bool) -> Rc<FormPat> {
    Rc::new(FormPat::Scope(
        unquote_form(nt, pos_quot, 1),
        if pos_quot {
            crate::beta::ExportBeta::Nothing
        } else {
            crate::beta::ExportBeta::Use(n("body"))
        },
    ))
}

pub fn unquote_form(nt: Name, pos_quot: bool, depth: u8) -> Rc<Form> {
    let form_delim_start = &format!("{}[", ",".repeat(depth as usize));

    Rc::new(Form {
        name: n("unquote"),
        grammar:
            // It's a pain to determine whether type annotation is needed at syntax time,
            //  so it's optional
            Rc::new(if pos_quot {
                form_pat!((delim form_delim_start, "[",
                    [(named "nt", (anyways (, VariableReference(nt)))),
                     (alt
                        [],
                        [(name_lit__by_name nt),
                         (call "DefaultSeparator"), (scan r"(<)"),
                         (named "ty_annot", (call "Type")),
                         (call "DefaultSeparator"), (scan r"(>)"), (lit "|")]),
                     (named "body", (-- depth (call "Expr")))]))
            } else {
                form_pat!((delim form_delim_start, "[",
                    [(named "nt", (anyways (, VariableReference(nt)))),
                     (alt
                        [],
                        [(name_lit__by_name nt),
                         (call "DefaultSeparator"), (scan r"(<)"),
                         (named "ty_annot", (call "Type")),
                         (call "DefaultSeparator"), (scan r"(>)"),
                         (lit "|")]),
                     (named "body", (-- depth (call "Pat")))]))
            }),
        type_compare: Positive(NotWalked), // this is not a type form
        synth_type:
            // `nt_is_positive` and `pos_quot` have opposite roles from `quote`
            if nt_is_positive(nt) {
                //  For example: (this quotation could be positive or negative)
                // (nt_is_positive is true in this example, though)
                // ` '[Expr | .[a : Int . ,[Expr<String> | body], ]. ]' `
                //                        ^^^^^^^^^^^^^^^^^^^^^^^
                Positive(
                    // `body` has the type `Expr<String>` (annotation is superfluous):
                    cust_rc_box!( move | unquote_parts | {
                        let ast_for_errors = unquote_parts.get_term(n("body"));

                        let res = if pos_quot {
                            // TODO: check annotation if present

                            let mut res = unquote_parts.get_res(n("body"))?; // `Expr<String>`
                            for _ in 0..(depth-1) {
                                res = less_quoted_ty(&res, None, &ast_for_errors)?;
                            } // HACK: we only know the last `nt` to expect
                            less_quoted_ty(&res, Some(nt), &ast_for_errors)?
                        } else {
                            // need a type annotation
                            if !unquote_parts.has(n("ty_annot")) {
                                ty_err!(AnnotationRequired (()) at unquote_parts.this_ast);
                            }
                            let expected_type = unquote_parts.get_res(n("ty_annot"))?;

                            let mut ctxt_elt = expected_type.clone();
                            for _ in 0..(depth-1) {
                                unimplemented!("We may need a stack of what NTs are quoted")
                            }
                            ctxt_elt = more_quoted_ty(&ctxt_elt, nt);

                            let negative_parts = unquote_parts.switch_mode::<crate::ty::UnpackTy>();
                            let _res = negative_parts.with_context(ctxt_elt).get_res(n("body"))?;

                            expected_type
                        };

                        Ok(adjust_opacity(&res, unquote_parts.env, i32::from(depth)))
                    }))
            } else {
                // For example: ` '[Pat | (x, ,[Pat<String> | body], ) ]' `
                //                            ^^^^^^^^^^^^^^^^^^^^^^
                Negative(
                    cust_rc_box!( move | unquote_parts | {
                        let ast_for_errors = unquote_parts.get_term(n("body"));
                        let ctxt_elt = remove_opacity(unquote_parts.context_elt(),
                                                      -(i32::from(depth)));

                        let mut ctxt_elt = ctxt_elt;
                        for _ in 0..(depth-1) {
                            unimplemented!("We may need a stack of what NTs are quoted")
                        }
                        ctxt_elt = more_quoted_ty(&ctxt_elt, nt);

                        if pos_quot {
                            // `String`
                            let lq_parts = unquote_parts.switch_mode::<crate::ty::SynthTy>();
                            let res = lq_parts.get_res(n("body"))?;

                            // Bonus typecheck
                            ty_exp!(&ctxt_elt, &res, ast_for_errors);

                            Ok(Assoc::new()) // TODO: this seems like it shouldn't be empty
                        } else {
                            // phase-shift the context_elt:
                            let _res = unquote_parts.with_context(ctxt_elt).get_res(n("body"))?;

                            Ok(Assoc::new()) // TODO: does this make sense?
                        }
                    })
                )
            },

            // Also, let's suppose that we have something like:
            //   let some_pattern : pat<int> = ...
            //   let s = '[{pat} struct { a: ,[ some_pattern ],  b: b_var} ]'
            // ...what then?
        eval:
            Both(NotWalked, NotWalked), // Outside a quotation? Makes no sense!
        quasiquote: // TODO #26: this and "dotdotdot" are the only forms that *aren't* `LiteralLike`
            Both( // TODO: double-check that `pos` and `neg` don't matter here
                cust_rc_box!( move | unquote_parts | {
                    let lq_parts = unquote_parts.switch_mode::<Eval>();
                    crate::ast_walk::walk::<Eval>(lq_parts.get_term_ref(n("body")), &lq_parts)
                }),
                cust_rc_box!( move | unquote_parts | {
                    let context = unquote_parts.context_elt().clone();

                    let lq_parts = unquote_parts.switch_mode::<Destructure>();
                    crate::ast_walk::walk::<Destructure>(lq_parts.get_term_ref(n("body")),
                        &lq_parts.with_context(context))
                }))
    })
}

// Macro By Example transcription. TODO: currently positive-only
// There are two parts to the way that Macro By Example works in Unseemly.
//
// The first is the types and how to construct them:
//  If `T` is `**[Int Float]**,
//   then `:::[T >> Expr<T> ]:::` is `**[Expr<Int>  Expr<Float>]**`.
//  If you match syntax under a `*`, you'll get something like `::[T >> Expr<T> ]:::`.
//
// The second is how we use them:
//  In a syntax quotation, you can write `...[,x, >> some_syntax]...`
pub fn dotdotdot(nt: Name) -> Rc<FormPat> {
    Rc::new(FormPat::Scope(dotdotdot_form(nt), crate::beta::ExportBeta::Nothing))
}

// Once it's possible to write `where Mode::Elt = Ast and Mode::Err = <whatever>`,
//  this can be turned into a function.
// The behavior of `...[]...` is identical in positive and negative modes.
macro_rules! ddd_type__body {
    ($ddd_parts:expr) => {
        {
            let drivers : Vec<Name> = $ddd_parts.get_rep_term(n("driver")).into_iter().map(|a| {
                match a {
                    QuoteLess(ref d, _) => d.vr_to_name(),
                    _ => icp!()
                }
            }).collect();


            // HACK: we want to operate on the environment one level less quoted
            //  (that's why we put commas around the drivers)
            // Not sure what how OEH interacts with this. Doesn't matter in the positive case.
            let (_, ddd_parts_uq) = $ddd_parts.quote_less();

            let mut walked_env = Assoc::new();

            let repeats = match ddd_parts_uq.env.find(&drivers[0]) {
                Some(&Node(ref form, ref parts, _)) if form.name == n("tuple") => {
                    parts.get_rep_leaf_or_panic(n("component")).len()
                }
                // TODO: what if some are `tuple` and others are `dotdotdot`?
                Some(&Node(ref form, _, _)) if form.name == n("dotdotdot") => 1,
                Some(other_t) => {
                    ty_err!(UnableToDestructure(other_t.clone(), n("tuple"))
                                at ddd_parts_uq.this_ast);
                }
                _ => ty_err!(UnboundName(drivers[0]) at ddd_parts_uq.this_ast),
            };

            // We should be invoking `get_res` once per repetition,
            //  and reconstructing a repetition... somehow.
            for i in 0..repeats {
                for (name, ty) in ddd_parts_uq.env.iter_pairs() {
                    if drivers.contains(name) {
                        walked_env = walked_env.set(*name, match ty {
                            Node(ref form, ref parts, _) if form.name == n("tuple") => {
                                let component
                                    = parts.get_rep_leaf_or_panic(n("component"))[i].clone();
                                let ddd2_form = crate::core_forms::find("Type", "dotdotdot_type");
                                if let Some(ddd2_parts) = component.destructure(ddd2_form) {
                                    // HACK! If the tuple had a ddd, we should just unwrap it.
                                    // We should somehow eliminate this linkage between
                                    //  syntax repetition and tuples with type repetition.
                                    ddd2_parts.get_leaf_or_panic(&n("body")).clone()
                                } else {
                                    component
                                }
                            }
                            Node(ref form, ref parts, _) if form.name == n("dotdotdot") =>
                            {
                                parts.get_leaf_or_panic(&n("body")).clone()
                            }
                            t => ty_err!(UnableToDestructure(t.clone(), n("tuple")) at t),
                        });
                    } else {
                        walked_env = walked_env.set(*name, ty.clone());
                    }
                }
            }
            ddd_parts_uq.with_environment(walked_env).quote_more(None).get_res(n("body"))
        }
    };
}

// TODO #38: This should take a grammar, not an NT, as an argument,
//  and be located underneath each Plus or Star.
pub fn dotdotdot_form(nt: Name) -> Rc<Form> {
    Rc::new(Form {
        name: n("dotdotdot"),
        grammar: Rc::new(form_pat!((delim "...[", "[",
            [(star [(call "DefaultSeparator"), (scan "(,)"),
             (named "driver", (-- 1 varref)),
             (call "DefaultSeparator"), (scan "(,)")]), (lit ">>"),
             (named "body", (call_by_name nt))]))),
        type_compare: Positive(NotWalked), // this is not a type form
        synth_type: Both(
            cust_rc_box!(|ddd_parts| { ddd_type__body!(ddd_parts) }),
            cust_rc_box!(|ddd_parts| { ddd_type__body!(ddd_parts) }),
        ),
        // An evaluate-time version of this might be a good idea;
        //  it might be all that's needed to implement variable-number-of-argument functions.
        // It shouldn't be the same form, though. Maybe `...( >> )...` ?
        eval: Positive(NotWalked),
        quasiquote: Positive(cust_rc_box!(|ddd_parts| {
            use crate::{
                runtime::eval::{Sequence, Value},
                walk_mode::WalkElt,
            };

            let (_, ddd_parts_uq) = ddd_parts.quote_less();

            let drivers: Vec<Name> = ddd_parts_uq
                .get_rep_term(n("driver"))
                .into_iter()
                .map(|a| match a {
                    QuoteLess(ref d, _) => d.vr_to_name(),
                    _ => icp!(),
                })
                .collect();

            // TODO: the typechecker should reject dotdotdotds with no drivers,
            // or where a driver isn't in scope.
            let count = match *ddd_parts_uq.env.find_or_panic(&drivers[0]) {
                Sequence(ref contents) => contents.len(),
                _ => icp!("type error"),
            };
            let mut reps: Vec<Ast> = vec![];

            for i in 0..count {
                let mut walked_env = Assoc::new();
                for (n, val) in ddd_parts_uq.env.iter_pairs() {
                    let walked_val = if drivers.contains(n) {
                        match *val {
                            Sequence(ref contents) => (*contents[i]).clone(),
                            _ => icp!("type error"),
                        }
                    } else {
                        val.clone()
                    };
                    walked_env = walked_env.set(*n, walked_val);
                }

                ddd_parts_uq.clear_memo();
                reps.push(
                    ddd_parts_uq
                        .with_environment(walked_env)
                        .quote_more(None)
                        .get_res(n("body"))?
                        .to_ast(),
                );
            }

            // HACK: this tells `walk_quasi_literally` to splice (TODO #40?)
            Ok(Value::from_ast(&Shape(reps)))
        })),
    })
}

// How do we walk quasiquotations?
// During type synthesis, we are checking the internal structure of the quoted syntax,
//  and we walk it just like we walk normal AST; just with a shifted environment.
// This is why we sometimes need type annotations.

// During evaluation, quoted terms are inactive.
// Everything (except `unquote` and `dotdotdot`!) is LiteralLike.
// Furthermore, the direction of the walk is determined by the direction of the original quotation.

pub fn quote(pos: bool) -> Rc<Form> {
    use crate::{earley::ParseContext, grammar::FormPat::*};

    let perform_quotation = move |pc: ParseContext, starter_info: Ast| -> ParseContext {
        let starter_nt = match starter_info {
            IncompleteNode(ref parts) => parts.get_leaf_or_panic(&n("nt")).vr_to_name(),
            _ => icp!("malformed quotation"),
        };
        fn already_has_unquote(fp: &FormPat) -> bool {
            match *fp {
                Alt(ref parts) => parts.iter().any(|sub_fp| already_has_unquote(&*sub_fp)),
                Biased(ref plan_a, ref plan_b) => {
                    already_has_unquote(&*plan_a) || already_has_unquote(&*plan_b)
                }
                Scope(ref f, _) => f.name == n("unquote"),
                _ => false,
            }
        }

        let pos_inside = nt_is_positive(starter_nt);

        // TODO: Editing forms is really sketchy!
        // Maybe we should go back to having a special (gensymmed) NT
        //  or some other way to signal to the parser to treat repetitions differently.
        let new_grammar = pc
            .grammar
            .keyed_map_borrow_f(&mut |nt: &Name, nt_def: &Rc<FormPat>| {
                if already_has_unquote(nt_def)
               // HACK: this is to avoid hitting "starterer". TODO: find a better way
               || (nt != &n("Expr") && nt != &n("Pat") && nt != &n("Type") && nt != &n("AtomNotInPat"))
                {
                    nt_def.clone()
                } else {
                    let nt_for_type = if nt == &n("AtomNotInPat") { n("Atom") } else { *nt };
                    // TODO #38: we should insert `dotdotdot` under Star and Plus,
                    //  not at the top level
                    Rc::new(Biased(
                        unquote(nt_for_type, pos),
                        Rc::new(Biased(dotdotdot(*nt), nt_def.clone())),
                    ))
                }
            })
            .set(
                n("QuotationBody"),
                Rc::new(form_pat!(
                    // HACK: The `nt` from outside isn't in the same Scope, it seems:
                    [(named "nt", (anyways (, VariableReference(starter_nt)))),
                     (alt
                        [],
                        [(call "DefaultSeparator"), (scan r"(<)"),
                         (named "ty_annot", (call "Type")),
                         (call "DefaultSeparator"), (scan r"(>)")]),
                     (lit "|"),
                     (named "body", (++ pos_inside (call_by_name starter_nt)))])),
            );

        pc.with_grammar(new_grammar)
    };

    // TODO #4: the following hardcodes positive walks as `Expr` and negative walks as `Pat`.
    // What happens when more NTs are added?
    Rc::new(Form {
        name: if pos { n("quote_expr") } else { n("quote_pat") },
        grammar: Rc::new(form_pat!((delim "'[", "[",
            // TODO: use `extend`, not `extend_nt`. Can it resolve the HACK above?
            [(extend_nt (named "nt", varref), "QuotationBody", perform_quotation)]))),
        type_compare: Both(NotWalked, NotWalked), // Not a type
        synth_type: if pos {
            Positive(cust_rc_box!(|quote_parts| {
                if nt_is_positive(quote_parts.get_term(n("nt")).vr_to_name()) {
                    // TODO #9: if the user provides an annotation, check it!
                    Ok(ast!({"Type" "type_apply" :
                        "type_rator" =>
                            (, nt_to_type(quote_parts.get_term(n("nt")).vr_to_name()) ),
                        "arg" => [(, remove_opacity(&quote_parts.get_res(n("body"))?, -1) )]
                    }))
                } else {
                    if !quote_parts.has(n("ty_annot")) {
                        ty_err!(AnnotationRequired (()) at quote_parts.this_ast);
                    }
                    let expected_type = &quote_parts.get_res(n("ty_annot"))?;

                    // We're looking at things 1 level deeper:
                    let prot_expected_type =
                        adjust_opacity(expected_type, quote_parts.env.clone(), 1);

                    // TODO: do we need this result environment somewhere?
                    // Note that `Pat<Point>` (as opposed to `Pat <:[x: Real, y: Real>:`)
                    //  is what we want!
                    // In other words, syntax types don't care about positive vs. negative!
                    // There's a longer argument in the form of code to this effect elsewhere,
                    //  but it boils down to this: environments can always be managed directly,
                    //   by introducing and referencing bindings.
                    let _ = &quote_parts.with_context(prot_expected_type).get_res(n("body"));

                    Ok(ast!({"Type" "type_apply" :
                            "type_rator" =>
                                (, nt_to_type(quote_parts.get_term(n("nt")).vr_to_name()) ),
                            "arg" => [ (,expected_type.clone()) ]}))
                }
            }))
        } else {
            Negative(cust_rc_box!(|quote_parts| {
                // There's no need for a type annotation
                let nt = quote_parts.get_term(n("nt")).vr_to_name();
                if nt_is_positive(nt) {
                    // TODO #9: check that this matches the type annotation, if provided!
                    quote_parts.get_res(n("body"))
                } else {
                    let new_context =
                        less_quoted_ty(quote_parts.context_elt(), Some(nt), &quote_parts.this_ast)?;
                    // TODO #9: check that this matches the type annotation, if provided!
                    quote_parts.with_context(new_context).get_res(n("body"))
                }
            }))
        },
        eval: if pos {
            Positive(cust_rc_box!(|quote_parts| {
                let mq_parts = quote_parts.switch_mode::<QQuote>().quote_more(None);
                match mq_parts.get_term_ref(n("body")) {
                    // Strip the `QuoteMore`:
                    QuoteMore(ref a, _) => crate::ast_walk::walk::<QQuote>(&*a, &mq_parts),
                    _ => icp!(),
                }
            }))
        } else {
            Negative(cust_rc_box!(|quote_parts| {
                let context = quote_parts.context_elt().clone();

                let mq_parts =
                    quote_parts.switch_mode::<QQuoteDestr>().quote_more(None).with_context(context);
                match mq_parts.get_term_ref(n("body")) {
                    // Strip the `QuoteMore`:
                    QuoteMore(ref body, _) => {
                        crate::ast_walk::walk::<QQuoteDestr>(&*body, &mq_parts)
                    }
                    _ => icp!(),
                }
            }))
        },
        quasiquote: Both(LiteralLike, LiteralLike),
    })
}

#[test]
fn quote_unquote_eval_basic() {
    use crate::{ast_walk::LazyWalkReses, runtime::eval::Value};

    let pos = true;
    let neg = false;

    let env = assoc_n!(
        "n" => val!(i 5),
        "en" => val!(ast (vr "qn"))
    );

    let qenv = assoc_n!(
        "qn" => val!(i 6)
    );

    fn eval_two_phased(
        expr: &Ast,
        env: Assoc<Name, Value>,
        qenv: Assoc<Name, Value>,
    ) -> Result<Value, ()> {
        crate::ast_walk::walk::<Eval>(expr, &LazyWalkReses::new_mq_wrapper(env, vec![qenv]))
    }

    fn destr_two_phased(
        pat: &Ast,
        env: Assoc<Name, Value>,
        qenv: Assoc<Name, Value>,
        ctxt: Value,
    ) -> Result<Assoc<Name, Value>, ()> {
        crate::ast_walk::walk::<Destructure>(
            pat,
            &LazyWalkReses::new_mq_wrapper(env, vec![qenv]).with_context(ctxt),
        )
    }

    assert_eq!(
        eval_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true (vr "qn"))}),
            env.clone(),
            qenv.clone()
        ),
        Ok(val!(ast (vr "qn")))
    );

    assert_eq!(
        eval_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"),
        "body" => (++ true {unquote_form(n("Expr"), true, 1) ; "nt" => (vr "Expr"),
            "body" => (-- 1 (vr "en"))})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(val!(ast (vr "qn")))
    );

    assert_eq!(
        destr_two_phased(
            &ast!({quote(neg) ; "nt" => (vr "Expr"), "body" => (++ false (vr "qn"))}),
            env.clone(),
            qenv.clone(),
            val!(ast (vr "qn"))
        ),
        Ok(Assoc::<Name, Value>::new())
    );

    // '[Expr | match qn { x => qn }]'
    assert_m!(
        eval_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true
                {"Expr" "match" :
                    "scrutinee" => (vr "qn"),
                    "p" => [@"c" "x"],
                    "arm" => [@"c" (import ["p" = "scrutinee"] (vr "qn"))]})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(_)
    );
}

#[test]
fn quote_type_basic() {
    let pos = true;
    let neg = false;

    let env = assoc_n!(
        "n" => ast!({"Type" "Nat" :})
    );

    let qenv = assoc_n!(
        "qn" => ast!({"Type" "Nat" :})
    );

    let expr_type = crate::core_type_forms::get__primitive_type(n("Expr"));
    let pat_type = crate::core_type_forms::get__primitive_type(n("Pat"));

    fn synth_type_two_phased(
        expr: &Ast,
        env: Assoc<Name, Ast>,
        qenv: Assoc<Name, Ast>,
    ) -> crate::ty::TypeResult {
        crate::ast_walk::walk::<crate::ty::SynthTy>(
            expr,
            &crate::ast_walk::LazyWalkReses::new_mq_wrapper(env, vec![qenv]),
        )
    }

    // '[Expr | qn]'
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true (vr "qn"))}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Nat" :}]}))
    );

    // '[Expr | match qn { x => qn }]'
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true
                {"Expr" "match" :
                    "scrutinee" => (vr "qn"),
                    "p" => [@"c" "x"],
                    "arm" => [@"c" (import ["p" = "scrutinee"] (vr "qn"))]})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Nat" :}]}))
    );

    // previously unaccessed environments default to the core values/types
    // '[Expr | '[Expr | five]']'
    assert_eq!(
        crate::ty::synth_type(
            // By default, `synth_type` uses the same env in all phases.
            &ast!(
            {quote(pos) ; "nt" => (vr "Expr"), "body" =>
                (++ true {quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true (vr "five"))})}),
            assoc_n!("five" => uty!({Int :}))
        ),
        Ok(ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" =>
                [{"Type" "type_apply" :
                    "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Int" :}]}]}))
    );

    // '[Expr<Nat> | qn]'
    // With type annotation, same result:
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true (vr "qn")),
                "ty_annot" => {"Type" "Nat" :}}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Nat" :}]}))
    );

    // '[Expr | n]'
    assert_m!(
        synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true (vr "n"))}),
            env.clone(),
            qenv.clone()
        ),
        ty_err_p!(UnboundName(_))
    );

    // '[Expr | { x: qn  y: qn }]'
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"),
                "body" => (++ true {"Expr" "struct_expr" :
                    "component_name" => [@"c" "x", "y"],
                    "component" => [@"c" (vr "qn"), (vr "qn")]
            })}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
        "type_rator" => (,expr_type.clone()), "arg" => [{ "Type" "struct" :
            "component_name" => [@"c" "x", "y"],
            "component" => [@"c" {"Type" "Nat":}, {"Type" "Nat" :}]
        }]}))
    );

    fn unpack_type_two_phased(
        pat: &Ast,
        env: Assoc<Name, Ast>,
        qenv: Assoc<Name, Ast>,
        ctxt: Ast,
    ) -> Result<Assoc<Name, Ast>, crate::ty::TypeError> {
        crate::ast_walk::walk::<crate::ty::UnpackTy>(
            pat,
            &crate::ast_walk::LazyWalkReses::new_mq_wrapper(env, vec![qenv]).with_context(ctxt),
        )
    }

    // A trivial pattern containing an expression
    // '[Expr< struct {} > | *[]* ]'
    assert_eq!(
        unpack_type_two_phased(
            &ast!({quote(neg) ;
                "nt" => (vr "Expr"),
                "ty_annot" => {"Type" "struct":
                    "component_name" => [@"c"], "component" => [@"c"]},
                "body" => (++ true {"Expr" "struct_expr":
                    "component_name" => [@"c"], "component" => [@"c"]})}),
            env.clone(),
            qenv.clone(),
            ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{ "Type" "struct" :
                "component_name" => [@"c"], "component" => [@"c"]
            }]})
        ),
        Ok(assoc_n!())
    );

    // A trivial pattern containing a pattern
    // '[Pat< struct {} > | *[]* ]'
    assert_eq!(
        unpack_type_two_phased(
            &ast!({quote(neg) ;
                "nt" => (vr "Pat"),
                "ty_annot" => {"Type" "struct":
                    "component_name" => [@"c"], "component" => [@"c"]},
                "body" => (++ false {"Pat" "struct_pat":
                    "component_name" => [@"c"], "component" => [@"c"]})}),
            env.clone(),
            qenv.clone(),
            ast!({"Type" "type_apply" :
            "type_rator" => (,pat_type.clone()), "arg" => [{ "Type" "struct" :
                "component_name" => [@"c"], "component" => [@"c"]
            }]})
        ),
        Ok(assoc_n!())
    );

    // A slightly-less trivial pattern containing a pattern (but still no unquotes)
    // '[Pat< struct {x: Nat} > | *[x: qfoo]* ]'
    assert_eq!(
        unpack_type_two_phased(
            &ast!({quote(neg) ;
                "nt" => (vr "Pat"),
                "ty_annot" => {"Type" "struct":
                    "component_name" => [@"c" "x"], "component" => [@"c" {"Type" "Nat" :}]},
                "body" => (++ false {"Pat" "struct_pat":
                    "component_name" => [@"c" "x"], "component" => [@"c" "qfoo"]})}),
            env.clone(),
            qenv.clone(),
            ast!({"Type" "type_apply" :
            "type_rator" => (,pat_type.clone()), "arg" => [{ "Type" "struct" :
                "component_name" => [@"c" "x"], "component" => [@"c" {"Type" "Nat" :}]
            }]})
        ),
        Ok(assoc_n!())
    );
}

#[test]
fn quote_unquote_type_basic() {
    let pos = true;
    let neg = false;

    let expr_type = crate::core_type_forms::get__primitive_type(n("Expr"));
    let pat_type = crate::core_type_forms::get__primitive_type(n("Pat"));

    assert_eq!(
        crate::ty::synth_type(
            &ast!(
        {quote(pos) ; "nt" => (vr "Pat"), "ty_annot" => {"Type" "Nat" :},
                      "body" => (++ false "x")}),
            Assoc::new()
        ),
        Ok(ast!({"Type" "type_apply" : "type_rator" => (,pat_type.clone()),
            "arg" => [{"Type" "Nat" :}]}))
    );

    let env = assoc_n!(
        "T" => ast!((vr "T")), // we're under a `forall T . ⋯`
        "n" => ast!({"Type" "Nat" :}),
        "en" => ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Nat" :}]}),
        "pn" => ast!({"Type" "type_apply" :
            "type_rator" => (,pat_type.clone()), "arg" => [{"Type" "Nat" :}]}),
        "pT" => ast!({"Type" "type_apply" :
            "type_rator" => (,pat_type.clone()), "arg" => [(vr "T")]}),
        "ef" => ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Float" :}]}),
        "eT" => ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [(vr "T")]}),
        "eT_to_T" => ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" =>
                [{"Type" "fn" : "param" => [(vr "T")], "ret" => (vr "T")}]})
    );

    let qenv = assoc_n!(
        "qn" => ast!({"Type" "Nat" :}),
        // We're under a (differently-phased) `forall T . ⋯`
        "qT" => adjust_opacity(&ast!((vr "T")), Assoc::new(), 1)
    );

    fn synth_type_two_phased(
        expr: &Ast,
        env: Assoc<Name, Ast>,
        qenv: Assoc<Name, Ast>,
    ) -> crate::ty::TypeResult {
        crate::ast_walk::walk::<crate::ty::SynthTy>(
            expr,
            &crate::ast_walk::LazyWalkReses::new_mq_wrapper(env, vec![qenv]),
        )
    }
    // An expression containing an expression
    // '[Expr |
    //     *[x: ,[Expr | en], y: ,[Expr | ef], z: baz]* ]'
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ;
            "nt" => (vr "Expr"),
            "body" => (++ true {"Expr" "struct_expr":
                "component_name" => [@"c" "x", "y", "z"],
                "component" => [@"c"
                    {unquote_form(n("Expr"), pos, 1) ;
                        "nt" => (vr "Expr"), "body" => (-- 1 (vr "en"))},
                    {unquote_form(n("Expr"), pos, 1) ;
                        "nt" => (vr "Expr"), "body" => (-- 1 (vr "ef"))},
                    (vr "qn")
                ]})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" : "type_rator" => (,expr_type.clone()),
            "arg" => [{"Type" "struct":
                "component_name" => [@"c" "x", "y", "z"],
                "component" => [@"c" {"Type" "Nat" :}, {"Type" "Float" :}, {"Type" "Nat" :}]}]}))
    );

    // '[Expr | (,[Expr | eT_to_T],  ,[Expr | eT],) ]'
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ;
                "nt" => (vr "Expr"),
                "body" => (++ true {"Expr" "apply":
                    "rator" => {unquote_form(n("Expr"), pos, 1) ; "nt" => (vr "Expr"), "body" =>
                        (-- 1 (vr "eT_to_T"))},
                    "rand" => [{unquote_form(n("Expr"), pos, 1) ; "nt" => (vr "Expr"), "body" =>
                        (-- 1 (vr "eT"))}]})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" : "type_rator" => (,expr_type.clone()),
            "arg" => [(vr "T")]}))
    );

    fn unpack_type_two_phased(
        pat: &Ast,
        env: Assoc<Name, Ast>,
        qenv: Assoc<Name, Ast>,
        ctxt: Ast,
    ) -> Result<Assoc<Name, Ast>, crate::ty::TypeError> {
        crate::ast_walk::walk::<crate::ty::UnpackTy>(
            pat,
            &crate::ast_walk::LazyWalkReses::new_mq_wrapper(env, vec![qenv]).with_context(ctxt),
        )
    }

    // A pattern containing a pattern
    // '[Pat< struct {x : Nat y : Float z : Nat} > |
    //     *[x: ,[Pat | foo], y: ,[Pat | bar], z: baz]* ]'
    assert_eq!(
        unpack_type_two_phased(
            &ast!({quote(neg) ;
            "nt" => (vr "Pat"),
            "ty_annot" => {"Type" "struct":
                "component_name" => [@"c" "x", "y", "z"],
                "component" => [@"c" {"Type" "Nat" :}, {"Type" "Float" :}, {"Type" "Nat" :}]},
            "body" => (++ false {"Pat" "struct_pat":
                "component_name" => [@"c" "x", "y", "z"],
                "component" => [@"c"
                    {unquote_form(n("Pat"), neg, 1) ; "nt" => (vr "Pat"), "body" => (-- 1 "foo")},
                    {unquote_form(n("Pat"), neg, 1) ; "nt" => (vr "Pat"), "body" => (-- 1 "bar")},
                    "baz"
                ]})}),
            env.clone(),
            qenv.clone(),
            ast!({"Type" "type_apply" :
            "type_rator" => (,pat_type.clone()), "arg" => [{ "Type" "struct" :
                "component_name" => [@"c" "x", "y", "z"],
                "component" => [@"c" {"Type" "Nat" :}, {"Type" "Float" :}, {"Type" "Nat" :}]
            }]})
        ),
        Ok(assoc_n!(
            "foo" => ast!({"Type" "type_apply" :
                "arg" => [{"Type" "Nat" :}],
                "type_rator" => (,pat_type.clone())}),
            "bar" => ast!({"Type" "type_apply" :
                "arg" => [{"Type" "Float" :}],
                "type_rator" => (,pat_type.clone())})))
    );

    // Interpolate a pattern
    // '[Expr | match qn { ,[Pat<Nat> | pn], => qn }]
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ;
                "nt" => (vr "Expr"),
                "body" => (++ true {"Expr" "match":
                    "scrutinee" => (vr "qn"),
                    "p" => [@"c" {unquote_form(n("Pat"), pos, 1);
                         "nt" => (vr "Pat"),
                         "ty_annot" => {"Type" "type_apply" :
                                        "type_rator" => (,pat_type.clone()),
                                        "arg" => {"Type" "Nat" :}},
                         "body" => (-- 1 (vr "pn"))}],
                    "arm" => [@"c" (import ["p" = "scrutinee"] (vr "qn"))]})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
                "type_rator" => (,expr_type.clone()), "arg" => [{ "Type" "Nat" :}]}))
    );

    // Interpolate a pattern, with abstract types
    // '[Expr | match qT { ,[Pat<T> | pT], => qT }]
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ;
                "nt" => (vr "Expr"),
                "body" => (++ true {"Expr" "match":
                    "scrutinee" => (vr "qT"),
                    "p" => [@"c" {quote(neg) ; "nt" => (vr "Pat"),
                                               "ty_annot" =>
                                                    {"Type" "type_apply" :
                                                        "type_rator" => (,pat_type.clone()),
                                                        "arg" => (vr "T")},
                                                "body" => (-- 1 (vr "pT"))}],
                    "arm" => [@"c" (vr "qT")]})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
                "type_rator" => (,expr_type.clone()), "arg" => [(vr "T")]}))
    );
}

#[test]
fn unquote_type_basic() {
    use crate::ast_walk::LazyWalkReses;
    let pos = true;
    let _neg = false;

    let expr_type = crate::core_type_forms::get__primitive_type(n("Expr"));
    let _pat_type = crate::core_type_forms::get__primitive_type(n("Pat"));

    let env = assoc_n!(
        "n" => ast!({"Type" "Nat" :}),
        "en" => ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Nat" :}]})
    );

    let qenv = assoc_n!(
        "qn" => ast!({"Type" "Nat" :})
    );

    fn synth_type_two_phased_lq(
        expr: &Ast,
        env: Assoc<Name, Ast>,
        qenv: Assoc<Name, Ast>,
    ) -> crate::ty::TypeResult {
        let parts = LazyWalkReses::new_wrapper(env);
        let qparts = parts.quote_more(None).with_environment(qenv);

        crate::ast_walk::walk::<crate::ty::SynthTy>(expr, &qparts)
    }

    // ,[Expr | en ],
    let res = synth_type_two_phased_lq(
        &ast!({unquote_form(n("Expr"), pos, 1) ;
            "nt" => (vr "Expr"), "body" => (-- 1 (vr "en"))}),
        env,
        qenv,
    );
    assert_eq!(res, Ok(ast!({"Type" "Nat" :})));
}

#[test]
fn use_dotdotdot() {
    use crate::runtime::eval::Value;

    let pos = true;
    let expr_type = crate::core_type_forms::get__primitive_type(n("Expr"));

    let env = assoc_n!(
        "n" => ast!({"Type" "Nat" :}),
        "ns" => ast!({"Type" "tuple" :
            "component" =>
                [{"Type" "type_apply" :
                     "type_rator" => (,expr_type.clone()),
                     "arg" => [{"Type" "Nat" :}]},
                 {"Type" "type_apply" :
                     "type_rator" => (,expr_type.clone()),
                     "arg" => [{"Type" "Nat" :}]}]})

    );

    let qenv = assoc_n!(
        "qn" => ast!({"Type" "Nat" :}),
        "five" => ast!({"Type" "Int" :})
    );

    let eval_env = assoc_n!(
        "n" => val!(i 5),
        "en" => val!(ast (vr "qn")),
        "ns" => val!(seq (ast (vr "qn")) (ast (vr "qnn")))
    );

    let eval_qenv = assoc_n!(
        "qn" => val!(i 6),
        "qnn" => val!(i 7)
    );

    let expr_type = crate::core_type_forms::get__primitive_type(n("Expr"));

    fn synth_type_two_phased(
        expr: &Ast,
        env: Assoc<Name, Ast>,
        qenv: Assoc<Name, Ast>,
    ) -> crate::ty::TypeResult {
        crate::ast_walk::walk::<crate::ty::SynthTy>(
            expr,
            &crate::ast_walk::LazyWalkReses::new_mq_wrapper(env, vec![qenv]),
        )
    }

    fn eval_two_phased(
        expr: &Ast,
        eval_env: Assoc<Name, Value>,
        eval_qenv: Assoc<Name, Value>,
    ) -> Result<Value, ()> {
        crate::ast_walk::walk::<Eval>(
            expr,
            &crate::ast_walk::LazyWalkReses::new_mq_wrapper(eval_env, vec![eval_qenv]),
        )
    }

    // TODO: it would be much more natural if you could put `...[ ]...` around the whole p-and-arm.
    // '[Expr | match qn { x =>  ...[ns >> ,[Expr | ns],]... }]'
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true
                {"Expr" "match" :
                    "scrutinee" => (vr "qn"),
                    "p" => [@"c" "x"],
                    "arm" => [@"c" (import ["p" = "scrutinee"]
                        {dotdotdot_form(n("Expr")) ;
                            "driver" => [(-- 1 (vr "ns"))],
                            "body" =>
                                {unquote_form(n("Expr"), pos, 1) ;
                                 "body" => (-- 1 (vr "ns"))}})]})}),
            env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Nat" :}]}))
    );
    without_freshening! {
        assert_eq!(eval_two_phased(
                &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true
                    {"Expr" "match" :
                        "scrutinee" => (vr "qn"),
                        "p" => [@"c" "x"],
                        "arm" => [@"c" (import ["p" = "scrutinee"]
                            {dotdotdot_form(n("Expr")) ;
                                "driver" => [(-- 1 (vr "ns"))],
                                "body" =>
                                    {unquote_form(n("Expr"), pos, 1) ;
                                     "body" => (-- 1 (vr "ns"))}})]})}),
                eval_env.clone(), eval_qenv.clone()),
            Ok(val!(ast {"Expr" "match" :
                        "scrutinee" => (vr "qn"),
                        "p" => [@"c" "x", "x"],
                        "arm" => [@"c" (import ["p" = "scrutinee"] (vr "qn")),
                                    (import ["p" = "scrutinee"] (vr "qnn"))]})));
    }

    let type_type = crate::core_type_forms::get__primitive_type(n("Type"));

    let ddd_env = assoc_n!(
        "names" =>  ast!({"Type" "tuple" :
            "component" => [{"Type" "Ident" : }, {"Type" "Ident" :}]}),
        "types" => ast!({"Type" "tuple" :
            "component" =>
                [{"Type" "type_apply" :
                     "type_rator" => (,type_type.clone()),
                     "arg" => [{"Type" "Float" :}]},
                 {"Type" "type_apply" :
                     "type_rator" => (,type_type.clone()),
                     "arg" => [{"Type" "Nat" :}]}]}),
        "args" => ast!({"Type" "tuple" :
            "component" =>
                [{"Type" "type_apply" :
                     "type_rator" => (,expr_type.clone()),
                     "arg" => [{"Type" "Float" :}]},
                 {"Type" "type_apply" :
                     "type_rator" => (,expr_type.clone()),
                     "arg" => [{"Type" "Nat" :}]}]})
    );

    // Invoke a function on some number of arguments, not necessarily with the same type:
    // '[Expr | (.[ ...[names >> ,[Ident | names],]... : ...[types >> ,[Type | types],]...
    //              . five].
    //           ...[args >> ,[Expr | args],]...)]'
    assert_eq!(
        synth_type_two_phased(
            &ast!({quote(pos) ; "nt" => (vr "Expr"), "body" => (++ true
            {"Expr" "apply" :
                "rator" => {"Expr" "lambda" :
                    "param" => [@"p" {dotdotdot_form(n("Ident")) ;
                        "driver" => [(-- 1 (vr "names"))],
                        "body" => {unquote_form(n("Ident"), pos, 1);
                            "body" => (-- 1 (vr "names"))}
                    }],
                    "p_t" => [@"p" {dotdotdot_form(n("Type")) ;
                        "driver" => [(-- 1 (vr "types"))],
                        "body" => {unquote_form(n("Type"), pos, 1);
                            "body" => (-- 1 (vr "types"))}
                    }],
                    "body" => (vr "five")
                },
                "rand" => [{dotdotdot_form(n("Expr")) ;
                    "driver" => [(-- 1 (vr "args"))],
                    "body" => {unquote_form(n("Expr"), pos, 1);
                        "body" => (-- 1 (vr "args"))}}]
            })}),
            ddd_env.clone(),
            qenv.clone()
        ),
        Ok(ast!({"Type" "type_apply" :
            "type_rator" => (,expr_type.clone()), "arg" => [{"Type" "Int" :}]}))
    );

    let ddd_abs_env = assoc_n!(
        "T" => uty!(T),
        "vals" => uty!({tuple : [{dotdotdot_type : [T] {type_apply : (prim Expr) [T]}}]}),
        "ops" => uty!({tuple : [{dotdotdot_type : [T]
            {type_apply : (prim Expr) [{fn : [T] {Int :}}]}}]}));

    assert_eq!(
        synth_type_two_phased(
            &ast!({"Expr" "quote_expr" :
                "nt" => (vr "Expr"),
                "body" => (++ true (, u!({tuple_expr :
                    [{dotdotdot_form(n("Expr")) ; [(~ ops); (~ vals)]
                        {apply : {unquote_form(n("Expr"), pos, 1) ; (~) ops}
                            [{unquote_form(n("Expr"), pos, 1) ; (~) vals}]}}]})))
            }),
            ddd_abs_env.clone(),
            qenv.clone()
        ),
        Ok(uty!({type_apply : (prim Expr) [{tuple : [{Int :}]}]}))
    );
}

// TODO:
// '[Expr | ( ,[Expr | could_be_anything ], five)]'
#[test]
fn subtyping_under_negative_quote() {}
