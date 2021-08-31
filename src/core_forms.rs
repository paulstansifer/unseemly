// This virtual machine kills cyber-fascists.

use crate::{
    ast::*,
    ast_walk::{LazyWalkReses, WalkRule::*},
    core_type_forms::*,
    form::Form,
    grammar::{
        FormPat::{self, *},
        SynEnv,
    },
    name::*,
    runtime::eval::*,
    ty::*,
    util::assoc::Assoc,
};
use std::rc::Rc; // type forms are kinda bulky

// Core forms!
//
// This is the definition of Unseemly, the bizarre boiled-down programming language.
//
// Unseemly programs have expressions and types (and probably kinds, too).

/// Remove an `ExtendEnv` without respecting its binding behavior.
/// This is safe if directly inside a `Node` that was just freshened.
/// (TODO: think about what "just" means here. It's super-subtle!)
pub fn strip_ee(a: &Ast) -> &Ast {
    match a.c() {
        ExtendEnv(body, _) => (&*body),
        ExtendEnvPhaseless(body, _) => (&*body),
        _ => icp!("Not an EE"),
    }
}

pub fn strip_ql(a: &Ast) -> &Ast {
    match a.c() {
        QuoteLess(body, _) => &*body,
        _ => icp!("Not an unquote"),
    }
}

// lambda ==> [param: Atom  p_t: Type]*  body: Expr
fn type_lambda(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    let lambda_type: Ast = ast!({ find_type("fn") ;
         "param" => [* part_types =>("param") part_types : (, part_types.get_res(n("p_t"))? )],
         "ret" => (, part_types.get_res(n("body"))? )});
    Ok(lambda_type)
}
fn eval_lambda(part_values: LazyWalkReses<Eval>) -> Result<Value, ()> {
    Ok(Function(Rc::new(Closure {
        body: strip_ee(part_values.get_term_ref(n("body"))).clone(),
        params: part_values.get_rep_term(n("param")).iter().map(Ast::to_name).collect(),
        env: part_values.env,
    })))
}

// apply ==>  rator: Expr  [rand: Expr]*
fn type_apply(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    use crate::walk_mode::WalkMode;
    let return_type = crate::ty_compare::Subtype::underspecified(n("<return_type>"));

    // The `rator` must be a function that takes the `rand`s as arguments:
    let _ = crate::ty_compare::is_subtype(
        &ast!({ "Type" "fn" :
            "param" => (,seq part_types.get_rep_res(n("rand"))? ),
            "ret" => (, return_type.clone() )}),
        &part_types.get_res(n("rator"))?,
        &part_types,
    )
    .map_err(|e| crate::util::err::sp(e, part_types.this_ast.clone()))?;

    // TODO: write a test that exercises this (it's used in the prelude)
    // What return type made that work?
    crate::ty_compare::unification.with(|unif| {
        let res = crate::ty_compare::resolve(
            crate::ast_walk::Clo { it: return_type, env: part_types.env.clone() },
            &unif.borrow(),
        );

        // Canonicalize the type in its environment:
        let res = crate::ty_compare::canonicalize(&res.it, res.env);
        res.map_err(|e| crate::util::err::sp(e, part_types.this_ast.clone()))
    })
}
fn eval_apply(part_values: LazyWalkReses<Eval>) -> Result<Value, ()> {
    match part_values.get_res(n("rator"))? {
        Function(clos) => {
            let mut new_env = clos.env.clone();
            for (p, v) in clos.params.iter().zip(part_values.get_rep_res(n("rand"))?) {
                new_env = new_env.set(*p, v);
            }

            // TODO: this seems wrong; it discards other phase information.
            // But would it be correct to have closures capture at all phases?
            crate::runtime::eval::eval(&clos.body, new_env)
        }
        BuiltInFunction(crate::runtime::eval::BIF(f)) => Ok(f(part_values.get_rep_res(n("rand"))?)),
        other => {
            icp!("[type error] invoked {:#?} as if it were a function", other)
        }
    }
}

// match ==> scrutinee: Expr  [p: Pat  arm: Expr]*
fn type_match(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    let mut res: Option<Ast> = None;

    for arm_part_types in part_types.march_parts(&[n("arm"), n("p")]) {
        // We don't need to manually typecheck that the arm patterns match the scrutinee;
        //  the import handles that for us.

        let arm_res = arm_part_types.get_res(n("arm"))?;

        match res {
            None => res = Some(arm_res),
            Some(ref old_res) => {
                ty_exp!(old_res, &arm_res, arm_part_types.get_term(n("arm")));
            }
        }
    }
    match res {
        None => {
            // TODO #2: this isn't anywhere near exhaustive
            ty_err!(NonExhaustiveMatch(part_types.get_res(n("scrutinee")).unwrap())
                at ast!((trivial)) /* TODO */)
        }
        Some(ty_res) => Ok(ty_res),
    }
}
fn eval_match(part_values: LazyWalkReses<Eval>) -> Result<Value, ()> {
    for arm_values in part_values.march_all(&[n("arm"), n("p")]) {
        // TODO: don't we need to set a context?
        match arm_values.get_res(n("arm")) {
            Ok(res) => {
                return Ok(res);
            }
            Err(()) => { /* try the next one */ }
        }
    }
    panic!("No arms matched! TODO #2");
}

// enum_expr ==> name: Atom [component: Expr]*
fn type_enum_expr(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    let res: Ast = part_types.get_res(n("t"))?;
    expect_ty_node!( (res ; find_type("enum") ; &part_types.this_ast)
        enum_type_parts;
        {
            for enum_type_part in enum_type_parts.march_all(&[n("name"), n("component")]) {
                if &part_types.get_term(n("name")) != enum_type_part.get_leaf_or_panic(&n("name")) {
                    continue; // not the right arm
                }

                let component_types : Vec<&Ast> =
                    enum_type_part.get_rep_leaf_or_panic(n("component"));

                // TODO: check that they're the same length!

                for (t, expected_t) in part_types.get_rep_res(n("component"))?
                        .iter().zip(component_types) {
                    ty_exp!(t, expected_t, part_types.this_ast);
                }
                return Ok(res);
            }

            ty_err!(NonexistentEnumArm(part_types.get_term(n("name")).to_name(), res)
                    at part_types.this_ast);
        }
    )
}
fn eval_enum_expr(part_values: LazyWalkReses<Eval>) -> Result<Value, ()> {
    Ok(Enum(part_values.get_term(n("name")).to_name(), part_values.get_rep_res(n("component"))?))
}

// struct_expr ==> [component_name: Atom  component: Expr]*
fn type_struct_expr(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    Ok(ast!({ find_type("struct") ;
        "component_name" => (@"c" ,seq part_types.get_rep_term(n("component_name"))),
        "component" => (@"c" ,seq part_types.get_rep_res(n("component"))?)
    }))
}
fn eval_struct_expr(part_values: LazyWalkReses<Eval>) -> Result<Value, ()> {
    let mut res = Assoc::new();

    for component_parts in part_values.march_parts(&[n("component"), n("component_name")]) {
        res = res.set(
            component_parts.get_term(n("component_name")).to_name(),
            component_parts.get_res(n("component"))?,
        );
    }

    Ok(Struct(res))
}

// tuple_expr ==> [component: Expr]*
fn type_tuple_expr(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    Ok(uty!({tuple : [, part_types.get_rep_res(n("component"))? ]}))
}
fn eval_tuple_expr(part_values: LazyWalkReses<Eval>) -> Result<Value, ()> {
    Ok(crate::runtime::eval::Value::Sequence(
        part_values.get_rep_res(n("component"))?.into_iter().map(Rc::new).collect(),
    ))
}

// unfold ==> body: Expr
fn type_unfold(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    // TODO: this "evaluates" types twice; once in `get_res` and once in `synth_type`
    // It shouldn't be necessary, and it's probably quadratic.
    // Maybe this points to a weakness in the LiteralLike approach to traversing types?
    let mu_typed = part_types.get_res(n("body"))?;

    // Pull off the `mu` (and the `ExtendEnv` that it carries):
    // (This is sound because `mu`'s param must already be in the environment.)
    expect_ty_node!( (mu_typed ; find_type("mu_type") ;  &part_types.this_ast)
    mu_parts;
    {
        // This acts like the `mu` was never there (and hiding the binding)
        if let ExtendEnv(body, _) = mu_parts.get_leaf_or_panic(&n("body")).c() {
            synth_type(body, part_types.env)
        } else { icp!("no protection to remove!"); }
    })
}

// fold ==> body: Expr  t: Type
fn type_fold(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    let goal_type = part_types.get_res(n("t"))?;
    // TODO: I can't figure out how to pull this out into a function
    //  to invoke both here and above, since `mu_type_0` needs cloning...
    let folded_goal = expect_ty_node!(
        (goal_type.clone() ; find_type("mu_type") ; &part_types.this_ast)
    mu_parts;
    {
        // This acts like the `mu` was never there (and hiding the binding)
        if let ExtendEnv(ref body, _) = mu_parts.get_leaf_or_panic(&n("body")).c() {
            synth_type(body, part_types.env.clone())?
        } else {
            icp!("no protection to remove!");
        }
    });

    ty_exp!(&part_types.get_res(n("body"))?, &folded_goal, part_types.this_ast);
    Ok(goal_type)
}

// forall_expr ==> [param: Atom]*  body: Expr
fn type__forall_expr(part_types: LazyWalkReses<SynthTy>) -> TypeResult {
    Ok(ast!({"Type" "forall_type" :
        "param" => (,seq part_types.get_rep_term(n("param"))),
        "body" => (import [* [forall "param"]] (, part_types.get_res(n("body"))?))
    }))
}

// TODO: pull out all the other form implementations into freestanding functions.

/// This is the Unseemly language.
pub fn make_core_syn_env() -> SynEnv {
    color_backtrace::install(); // HACK: this is around the first thing that happens in any test.

    let ctf: SynEnv = get_core_types();
    let cmf: SynEnv = crate::core_macro_forms::make_core_macro_forms();

    // Unseemly expressions
    let main_expr_forms = forms_to_form_pat![
        typed_form!("lambda",
            (delim ".[", "[", [ // TODO: add comma separators to the syntax!
                            (star [(named "param", atom), (lit ":"),
                                    (named "p_t", (call "Type"))]), (lit "."),
                (named "body",
                    (import [* ["param" : "p_t"]], (call "Expr")))]),
            cust_rc_box!(type_lambda),
            cust_rc_box!(eval_lambda)),
        typed_form!("apply", /* function application*/
            (delim "(", "(", [(named "rator", (call "Expr")),
                (star (named "rand", (call "Expr")))]),
            cust_rc_box!(type_apply),
            cust_rc_box!(eval_apply)),
        typed_form!("match",
            [(lit "match"), (named "scrutinee", (call "Expr")),
             (delim "{", "{",
                 (plus [(named "p", (call "Pat")), (lit "=>"),
                        (named "arm", (import ["p" = "scrutinee"], (call "Expr")))]))],
            cust_rc_box!(type_match),
            cust_rc_box!(eval_match)
        ),
        // Note that we inconveniently require the user to specify the type.
        // "real" languages infer the type from the (required-to-be-unique)
        // component name.
        typed_form!("enum_expr",
            [(delim "+[", "[", [(named "name", atom),
                                (star (named "component", (call "Expr")))]),
            (lit ":"), (named "t", (call "Type"))],
            cust_rc_box!(type_enum_expr),
            cust_rc_box!(eval_enum_expr)),
        typed_form!("struct_expr",
            (delim "*[", "[",
                (star [(named "component_name", atom), (lit ":"),
                    (named "component", (call "Expr"))])),
            cust_rc_box!(type_struct_expr),
            cust_rc_box!(eval_struct_expr)),
        typed_form!("tuple_expr",
            (delim "**[", "[", (star (named "component", (call "Expr")))),
            cust_rc_box!(type_tuple_expr),
            cust_rc_box!(eval_tuple_expr)
        ),
        // e.g.
        // let_type
        //   pair = mu lhs rhs. {l: lhs, r: rhs}
        //   point = pair<int, int>
        // in ...
        typed_form!("let_type",
            [(lit "let_type"),
             (named "type_kind_stx", (anyways "*")),
             (star [(named "type_name", atom),
                    (lit "="),
                    (named "type_def", (import [* ["type_name" = "type_def"]], (call "Type")))]),
             (lit "in"),
             (named "body", (import [* ["type_name" = "type_def"]], (call "Expr")))],
            Body(n("body")),
            // HACK: like `Body(n("body"))`, but ignoring the binding, since it's type-level.
            // This feels like it ought to be better-handled by `beta`, or maybe a kind system.
            cust_rc_box!( move | let_type_parts | {
                crate::ast_walk::walk::<Eval>(
                    strip_ee(&let_type_parts.get_term(n("body"))), &let_type_parts)
            })),
        // e.g. where List = ∀ X. μ List. enum { Nil(), Cons(X, List<X>) }
        // .[x : List<X>  . match (unfold x) ... ].
        // (unfold is needed because `match` wants an `enum`, not a `μ`)
        // Exposes the inside of a μ type by performing one level of substitution.
        typed_form!("unfold",
            [(lit "unfold"), (named "body", (call "Expr"))],
            cust_rc_box!(type_unfold),
            Body(n("body"))),
        // e.g. where List = ∀ X. μ List. enum { Nil (), Cons (X, List<X>) }
        // (.[x : List<X> . ...]. (fold +[Nil]+) ) : List<X>
        typed_form!("fold",
            [(lit "fold"), (named "body", (call "Expr")), (lit ":"), (named "t", (call "Type"))],
            cust_rc_box!(type_fold),
            Body(n("body"))),
        typed_form!("forall_expr",
            [(lit "forall"), (star (named "param", atom)), (lit "."),
             (named "body", (import [* [forall "param"]], (call "Expr")))],
            cust_rc_box!(type__forall_expr),
            Body(n("body"))),
        crate::core_qq_forms::quote(/* positive= */ true),
        crate::core_macro_forms::extend_syntax()
    ];

    let main_pat_forms = forms_to_form_pat_export![
        negative_typed_form!("enum_pat",
            (delim "+[", "[", [(named "name", atom),
                               (star (named "component", (call "Pat")))]),
            /* (Negatively) Typecheck: */
            cust_rc_box!( move | part_types |
                expect_ty_node!( (part_types.context_elt() ; find_type("enum") ;
                                      &part_types.this_ast)
                    enum_type_parts;
                    {
                        let arm_name = &part_types.get_term(n("name"));

                        for enum_type_part in enum_type_parts
                                .march_all(&[n("name"), n("component")]) {
                            if arm_name != enum_type_part.get_leaf_or_panic(&n("name")) {
                                continue; // not the right arm
                            }

                            let component_types : Vec<Ast> =
                                enum_type_part.get_rep_leaf_or_panic(n("component")).into_iter().cloned().collect();

                            let mut res = Assoc::new();
                            for sub_res in &part_types
                                    .get_rep_res_with(n("component"), component_types)? {
                                res = res.set_assoc(sub_res);
                            }

                            return Ok(res);
                        }
                        ty_err!(NonexistentEnumArm(arm_name.to_name(),
                            ast!((trivial))) /* TODO `LazyWalkReses` needs more information */
                            at arm_name.clone())
                }
            )),
            /* (Negatively) Evaluate: */
            cust_rc_box!( move | part_values | {
                match *part_values.context_elt() /* : Value */ {
                    Enum(ref name, ref elts) => {
                        // "Try another branch"
                        if name != &part_values.get_term(n("name")).to_name() {
                            return Err(());
                        }

                        let mut res = Assoc::new();
                        for sub_res in &part_values.get_rep_res_with(n("component"),
                                                                     elts.clone())? {
                            res = res.set_assoc(sub_res);
                        }

                        Ok(res)
                    }
                    _ => icp!("[type error] non-enum")
                }
            })) => [* ["component"]],
        negative_typed_form!("struct_pat",
            [(delim "*[", "[",
                 (star [(named "component_name", atom), (lit ":"),
                        (named "component", (call "Pat"))]))],
            /* (Negatively) typesynth: */
            cust_rc_box!( move | part_types |
                expect_ty_node!( (part_types.context_elt() ; find_type("struct") ;
                                      &part_types.this_ast)
                    struct_type_parts;
                    {
                        let mut res = Assoc::new();
                        for component_ctx in part_types
                                .march_parts(&[n("component"), n("component_name")]) {
                            let mut component_found = false;
                            for struct_type_part
                                    in struct_type_parts
                                        .march_all(&[n("component"), n("component_name")]) {
                                if &component_ctx.get_term(n("component_name"))
                                    != struct_type_part.get_leaf_or_panic(&n("component_name")) {
                                    continue;
                                }
                                component_found = true;

                                let component_type =
                                    struct_type_part.get_leaf_or_panic(&n("component")).clone();
                                res = res.set_assoc(
                                    &component_ctx.with_context(component_type)
                                        .get_res(n("component"))?);
                                break;
                            }
                            if !component_found {
                                ty_err!(NonexistentStructField(
                                        component_ctx.get_term(n("component_name")).to_name(),
                                        part_types.context_elt().clone())
                                    at part_types.get_rep_term(n("component"))[0].clone());
                            }
                        }
                        Ok(res)
                    })),
            cust_rc_box!( move | part_values | {
                match *part_values.context_elt() {
                    Struct(ref contents) => {
                        let mut res = Assoc::new();

                        for component_ctx in part_values
                                .march_parts(&[n("component"), n("component_name")]) {
                            res = res.set_assoc(
                                &component_ctx
                                    .with_context(contents.find_or_panic(
                                        &component_ctx.get_term(n("component_name")).to_name())
                                            .clone())
                                    .get_res(n("component"))?);
                        }

                        Ok(res)
                    }
                    _ => icp!("[type error] non-struct")
                }
            }))  => [* ["component"]],
        negative_typed_form!("tuple_pat",
            (delim "**[", "[", (star (named "component", (call "Pat")))),
            cust_rc_box!( move |part_types|
                expect_ty_node!( (part_types.context_elt() ; find_type("tuple") ;
                                    &part_types.this_ast)
                    ctxt_type_parts;
                    {
                        let component_types : Vec<Ast> =
                            ctxt_type_parts.get_rep_leaf_or_panic(n("component"))
                                .into_iter().cloned().collect();

                        let mut res = Assoc::new();
                        for sub_res in &part_types
                                .get_rep_res_with(n("component"), component_types)? {
                            res = res.set_assoc(sub_res);
                        }

                        return Ok(res);

                    }
            )),
            cust_rc_box!( move |part_values| {
                match *part_values.context_elt() {
                    Sequence(ref sub_vals) => {
                        let sub_vals: Vec<Value> = sub_vals.iter()
                            .map(|rcv: &Rc<Value>| (**rcv).clone()).collect();
                        let mut res = Assoc::new();
                        for sub_res in &part_values.get_rep_res_with(n("component"), sub_vals)? {
                            res = res.set_assoc(sub_res);
                        }

                        Ok(res)
                    }
                    _ =>  icp!("[type error] non-tuple")
                }
            })

        ) => [* ["component"]],
            // TODO #16: We need a pattern for destructuring tuples.
            crate::core_qq_forms::quote(/*positive=*/false) => ["body"]];

    let reserved_names = vec![
        n("forall"),
        n("mu_type"),
        n("Int"),
        n("Ident"),
        n("Float"),
        n("match"),
        n("enum"),
        n("struct"),
        n("fold"),
        n("unfold"),
        n("extend_syntax"),
        n("in"),
        n("import"),
        n("capture_language"),
    ];

    syn_env!(
        "Pat" => (biased (,main_pat_forms), (call "DefaultAtom")),
        "Expr" => (biased
            (alt (, main_expr_forms),
                    (, crate::core_extra_forms::make_core_extra_forms())),
            (call "DefaultReference")),
        "Ident" => (call "DefaultAtom"),
        "AtomNotInPat" => (call "DefaultAtom"),
        "DefaultReference" => (varref_call "DefaultAtom"),
        "DefaultSeparator" => (scan r"(\s*)"),
        "DefaultAtom" => (common (reserved_by_name_vec (call "DefaultWord"), reserved_names)),
        "DefaultWord" => (common (pick [(call "DefaultSeparator"),
            (named "name", (scan_cat r"(\p{Letter}(?:\p{Letter}|\p{Number}|[_?])*)",
                                     "variable"))],
                "name")),
        // TODO: come up with more normal tokenization rules.
        // HACK: it's really confusing to weld semicolon and colon onto brackets, so exempt them.
        "OpenDelim" =>
            (common (pick [(call "DefaultSeparator"),
                (named "tok",
                    (scan_cat r"([^\[\]\(\)\{\}\s;:]*[\[\(\{])", "paren.lparen"))], "tok")),
        "CloseDelim" =>
            (common (pick [(call "DefaultSeparator"),
                (named "tok",
                    (scan_cat r"([\]\)\}][^\[\]\(\)\{\}\s;:]*)", "paren.rparen"))], "tok")),
        "DefaultToken" =>
           (common (pick [(call "DefaultSeparator"),
                   (named "tok",
                       (scan r"([^\[\]\(\)\{\}\s]+)"))],
            "tok"))
    )
    .set_assoc(&ctf) // throw in types!
    .set_assoc(&cmf) // throw in the types and macros!
}

/// Mostly for testing purposes, this looks up forms by name.
/// In the "real world", programmers look up forms by syntax, using a parser.
pub fn find_form(se: &SynEnv, nt: &str, form_name: &str) -> Rc<Form> {
    fn find_form_rec(f: &FormPat, form_name: &str) -> Option<Rc<Form>> {
        match *f {
            Scope(ref f, _) => {
                if f.name.is(form_name) {
                    Some(f.clone())
                } else {
                    None
                }
            }
            Alt(ref vf) => {
                for f in vf {
                    let res = find_form_rec(f, form_name);
                    if res.is_some() {
                        return res;
                    }
                }
                None
            }
            Biased(ref lhs, ref rhs) => {
                let l_res = find_form_rec(lhs, form_name);
                if l_res.is_some() {
                    l_res
                } else {
                    find_form_rec(rhs, form_name)
                }
            }
            _ => None,
        }
    }
    let pat = se.find_or_panic(&n(nt));

    find_form_rec(pat, form_name)
        .unwrap_or_else(|| icp!("{:#?} not found in {:#?}", form_name, pat))
}

// Inserts a new form into a grammar in the "sensible" place
//  (underneath any number of `Biased`s, as a new arm of an `Alt`).
// Macros will usually want to do this to extend an existing NT.
pub fn insert_form_pat(se: &SynEnv, nt: Name, f: &FormPat) -> SynEnv {
    let nt_form: Rc<FormPat> = se.find_or_panic(&nt).clone();

    se.set(nt, Rc::new(add_form_at_the_alt(nt_form, f).unwrap()))
}

pub fn add_form_at_the_alt(outer: Rc<FormPat>, inner: &FormPat) -> Option<FormPat> {
    match *outer {
        Biased(ref l, ref r) => {
            if let Some(new_l) = add_form_at_the_alt(l.clone(), inner) {
                return Some(Biased(Rc::new(new_l), r.clone()));
            }
            if let Some(new_r) = add_form_at_the_alt(r.clone(), inner) {
                return Some(Biased(l.clone(), Rc::new(new_r)));
            }
            return None;
        }
        Alt(ref subs) => {
            let mut my_subs: Vec<Rc<FormPat>> = subs.clone();
            my_subs.push(Rc::new(inner.clone()));
            return Some(Alt(my_subs));
        }
        _ => None,
    }
}

thread_local! {
    pub static core_forms: SynEnv = make_core_syn_env();
}

pub fn outermost_form() -> FormPat {
    // `(call "Expr")`, except allowing whitespace (etc) at the end of a file:
    form_pat!((pick [(named "program", (call "Expr")), (call "DefaultSeparator")], "program"))
}

pub fn outermost__parse_context() -> crate::earley::ParseContext {
    crate::earley::ParseContext {
        grammar: get_core_forms(),
        type_ctxt: crate::ast_walk::LazyWalkReses::new_wrapper(
            crate::runtime::core_values::core_types(),
        ),
        eval_ctxt: crate::ast_walk::LazyWalkReses::new_wrapper(
            crate::runtime::core_values::core_values(),
        ),
    }
}

pub fn find(nt: &str, name: &str) -> Rc<Form> { core_forms.with(|cf| find_form(cf, nt, name)) }

// Deprecated; use `::core_forms::find` instead (keep it qualified!)
pub fn find_core_form(nt: &str, name: &str) -> Rc<Form> { find(nt, name) }

pub fn get_core_forms() -> SynEnv { core_forms.with(|cf| cf.clone()) }

#[test]
fn form_grammar() {
    assert_eq!(
        crate::grammar::parse(
            &form_pat!((call "Type")),
            outermost__parse_context(),
            tokens_s!("[" "Ident" "->" "Ident" "]"),
        ),
        Ok(ast!({ find("Type", "fn");
                   ["ret" => {find("Type", "Ident") ; []},
                    "param" => [{find("Type", "Ident") ; []}]]}))
    );
}

#[test]
fn form_expect_node() {
    let ast = u!({apply : f [x]});
    let _: Result<(), ()> = expect_node!(
    ( ast ; find_core_form("Expr", "apply")) env;
    {
        assert_eq!(env.get_leaf_or_panic(&n("rator")), &ast!((vr "f")));
        assert_eq!(env.get_rep_leaf_or_panic(n("rand")), vec![&ast!((vr "x"))]);
        Ok(())
    });
}

#[test]
fn form_type() {
    let simple_ty_env = assoc_n!(
        "x" => uty!({Int :}),
        "n" => uty!({Nat :}));

    assert_eq!(synth_type(&ast!( (vr "x") ), simple_ty_env.clone()), Ok(uty!({Int :})));

    assert_eq!(
        synth_type(&u!({lambda : [y {Type Nat :}] x}), simple_ty_env.clone()),
        Ok(uty!({fn : [{Nat :}] {Int :}}))
    );
}

#[test]
fn type_apply_with_subtype() {
    // Application can perform subtyping

    let nat_ty = ast!({ "Type" "Nat" : });

    let ty_env = assoc_n!(
        "N" => uty!({Nat :}),
        "nat_to_nat" => uty!({fn : [{Nat :}] {Nat :}}),
        "forall_t_t_to_t" => uty!({forall_type : [T] {fn : [T] T}}));

    assert_eq!(synth_type(&u!({apply : nat_to_nat [N]}), ty_env.clone()), Ok(nat_ty.clone()));

    assert_eq!(synth_type(&u!({apply : forall_t_t_to_t [N]}), ty_env.clone()), Ok(nat_ty.clone()));
}

#[test]
fn form_eval() {
    use num::bigint::ToBigInt;

    let simple_env = assoc_n!("x" => val!(i 18),
                              "w" => val!(i 99),
                              "b" => val!(b false));

    assert_eq!(eval(&ast!((vr "x")), simple_env.clone()), Ok(Int(18.to_bigint().unwrap())));

    // (λy.w) x
    assert_eq!(
        eval(&u!({apply : {lambda : [y {Type Int :}] w} [x]}), simple_env.clone()),
        Ok(Int(99.to_bigint().unwrap()))
    );

    // (λy.y) x
    assert_eq!(
        eval(&u!({apply : {lambda : [y {Type Int :}] y} [x]}), simple_env.clone()),
        Ok(Int(18.to_bigint().unwrap()))
    );
}

#[test]
fn alg_type() {
    let mt_ty_env = Assoc::new();
    let simple_ty_env = assoc_n!(
        "x" => uty!({Type Int :}), "n" => uty!({Type Nat :}), "f" => uty!({Type Float :}));

    let my_enum = ast!({ "Type" "enum" :
        "name" => [@"c" "Adams", "Jefferson", "Burr"],
        "component" => [@"c" [{"Type" "Int":}],
                             [{"Type" "Int":}, {"Type" "Nat":}],
                             [{"Type" "Float" :}, {"Type" "Float" :}]]
    });

    // Typecheck enum pattern
    assert_eq!(
        neg_synth_type(
            &u!({Pat enum_pat : Jefferson [(at abc) ; (at def)]}),
            mt_ty_env.set(negative_ret_val(), my_enum.clone())
        ),
        Ok(Assoc::new().set(n("abc"), ast!({"Type" "Int":})).set(n("def"), ast!({"Type" "Nat":})))
    );

    // Typecheck enum expression
    assert_eq!(
        synth_type(&u!({enum_expr : Jefferson [x ; n] (, my_enum.clone())}), simple_ty_env.clone()),
        Ok(my_enum.clone())
    );

    let my_struct = ast!({ "Type" "struct" :
        "component_name" => [@"c" "x", "y"],
        "component" => [@"c" {"Type" "Int":}, {"Type" "Float" :}]
    });

    // Typecheck struct pattern
    assert_eq!(
        neg_synth_type(
            &ast!(
            { "Pat" "struct_pat" :
                "component_name" => [@"c" "y", "x"],
                "component" => [@"c" "yy", "xx"]
            }),
            mt_ty_env.set(negative_ret_val(), my_struct.clone())
        ),
        Ok(assoc_n!("yy" => ast!({"Type" "Float" :}), "xx" => ast!({"Type" "Int":})))
    );

    // Typecheck struct expression

    // TODO: currently {x: integer, y: float} ≠ {y: float, x: integer}
    // Implement proper type equality!
    assert_eq!(
        synth_type(
            &ast!(
            { "Expr" "struct_expr" :
                "component_name" => [@"c" "x", "y"],
                "component" => [@"c" (vr "x"), (vr "f")]
            }),
            simple_ty_env.clone()
        ),
        Ok(my_struct)
    );

    // Typecheck tuple expression

    assert_eq!(
        synth_type(&u!({ tuple_expr: [x; f] }), simple_ty_env.clone()),
        Ok(uty!({tuple : [{Int :}; {Float :}]}))
    );

    // Simple match...

    assert_eq!(
        synth_type(
            &u!({Expr match : f [(at my_new_name) my_new_name; (at unreachable) f]}),
            simple_ty_env.clone()
        ),
        Ok(ast!({"Type" "Float" :}))
    );

    assert_m!(
        synth_type(
            &u!({Expr match : n [(at my_new_name) my_new_name; (at unreachable) f]}),
            simple_ty_env.clone()
        ),
        ty_err_p!(Mismatch(_, _))
    );

    assert_m!(
        synth_type(
            &u!({Expr match : my_enum
                    [{Pat enum_pat => [* ["component"]] : Hamilton [(at ii)]} ii]}),
            simple_ty_env.set(n("my_enum"), my_enum.clone())
        ),
        ty_err_p!(NonexistentEnumArm(_, _)) // Never gonna be president...
    );

    assert_eq!(
        synth_type(
            &u!({Expr match : my_enum
                    [{Pat enum_pat => [* ["component"]] : Adams [(at ii)]} ii;
                     {Pat enum_pat => [* ["component"]] : Jefferson [(at ii) ; (at bb)]} ii;
                     {Pat enum_pat => [* ["component"]] : Burr [(at xx) ; (at yy)]} x]}),
            simple_ty_env.set(n("my_enum"), my_enum.clone())
        ),
        Ok(ast!({"Type" "Int":}))
    );

    assert_eq!(
        synth_type(
            &u!({match : my_tuple [{Pat tuple_pat => [* ["component"]] : [(at e1) ; (at e2)]} e1]}),
            simple_ty_env.set(n("my_tuple"), uty!({tuple : [{Int :} ; {Float :}] }))
        ),
        Ok(uty!({Int :}))
    )
}

#[test]
fn alg_eval() {
    let mt_env = Assoc::new();
    let simple_env = assoc_n!("x" => val!(i 18), "w" => val!(i 99), "b" => val!(b false));

    // Evaluate enum pattern
    assert_eq!(
        neg_eval(
            &u!({Pat enum_pat => [* ["component"]] : choice1 [(at abc); (at def)]}),
            mt_env.set(negative_ret_val(), val!(enum "choice1", (i 9006), (b true)))
        ),
        Ok(assoc_n!("abc" => val!(i 9006), "def" => val!(b true)))
    );

    assert_eq!(
        neg_eval(
            &u!({Pat enum_pat => [* ["component"]] : choice1 [(at abc); (at def)]}),
            mt_env.set(negative_ret_val(), val!(enum "choice0", (i 12321)))
        ),
        Err(())
    );

    // Evaluate enum expression

    let my_enum_t = u!({Type enum : [choice0 [{Int :}];
                                     choice1 [{Int :}; {Nat :}];
                                     choice2 [{Float :}; {Float :}]]});

    let choice1_e = u!({enum_expr : choice1 [x; b] (, my_enum_t.clone())});

    assert_eq!(eval(&choice1_e, simple_env.clone()), Ok(val!(enum "choice1", (i 18), (b false))));

    // Evaluate struct pattern

    assert_eq!(
        neg_eval(
            &u!({Pat struct_pat => [* ["component"]] : [x (at xx); y (at yy)]}),
            mt_env.set(negative_ret_val(), Struct(assoc_n!("x" => val!(i 0), "y" => val!(b true))))
        ),
        Ok(assoc_n!("xx" => val!(i 0), "yy" => val!(b true)))
    );

    // Evaluate match

    assert_eq!(
        eval(
            &u!({match : x [(at my_new_name) my_new_name; (at unreachable) x]}),
            simple_env.clone()
        ),
        Ok(val!(i 18))
    );

    assert_eq!(
        eval(
            &u!({match : (, choice1_e)
                    [{Pat enum_pat => [* ["component"]] : choice2 [(at xx) ; (at yy)]} yy;
                     {Pat enum_pat => [* ["component"]] : choice1 [(at ii) ; (at bb)]} bb;
                     {Pat enum_pat => [* ["component"]] : choice0 [(at ii)]} ii]}),
            simple_env.clone()
        ),
        Ok(val!(b false))
    );

    // Evaluate tuple expression

    assert_eq!(
        eval(&u!({ tuple_expr: [x; b] }), simple_env.clone()),
        Ok(val!(seq (i 18) (b false)))
    );

    assert_eq!(
        eval(
            &u!({match : my_tuple [{Pat tuple_pat => [* ["component"]] : [(at e1) ; (at e2)]} e1]}),
            simple_env.set(n("my_tuple"), val!(seq (i 8) (i 3)))
        ),
        Ok(val!(i 8))
    )
}

#[test]
fn recursive_types() {
    let int_list_ty = ast!( { "Type" "mu_type" :
            "param" => [(import [prot "param"] (vr "IntList"))],
            "body" => (import [* [prot "param"]] { "Type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [], [{"Type" "Int":}, (vr "IntList") ]]})});

    let ty_env = assoc_n!(
        "IntList" => int_list_ty.clone(),  // this is a type definition...
        "il_direct" => int_list_ty.clone()  // ...and this is a value with a type
        // TODO #3: ... distinguish between these kinds in the environment!

        // We should never have `vr`s in the environment unless "protected" by a μ.
        // TODO: enforce that:
        //"il_named" => ast!((vr "IntList"))
    );

    // `IntList` shouldn't substitute
    assert_eq!(synth_type(&ast!((vr "il_direct")), ty_env.clone()), Ok(int_list_ty.clone()));

    // I don't want these tests to depend on alpha-equivalence, so just disable freshening here.
    without_freshening! {
    // Test that unfolding a type produces one that's "twice as large", minus the outer mu
    assert_eq!(synth_type(
        &ast!({"Expr" "unfold" : "body" => (vr "il_direct")}), ty_env.clone()),
        Ok(ast!({ "Type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [], [{"Type" "Int":}, (, int_list_ty.clone()) ]]})));

    // folding an unfolded thing should give us back the same thing
    assert_eq!(synth_type(
        &ast!( { find_core_form("Expr", "fold") ;
            "body" => { find_core_form("Expr", "unfold") ;
                "body" => (vr "il_direct") },
            "t" => (, int_list_ty.clone() )}),
        ty_env.clone()),
        Ok(int_list_ty.clone()));

    // Unfold a type and then match it
    assert_eq!(synth_type(
        &ast!( { "Expr" "match" :
            "scrutinee" => { "Expr" "unfold" : "body" => (vr "il_direct") },
            "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                "name" => "Cons",
                "component" => ["car", "cdr"],
                "t" => (vr "IntList")
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "car"))]
        }),
        ty_env.clone()),
        Ok(ast!({"Type" "Int":})));

    // Unfold a type and then extract the part that should have the same type as the outer type
    assert_eq!(synth_type(
        &ast!( { "Expr" "match" :
            "scrutinee" => { "Expr" "unfold" : "body" => (vr "il_direct") },
            "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                "name" => "Cons",
                "component" => ["car", "cdr"],
                "t" => (vr "IntList")
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "cdr"))]
        }),
        ty_env.clone()),
        Ok(int_list_ty.clone())
    );
    };

    // Test that missing an unfold fails
    assert_m!(
        synth_type(
            &ast!( { "Expr" "match" :
                    "scrutinee" =>  (vr "il_direct") ,
                    "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                    "name" => "Cons",
                    "component" => ["car", "cdr"],
                    "t" => (vr "IntList")
                }],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "car"))]
            }),
            ty_env.clone()
        ),
        ty_err_p!(UnableToDestructure(_, name_enum)),
        name_enum == n("enum")
    );
}

#[test]
fn use__let_type() {
    // Basic usage:
    assert_eq!(
        synth_type(
            &ast!( { "Expr" "let_type" :
                "type_name" => [@"t" "T"],
                "type_def" => [@"t"  { "Type" "Nat" :}],
                "body" => (import [* ["type_name" = "type_def"]] { "Expr" "lambda" :
                    "param" => [@"p" "x"],
                    "p_t" => [@"p" (vr "T")],
                    "body" => (import [* ["param" : "p_t"]] (vr "x"))
                })
            }),
            Assoc::new()
        ),
        Ok(ast!( { "Type" "fn" : "param" => [ {"Type" "Nat" :}], "ret" => {"Type" "Nat" :}}))
    );

    // useless type, but self-referential:
    let trivial_mu_type = ast!( { "Type" "mu_type" : "param" => [(import [prot "param"] (vr "T"))],
                                  "body" => (import [* [prot "param"]] (vr "T")) });

    without_freshening! {
    // Recursive usage:
    assert_eq!(synth_type(&ast!( { "Expr" "let_type" :
            "type_name" => [@"t" "T"],
            "type_def" => [@"t"  (, trivial_mu_type.clone())],
            "body" => (import [* ["type_name" = "type_def"]] { "Expr" "lambda" :
                "param" => [@"p" "x"],
                "p_t" => [@"p" (vr "T")],
                // The unfold is a no-op, but it needs `T` to be defined:
                "body" => (import [* ["param" : "p_t"]] { "Expr" "unfold" : "body" => (vr "x") })
            })
        }), Assoc::new()),
    Ok(ast!( { "Type" "fn" :
        "param" => [(,trivial_mu_type.clone())], "ret" => (,trivial_mu_type.clone())})));
    }

    // Basic usage, evaluated:
    assert_m!(
        eval(
            &ast!( { "Expr" "let_type" :
                "type_name" => [@"t" "T"],
                "type_def" => [@"t" { "Type" "Nat" :}],
                "body" => (import [* ["type_name" = "type_def"]] { "Expr" "lambda" :
                    "param" => [@"p" "x"],
                    "p_t" => [@"p" (vr "T")],
                    "body" => (import [* ["param" : "p_t"]] (vr "x"))
                })
            }),
            Assoc::new()
        ),
        Ok(_)
    );
}

#[test]
fn use__insert_form_pat() {
    let se = syn_env!("Pat" => (impossible),
                      "Expr" => (biased (biased atom, atom),
                                        (biased (alt (lit "a"), (lit "b")), atom)));
    assert_eq!(
        insert_form_pat(&se, n("Expr"), &form_pat!((lit "c"))),
        syn_env!("Pat" => (impossible),
                      "Expr" => (biased (biased atom, atom),
                                        (biased (alt (lit "a"), (lit "b"), (lit "c")), atom)))
    );
}

// This belongs in `flimsy_syntax.rs`, except that `ast!` is not available there
#[test]
fn generate_flimsy_syntax() {
    assert_eq!(
        u!({apply : nat_to_nat [x]}),
        ast!({ "Expr" "apply" : "rator" => (vr "nat_to_nat") , "rand" => [ (vr "x") ]})
    );
    assert_eq!(
        u!({lambda : [y {Type Nat :}; z T] body}),
        ast!({ "Expr" "lambda" :
            "param" => [@"p" "y", "z"],
            "p_t" => [@"p" {"Type" "Nat" :}, (vr "T")],
            "body" => (import [* [ "param" : "p_t" ]]  (vr "body"))})
    )
}
