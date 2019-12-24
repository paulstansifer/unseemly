use crate::{
    ast::Ast,
    ast_walk::{LazyWalkReses, WalkRule, WalkRule::LiteralLike},
    form::Form,
    name::{n, Name},
    runtime::{eval, eval::Value},
    util::assoc::Assoc,
    walk_mode::{NegativeWalkMode, WalkElt, WalkMode},
};

custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct ExpandMacros {}
}
custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct UnusedNegativeExpandMacros {}
}

impl WalkMode for ExpandMacros {
    fn name() -> &'static str { "MExpand" }
    type Elt = Value;
    type Negated = UnusedNegativeExpandMacros;
    type AsPositive = ExpandMacros;
    type AsNegative = UnusedNegativeExpandMacros;
    type Err = <eval::Eval as WalkMode>::Err;
    type D = crate::walk_mode::Positive<ExpandMacros>;
    type ExtraInfo = ();

    fn get_walk_rule(f: &Form) -> WalkRule<ExpandMacros> {
        if f.name == n("macro_invocation") {
            let rule = f.eval.pos().clone();
            cust_rc_box!(move |parts| {
                match rule {
                    WalkRule::Custom(ref ts_fn) => ts_fn(parts.switch_mode::<eval::Eval>()),
                    _ => icp!(),
                }
            })
        } else {
            LiteralLike
        }
    }
    fn automatically_extend_env() -> bool { false }

    // TODO: maybe keep this from being called?
    fn underspecified(_: Name) -> Value { val!(enum "why is this here?", ) }

    fn walk_var(
        name: Name,
        _parts: &crate::ast_walk::LazyWalkReses<ExpandMacros>,
    ) -> Result<Value, Self::Err>
    {
        use crate::runtime::reify::Reifiable;
        Ok(crate::ast::VariableReference(name).reify()) // Even variables are literal in macro expansion!
    }
}
impl WalkMode for UnusedNegativeExpandMacros {
    fn name() -> &'static str { "XXXXX" }
    type Elt = Value;
    type Negated = ExpandMacros;
    type AsPositive = ExpandMacros;
    type AsNegative = UnusedNegativeExpandMacros;
    type Err = <eval::Eval as WalkMode>::Err;
    type D = crate::walk_mode::Negative<UnusedNegativeExpandMacros>;
    type ExtraInfo = ();
    fn get_walk_rule(_: &Form) -> WalkRule<UnusedNegativeExpandMacros> { icp!() }
    fn automatically_extend_env() -> bool { icp!() }
}

impl NegativeWalkMode for UnusedNegativeExpandMacros {
    fn needs_pre_match() -> bool { panic!() }
}

// I *think* the environment doesn't matter
pub fn expand(ast: &Ast) -> Result<Ast, ()> {
    use crate::runtime::reify::Reifiable;
    Ok(Ast::reflect(&crate::ast_walk::walk::<ExpandMacros>(ast, &LazyWalkReses::new_empty())?))
}

#[test]
fn expand_basic_macros() {
    use crate::core_macro_forms::macro_invocation;

    // Quasiquotation doesn't work with `u!`, so we have to use `ast!`:
    let macro_body_0_args = ast!({"Expr" "quote_expr" : "nt" => (vr "Expr"),
        "body" => (++ true (,u!({apply : plus [one ; two]})))});

    let uqef = crate::core_qq_forms::unquote_form(n("Expr"), true, 1);
    let uqpf = crate::core_qq_forms::unquote_form(n("Pat"), true, 1);

    let macro_def_0_args = u!({Syntax scope :
        [] {literal => [] : {call : DefaultToken} (at just_add_1_and_2)}
        just_add_1_and_2_macro
        (,macro_body_0_args.clone())
    });

    // Full of closures, so hard to compare:
    assert_m!(eval::eval_top(&macro_def_0_args), Ok(_));

    assert_eq!(
        expand(&u!({
            macro_invocation(
                form_pat!((lit "just_add_1_and_2")),
                n("just_add_1_and_2_macro"),
                eval::Closure { body: macro_body_0_args, params: vec![], env: Assoc::new() },
                vec![],
            );
        })),
        Ok(u!({apply : plus [one ; two]}))
    );

    // A macro that generates a one-adding expression:

    let macro_body_1_arg = ast!({"Expr" "quote_expr" : "nt" => (vr "Expr"),
        "body" => (++ true (,u!({apply : plus [one ; { uqef.clone(); (~) e}]})))});

    let macro_def_1_arg = u!({Syntax scope :
        [] {seq => [* ["elt"]] : [{literal => [] : {call : DefaultToken} (at add_1)} ;
                                  {named => ["part_name"] : e {call : Expr}}] }
        add_1_macro
        (,macro_body_1_arg.clone())
    });

    // Full of closures, so hard to compare:
    assert_m!(eval::eval_top(&macro_def_1_arg), Ok(_));

    assert_eq!(
        expand(&u!({
            macro_invocation(
                // duplicates the syntax syntax above
                form_pat!([(lit "add_1"), (named "e", (call "Expr"))]),
                n("add_1_macro"),
                eval::Closure { body: macro_body_1_arg, params: vec![n("e")], env: Assoc::new() },
                vec![],
            );
            five // syntax argument for e
        })),
        Ok(u!({apply : plus [one ; five]}))
    );

    // A let macro:

    let macro_body_let = ast!({"Expr" "quote_expr" : "nt" => (vr "Expr"),
     "body" => (++ true (,u!(
         {match : { uqef.clone(); (~) let_val}
            [{ uqpf.clone(); (~) let_pat } {uqef.clone(); (~) let_body}]})))});

    let macro_def_let = u!({Syntax scope :
        [T; S] {seq => [* ["elt"]] : [{literal => [] : {call : DefaultToken} (at let)} ;
                                      {named => ["part_name"] : let_pat {call : Pat}} ;
                                      {named => ["part_name"] : let_val {call : Expr}} ;
                                      {named => ["part_name"] : let_body {call : Expr}}] }
        let_macro
        (,macro_body_let.clone())
    });

    // Full of closures, so hard to compare:
    assert_m!(eval::eval_top(&macro_def_let), Ok(_));

    assert_eq!(
        expand(&u!({
            macro_invocation(
                // duplicates the syntax syntax above
                form_pat!([(lit "let"), (named "let_pat", (call "Pat")),
                           (named "let_val", (call "Expr")), (named "let_body", (call "Expr"))]),
                n("let_macro"),
                eval::Closure {
                    body: macro_body_let,
                    params: vec![n("let_val"), n("let_pat"), n("let_body")],
                    env: Assoc::new(),
                },
                vec![],
            );
            x // let_pat
            five // let_val
            {apply : times [x ; eight]} // let_body
        })),
        Ok(u!({match : five [x {apply : times [x ; eight]}]}))
    );

    // An n-ary let macro:

    let dddef = crate::core_qq_forms::dotdotdot_form(n("Expr"));
    let dddpf = crate::core_qq_forms::dotdotdot_form(n("Pat"));

    let macro_body_nary_let = ast!({"Expr" "quote_expr" : "nt" => (vr "Expr"),
     "body" => (++ true (, u!(
         {match : {tuple_expr : [{dddef.clone() ; [(~ let_val)] { uqef.clone(); (~) let_val}}]}
            [{Pat tuple_pat : [{dddpf.clone() ; [(~ let_pat)] { uqpf.clone(); (~) let_pat }}]}
             { uqef.clone(); (~) let_body}]})))});

    let macro_def_nary_let = u!({Syntax scope :
        [T; S] {seq => [* ["elt"]] :
            [{literal => [] : {call : DefaultToken} (at let)} ;
             {star => ["body"] : {named => ["part_name"] : let_pat {call : Pat}}} ;
             {star => ["body"] : {named => ["part_name"] : let_val {call : Expr}}} ;
             {named => ["part_name"] : let_body {call : Expr}}] }
        nary_let_macro
        (,macro_body_nary_let.clone())
    });

    // Full of closures, so hard to compare:
    assert_m!(eval::eval_top(&macro_def_nary_let), Ok(_));

    assert_eq!(
        expand(&u!({
            macro_invocation(
                // duplicates the syntax syntax above
                form_pat!([(lit "let"), (star (named "let_pat", (call "Pat"))),
                           (star (named "let_val", (call "Expr"))),
                           (named "let_body", (call "Expr"))]),
                n("nary_let_macro"),
                eval::Closure {
                    body: macro_body_nary_let,
                    params: vec![n("let_val"), n("let_pat"), n("let_body")],
                    env: Assoc::new(),
                },
                vec![],
            );
            [x; y] // let_pat
            [five; seven] // let_val
            {apply : times [x ; eight]} // let_body
        })),
        Ok(u!({match : {tuple_expr : [five; seven]}
            [{Pat tuple_pat : [x; y]} {apply : times [x; eight]}]}))
    );
}
