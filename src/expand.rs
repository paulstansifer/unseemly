use ast::Ast;
use ast_walk::{LazyWalkReses, WalkRule::LiteralLike};
use form::Form;
use name::{n, Name};
use runtime::eval::Value;
use util::assoc::Assoc;
use walk_mode::{WalkElt, WalkMode};

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
    type Err = <::runtime::eval::Eval as WalkMode>::Err;
    type D = ::walk_mode::Positive<ExpandMacros>;
    type ExtraInfo = ();

    fn get_walk_rule(f: &Form) -> ::ast_walk::WalkRule<ExpandMacros> {
        if f.name == n("macro_invocation") {
            let rule = f.eval.pos().clone();
            cust_rc_box!(move |parts| {
                match rule {
                    ::ast_walk::WalkRule::Custom(ref ts_fn) => {
                        ts_fn(parts.switch_mode::<::runtime::eval::Eval>())
                    }
                    _ => icp!(),
                }
            })
        } else {
            LiteralLike
        }
    }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(
        name: Name,
        _parts: &::ast_walk::LazyWalkReses<ExpandMacros>,
    ) -> Result<Value, Self::Err>
    {
        use runtime::reify::Reifiable;
        Ok(::ast::VariableReference(name).reify()) // Even variables are literal in macro expansion!
    }
}
impl WalkMode for UnusedNegativeExpandMacros {
    fn name() -> &'static str { "XXXXX" }
    type Elt = Value;
    type Negated = ExpandMacros;
    type Err = <::runtime::eval::Eval as WalkMode>::Err;
    type D = ::walk_mode::Positive<UnusedNegativeExpandMacros>;
    type ExtraInfo = ();
    fn get_walk_rule(_: &Form) -> ::ast_walk::WalkRule<UnusedNegativeExpandMacros> { icp!() }
    fn automatically_extend_env() -> bool { icp!() }
}

// I *think* the environment doesn't matter
pub fn expand(ast: &Ast) -> Result<Ast, ()> {
    use runtime::reify::Reifiable;
    Ok(Ast::reflect(&::ast_walk::walk::<ExpandMacros>(ast, &LazyWalkReses::new_empty())?))
}

#[test]
fn expand_basic_macros() {
    // Quasiquotation doesn't work with `u!`, so we have to use `ast!`:
    let make_expr = ast!({"Expr" "quote_expr" : "nt" => (vr "Expr"),
        "body" => (++ true (,u!({apply : plus [one ; two]})))});

    let macro_def = u!({Syntax scope :
        [] {literal => [] : {call : DefaultToken} just_add_1_and_2}
        {Type Nat :} // "unused_type"
        just_add_1_and_2_macro
        (,make_expr.clone())
    });

    assert_m!(::runtime::eval::eval_top(&macro_def), Ok(_));

    assert_eq!(
        expand(&u!({
            ::core_macro_forms::macro_invocation(
                form_pat!((lit "just_add_1_and_2")),
                n("just_add_1_and_2_macro"),
                ::runtime::eval::Closure { body: make_expr, params: vec![], env: Assoc::new() },
                vec![],
            );
        })),
        Ok(u!({apply : plus [one ; two]}))
    );
}
