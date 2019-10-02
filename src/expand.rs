use ast::Ast;
use ast_walk::{LazyWalkReses, WalkRule::LiteralLike};
use form::Form;
use name::{n, Name};
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

fn expand_macro(parts: ::ast_walk::LazyWalkReses<ExpandMacros>) -> Result<Ast, ()> {
    // TODO: should there be something in scope here? Or is everything captured?
    let mut env = Assoc::new();

    let macro_form: &Form = parts.this_ast.node_form();

    // Turn the subterms into values
    for (binder, _depth) in macro_form.grammar.binders() {
        let nt = macro_form.grammar.find_named_call(binder).unwrap();
        if nt != n("DefaultName") && nt != n("Ident") {
            // TODO: why not?
            env = env.set(binder, ::runtime::eval::Value::from_ast(&parts.get_term(binder)));
        }
    }

    let expanded = ::runtime::eval::eval(&parts.get_term(n("implementation")), env)?.to_ast();

    // Expand any macros that were produced by expansion, or were already present in subterms:
    // TODO #25: hygiene violation (see the `syntax_syntax!` for `Scope`)
    expand(&expanded)
}

impl WalkMode for ExpandMacros {
    fn name() -> &'static str { "MExpand" }
    type Elt = Ast;
    type Negated = UnusedNegativeExpandMacros;
    type Err = <::runtime::eval::Eval as WalkMode>::Err;
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
    type Err = <::runtime::eval::Eval as WalkMode>::Err;
    type D = ::walk_mode::Positive<UnusedNegativeExpandMacros>;
    type ExtraInfo = ();
    fn get_walk_rule(_: &Form) -> ::ast_walk::WalkRule<UnusedNegativeExpandMacros> { icp!() }
    fn automatically_extend_env() -> bool { icp!() }
}

// I *think* the environment doesn't matter
pub fn expand(ast: &Ast) -> Result<Ast, ()> {
    ::ast_walk::walk::<ExpandMacros>(ast, &LazyWalkReses::new_empty())
}

#[test]
fn expand_basic_macros() {
    // Quasiquotation doesn't work with `u!`, so we have to use `ast!`:
    let make_expr = ast!({"Expr" "quote_expr" : "nt" => (vr "Expr"),
        "body" => (++ true (,u!({apply : plus [one two]})))});

    let macro_def = u!({Syntax scope :
        [] {literal => [] : {call : DefaultToken} just_add_1_and_2}
        {Type Nat :} // "unused_type"
        just_add_1_and_2_macro
        (,make_expr)
    });

    assert_m!(::runtime::eval::eval_top(&macro_def), Ok(_))
}
