use grammar::FormPat::*;
use grammar::FormPat;
use grammar::SynEnv;
use std::rc::Rc;
use name::*;
use form::Form;
use ast_walk::WalkRule::{NotWalked, LiteralLike, Custom};
use runtime::reify::Reifiable;

macro_rules! syntax_syntax {  // No, don't run away! This macro isn't that bad!

    // atomic FormPat
    (( $($gram:tt)* )  $syntax_name:ident  ) => {
        Rc::new(Form {
            name: n(&stringify!($syntax_name).to_lowercase()),
            grammar: Rc::new(form_pat!( $($gram)* )),
            type_compare: ::form::Both(NotWalked,NotWalked), // Not a type
            synth_type: ::form::Both(NotWalked,NotWalked), // Doesn't even have a type
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
            synth_type: ::form::Both(NotWalked,NotWalked), // Doesn't even have a type
            eval: ::form::Positive(cust_rc_box!(|parts| {
                Ok(::grammar::FormPat::$syntax_name(
                    $( { let $arg = parts.get_res(n(&stringify!($arg)))?; $e } ),*
                ).reify())}
            )),
            quasiquote: ::form::Both(LiteralLike, LiteralLike)
        })
    };
}


pub fn make_core_macro_forms() -> SynEnv {
    let grammar_grammar = forms_to_form_pat![
        syntax_syntax!( ( (delim ",{", "{", (named "body", (call "Expr"))) ) Anyways (
            body => ::ast::Ast::reflect(&body)
        )),
        syntax_syntax!( ((lit "impossible")) Impossible ),
        syntax_syntax!( ((delim "{", "{", [(lit "lit"), (named "body", aat)]) ) Literal (
            body => ::name::Name::reflect(&body)
        )),
        syntax_syntax!( ((lit "any_token")) AnyToken ),
        syntax_syntax!( ((lit "atom")) AnyToken ),
        syntax_syntax!( ((lit "vr")) VarRef ),
        syntax_syntax!( ([(lit "delim"), (named "name", aat), (named "br", (anyways "[")),
                          (delim "[", "[", (named "body", (call "Syntax"))) ]  ) Delimited (
            name => ::name::Name::reflect(&name),
            br => ::read::delim(&::name::Name::reflect(&br).sp()),
            body => Rc::new(FormPat::reflect(&body))
        )),
        syntax_syntax!( ([(named "body", (call "Syntax")), (lit "*")]) Star (
            body => Rc::new(FormPat::reflect(&body))
        ))
    ];

    assoc_n!("Syntax" => Rc::new(grammar_grammar))
}

#[test]
fn syntax_basics() {
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