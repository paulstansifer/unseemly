#![allow(dead_code)]
/**
 Core forms!


 Expr @ S -> T ::=  '[ [ ,[x : Name @ T], : ,[t : Type], ]
                         -> ,[ bind(body <-- x : t)bind : Expr @ S], ] ]'
 Expr @ T ::= '[ ( ,[rator : Expr @ S -> T],   ,[rand : Expr @ S], ) ]'
 Expr @ T ::= x : Name @ T

 // Ths has a bunch of tricky ambiguity and quoting stuff not worked out yet
 SynQuote ::= ''[ '[ ,,[content : QuoteContents],, ]' ]''
 QuoteContents ::= ''[ ,[ ,,[n : Name @ T],, : ,,[t : Type],, ], ]'' exports (n : t)
 QuoteContents ::= '[ ...[,[t : TokenTree],]...  ]'

 Where T is a Term (i.e. Expr, SynQuote, etc.)
 T ::= '[ ]'





 It would be really nice to be able to use types as names: `[Num -> Num+1]`.

 */


use name::*;
use std::collections::HashMap;
use parse::{SynEnv, parse};
use parse::FormPat::*;
use read::DelimChar::*;
use read::{Token, TokenTree, DelimChar, Group, Simple, delim};
use form::{Form, simple_form};
use util::assoc::Assoc;
use ast::*;
use std::rc::Rc;

/* Note that both types and terms are represented as Ast<'t> */

fn make_core_syn_env<'t>() -> SynEnv<'t> {
    assoc_n!(
        "expr" => vec![
            simple_form("lambda",
                form_pat!((delim ".[", "[", [
                    (named "param", aat), (lit ":"), 
                    (named "p_t", (call "type")), (lit "."),
                    (named "body", (call "expr"))]))),
            simple_form("apply",
                form_pat!([ (named "rator", (call "expr")),
                            (named "rand", (call "expr"))])),
            simple_form("varref", form_pat!(aat)),
            simple_form("synquote",
                form_pat!((delim "'[", "[",
                    (star (biased (delim ",[", "[", (call "expr")), at)))))
        ],
        "type" => vec![
            simple_form("fn",
                form_pat!((delim "[", "[",
                        [ (named "rator", (call "type")), (lit "->"), 
                          (named "rand", (call "type") ) ]))),
            simple_form("ident", form_pat!((lit "ident")))
        ]
        )
}


//const under_quote_grammar : FormPat<'static> =
//    Alt(vec![Delimited]);

//const grammar_grammar : FormPat<'static> = AnyAtom;


/// intended for use in tests
fn find_form<'t>(name: &str, se: &SynEnv<'t>) -> Rc<Form<'t>> { 
    let mut cur = &se.n;
    while let &Some(ref node) = cur {
        for form in &node.v {
            if form.name.is(name) { return form.clone() }
        }
        cur = &node.next.n;
    }
    panic!("not found!");
}


#[test]
fn form_grammar_tests() {
    let cse = make_core_syn_env();
    assert_eq!(parse(&form_pat!((call "type")),
                     cse.clone(),
                     &tokens!([""; "ident" "->" "ident"])).unwrap(),
               ast_elt!({ find_form("fn", &cse); ["rand"; {find_form("ident", &cse) ; []},
                                                  "rator"; {find_form("ident", &cse) ; []}]}));
}

macro_rules! expect_node {
    ( ($form:expr) $( $n:ident = $name:expr ),* ; $body:expr ) => (
        | node | {
            if let Node(f, boxed_env) = node {
                if let Env(e) = *boxed_env {
                    if f == $form { 
                        let ( $( $n ),* ) = ( $( e.find(&n($name)).unwrap() ),* );
                        $body
                    } else {
                       Err(())
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
    })
}

#[test]
fn form_expect_node_test() {
    let cse = make_core_syn_env();
    let ast = ast_elt!({ find_form("apply", &cse); 
        ["rand"; {find_form("varref", &cse) ; "f"},
         "rator"; {find_form("varref", &cse) ; "x"}]});
    let _ = expect_node!( (find_form("apply", &cse)) expect_f = "rand", expect_x = "rator";
        {
            assert_eq!(expect_f, &ast_elt!({find_form("varref", &cse); "f"}));
            assert_eq!(expect_x, &ast_elt!({find_form("varref", &cse); "x"}));
            Ok(())
        })(ast);
}
