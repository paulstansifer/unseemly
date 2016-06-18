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
use ty::*;
use beta::*;
use ast_walk::WalkRule::*;

macro_rules! expect_node {
    ( ($node:expr ; $form:expr) $( $n:ident = $name:expr ),* ; $body:expr ) => (
        if let Node(ref f, ref boxed_env) = $node {
            if let Env(ref e) = **boxed_env {
                if *f == $form { 
                    // This is tied to the signature of `Custom`
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
    )
}


/* Note that both types and terms are represented as Ast<'t> */

fn make_core_syn_env<'t>() -> SynEnv<'t> {
    let fn_type = 
        simple_form("fn", 
            form_pat!((delim "[", "[",
                [ (named "param", (call "type")), (lit "->"), 
                  (named "ret", (call "type") ) ])));
                  
    /* This seems to be necessary to get separate `Rc`s into the closures. */
    let fn_type_0 = fn_type.clone();
    let fn_type_1 = fn_type.clone();

    

    assoc_n!(
        "expr" => vec![
            typed_form!("lambda",
                /* syntax */
                (delim ".[", "[", [
                    (named "param", aat), (lit ":"), 
                    (named "p_t", (call "type")), (lit "."),
                    (import ["param" : "p_t"],
                        (named "body", (call "expr")))]),
                /* type */
                Custom(Box::new( move | part_types | {                    
                    let lambda_type : Ast<'t> = 
                        ast_elt!({ fn_type_0.clone() ;
                            [ "param" => (, part_types.get_term(&n("p_t"))),
                              "ret" => (, try!(part_types.get_res(&n("body"))))]}); 
                    Ok(lambda_type)
                }))),
            
            typed_form!("apply",
                [(named "rator", (call "expr")), 
                 (named "rand", (call "expr"))],
                Custom(Box::new(move | part_types |
                    expect_node!( (try!(part_types.get_res(&n("rator"))) ; 
                                   fn_type_1)
                        input = "param", output = "ret";
                        
                        if input == &try!(part_types.get_res(&n("rand"))) {
                            Ok(output.clone())
                        } else {
                            Err(())
                        })))),
                        
            typed_form!("var_ref", aat, VarRef)

            // The first use for syntax quotes will be in macro definitions.
            // But we will someday need them as expressions.                    
        ] ,
        "type" => vec![
            fn_type.clone(),
            simple_form("ident", form_pat!((lit "ident")))
        ]
    )
}

fn find_form<'t>(se: &SynEnv<'t>, nt: &str, form_name: &str)
         -> Rc<Form<'t>> {
    for form in se.find(&n(nt)).unwrap() {
        if form.name.is(form_name) {
            return form.clone();
        }
    }
    panic!("{:?} not found in {:?}", form_name, nt)
}


#[test]
fn form_grammar_tests() {
    let cse = make_core_syn_env();
    assert_eq!(parse(&form_pat!((call "type")),
                     cse.clone(),
                     &tokens!([""; "ident" "->" "ident"])).unwrap(),
               ast_elt!({ find_form(&cse, "type", "fn"); 
                   ["ret" => {find_form(&cse, "type", "ident") ; []},
                    "param" => {find_form(&cse, "type", "ident") ; []}]}));
}


#[test]
fn form_expect_node_test() {
    let cse = make_core_syn_env();
    let ast = ast_elt!({ find_form(&cse, "expr", "apply"); 
        ["rand" => {find_form(&cse, "expr", "var_ref") ; "f"},
         "rator" => {find_form(&cse, "expr", "var_ref") ; "x"}]});
    let _ = expect_node!( ( ast ; find_form(&cse, "expr", "apply")) expect_f = "rand", expect_x = "rator";
        {
            assert_eq!(expect_f, &ast_elt!({find_form(&cse, "expr", "var_ref"); "f"}));
            assert_eq!(expect_x, &ast_elt!({find_form(&cse, "expr", "var_ref"); "x"}));
            Ok(())
        });
}

#[test]
fn form_type_tests() {
    let cse = make_core_syn_env();
    
    let mt_ty_env = Assoc::new();
    let simple_ty_env = mt_ty_env.set(n("x"), ast_elt!("integer"));
    
    let vr = find_form(&cse, "expr", "var_ref");
    let lam = find_form(&cse, "expr", "lambda");
    let fun = find_form(&cse, "type", "fn");

    
    assert_eq!(synth_type(&ast_elt!( { vr.clone() ; "x" }),
                          simple_ty_env.clone()),
               Ok(ast_elt!("integer")));
    
    assert_eq!(synth_type(&ast_elt!( 
        { lam.clone() ;
            [ "param" => "y", 
              "p_t" => "float",
              "body" => (import [ "param" : "p_t" ]  { vr.clone() ; "x"})]}),
        simple_ty_env.clone()),
        Ok(ast_elt!({ fun.clone() ; 
            [ "param" => "float", "ret" => "integer" ]})));
}