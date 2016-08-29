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
use parse::{SynEnv, parse, FormPat};
use parse::FormPat::*;
use read::DelimChar::*;
use read::{Token, TokenTree, DelimChar, Group, Simple, delim};
use form::{Form, simple_form};
use util::assoc::Assoc;
use ast::*;
use std::rc::Rc;
use ty::*;
use eval::*;
use beta::*;
use ast_walk::WalkRule::*;
use num::bigint;
use num::bigint::ToBigInt;



// TODO: this ought to have some MBE support
macro_rules! expect_node {
    ( ($node:expr ; $form:expr) $env:ident ; $body:expr ) => (
        // This is tied to the signature of `Custom`
        if let Node(ref f, ref $env) = $node {
            if *f == $form { 
                $body
            } else {
               Err(())
            }
        } else {
            Err(())
        }
    )
}

macro_rules! destructure_node {
    ( ($node:expr ; $form:expr) $( $n:ident = $name:expr ),* ; $body:expr ) => (
        expect_node!( ($node ; $form) env ; {
            let ( $( $n ),* ) = ( $( env.get_leaf_or_panic(&n($name)) ),* );
            $body
        })
    )
}

macro_rules! forms_to_form_pat {
    ( $( $form:expr ),* ) => {
        form_pat!((alt $( (scope $form) ),* ))
    }
}


/* Note that both types and terms are represented as Ast<'t> */

pub fn make_core_syn_env<'t>() -> SynEnv<'t> {
    let fn_type = 
        simple_form("fn", 
            form_pat!((delim "[", "[",
                [ (star (named "param", (call "type"))), (lit "->"), 
                  (named "ret", (call "type") ) ])));
    
                  
    /* This seems to be necessary to get separate `Rc`s into the closures. */
    let fn_type_0 = fn_type.clone();
    let fn_type_1 = fn_type.clone();

    let main_expr_forms = forms_to_form_pat![
        typed_form!("lambda",
            /* syntax */ /* TODO: add comma separators to the syntax! */
            (delim ".[", "[", [
                               (star [(named "param", aat), (lit ":"), 
                                      (named "p_t", (call "type"))]), (lit "."),
                (named "body",
                    (import [* ["param" : "p_t"]], (call "expr")))]),
            /* type */
            Custom(Box::new( move | part_types | {
                let lambda_type : Ast<'t> = 
                    ast!({ fn_type_1.clone() ;
                         "param" => [* part_types =>("param") part_types :
                                       (, part_types.get_term(&n("p_t")))],
                         "ret" => (, try!(part_types.get_res(&n("body"))))});
                Ok(lambda_type)})),
            /* evaluation */
            Custom(Box::new( move | part_values | {
                Ok(Function(Rc::new(Closure {
                    body: part_values.get_term(&n("body")),
                    params: 
                    part_values.get_rep_term(&n("param")).iter().map(|ast|
                        match ast { &Atom(n) => n, _ => { panic!("internal error!") } } 
                    ).collect(),
                    env: part_values.env
                })))
            }))
            ),
        
        typed_form!("apply",
            [(named "rator", (call "expr")), 
             (star (named "rand", (call "expr")))],
            Custom(Box::new(move | part_types |
                expect_node!( (try!(part_types.get_res(&n("rator"))) ; 
                               fn_type_0)
                    env;
                    {
                        for (input, expected) in env.get_rep_leaf_or_panic(&n("param")).iter().zip(
                            &try!(part_types.get_rep_res(&n("rand")))
                        ) {
                            if input != &expected { return Err(()); }
                        }
                    
                        Ok(env.get_leaf_or_panic(&n("ret")).clone())
                    }
                ))),
            Custom(Box::new( move | part_values | {
                print!("Trying to evaluate {:?}\n", part_values);
                match try!(part_values.get_res(&n("rator"))) {
                    Function(clos) => {
                        let mut env = clos.env.clone();
                        for (p, a) in clos.params.iter().zip(
                            try!(part_values.get_rep_res(&n("rand")))
                        ) {
                            env = env.set(*p, a);
                        }
                        
                        eval(&clos.body, env)
                    },
                    BuiltInFunction(::eval::BIF(f)) => {
                        Ok(f(try!(part_values.get_rep_res(&n("rand")))))
                    }
                    other => { 
                        panic!("Type soundness bug: attempted to invoke {:?} 
                        as if it were a function", other)
                    }
                }
            })))
        // The first use for syntax quotes will be in macro definitions.
        // But we will someday need them as expressions.                    
    ];

    assoc_n!(
        "expr" => Biased(Box::new(main_expr_forms), Box::new(VarRef)),
        "type" => forms_to_form_pat![
            fn_type.clone(),
            simple_form("ident", form_pat!((lit "ident"))),
            simple_form("int", form_pat!((lit "int")))
        ]
    )
}







pub fn find_form<'t>(se: &SynEnv<'t>, nt: &str, form_name: &str)
         -> Rc<Form<'t>> {             

    fn find_form_rec<'t>(f: &FormPat<'t>, form_name: &str) -> Option<Rc<Form<'t>>> {
        match f {
            &Scope(ref f) => {
                if f.name.is(form_name) {
                    Some(f.clone())
                } else {
                    None
                }
            }
            &Alt(ref vf) => {
                for f in vf {
                    let res = find_form_rec(f, form_name);
                    if res.is_some() { return res; }
                }
                None
            }
            &Biased(ref lhs, ref rhs) => {
                let l_res = find_form_rec(lhs, form_name);
                if l_res.is_some() { l_res } else { find_form_rec(rhs, form_name) }
            }
            _ => { None }
        }        
    }
    let pat = se.find_or_panic(&n(nt));
    
    find_form_rec(pat, form_name)
        .expect(format!("{:?} not found in {:?}", form_name, pat).as_str())
}


#[test]
fn form_grammar_tests() {
    let cse = make_core_syn_env();
    assert_eq!(parse(&form_pat!((call "type")),
                     cse.clone(),
                     &tokens!([""; "ident" "->" "ident"])).unwrap(),
               ast!({ find_form(&cse, "type", "fn"); 
                   ["ret" => {find_form(&cse, "type", "ident") ; []},
                    "param" => [{find_form(&cse, "type", "ident") ; []}]]}));
}


#[test]
fn form_expect_node_test() {
    let cse = make_core_syn_env();
    let ast = ast!({ find_form(&cse, "expr", "apply"); 
        ["rand" => [(vr "f")], "rator" => (vr "x")]});
    let _ = expect_node!( ( ast ; find_form(&cse, "expr", "apply")) env; //expect_f = "rand", expect_x = "rator";
        {
            assert_eq!(env.get_rep_leaf_or_panic(&n("rand")), vec![&ast!((vr "f"))]);
            assert_eq!(env.get_leaf_or_panic(&n("rator")), &ast!((vr "x")));
            Ok(())
        });
}

#[test]
fn form_type_tests() {
    let cse = make_core_syn_env();
    
    let mt_ty_env = Assoc::new();
    let simple_ty_env = mt_ty_env.set(n("x"), ast!("integer"));
    
    let lam = find_form(&cse, "expr", "lambda");
    let fun = find_form(&cse, "type", "fn");

    
    assert_eq!(synth_type(&ast!( (vr "x") ),
                          simple_ty_env.clone()),
               Ok(ast!("integer")));
    
    assert_eq!(synth_type(&ast!( 
        { lam.clone() ;
            [ "param" => [@"p" "y"], 
              "p_t" => [@"p" "float"],
              "body" => (import [* [ "param" : "p_t" ]] (vr "x"))]}),
        simple_ty_env.clone()),
        Ok(ast!({ fun.clone() ; 
            [ "param" => ["float"], "ret" => "integer" ]})));
}

#[test]
fn form_eval_tests() {
    let cse = make_core_syn_env();
    
    let mt_env = Assoc::new();
    // x is 18, w is 99
    let simple_env = mt_env.set(n("x"), Int(18.to_bigint().unwrap()))
        .set(n("w"), Int(99.to_bigint().unwrap()));
    
    let lam = find_form(&cse, "expr", "lambda");
    let app = find_form(&cse, "expr", "apply");

    
    assert_eq!(eval(&ast!((vr "x")), simple_env.clone()),
               Ok(Int(18.to_bigint().unwrap())));
    
    // (λy.w) x
    assert_eq!(eval(&ast!( 
        { app.clone() ;
            [
             "rator" => 
                { lam.clone() ;
                    "param" => [@"p" "y"], 
                    "p_t" => [@"p" "integer"],
                    "body" => (import [* [ "param" : "p_t" ]]  (vr "w"))},
             "rand" => [(vr "x")]
            ]}),
        simple_env.clone()),
        Ok(Int(99.to_bigint().unwrap())));
    
    // (λy.y) x
    assert_eq!(eval(&ast!( 
        { app.clone() ;
            [
             "rator" => 
                { lam.clone() ;
                    "param" => [@"p" "y"], 
                    "p_t" => [@"p" "integer"],
                    "body" => (import [* [ "param" : "p_t" ]]  (vr "y"))},
             "rand" => [(vr "x")]
            ]}),
        simple_env.clone()),
        Ok(Int(18.to_bigint().unwrap())));
}