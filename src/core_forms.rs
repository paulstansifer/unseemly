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
use runtime::eval::*;
use beta::*;
use ast_walk::WalkRule::*;
use num::bigint;
use num::bigint::ToBigInt;


/* Unpacking `Ast`s into environments is a pain, so here's a macro for it*/
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

// TODO: this ought to have some MBE support
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

fn ast_to_atom<'t>(ast: &Ast<'t>) -> Name<'t> {
    match ast { &Atom(n) => n, _ => { panic!("internal error!") } }
}


/* Note that both types and terms are represented as Ast<'t> */

pub fn make_core_syn_env<'t>() -> SynEnv<'t> {
    let fn_type = 
        simple_form("fn", 
            /* Friggin' Atom bracket matching doesn't ignore strings or comments. */
            form_pat!((delim "[", "[", /*]]*/
                [ (star (named "param", (call "type"))), (lit "->"), 
                  (named "ret", (call "type") ) ])));
                  
    let enum_type = 
        simple_form("enum", form_pat!([(lit "enum"),
            (delim "{", "{", /*}}*/ (star [(named "name", aat), 
                (delim "(", "(", /*))*/ [(star (named "component", (call "type")))])]))]));
                
    let struct_type =
        simple_form("struct", form_pat!(
            [(lit "struct"),
             (delim "{", "{", /*}}*/ (star [(named "component_name", aat), (lit ":"), 
                                           (named "component", (call "type"))]))]));
            
    /* This seems to be necessary to get separate `Rc`s into the closures. */
    let fn_type_0 = fn_type.clone();
    let fn_type_1 = fn_type.clone();
    let enum_type_0 = enum_type.clone();
    let enum_type_1 = enum_type.clone();
    let struct_type_0 = struct_type.clone();
    let struct_type_1 = struct_type.clone();

    let main_expr_forms = forms_to_form_pat![
        typed_form!("lambda",
            /* syntax */ /* TODO: add comma separators to the syntax! */
            (delim ".[", "[", /*]]*/ [
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
                    part_values.get_rep_term(&n("param")).iter().map(ast_to_atom).collect(),
                    env: part_values.env
                })))
            }))),
        
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
                    BuiltInFunction(::runtime::eval::BIF(f)) => {
                        Ok(f(try!(part_values.get_rep_res(&n("rand")))))
                    }
                    other => { 
                        panic!("Type soundness bug: attempted to invoke {:?} 
                        as if it were a function", other)
                    }
                }
            }))),
            
        typed_form!("enum_expr",
            [(named "name", aat), 
             (delim "(", "(", /*))*/ [(star (named "component", (call "pat")))]),
             (lit ":"), (named "t", (call "type"))],
            /* Typesynth: */
            Custom(Box::new( move | part_types | {
                let res = part_types.get_term(&n("t"));
                expect_node!( (res ; enum_type_1)
                    enum_type_parts; 
                    {
                        for enum_type_part in enum_type_parts.march_all(&vec![n("name")]) {
                            if &part_types.get_term(&n("name")) 
                                    != enum_type_part.get_leaf_or_panic(&n("name")) {
                                continue; // not the right arm
                            }
                            
                            let component_types : Vec<Ast<'t>> = 
                                enum_type_part.get_rep_leaf_or_panic(&n("component"))
                                    .iter().map(|a| (*a).clone()).collect();
                                    
                            for (t, expected_t) in try!(part_types.get_rep_res(&n("component")))
                                .iter().zip(component_types) {
                                if t != &expected_t {
                                    panic!("Expected type: {:?}, got: {:?}", expected_t, t)
                                }
                            }
                            
                            return Ok(res.clone());
                        }
                        panic!("{:?} is not a valid arm for the type {:?}", 
                            part_types.get_term(&n("name")), res)
                    }        
                )            
            })),
            /* Evaluate: */
            Custom(Box::new( move | part_values | {
                Ok(Enum(ast_to_atom(&part_values.get_term(&n("name"))),
                    try!(part_values.get_rep_res(&n("component")))))
            }))),
        typed_form!("struct_expr",
            (delim "{", "{", /*}}*/ 
                (star [(named "component_name", aat), (lit ":"), 
                       (named "component", (call "expr"))])),
            Custom(Box::new( move | part_types | {
                Ok(ast!({ struct_type_1.clone() ;
                    "component_name" => (@"c" ,seq part_types.get_rep_term(&n("component_name"))),
                    "component" => (@"c" ,seq try!(part_types.get_rep_res(&n("component"))))
                }))
            })),
            Custom(Box::new( move | part_values | {
                let mut res = Assoc::new();
                
                for component_parts in part_values.march_parts(&vec![n("component")]) {
                    res = res.set(ast_to_atom(&component_parts.get_term(&n("component_name"))),
                                  try!(component_parts.get_res(&n("component"))));
                }
                
                Ok(Struct(res))
            })))

        /*,
            
        typed_form!("match",
            []
    )*/
        // The first use for syntax quotes will be in macro definitions.
        // But we will someday need them as expressions.                    
    ];
    
    let main_pat_forms = forms_to_form_pat![
        negative_typed_form!("enum_pat",
            [(named "name", aat), 
             (delim "(", "(", /*))*/ [(star (named "component", (call "pat")))])],
            /* (Negatively) Typecheck: */
            Custom(Box::new( move | part_types |
                expect_node!( (*part_types.context_elt() ; enum_type_0)
                    enum_type_parts;
                    {
                        for enum_type_part in enum_type_parts.march_all(&vec![n("name")]) {
                        
                            if &part_types.get_term(&n("name")) 
                                    != enum_type_part.get_leaf_or_panic(&n("name")) {
                                continue; // not the right arm
                            }
                        
                            let component_types : Vec<Ast<'t>> = 
                                enum_type_part.get_rep_leaf_or_panic(&n("component"))
                                    .iter().map(|a| (*a).clone()).collect();
                           
                            let mut res = Assoc::new();
                            for sub_res in &try!(part_types
                                    .get_rep_res_with(&n("component"), component_types)) {
                                res = res.set_assoc(sub_res);
                            }
                        
                            return Ok(res);
                        }
                        panic!("Type error: enum branch not found");
                }
            ))),
            /* (Negatively) Evaluate: */
            Custom(Box::new( move | part_values | {
                match part_values.context_elt() /* : Value<'t> */ {
                    &Enum(ref name, ref elts) => {
                        // "Try another branch"
                        if name != &ast_to_atom(&part_values.get_term(&n("name"))) {
                            return Err(()); 
                        }
                        
                        let mut res = Assoc::new();
                        for sub_res in &try!(part_values.get_rep_res_with(&n("component"), 
                                                                          elts.clone())) {
                            res = res.set_assoc(sub_res);
                        }
                        
                        Ok(res)
                    }
                    _ => panic!("Type ICE: non-enum")
                }            
            }))),
        negative_typed_form!("struct_pat",
            [(delim "{", "{", /*}}*/ 
                 (star [(named "component_name", aat), (lit ":"), 
                        (named "component", (call "pat"))]))],
            /* (Negatively) typesynth: */
            Custom(Box::new( move | part_types | 
                expect_node!( (*part_types.context_elt() ; struct_type_0)
                    struct_type_parts;
                    {
                        let mut res = Assoc::new();
                        for component_ctx in part_types.march_parts(&vec![n("component")]) {
                            let mut component_found = false;
                            for struct_type_part 
                                    in struct_type_parts.march_all(&vec![n("component")]) {
                                if &component_ctx.get_term(&n("component_name"))
                                    != struct_type_part.get_leaf_or_panic(&n("component_name")) {
                                    continue;
                                }
                                component_found = true;
                                res = res.set_assoc(
                                    &try!(component_ctx
                                        .with_context(
                                            struct_type_part.get_leaf_or_panic(&n("component"))
                                                .clone())
                                        .get_res(&n("component"))));
                                break;
                            }
                            if !component_found {
                                panic!("Type error: {:?} isn't a field of {:?}", 
                                    component_ctx.get_term(&n("component_name")),
                                    part_types.context_elt());
                            }
                        }
                        Ok(res)
                    }))),
            Custom(Box::new( move | part_values | {
                match part_values.context_elt() {
                    &Struct(ref contents) => {
                        let mut res = Assoc::new();
                        
                        for component_ctx in part_values.march_parts(&vec![n("component")]) {
                            res = res.set_assoc(
                                &try!(component_ctx
                                    .with_context(contents.find_or_panic(
                                        &ast_to_atom(
                                            &component_ctx.get_term(&n("component_name"))))
                                            .clone())
                                    .get_res(&n("component"))));
                        }
                        
                        Ok(res)
                    }
                    _ => panic!("Type ICE: non-struct")
                }
            })))];

    assoc_n!(
        "pat" => Biased(Box::new(main_pat_forms), Box::new(VarRef)),
        "expr" => Biased(Box::new(main_expr_forms), Box::new(VarRef)),
        "type" => forms_to_form_pat![
            fn_type.clone(),
            simple_form("ident", form_pat!((lit "ident"))),
            simple_form("int", form_pat!((lit "int"))),
            enum_type.clone(),
            struct_type.clone()
            /*
            // TODO: these should be user-definable
            simple_form("list", 
                form_pat!([(lit "list"), (lit "<"), (named "elt", (call "type")), (lit ">")])),
            simple_form("tuple", 
                form_pat!([(lit "tuple"), 
                    (lit "<"), (star (named "elt", (call "type"))), (lit ">")]))
            */
        ]
    )
}






/**
 * Mostly for testing purposes, this looks up forms by name.
 * In the "real world", programmers look up forms by syntax, using a parser. 
 */
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
fn form_grammar() {
    let cse = make_core_syn_env();
    assert_eq!(parse(&form_pat!((call "type")),
                     cse.clone(),
                     &tokens!([""; "ident" "->" "ident"])).unwrap(),
               ast!({ find_form(&cse, "type", "fn"); 
                   ["ret" => {find_form(&cse, "type", "ident") ; []},
                    "param" => [{find_form(&cse, "type", "ident") ; []}]]}));
}


#[test]
fn form_expect_node() {
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
fn form_type() {
    let cse = make_core_syn_env();
    
    let simple_ty_env = assoc_n!("x" => ast!("integer"), "b" => ast!("bool"));
    
    let lam = find_form(&cse, "expr", "lambda");
    let fun = find_form(&cse, "type", "fn");

    
    assert_eq!(synth_type(&ast!( (vr "x") ),
                          simple_ty_env.clone()),
               Ok(ast!("integer")));
    
    assert_eq!(synth_type(&ast!( 
        { lam.clone() ;
            "param" => [@"p" "y"], 
            "p_t" => [@"p" "float"],
            "body" => (import [* [ "param" : "p_t" ]] (vr "x"))}),
        simple_ty_env.clone()),
        Ok(ast!({ fun.clone() ; 
            "param" => ["float"], "ret" => "integer"})));
    
}

#[test]
fn form_eval() {
    let cse = make_core_syn_env();
    
    let simple_env = assoc_n!("x" => Int(18.to_bigint().unwrap()),
                              "w" => Int(99.to_bigint().unwrap()),
                              "b" => Bool(false));    
    
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

#[test]
fn alg_type() {
    let cse = make_core_syn_env();
    
    let mt_ty_env = Assoc::new();
    let simple_ty_env = assoc_n!(
        "x" => ast!("integer"), "b" => ast!("bool"), "f" => ast!("float"));

    /* Typecheck enum pattern */
    let enum_p = find_form(&cse, "pat", "enum_pat");
    let enum_t = find_form(&cse, "type", "enum");
    
    let my_enum = ast!({ enum_t.clone() ;
        "name" => [@"c" "choice0", "choice1", "choice2"],
        "component" => [@"c" ["integer"], ["integer", "bool"], ["float", "float"]]
    });
        
    assert_eq!(neg_synth_type(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_ty_env.set(negative_ret_val, my_enum.clone())),
        Ok(Assoc::new().set(n("abc"), ast!("integer")).set(n("def"), ast!("bool"))));
    
    /* Typecheck enum expression */
    let enum_e = find_form(&cse, "expr", "enum_expr");
    
    assert_eq!(synth_type(&ast!(
        { enum_e.clone() ;
            "name" => "choice1",
            "component" => [(vr "x"), (vr "b")],
            "t" => (, my_enum.clone())
        }),
        simple_ty_env.clone()),
        Ok(my_enum));
        
        
    /* Typecheck struct pattern */    
    
    let struct_p = find_form(&cse, "pat", "struct_pat");
    let struct_t = find_form(&cse, "type", "struct");
    
    let my_struct = ast!({ struct_t.clone() ;
        "component_name" => [@"c" "x", "y"],
        "component" => [@"c" "integer", "float"]
    });
    
    assert_eq!(neg_synth_type(&ast!(
            { struct_p.clone() ;
                "component_name" => [@"c" "y", "x"],
                "component" => [@"c" (vr "yy"), (vr "xx")]
            }),
            mt_ty_env.set(negative_ret_val, my_struct.clone())),
        Ok(assoc_n!("yy" => ast!("float"), "xx" => ast!("integer"))));
        
    /* Typecheck struct expression */ 
    let struct_e = find_form(&cse, "expr", "struct_expr");
    
    // TODO: currently {x: integer, y: float} ≠ {y: float, x: integer}
    // Implement proper type equality!
    assert_eq!(synth_type(&ast!(
            { struct_e.clone() ;
                "component_name" => [@"c" "x", "y"],
                "component" => [@"c" (vr "x"), (vr "f")]
            }),
            simple_ty_env.clone()),
        Ok(my_struct)
    )


    
}

#[test]
fn alg_eval() {
    let cse = make_core_syn_env();
    
    let mt_env = Assoc::new();
    let simple_env = assoc_n!("x" => Int(18.to_bigint().unwrap()),
                              "w" => Int(99.to_bigint().unwrap()),
                              "b" => Bool(false));
    
    /* Evaluate enum pattern */
    let enum_p = find_form(&cse, "pat", "enum_pat");
    
    assert_eq!(neg_eval(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_env.set(negative_ret_val, 
            Enum(n("choice1"), vec![Int(9006.to_bigint().unwrap()), Bool(true)]))),
        Ok(assoc_n!("abc" => Int(9006.to_bigint().unwrap()), "def" => Bool(true))));
            
    assert_eq!(neg_eval(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_env.set(negative_ret_val, 
            Enum(n("choice0"), vec![Int(12321.to_bigint().unwrap())]))),
        Err(()));

    /* Evaluate enum expression */

    let enum_t = find_form(&cse, "type", "enum");
    
    let my_enum = ast!({ enum_t.clone() ;
        "name" => [@"c" "choice0", "choice1", "choice2"],
        "component" => [@"c" ["integer"], ["integer", "bool"], ["float", "float"]]
    });

    let enum_e = find_form(&cse, "expr", "enum_expr");
    
    assert_eq!(eval(&ast!(
        { enum_e.clone() ;
            "name" => "choice1",
            "component" => [(vr "x"), (vr "b")],
            "t" => (, my_enum.clone())
        }),
        simple_env.clone()),
        Ok(Enum(n("choice1"), vec![Int(18.to_bigint().unwrap()), Bool(false)])));
        
    /* Evaluate struct pattern */
    
    let struct_p = find_form(&cse, "pat", "struct_pat");
    assert_eq!(neg_eval(&ast!(
        { struct_p.clone() ;
            "component_name" => [@"c" "x", "y"],
            "component" => [@"c" (vr "xx"), (vr "yy")]
        }),
        mt_env.set(negative_ret_val,
                   Struct(assoc_n!("x" => Int(0.to_bigint().unwrap()), "y" => Bool(true))))),
        Ok(assoc_n!("xx" => Int(0.to_bigint().unwrap()), "yy" => Bool(true))));
    
}