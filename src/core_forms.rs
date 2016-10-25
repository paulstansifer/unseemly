#![allow(dead_code, non_upper_case_globals)]

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



fn ast_to_atom<'t>(ast: &Ast<'t>) -> Name<'t> {
    match ast { &Atom(n) => n, _ => { panic!("internal error!") } }
}

macro_rules! cust_rc_box {
    ($contents:expr) => { Custom(Rc::new(Box::new($contents))) }
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
            cust_rc_box!( move | part_types | {
                let lambda_type : Ast<'t> = 
                    ast!({ fn_type_1.clone() ;
                         "param" => [* part_types =>("param") part_types :
                                       (, part_types.get_term(&n("p_t")))],
                         "ret" => (, try!(part_types.get_res(&n("body"))))});
                Ok(lambda_type)}),
            /* evaluation */
            cust_rc_box!( move | part_values | {
                Ok(Function(Rc::new(Closure {
                    body: part_values.get_term(&n("body")),
                    params: 
                    part_values.get_rep_term(&n("param")).iter().map(ast_to_atom).collect(),
                    env: part_values.env
                })))
            })),
        
        typed_form!("apply",
            [(named "rator", (call "expr")), 
             (star (named "rand", (call "expr")))],
            cust_rc_box!(move | part_types |
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
                )),
            cust_rc_box!( move | part_values | {
                match try!(part_values.get_res(&n("rator"))) {
                    Function(clos) => {

                        
                        // Evaluate arguments into a fake LazyWalkReses,
                        //  making a dummy form that has the actual arguments and the body together
                        let mut params = vec![];
                        for (p, t) in clos.params.iter().zip(
                                part_values.get_rep_term(&n("rand"))) {
                            let new_arg_parts = ::util::mbe::EnvMBE::new_from_leaves(
                                assoc_n!("param" => Atom(*p), "p_t" => t));
                            params.push(new_arg_parts);
                            //new_env_parts.add_leaf(*p, t);
                        }
                        
                        // All these colons suggest that maybe there's 
                        // some other interface that should exist.
                        
                        let new_env_parts = ::util::mbe::EnvMBE::new_from_anon_repeat(params);
                        
                        ::ast_walk::walk::<::runtime::eval::Evaluate>(&clos.body,
                            &::ast_walk::LazyWalkReses::new(clos.env.clone(), new_env_parts))
                    },
                    BuiltInFunction(::runtime::eval::BIF(f)) => {
                        Ok(f(try!(part_values.get_rep_res(&n("rand")))))
                    }
                    other => { 
                        panic!("Type soundness bug: attempted to invoke {:?} 
                        as if it were a function", other)
                    }
                }
            })),
        // Need to get imports of pats working first!
        typed_form!("match",
            [(lit "match"), (named "scrutinee", (call "expr")),
             (delim "{", "{", 
                 (star [(named "p", (call "pat")), (lit "=>"),
                        (named "arm", (import ["p" = "scrutinee"], (call "expr")))]))],
            /* Typesynth: */
            cust_rc_box!(move | part_types | {
                let mut res = None;
                for arm_part_types in part_types.march_parts(&vec![n("arm")]) {
                    let arm_res = try!(arm_part_types.get_res(&n("arm")));

                    match res {
                        None => { res = Some(arm_res) }
                        Some(ref old_res) => {
                            if old_res != &arm_res {
                                panic!("Type error: arm mismatch: {:?} vs. {:?}", old_res, arm_res)
                            }
                        }
                    }
                }
                
                Ok(res.expect("Type error: no arms!"))                
            }),
            /* Evaluation: */
            cust_rc_box!( move | part_values | {
                for arm_values in part_values.march_all(&vec![n("arm")]) {
                    match arm_values.get_res(&n("arm")) {
                        Ok(res) => { return Ok(res); }
                        Err(()) => { /* try the next one */ }
                    }
                }
                panic!("No arms matched! This ought to be a type error, but isn't.");
            })
        ),
            
        typed_form!("enum_expr",
            [(named "name", aat), 
             (delim "(", "(", /*))*/ [(star (named "component", (call "pat")))]),
             (lit ":"), (named "t", (call "type"))],
            /* Typesynth: */
            cust_rc_box!( move | part_types | {
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
            }),
            /* Evaluate: */
            cust_rc_box!( move | part_values | {
                Ok(Enum(ast_to_atom(&part_values.get_term(&n("name"))),
                    try!(part_values.get_rep_res(&n("component")))))
            })),
        typed_form!("struct_expr",
            (delim "{", "{", /*}}*/ 
                (star [(named "component_name", aat), (lit ":"), 
                       (named "component", (call "expr"))])),
            cust_rc_box!( move | part_types | {
                Ok(ast!({ struct_type_1.clone() ;
                    "component_name" => (@"c" ,seq part_types.get_rep_term(&n("component_name"))),
                    "component" => (@"c" ,seq try!(part_types.get_rep_res(&n("component"))))
                }))
            }),
            cust_rc_box!( move | part_values | {
                let mut res = Assoc::new();
                
                for component_parts in part_values.march_parts(&vec![n("component")]) {
                    res = res.set(ast_to_atom(&component_parts.get_term(&n("component_name"))),
                                  try!(component_parts.get_res(&n("component"))));
                }
                
                Ok(Struct(res))
            }))

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
            cust_rc_box!( move | part_types |
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
            )),
            /* (Negatively) Evaluate: */
            cust_rc_box!( move | part_values | {
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
            })),
        negative_typed_form!("struct_pat",
            [(delim "{", "{", /*}}*/ 
                 (star [(named "component_name", aat), (lit ":"), 
                        (named "component", (call "pat"))]))],
            /* (Negatively) typesynth: */
            cust_rc_box!( move | part_types | 
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
                    })),
            cust_rc_box!( move | part_values | {
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
            }))];

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

thread_local! {
    pub static core_forms: SynEnv<'static> = make_core_syn_env();
}

pub fn find_core_form(nt: &str, name: &str) -> Rc<Form<'static>> {
    core_forms.with(|cf| find_form(cf, nt, name))
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
    let ast = ast!({ find_core_form("expr", "apply"); 
        ["rand" => [(vr "f")], "rator" => (vr "x")]});
    let _ = expect_node!( ( ast ; find_core_form("expr", "apply")) env; //expect_f = "rand", expect_x = "rator";
        {
            assert_eq!(env.get_rep_leaf_or_panic(&n("rand")), vec![&ast!((vr "f"))]);
            assert_eq!(env.get_leaf_or_panic(&n("rator")), &ast!((vr "x")));
            Ok(())
        });
}

#[test]
fn form_type() {
    let simple_ty_env = assoc_n!("x" => ast!("integer"), "b" => ast!("bool"));
    
    let lam = find_core_form("expr", "lambda");
    let fun = find_core_form("type", "fn");

    
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
        Ok(my_struct));
    
    /* Simple match... */
    
    let mtch = find_form(&cse, "expr", "match");
    
    assert_eq!(synth_type(&ast!({ mtch.clone() ;
                "scrutinee" => (vr "f"),
                "p" => [@"arm" (vr "my_new_name"), (vr "unreachable")],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "my_new_name")), 
                                 (import ["p" = "scrutinee"] (vr "f"))]
            }),
            simple_ty_env.clone()),
        Ok(ast!("float")));
    
        
    // TODO: use this test when type errors aren't panics
        /*
    assert_eq!(synth_type(&ast!({ mtch.clone() ;
                "scrutinee" => (vr "b"),
                "p" => [@"arm" (vr "my_new_name"), (vr "unreachable")],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "my_new_name")), 
                                 (import ["p" = "scrutinee"] (vr "f"))]
            }),
            simple_ty_env.clone()),
        Err(())); */

    
}

#[test]
fn alg_eval() {
    let cse = make_core_syn_env();
    
    let mt_env = Assoc::new();
    let simple_env = assoc_n!("x" => val!(i 18), "w" => val!(i 99), "b" => val!(b false));
    
    /* Evaluate enum pattern */
    let enum_p = find_form(&cse, "pat", "enum_pat");
    
    assert_eq!(neg_eval(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_env.set(negative_ret_val, val!(enum "choice1", (i 9006), (b true)))),
        Ok(assoc_n!("abc" => val!(i 9006), "def" => val!(b true))));
            
    assert_eq!(neg_eval(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_env.set(negative_ret_val, val!(enum "choice0", (i 12321)))),
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
        Ok(val!(enum "choice1", (i 18), (b false))));
        
    /* Evaluate struct pattern */
    
    let struct_p = find_form(&cse, "pat", "struct_pat");
    assert_eq!(neg_eval(&ast!(
        { struct_p.clone() ;
            "component_name" => [@"c" "x", "y"],
            "component" => [@"c" (vr "xx"), (vr "yy")]
        }),
        mt_env.set(negative_ret_val,
                   Struct(assoc_n!("x" => val!(i 0), "y" => val!(b true))))),
        Ok(assoc_n!("xx" => val!(i 0), "yy" => val!(b true))));
    
    /* Evaluate match */
    
    let mtch = find_form(&cse, "expr", "match");
    
    assert_eq!(eval(&ast!({ mtch.clone() ;
                "scrutinee" => (vr "x"),
                "p" => [@"arm" (vr "my_new_name"), (vr "unreachable")],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "my_new_name")), 
                                 (import ["p" = "scrutinee"] (vr "x"))]
        }),
        simple_env.clone()),
        Ok(val!(i 18)));
    
}