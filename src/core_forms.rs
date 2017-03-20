/* This virtual machine kills cyber-fascists. */

#![allow(dead_code, non_upper_case_globals)]

/*
 * Core forms!
 * 
 * This is the definition of Unseemly, the bizarre boiled-down programming language.
 *
 * Unseemly programs have expressions and types (and probably kinds, too).
 */

use name::*;
use parse::{SynEnv, FormPat};
use parse::FormPat::*;
use form::{Form, simple_form, Positive, Negative};
use util::assoc::Assoc;
use ast::*;
use std::rc::Rc;
use ty::*;
use runtime::eval::*;
use beta::*;
use ast_walk::WalkRule::*;
use num::bigint::ToBigInt;
use core_type_forms::*; // type forms are kinda bulky

pub fn ast_to_atom(ast: &Ast) -> Name {
    match *ast { Atom(n) => n, _ => { panic!("internal error!") } }
}

/* 
 * A brief digression about types and syntax quotation...
 * Expressions are "positive", and are traversed leaf-to-root in an environment, producing a type.
 * Patterns are "negative", and are traversed root-to-leave from a type, producing an environment.
 * (`match` and `lambda` are examples of interactions between expressions and patterns.)
 * Syntax quotation and unquotation embeds expressions/patterns 
 *  (at a different phase, which matters suprisingly little)
 *  inside expressions/patterns.
 * 
 * This looks like:
 *                     pattern outside | expression outside      <-- (provides context)
 *                   --------------------------------------
 * pattern inside    | ok              | needs annotation
 * expression inside | bonus check     | ok
 *  
 * Examples of needed annotation: 
 * 
 *   optimize_pat '[{Pat<[List<[Int]<]<} cons a b]'  
 * In this case, we need to know the type of the syntax quote, 
 *  but the pattern wants to know its type so that it can tell us its environment.
 * 
 *   match stx { '[{Pat} 1 + 5 * ,[{Expr<[Nat]<} stx_num], ]' => ... }
 * In this case (looking at the expression interpolation),
 *  we need to know the type of the interpolated expression syntax (a pattern)
 *   in order to type-synthesize the arithmetic.
 *  
 * 
 * Examples of when we get to do a bonus typecheck:
 *  
 *   match stx { '[{Expr} f x]' => ... }
 * In this case, we can check that the type of the scrutinee
 *  (which is the type of the syntax quotation pattern)
 *   equals Expr<[ (whatever `f` returns) ]<.
 *   
 *   optimize_expr '[{Expr} match stx { ,[{Pat} my_pat], => ... } ]'
 * In this case (looking at the Pat interpolation),
 *  we can check that the type of the quoted scrutinee is the same as
 *   the type of `my_pat` (after peeling off its `Pat<[]<`).
 *
 * Note that it doesn't matter whether the boundary is a quotation or an unquotation!
 * Like I said, the phase doesn't matter much.
 */

// This form isn't part of any nt! Instead, it's inserted into nts by `quote`.

/// Generate an unquoting form.
fn unquote<Mode: ::ast_walk::WalkMode>(nt: Name, ctf: SynEnv, pos: bool) -> Rc<Form> {
    Rc::new(Form {
        name: n("unquote"), // maybe add the `nt` to the name?
        grammar: 
            if pos {
                form_pat!([(delim ",[", "[", /*]]*/ (named "body", (call "expr")))])             
            } else {
                form_pat!([(delim ",[", "[", /*]]*/ (named "body", (call "pat")))])
            },
        synth_type: 
            // imagine: ` '[{expr} .[a : int . ,[body], ]. ]' `
            if pos {
                Positive(
                    // suppose that this is an expr, and `body` has the type `expr <[string]<`:
                    cust_rc_box!( move | unquote_parts | {
                        let interpolate_type = try!(unquote_parts.get_res(&n("body")));
                        expect_node!( (interpolate_type.0 ; find_type(&ctf, "type_apply"))
                            apply_parts;
                            {
                                if ast_to_atom(apply_parts.get_leaf_or_panic(&n("type_name"))) != nt {
                                    panic!("Type error: tried to interpolate {} at a {} node", 
                                        interpolate_type, nt);
                                }
                                let args = apply_parts.get_rep_leaf_or_panic(&n("arg"));
                                if args.len() != 1 {
                                    panic!("Kind error: expected one argument, got {:?}", args)
                                }
                                Ok(Ty(args[0].clone()))
                })}))
            } else {
                Negative(
                    // suppose that this is a pat, 
                    // and the whole thing has type `expr <[ [int -> string] ]<`
                    cust_rc_box!( move | _unquote_parts | {
                        panic!("")
                    })
                )
            },
            
            // Also, let's suppose that we have something like:
            //   let some_pattern : pat <[int]< = ...
            //   let s = '[{pat} struct { a: ,[ some_pattern ],  b: b_var} ]'
            // ...what then?
        eval: // should be both
            Positive(cust_rc_box!( move | _unquote_parts | {
                panic!("");
            })),
        quasiquote: //should be both
            Positive(cust_rc_box!( move | _unquote_parts | {
                panic!("");
            })),
        relative_phase: Assoc::new()
    }
)}


/*
fn eval_quoted_stx(a: Ast, env: Assoc<Name, Value>) -> Ast {
    match a {
        Trivial | Atom(_) | VariableReference(_)
    }
}
*/
/// This is the Unseemly language.
pub fn make_core_syn_env() -> SynEnv {
    
    let ctf : SynEnv = make_core_syn_env_types();
    
    /* This seems to be necessary to get separate `Rc`s into the closures. */
    let ctf_0 = ctf.clone();
    let ctf_1 = ctf.clone();
    let ctf_2 = ctf.clone();
    let ctf_3 = ctf.clone();
    let ctf_4 = ctf.clone();
    let ctf_5 = ctf.clone();
    let ctf_6 = ctf.clone();
    let ctf_7 = ctf.clone();
    let ctf_8 = ctf.clone();
            
    // Unseemly expressions
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
                let lambda_type : Ty = 
                    ty!({ find_type(&ctf_0, "fn") ;
                         "param" => [* part_types =>("param") part_types :
                                       (, try!(part_types.get_res(&n("p_t"))).0)],
                         "ret" => (, try!(part_types.get_res(&n("body"))).0)});
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
        
        typed_form!("apply", /* function application*/
            [(named "rator", (call "expr")), 
             (star (named "rand", (call "expr")))],
            cust_rc_box!(move | part_types |
                expect_node!( (try!(part_types.get_res(&n("rator"))).0 ; 
                               find_type(&ctf_1, "fn"))
                    env;
                    {
                        for (input, expected) in env.get_rep_leaf_or_panic(&n("param")).iter().zip(
                            &try!(part_types.get_rep_res(&n("rand")))
                        ) {
                            // TODO: proper type comparison
                            if input != &&expected.0 { return Err(()); }
                        }
                    
                        Ok(Ty(env.get_leaf_or_panic(&n("ret")).clone()))
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
                        
                        ::ast_walk::walk::<::runtime::eval::Eval>(&clos.body,
                            &::ast_walk::LazyWalkReses::new(
                                clos.env.clone(), new_env_parts, part_values.this_form))
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
        typed_form!("match",
            [(lit "match"), (named "scrutinee", (call "expr")),
             (delim "{", "{", 
                 (star [(named "p", (call "pat")), (lit "=>"),
                        (named "arm", (import ["p" = "scrutinee"], (call "expr")))]))],
            /* Typesynth: */
            cust_rc_box!(move | part_types | {
                let mut res : Option<Ty> = None;
                for arm_part_types in part_types.march_parts(&[n("arm")]) {
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
                for arm_values in part_values.march_all(&[n("arm")]) {
                    match arm_values.get_res(&n("arm")) {
                        Ok(res) => { return Ok(res); }
                        Err(()) => { /* try the next one */ }
                    }
                }
                panic!("No arms matched! This ought to be a type error, but isn't.");
            })
        ),
        /* Note that we inconveniently require the user to specify the type.
           "real" languages infer the type from the (required-to-be-unique)
           component name. */
        typed_form!("enum_expr",
            [(named "name", aat), 
             (delim "(", "(", /*))*/ [(star (named "component", (call "expr")))]),
             (lit ":"), (named "t", (call "type"))],
            /* Typesynth: */
            cust_rc_box!( move | part_types | {
                let res : Ty = try!(part_types.get_res(&n("t")));
                expect_node!( (res.0 ; find_type(&ctf_2, "enum"))
                    enum_type_parts; 
                    {
                        for enum_type_part in enum_type_parts.march_all(&[n("name")]) {
                            if &part_types.get_term(&n("name")) 
                                    != enum_type_part.get_leaf_or_panic(&n("name")) {
                                continue; // not the right arm
                            }
                            
                            let component_types : Vec<Ty> = 
                                enum_type_part.get_rep_leaf_or_panic(&n("component"))
                                    .iter().map(|a| Ty((*a).clone())).collect();
                                    
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
                Ok(ty!({ find_type(&ctf_3, "struct") ;
                    "component_name" => (@"c" ,seq part_types.get_rep_term(&n("component_name"))),
                    "component" => (@"c" ,seq try!(part_types.get_rep_res(&n("component")))
                        .into_iter().map(|c : Ty| c.0))
                }))
            }),
            cust_rc_box!( move | part_values | {
                let mut res = Assoc::new();
                
                for component_parts in part_values.march_parts(&[n("component")]) {
                    res = res.set(ast_to_atom(&component_parts.get_term(&n("component_name"))),
                                  try!(component_parts.get_res(&n("component"))));
                }
                
                Ok(Struct(res))
            })),

        /* e.g.
         * let_type
         *   pair = mu lhs rhs. {l: lhs, r: rhs}
         *   point = pair <[int, int]<
         * in ...
         */
        typed_form!("let_type",
            [(lit "let_type"),
             (named "type_kind_stx", (anyways "*")),
             (import [* ["type_name" = "type_def"]], // put `pair` and `point` in type env
                 (star [(named "type_name", aat), (lit "="), (named "type_def", (call "type"))])),
             (lit "in"),
             (named "body", (import [* ["type_name" = "type_def"]], (call "expr")))],
            Body(n("body")),
            Body(n("body"))),
            
        /* e.g. where List = ∀ X. μ List. enum { Nil(), Cons(X, List<[X]<) }
         * '[x : List <[X]<  . match (unfold x) ... ]'
         * (unfold is needed because `match` wants an `enum`, not a `μ`)
         * Exposes the inside of a μ type by performing one level of substitution.
         */
        typed_form!("unfold",
            [(lit "unfold"), (named "body", (call "expr"))],
            cust_rc_box!( move |unfold_parts| {
                // TODO: this "evaluates" types twice; once in `get_res` and once in `synth_type`
                // It shouldn't be necessary, and it's probably quadratic.
                // Maybe this points to a weakness in the LiteralLike approach to traversing types?
                let mu_typed = try!(unfold_parts.get_res(&n("body")));

                // (also, the fact that we're pulling out a piece of a `Ty` and re-synthing it
                //   feels funny)
                expect_node!( (mu_typed.0.clone() ; find_type(&ctf_4, "mu_type") ) 
                    mu_parts;
                    {
                        synth_type(
                            mu_parts.get_leaf_or_panic(&n("body")), 
                            unfold_parts.env.set(
                                ast_to_atom(mu_parts.get_leaf_or_panic(&n("param"))),
                                // Maybe this ought to be a lookup of `param` in `ty_env`?
                                // Is there ever a difference?
                                mu_typed))
                    })
            }),
            Body(n("body"))),
        
        /* e.g. where List = ∀ X. μ List. enum { Nil(), Cons(X, List<[X]<) }
         * '[x : List <[X]<  ...]' fold Nil() : List<[X]<
         */
        typed_form!("fold",
            [(lit "fold"), (named "body", (call "expr")), (lit ":"), (named "t", (call "type"))],
            cust_rc_box!( move |fold_parts| {
                let goal_type = try!(fold_parts.get_res(&n("t")));
                // TODO: I can't figure out how to pull this out into a function 
                //  to invoke both here and above, since `mu_type_0` needs cloning...
                let folded_goal = expect_node!( (goal_type.0.clone() ; find_type(&ctf_5, "mu_type")) 
                    mu_parts;
                    {
                        try!(synth_type(
                            mu_parts.get_leaf_or_panic(&n("body")), 
                            fold_parts.env.set(
                                ast_to_atom(mu_parts.get_leaf_or_panic(&n("param"))),
                                // Maybe this ought to be a lookup of `param` in `ty_env`?
                                // Is there ever a difference?
                                goal_type.clone())))
                    });

                // TODO: do proper type comparison
                if folded_goal != try!(fold_parts.get_res(&n("body"))) {
                    panic!("Type error: {:?} ≠ {:?}\n", folded_goal, try!(fold_parts.get_res(&n("body"))));
                }
                Ok(goal_type)
            }),
            Body(n("body"))),


        typed_form!("quote",
            [(delim "`[", "[", /*]]*/ [/* TODO, maybe after the parser is improved */])],
            cust_rc_box!( move | quote_parts | {
                //TODO put variables in phases!!! !!!!! !!!!!!!!!!!!
                Ok(ty!({ find_type(&ctf_8, "type_apply") ;
                    "type_name" => (, quote_parts.get_term(&n("nt")) ),
                    "arg" => [ (, try!(quote_parts.get_res(&n("body"))).0 )]
                }))
            }),
            cust_rc_box!( move | _quote_values | {
                panic!("TODO")
                // Traverse the body, form 
            })
        )

        // The first use for syntax quotes will be in macro definitions.
        // But we will someday need them as expressions.                    
    ];
    
    
    let main_pat_forms = forms_to_form_pat![
        negative_typed_form!("enum_pat",
            [(named "name", aat), 
             (delim "(", "(", /*))*/ [(star (named "component", (call "pat")))])],
            /* (Negatively) Typecheck: */
            cust_rc_box!( move | part_types |
                expect_node!( (part_types.context_elt().0 ; find_type(&ctf_6, "enum"))
                    enum_type_parts;
                    {
                        for enum_type_part in enum_type_parts.march_all(&[n("name")]) {
                        
                            if &part_types.get_term(&n("name")) 
                                    != enum_type_part.get_leaf_or_panic(&n("name")) {
                                continue; // not the right arm
                            }
                        
                            let component_types : Vec<Ty> = 
                                enum_type_part.get_rep_leaf_or_panic(&n("component"))
                                    .iter().map(|a| Ty((*a).clone())).collect();
                           
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
                match *part_values.context_elt() /* : Value */ {
                    Enum(ref name, ref elts) => {
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
                expect_node!( (part_types.context_elt().0 ; find_type(&ctf_7, "struct"))
                    struct_type_parts;
                    {
                        let mut res = Assoc::new();
                        for component_ctx in part_types.march_parts(&[n("component")]) {
                            let mut component_found = false;
                            for struct_type_part 
                                    in struct_type_parts.march_all(&[n("component")]) {
                                if &component_ctx.get_term(&n("component_name"))
                                    != struct_type_part.get_leaf_or_panic(&n("component_name")) {
                                    continue;
                                }
                                component_found = true;
                                res = res.set_assoc(
                                    &try!(component_ctx
                                        .with_context(
                                            Ty(struct_type_part.get_leaf_or_panic(&n("component"))
                                                .clone()))
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
                match *part_values.context_elt() {
                    Struct(ref contents) => {
                        let mut res = Assoc::new();
                        
                        for component_ctx in part_values.march_parts(&[n("component")]) {
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
        "expr" => Biased(Box::new(main_expr_forms), Box::new(VarRef))
    ).set_assoc(&ctf) /* throw in the types! */
}






/**
 * Mostly for testing purposes, this looks up forms by name.
 * In the "real world", programmers look up forms by syntax, using a parser. 
 */
pub fn find_form(se: &SynEnv, nt: &str, form_name: &str)
         -> Rc<Form> {             

    fn find_form_rec(f: &FormPat, form_name: &str) -> Option<Rc<Form>> {
        match *f {
            Scope(ref f) => {
                if f.name.is(form_name) {
                    Some(f.clone())
                } else {
                    None
                }
            }
            Alt(ref vf) => {
                for f in vf {
                    let res = find_form_rec(f, form_name);
                    if res.is_some() { return res; }
                }
                None
            }
            Biased(ref lhs, ref rhs) => {
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

fn find_type(se: &SynEnv, form_name: &str) -> Rc<Form> {
    find_form(se, "type", form_name)
}

thread_local! {
    pub static core_forms: SynEnv = make_core_syn_env();
}

pub fn find_core_form(nt: &str, name: &str) -> Rc<Form> {
    core_forms.with(|cf| find_form(cf, nt, name))
}



/* TODO: this test is broken by identifiers-as-a-valid-type. Why? All other possible parses
         should override identifiers.
#[test]
fn form_grammar() {
    let cse = make_core_syn_env();
    assert_eq!(parse(&form_pat!((call "type")),
                     cse.clone(),
                     &tokens!([""; "ident" "->" "ident"])),
               Ok(ast!({ find_form(&cse, "type", "fn"); 
                   ["ret" => {find_form(&cse, "type", "ident") ; []},
                    "param" => [{find_form(&cse, "type", "ident") ; []}]]})));
    
}*/


#[test]
fn form_expect_node() {
    let ast = ast!({ find_core_form("expr", "apply"); 
        ["rand" => [(vr "f")], "rator" => (vr "x")]});
    let _ : Result<(), ()> = expect_node!( 
        ( ast ; find_core_form("expr", "apply")) env; //expect_f = "rand", expect_x = "rator";
        {
            assert_eq!(env.get_rep_leaf_or_panic(&n("rand")), vec![&ast!((vr "f"))]);
            assert_eq!(env.get_leaf_or_panic(&n("rator")), &ast!((vr "x")));
            Ok(())
        });
}

#[test]
fn form_type() {
    let simple_ty_env = assoc_n!(
        "x" => ty!({ find_core_form("type", "int") ; }),
        "b" => ty!({ find_core_form("type", "bool") ; }));
    
    let lam = find_core_form("expr", "lambda");
    let fun = find_core_form("type", "fn");

    
    assert_eq!(synth_type(&ast!( (vr "x") ), simple_ty_env.clone()),
               Ok(ty!( { find_core_form("type", "int") ; })));
    
    assert_eq!(synth_type(&ast!( 
        { lam.clone() ;
            "param" => [@"p" "y"], 
            "p_t" => [@"p" { find_core_form("type", "nat") ; }],
            "body" => (import [* [ "param" : "p_t" ]] (vr "x"))}),
        simple_ty_env.clone()),
        Ok(ty!({ fun.clone() ; 
            "param" => [{ find_core_form("type", "nat") ; }], 
            "ret" => { find_core_form("type", "int") ; }})));
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
        "x" => ty!("integer"), "b" => ty!("bool"), "f" => ty!("float"));

    /* Typecheck enum pattern */
    let enum_p = find_form(&cse, "pat", "enum_pat");
    let enum_t = find_form(&cse, "type", "enum");
    
    let my_enum = ty!({ enum_t.clone() ;
        "name" => [@"c" "Adams", "Jefferson", "Burr"],
        "component" => [@"c" ["integer"], ["integer", "bool"], ["float", "float"]]
    });
        
    assert_eq!(neg_synth_type(&ast!(
        { enum_p.clone() ; 
            "name" => "Jefferson",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_ty_env.set(negative_ret_val(), my_enum.clone())),
        Ok(Assoc::new().set(n("abc"), ty!("integer")).set(n("def"), ty!("bool"))));
    
    /* Typecheck enum expression */
    let enum_e = find_form(&cse, "expr", "enum_expr");
    
    assert_eq!(synth_type(&ast!(
        { enum_e.clone() ;
            "name" => "Jefferson",
            "component" => [(vr "x"), (vr "b")],
            "t" => (, my_enum.0.clone())
        }),
        simple_ty_env.clone()),
        Ok(my_enum));
        
        
    /* Typecheck struct pattern */    
    
    let struct_p = find_form(&cse, "pat", "struct_pat");
    let struct_t = find_form(&cse, "type", "struct");
    
    let my_struct = ty!({ struct_t.clone() ;
        "component_name" => [@"c" "x", "y"],
        "component" => [@"c" "integer", "float"]
    });
    
    assert_eq!(neg_synth_type(&ast!(
            { struct_p.clone() ;
                "component_name" => [@"c" "y", "x"],
                "component" => [@"c" (vr "yy"), (vr "xx")]
            }),
            mt_ty_env.set(negative_ret_val(), my_struct.clone())),
        Ok(assoc_n!("yy" => ty!("float"), "xx" => ty!("integer"))));
        
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
        Ok(ty!("float")));
    
        
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
        mt_env.set(negative_ret_val(), val!(enum "choice1", (i 9006), (b true)))),
        Ok(assoc_n!("abc" => val!(i 9006), "def" => val!(b true))));
            
    assert_eq!(neg_eval(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_env.set(negative_ret_val(), val!(enum "choice0", (i 12321)))),
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
        mt_env.set(negative_ret_val(),
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


#[test]
fn recursive_types() {
    fn tbn(nm: &'static str) -> Ty {
        ty!( { find_core_form("type", "type_by_name") ; "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }
    
    let int_list_ty = ty!( { find_core_form("type", "mu_type") ; 
        "param" => "int_list",
        "body" => { find_core_form("type", "enum") ; 
            "name" => [@"c" "Nil", "Cons"],
            "component" => [@"c" [], ["integer", (, tbn("int_list").0)]]}});
            
    let ty_env = assoc_n!(
        "int_list" => int_list_ty.clone(),  // this is a type definition...
        "il_direct" => int_list_ty.clone()  // ...and this is a value with a type
        // TODO: ... distinguish between these in the environment! Is the difference ... kind?

        // We should never have `tbn`s in the environment unless "protected" by a μ.
        // TODO: enforce that:
        //"il_named" => tbn("int_list")
    );
    
    // folding an unfolded thing should give us back the same thing
    assert_eq!(synth_type(
        &ast!( { find_core_form("expr", "fold") ;
            "body" => { find_core_form("expr", "unfold") ; 
                "body" => (vr "il_direct") },
            "t" => (, int_list_ty.0.clone())}),
        ty_env.clone()),
        Ok(int_list_ty.clone()));
    
    // Unfold a type and then match it
    assert_eq!(synth_type(
        &ast!( { find_core_form("expr", "match") ; 
            "scrutinee" => { find_core_form("expr", "unfold") ; "body" => (vr "il_direct") },
            "p" => [@"arm" { find_core_form("pat", "enum_pat") ;
                "name" => "Cons",
                "component" => [(vr "car"), (vr "cdr")],
                "t" => (, tbn("int_list").0)            
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "car"))]
        }),
        ty_env.clone()),
        Ok(ty!("integer"))
    );
    /*
    // When type errors aren't panics, uncomment this (test that missing an unfold fails)
    assert_eq!(synth_type(
        &ast!( { find_core_form("expr", "match") ; 
            "scrutinee" =>  (vr "il_direct") ,
            "p" => [@"arm" { find_core_form("pat", "enum_pat") ;
                "name" => "Cons",
                "component" => [(vr "car"), (vr "cdr")],
                "t" => (, tbn("int_list"))            
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "car"))]
        }),
        ty_env.clone()),
        Err(...)
    );*/
}