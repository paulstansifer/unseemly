/*

Type synthesis is a recursive traversal of an abstract syntax tree. 
It is compositional,
 except for binding, which is indicated by ExtendTypeEnv nodes. 
These nodes  may depend on 
 the result of synthesizing sibling AST nodes
 or the actual value of AST nodes corresponding to types 
  (i.e., type annotations).




*/

use beta::*;
use parse::FormPat::AnyToken; // for making simple forms for testing
use ast_walk::{walk, LazyWalkReses, WalkMode, WalkRule};
use ast_walk::WalkRule::*;
use form::Form;
use util::assoc::Assoc;
use util::mbe::EnvMBE;
use ast::*;

// for macros
use name::*;
use std::rc::Rc;


// maybe should do this, to be clear
// pub type Type<'t> = Ast<'t>;

#[derive(Clone, Copy, Debug)]
pub struct SynthesizeType {}

impl<'t> WalkMode<'t> for SynthesizeType {
    type Out = Ast<'t>;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        &f.synth_type
    }
    
    fn automatically_extend_env() -> bool { true }
    
    fn ast_to_out(a: Ast<'t>) -> Ast<'t> { a }
}

pub fn synth_type_top<'t>(expr: &Ast<'t>) ->  Result<Ast<'t>, ()> {
    walk(expr, SynthesizeType{}, 
         Assoc::new(), &LazyWalkReses::new(SynthesizeType{}, Assoc::new(), EnvMBE::new()))
}

pub fn synth_type<'t>(expr: &Ast<'t>, env: Assoc<Name<'t>, Ast<'t>>) -> Result<Ast<'t>, ()> {
    walk(expr, SynthesizeType{}, 
         env, &LazyWalkReses::new(SynthesizeType{}, Assoc::new(), EnvMBE::new()))
}


#[test]
fn test_type_synth() {
    let mt_ty_env = Assoc::new();
    let simple_ty_env = mt_ty_env.set(n("x"), ast!("integer"));
    
    let body = basic_typed_form!(at, Body(n("body")), NotWalked);
    let untypeable = basic_typed_form!(at, NotWalked, NotWalked);
    
    assert_eq!(synth_type(&ast!((vr "x")), 
               simple_ty_env.clone()),
               Ok(ast!("integer")));
               
    assert_eq!(synth_type(&ast!({body.clone() ; 
                                     ["irrelevant" => {untypeable.clone() ; },
                                      "body" => (vr "x")]}),
                          simple_ty_env.clone()),
               Ok(ast!("integer")));

    assert_eq!(synth_type(&ast!({body.clone() ;
                                     "type_of_new_var" => "integer",
                                     "new_var" => "y",
                                     "body" => (import ["new_var" : "type_of_new_var"] (vr "y"))}),
                          simple_ty_env.clone()),
               Ok(ast!("integer")));
               
    assert_eq!(synth_type(&ast!(
            {basic_typed_form!(at, Custom(Box::new(|_| Ok(ast!("string")))),
                               NotWalked) ; []}),
            simple_ty_env.clone()),
        Ok(ast!("string")));
}