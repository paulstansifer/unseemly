/*
Type synthesis is a recursive traversal of an abstract syntax tree. 
It is compositional,
 except for binding, which is indicated by ExtendTypeEnv nodes. 
These nodes may depend on
 the result of type-synthesizing sibling AST nodes
 or the actual value of AST nodes corresponding to types 
  (i.e., type annotations).
*/

use beta::*;
use ast_walk::{walk, LazyWalkReses, WalkMode, WalkRule};
use ast_walk::WalkRule::*;
use form::Form;
use util::assoc::Assoc;
use ast::*;

// for macros
use name::*;
use std::rc::Rc;


// maybe should do this, to be clear
// pub type Type<'t> = Ast<'t>;

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct SynthesizeType {}
}

impl<'t> WalkMode<'t> for SynthesizeType {
    type Out = Ast<'t>;
    type Elt = Ast<'t>;
    
    type Negative = NegativeSynthesizeType;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        f.synth_type.pos()
    }
    
    fn automatically_extend_env() -> bool { true }
    
    fn ast_to_elt(a: Ast<'t>, _: &LazyWalkReses<'t, Self>) -> Self::Elt { a }
    
    fn out_to_elt(o: Self::Out) -> Self::Elt { o }
    
    fn var_to_out(n: &Name<'t>, env: &Assoc<Name<'t>, Self::Elt>) -> Result<Self::Out, ()> {
        ::ast_walk::var_lookup(n, env)
    }
    
    fn positive() -> bool { true }
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct NegativeSynthesizeType {} 
}

impl<'t> WalkMode<'t> for NegativeSynthesizeType {
    type Out = Assoc<Name<'t>, Ast<'t>>;
    type Elt = Ast<'t>;
    
    type Negative = SynthesizeType;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        &f.synth_type.neg()
    }
    
    fn automatically_extend_env() -> bool { true }
    
    fn ast_to_elt(a: Ast<'t>, _: &LazyWalkReses<'t, Self>) -> Self::Elt { a }
    
    fn var_to_out(n: &Name<'t>, env: &Assoc<Name<'t>, Self::Elt>) -> Result<Self::Out, ()> {
        ::ast_walk::var_bind(n, env)
    }
    
    fn out_to_env(o: Self::Out) -> Assoc<Name<'t>, Self::Elt> { o }
    
    fn positive() -> bool { false }
}



pub fn synth_type_top<'t>(expr: &Ast<'t>) ->  Result<Ast<'t>, ()> {
    walk::<SynthesizeType>(expr, &LazyWalkReses::new(Assoc::new(), EnvMBE::new()))
}

pub fn synth_type<'t>(expr: &Ast<'t>, env: Assoc<Name<'t>, Ast<'t>>) -> Result<Ast<'t>, ()> {
    walk::<SynthesizeType>(expr, &LazyWalkReses::new(env, EnvMBE::new()))
}

pub fn neg_synth_type<'t>(pat: &Ast<'t>, env: Assoc<Name<'t>, Ast<'t>>)
        -> Result<Assoc<Name<'t>, Ast<'t>>, ()> {
    walk::<NegativeSynthesizeType>(pat, &LazyWalkReses::new(env, EnvMBE::new()))
}


#[test]
fn basic_type_synth() {
    let mt_ty_env = Assoc::new();
    let simple_ty_env = mt_ty_env.set(n("x"), ast!("integer"));
    
    let body = basic_typed_form!(at, Body(n("body")), NotWalked);
    let untypeable = basic_typed_form!(at, NotWalked, NotWalked);
    
    assert_eq!(synth_type(&ast!((vr "x")), simple_ty_env.clone()),
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
            {basic_typed_form!(at, Custom(Rc::new(Box::new(|_| Ok(ast!("string"))))),
                               NotWalked) ; []}),
            simple_ty_env.clone()),
        Ok(ast!("string")));
}