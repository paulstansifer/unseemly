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


#[derive(Clone, PartialEq)]
pub struct Ty<'t>(pub Ast<'t>);

impl<'t> ::std::fmt::Debug for Ty<'t> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "[TYPE {:?}]", self.0)
    }
}

impl<'t> ::runtime::reify::Reifiable<'t> for Ty<'t> {
    // TODO: this definitely will need to be transparent
    fn ty() -> Ast<'static> { ast!("type") }
    
    fn reify(&self) -> ::runtime::eval::Value<'t> { self.0.reify() }
    
    fn reflect(v: &::runtime::eval::Value<'t>) -> Self { Ty(Ast::<'t>::reflect(v))}
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct SynthesizeType {}
}

impl<'t> WalkMode<'t> for SynthesizeType {
    //TODO: these should be a newtype to prevent bugs
    type Out = Ty<'t>;
    type Elt = Ty<'t>;
    
    type Negative = NegativeSynthesizeType;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        f.synth_type.pos()
    }
    
    fn automatically_extend_env() -> bool { true }
    
    fn ast_to_elt(a: Ast<'t>, _: &LazyWalkReses<'t, Self>) -> Self::Elt { Ty(a) }
    
    fn ast_to_out(a: Ast<'t>) -> Self::Out { Ty(a) }
    
    fn out_to_elt(o: Self::Out) -> Self::Elt { o }
    
    fn out_to_ast(o: Self::Out) -> Ast<'t> { o.0 }
    
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
    type Out = Assoc<Name<'t>, Ty<'t>>;
    type Elt = Ty<'t>;
    
    type Negative = SynthesizeType;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        &f.synth_type.neg()
    }
    
    fn automatically_extend_env() -> bool { true }
    
    fn ast_to_elt(a: Ast<'t>, _: &LazyWalkReses<'t, Self>) -> Self::Elt { Ty(a) }
    
    fn var_to_out(n: &Name<'t>, env: &Assoc<Name<'t>, Self::Elt>) -> Result<Self::Out, ()> {
        ::ast_walk::var_bind(n, env)
    }
    
    fn out_to_env(o: Self::Out) -> Assoc<Name<'t>, Self::Elt> { o }
    
    fn positive() -> bool { false }
}



pub fn synth_type_top<'t>(expr: &Ast<'t>) ->  Result<Ty<'t>, ()> {
    walk::<SynthesizeType>(expr, &LazyWalkReses::new_wrapper(Assoc::new()))
}

pub fn synth_type<'t>(expr: &Ast<'t>, env: Assoc<Name<'t>, Ty<'t>>) -> Result<Ty<'t>, ()> {
    walk::<SynthesizeType>(expr, &LazyWalkReses::new_wrapper(env))
}

pub fn neg_synth_type<'t>(pat: &Ast<'t>, env: Assoc<Name<'t>, Ty<'t>>)
        -> Result<Assoc<Name<'t>, Ty<'t>>, ()> {
    walk::<NegativeSynthesizeType>(pat, &LazyWalkReses::new_wrapper(env))
}


#[test]
fn basic_type_synth() {
    let mt_ty_env = Assoc::new();
    let int_ty = ty!({ ::core_forms::find_core_form("type", "int") ; });
    let bool_ty = ty!({ ::core_forms::find_core_form("type", "bool") ; });
    
    let simple_ty_env = mt_ty_env.set(n("x"), int_ty.clone());
    
    let body = basic_typed_form!(at, Body(n("body")), NotWalked);
    let untypeable = basic_typed_form!(at, NotWalked, NotWalked);
    
    assert_eq!(synth_type(&ast!((vr "x")), simple_ty_env.clone()),
               Ok(int_ty.clone()));
               
    assert_eq!(synth_type(&ast!({body.clone() ; 
                                     ["irrelevant" => {untypeable.clone() ; },
                                      "body" => (vr "x")]}),
                          simple_ty_env.clone()),
               Ok(int_ty.clone()));

    assert_eq!(synth_type(&ast!({body.clone() ;
                                     "type_of_new_var" => (, int_ty.0.clone()),
                                     "new_var" => "y",
                                     "body" => (import ["new_var" : "type_of_new_var"] (vr "y"))}),
                          simple_ty_env.clone()),
               Ok(int_ty.clone()));
               
    assert_eq!(synth_type(
        &ast!(
            {basic_typed_form!(
                at, 
                Custom(Rc::new(Box::new(
                    |_| Ok(ty!({ ::core_forms::find_core_form("type", "bool") ; }))))),
                NotWalked) ; []}),
            simple_ty_env.clone()),
        Ok(bool_ty.clone()));
}