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

// TODO: we should validate that types don't have unexpected names in them 
// (i.e. `∀ X. List<X>` is okay, but `X` is not a type; it's just syntax)
#[derive(Clone, PartialEq)]
pub struct Ty(pub Ast);

impl ::std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "[TYPE {:?}]", self.0)
    }
}

// this kinda belongs in core_forms.rs
impl ::std::fmt::Display for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use core_forms::{find_core_form, ast_to_atom};
        match self.0 {
            // Not used, right? Maybe it should be...
            //VariableReference(ref n) => { write!(f, "{}", n) },
            Node(ref form, ref env) => {
                if form == &find_core_form("type", "ident") {
                    write!(f, "ident")
                } else if form == &find_core_form("type", "int") {
                    write!(f, "int")                    
                } else if form == &find_core_form("type", "nat") {
                    write!(f, "nat")                    
                } else if form == &find_core_form("type", "float") {
                    write!(f, "float")                    
                } else if form == &find_core_form("type", "bool") {
                    write!(f, "bool")                    
                } else if form == &find_core_form("type", "fn") {
                    try!(write!(f, "["));
                    let mut first = true;
                    for p in env.get_rep_leaf_or_panic(&n("param")) {
                        // TODO: use commas in the grammar
                        if !first { try!(write!(f, " ")); } first = false;
                        
                        try!(write!(f, "{}", Ty(p.clone())));
                    }
                    write!(f, " -> {}]", Ty(env.get_leaf_or_panic(&n("ret")).clone()))
                } else if form == &find_core_form("type", "enum") {
                    try!(write!(f, "enum{{"));
                    for subenv in env.march_all(&[n("name")]) {
                        try!(write!(f, " {}("/*)*/, 
                            ast_to_atom(&subenv.get_leaf_or_panic(&n("name")))));
                        if let Some(comps) = subenv.get_rep_leaf(&n("component")) {
                            let mut first = true;
                            for comp in comps {
                                if !first { try!(write!(f, " "))} first = false;
                                
                                try!(write!(f, "{}", Ty(comp.clone())));
                            }
                        }
                        try!(write!(f, /*(*/")"));
                    }
                    write!(f, "}}")
                } else if form == &find_core_form("type", "struct") {
                    try!(write!(f, "struct{{"));
                    for subenv in env.march_all(&[n("component_name")]) {
                        try!(write!(f, " {}: {}", 
                            ast_to_atom(&subenv.get_leaf_or_panic(&n("component_name"))),
                            Ty(subenv.get_leaf_or_panic(&n("component")).clone())));
                    }
                    write!(f, " }}")
                } else if form == &find_core_form("type", "forall_type") {
                    // This isn't the input syntax... maybe it should be when our parser is better
                    try!(write!(f, "∀"));
                    if let Some(args) = env.get_rep_leaf(&n("param")) {
                        for name in args {
                            try!(write!(f, " {}", ast_to_atom(name)));
                        }
                    }
                    write!(f, ". {}", Ty(env.get_leaf_or_panic(&n("body")).clone()))
                } else if form == &find_core_form("type", "mu_type") {
                    write!(f, "μ {}. {}", 
                        ast_to_atom(env.get_leaf_or_panic(&n("param"))),
                        Ty(env.get_leaf_or_panic(&n("body")).clone()))
                } else if form == &find_core_form("type", "type_by_name") {
                    write!(f, "{}", ast_to_atom(env.get_leaf_or_panic(&n("name"))))
                } else if form == &find_core_form("type", "type_apply") {
                    try!(write!(f, "{}<[", ast_to_atom(env.get_leaf_or_panic(&n("type_name")))));
                    let mut first = true;
                    if let Some(args) = env.get_rep_leaf(&n("arg")) {
                        for arg in args {
                            if !first { try!(write!(f, " ")); }
                            first = false;
                            try!(write!(f, "{}", Ty(arg.clone())));
                        }
                    }
                    write!(f, "]<")
                } else {
                    panic!("{:?} is not a well-formed type", self.0);
                }
            }
            _ => { panic!("{:?} is not a well-formed type", self.0); }
        }
    }
}

impl ::runtime::reify::Reifiable for Ty {
    fn ty() -> Ast { Ast::ty() }

    fn ty_name() -> Name { n("Type") }
    
    fn ty_invocation() -> Ast { Ast::ty_invocation() }
    
    fn reify(&self) -> ::runtime::eval::Value { self.0.reify() }
    
    fn reflect(v: &::runtime::eval::Value) -> Self { Ty(Ast::reflect(v))}
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct SynthesizeType {}
}

impl WalkMode for SynthesizeType {
    //TODO: these should be a newtype to prevent bugs
    type Out = Ty;
    type Elt = Ty;
    
    type Negative = NegativeSynthesizeType;
    
    fn get_walk_rule(f: &Form) -> &WalkRule<Self> {
        f.synth_type.pos()
    }
    
    fn automatically_extend_env() -> bool { true }
    
    fn ast_to_elt(a: Ast, _: &LazyWalkReses<Self>) -> Self::Elt { Ty(a) }
    
    fn ast_to_out(a: Ast) -> Self::Out { Ty(a) }
    
    fn out_to_elt(o: Self::Out) -> Self::Elt { o }
    
    fn out_to_ast(o: Self::Out) -> Ast { o.0 }
    
    fn var_to_out(n: &Name, env: &Assoc<Name, Self::Elt>) -> Result<Self::Out, ()> {
        ::ast_walk::var_lookup(n, env)
    }
    
    fn positive() -> bool { true }
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct NegativeSynthesizeType {} 
}

impl WalkMode for NegativeSynthesizeType {
    type Out = Assoc<Name, Ty>;
    type Elt = Ty;
    
    type Negative = SynthesizeType;
    
    fn get_walk_rule(f: &Form) -> &WalkRule<Self> {
        f.synth_type.neg()
    }
    
    fn automatically_extend_env() -> bool { true }
    
    fn ast_to_elt(a: Ast, _: &LazyWalkReses<Self>) -> Self::Elt { Ty(a) }
    
    fn var_to_out(n: &Name, env: &Assoc<Name, Self::Elt>) -> Result<Self::Out, ()> {
        ::ast_walk::var_bind(n, env)
    }
    
    fn out_to_env(o: Self::Out) -> Assoc<Name, Self::Elt> { o }
    fn env_to_out(e: Assoc<Name, Self::Elt>) -> Self::Out { e }
    
    fn positive() -> bool { false }
}



pub fn synth_type_top(expr: &Ast) ->  Result<Ty, ()> {
    walk::<SynthesizeType>(expr, &LazyWalkReses::new_wrapper(Assoc::new()))
}

pub fn synth_type(expr: &Ast, env: Assoc<Name, Ty>) -> Result<Ty, ()> {
    walk::<SynthesizeType>(expr, &LazyWalkReses::new_wrapper(env))
}

pub fn neg_synth_type(pat: &Ast, env: Assoc<Name, Ty>)
        -> Result<Assoc<Name, Ty>, ()> {
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