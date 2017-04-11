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
use util::mbe::EnvMBE;

// for macros
use name::*;
use std::rc::Rc;

/*
Suppose that we are in typechecking, and we want to know if `∀ T.…` is a function type. 
We need to peel off the the ∀, but we also need to make sure that, 
 if there are multiple references to T on the RHS, we constain them
  to all be the same type.
What to do?
Whenever we destructure a type, if it's
  *  `∀ T.…`, then we peel off the ∀, and note in the environment that `T` is underdetermined
  *  underdetermined, we determine it to be be the right atomic type or the right structure...
       ...and fill that structure with `∀ G. G` (note: be hygenic, hopefully automatically)
(Note that destructuring `∀ T. T` needs to hit both of these cases.)

Okay, but what if we want to use <underdetermined> as *part* of a type (e.g. `.[a:int . (error)].`)
We need turn it into `∀ G. G`.

*/

// TODO: we should validate that types don't have unexpected names in them
// (i.e. `∀ X. List<X>` is okay, but `X` is not a type; it's just syntax)
#[derive(PartialEq)]
// pub enum Ty {
//     ConcreteType(Ast),
//     Param(std::cell::RefCell<Ast>)
// }
// `None` means abstract, `Some` means concrete
pub struct Ty(pub ::std::cell::RefCell<Option<Ast>>);

impl ::std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "[TYPE {:?}]", self.0)
    }
}

impl Clone for Ty {
    fn clone(&self) -> Ty {
        match *self.0.borrow() {
            Some(ref a) => Ty::new(a.clone()),
            None => panic!("Turns out `Ty` needs an `Rc` around the `RefCell` to be correct.")
        }
    }
}

impl Ty {
    pub fn new(a: Ast) -> Ty {
        Ty(::std::cell::RefCell::new(Some(a)))
    }
    pub fn new_underdetermined() -> Ty {
        Ty(::std::cell::RefCell::new(None))
    }
    pub fn concrete(&self) -> Ast {
        match *self.0.borrow() {
            Some(ref a) => { return a.clone(); },
            None => {}
        }
        // Fix the most arbitrary type, `∀ U. U`:
        *self.0.borrow_mut() = Some(ast!({ "type" "forall_type" :
            "param" => ["underdetermined"],
            "body" => 
                { "type" "type_by_name" : "name" => "underdetermined" }}));
                
        return self.concrete(); // Now it'll be concrete!
    }
    
    pub fn destructure(&self, expected_form: Rc<Form>) -> Result<EnvMBE<Ast>, TypeError> {
        match *self.0.borrow() {
            Some(Node(ref f, ref env)) => {
                if f == &expected_form {
                    return Ok(env.clone());
                } 
                ty_err!(UnableToDestructure(self.clone(), expected_form.name) at Trivial /*TODO*/);
            }
            Some(_) => {
                ty_err!(UnableToDestructure(self.clone(), expected_form.name) at Trivial /*TODO*/);
            }
            None => {}
        }
        let _generic_environment : EnvMBE<Ast> = panic!("TODO");
        // cloning this environment is expensive... but I'm not sure how to avoid it
        //*self.0.borrow_mut() = Some(Node(expected_form, generic_environment.clone()));
        //return Ok(generic_environment);
    }
    
}

// this kinda belongs in core_forms.rs
impl ::std::fmt::Display for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use core_forms::{find_core_form, ast_to_atom};
        match *self.0.borrow() {
            None => { write!(f, "<underdetermined>")}
            // Not used, right? Maybe it should be...
            // Some(VariableReference(ref n)) => { write!(f, "{}", n) },
            Some(Node(ref form, ref env)) => {
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
                        
                        try!(write!(f, "{}", Ty::new(p.clone())));
                    }
                    write!(f, " -> {}]", Ty::new(env.get_leaf_or_panic(&n("ret")).clone()))
                } else if form == &find_core_form("type", "enum") {
                    try!(write!(f, "enum{{"));
                    for subenv in env.march_all(&[n("name")]) {
                        try!(write!(f, " {}("/*)*/, 
                            ast_to_atom(&subenv.get_leaf_or_panic(&n("name")))));
                        if let Some(comps) = subenv.get_rep_leaf(&n("component")) {
                            let mut first = true;
                            for comp in comps {
                                if !first { try!(write!(f, " "))} first = false;
                                
                                try!(write!(f, "{}", Ty::new(comp.clone())));
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
                            Ty::new(subenv.get_leaf_or_panic(&n("component")).clone())));
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
                    write!(f, ". {}", Ty::new(env.get_leaf_or_panic(&n("body")).clone()))
                } else if form == &find_core_form("type", "mu_type") {
                    write!(f, "μ {}. {}", 
                        ast_to_atom(env.get_leaf_or_panic(&n("param"))),
                        Ty::new(env.get_leaf_or_panic(&n("body")).clone()))
                } else if form == &find_core_form("type", "type_by_name") {
                    write!(f, "{}", ast_to_atom(env.get_leaf_or_panic(&n("name"))))
                } else if form == &find_core_form("type", "type_apply") {
                    try!(write!(f, "{}<[", ast_to_atom(env.get_leaf_or_panic(&n("type_name")))));
                    let mut first = true;
                    if let Some(args) = env.get_rep_leaf(&n("arg")) {
                        for arg in args {
                            if !first { try!(write!(f, " ")); }
                            first = false;
                            try!(write!(f, "{}", Ty::new(arg.clone())));
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
    
    fn reflect(v: &::runtime::eval::Value) -> Self { Ty::new(Ast::reflect(v))}
}

impl ::ast_walk::WalkElt<SynthTy> for Ty {
    type Err = TypeError;
    
    fn get_bidi_walk_rule(f: &Form) -> &::form::BiDiWR<SynthTy, UnpackTy> { &f.synth_type }
    
    fn automatically_extend_env() -> bool { true }
    
    fn from_ast(a: &Ast) -> Ty { Ty::new(a.clone()) }
    fn to_ast(&self) -> Ast { 
        match *self.0.borrow() {
            Some(ref a) => a.clone(),
            None => panic!("ICE: attempted to convert underdetermined type to AST")
            // (or just use `.concrete()`)
        }
    }
}

pub type SynthTy = ::ast_walk::PositiveWalkMode<Ty>;
pub type UnpackTy = ::ast_walk::NegativeWalkMode<Ty>;

pub fn synth_type_top(expr: &Ast) -> TypeResult {
    walk::<SynthTy>(expr, &LazyWalkReses::new_wrapper(Assoc::new()))
}

pub fn synth_type(expr: &Ast, env: Assoc<Name, Ty>) -> TypeResult {
    walk::<SynthTy>(expr, &LazyWalkReses::new_wrapper(env))
}

pub fn neg_synth_type(pat: &Ast, env: Assoc<Name, Ty>)
        -> Result<Assoc<Name, Ty>, TypeError> {
    walk::<UnpackTy>(pat, &LazyWalkReses::new_wrapper(env))
}

custom_derive! {
    #[derive(Reifiable, Clone, PartialEq)]
    pub enum TyErr {
        Mismatch(Ty, Ty), // got, expected
        NtInterpMismatch(Name, Name),
        NonexistentEnumArm(Name, Ty),
        NonexistentStructField(Name, Ty),
        NonExhaustiveMatch(Ty),
        UnableToDestructure(Ty, Name)
    }
}

impl ::std::fmt::Display for TyErr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use self::TyErr::*;
        match *self {
            Mismatch(ref got, ref exp) => {
                write!(f, "expected `{}`, found `{}`", exp, got)
            }
            NtInterpMismatch(got, exp) => {
                write!(f, "expected the nonterminal `{:?}`, but `{:?}` was interpolated",
                       exp, got)
            }
            NonexistentEnumArm(got_name, ref ty) => {
                write!(f, "the enum `{}` doesn't have an arm named `{:?}`",
                       ty, got_name)
            }
            NonexistentStructField(got_name, ref ty) => {
                write!(f, "the struct `{}` doesn't have a field named `{:?}`",
                       ty, got_name)
            }
            NonExhaustiveMatch(ref ty) => write!(f, "non-exhaustive match of `{}`", ty),
            UnableToDestructure(ref ty, expected_name) => {
                write!(f, "expected a `{}` type, got `{}`", expected_name, ty)
            }
        }
    }
}

// temporary, until we get rid of `Debug` as the way of outputting errors
impl ::std::fmt::Debug for TyErr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        ::std::fmt::Display::fmt(self, f)
    }
}

/*
// TODO: I hope I don't need this
impl From<()> for TyErr {
    fn from(_: ()) -> TyErr {
        panic!("Tried to discard a type error");
    }
}
*/

pub type TypeError = ::util::err::Spanned<TyErr>;


type TypeResult = Result<Ty, TypeError>;


pub fn expect_type(expected: &Ty, got: &Ty, loc: &Ast) -> TypeResult {
    if got != expected {
        Err(::util::err::Spanned { 
            loc: loc.clone(), body: TyErr::Mismatch(expected.clone(), got.clone()) 
        } )
    } else {
        Ok(got.clone()) // HACK: we don't really care about this value...
    }
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
                                     "type_of_new_var" => (, int_ty.concrete()),
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


#[test]
fn type_specialization() {
    let nat_ty = ty!( { "type" "nat" : });
    
    fn tbn(nm: &'static str) -> Ty {
        ty!( { "type" "type_by_name" : "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }
    
    let _para_ty_env = assoc_n!(
        "some_int" => ty!( { "type" "int" : }),
        "convert_to_nat" => ty!({ "type" "forall_type" :
            "param" => ["t"],
            "body" => { "type" "fn" :
                "param" => [ (, tbn("t").concrete() ) ],
                "ret" => (, nat_ty.concrete() ) }}),
        "identity" => ty!({ "type" "forall_type" :
            "param" => ["t"],
            "body" => { "type" "fn" :
                "param" => [ (, tbn("t").concrete() ) ],
                "ret" => (, tbn("t").concrete() ) }}));
    /*
    assert_eq!(synth_type(&ast!({ "expr" "apply" : 
                "rator" => (vr "convert_to_nat"),
                "rand" => [ (vr "some_int") ]
            }), para_ty_env.clone()),
        Ok(ty!( { "type" "nat" : })));

    assert_eq!(synth_type(&ast!({ "expr" "apply" : 
                "rator" => (vr "identity"),
                "rand" => [ (vr "some_int") ]
            }), para_ty_env.clone()),
        Ok(ty!( { "type" "int" : })));
    */
    // TODO: test that ∀ X. ∀ Y. [ X → Y ] is a sensible type 
    //        and that ∀ X. [ X → ∀ Y . Y ] is ridiculously permissive
}