// Designed for `use reify::*`
pub use ast::Ast;
pub use name::*;
pub use runtime::eval::Value;

use std::rc::Rc;
use num::bigint::BigInt;
use util::assoc::Assoc;

/** This is for parts of this compiler that need to be represented as object-level values.
 * Almost all of it, turns out!
 * 
 * Since this language is extensible, we need to connect the Rust code in the compiler
 *  with the Unseemly code that actually gets evaluated.
 * This is where the magic happens.
 *
 * This is also where ICEs can happen, so make sure that ::ty() is consistent with ::reify().
 */

pub trait Reifiable<'t> {
    /// The Unseemly type that corresponds to Self.
    /// Suitable for type definition, so any parameters will be abstract.
    /// e.g. `∀ A. Pair <[A int]<`
    /// TODO: this should return `Ty`
    fn ty() -> Ast<'static> {
        // By default, this is an opaque primitive.
        Ast::Node(Rc::new(::form::Form { 
            name: Self::ty_name(),
            grammar: ::parse::FormPat::Impossible,
            relative_phase: ::util::assoc::Assoc::new(),
            synth_type: ::form::Positive(::ast_walk::WalkRule::LiteralLike),
            eval: ::form::Positive(::ast_walk::WalkRule::NotWalked),
        }),
        ::util::mbe::EnvMBE::new())
    }
    
    /// A name for that type, so that recursive types are okay.
    /// e.g. `Annotated_with_int`
    fn ty_name() -> Name<'static>;

    /// How to refer to this type, given an environment in which 
    ///  `ty_name()` is defined to be `ty()`.
    /// Parameters will be concrete.
    /// e.g. `Annotated_with_int<[nat]<`
    /// (Types using this type will use this, rather than `ty`)
    /// This must be customized if `ty` is, I think...
    fn ty_invocation() -> Ast<'static> {
        ast!({ "type" "type_by_name" : 
            "name" => (, Ast::Atom(Self::ty_name()))
        })
    }
        
    /// The Unseemly value that corresponds to a value.
    fn reify(&self) -> Value<'t>;
    
    /// Get a value from an Unseemly value
    fn reflect(&Value<'t>) -> Self;
}

/* Core values */

macro_rules! basic_reifiability {
    ( $underlying_type:ty, $ty_name:tt, $value_name:ident ) => {
        impl<'t> Reifiable<'t> for $underlying_type {
            fn ty_name() -> Name<'static> { n($ty_name) }

            // TODO: can we remove these clones? are they even bad?
            // They seem redundant in the `Name<'t>` case, at least             
            fn reify(&self) -> Value<'t> { Value::$value_name(self.clone()) }
            
            fn reflect(v: &Value<'t>) -> Self { 
                extract!((v) Value::$value_name = (ref i) => i.clone())
            }
        }
    }
}

basic_reifiability!(BigInt, "integer", Int);

basic_reifiability!(bool, "bool", Bool);

basic_reifiability!(Name<'t>, "ident", Ident);


// note: primitives for these shouldn't have BigInt semantics!
impl<'t> Reifiable<'t> for usize {
    fn ty_name() -> Name<'static> { n("rust_usize") }
    
    fn reify(&self) -> Value<'t> { Value::Int(BigInt::from(*self)) }
    
    fn reflect(v: &Value<'t>) -> Self {
        use num::ToPrimitive;
        extract!((v) Value::Int = (ref i) => i.to_usize().unwrap()) 
    }
}
impl<'t> Reifiable<'t> for i32 {
    fn ty_name() -> Name<'static> { n("rust_i32") }
    
    fn reify(&self) -> Value<'t> { Value::Int(BigInt::from(*self)) }
    
    fn reflect(v: &Value<'t>) -> Self {
        use num::ToPrimitive;
        extract!((v) Value::Int = (ref i) => i.to_i32().unwrap()) 
    }
}
impl<'t> Reifiable<'t> for () {
    fn ty_name() -> Name<'static> { n("unit") }
    
    fn reify(&self) -> Value<'t> { Value::Bool(true) }
    
    fn reflect(_: &Value<'t>) -> Self { () }
}

// This is right, right?
impl<'t> Reifiable<'t> for Value<'t> {
    fn ty_name() -> Name<'static> { n("any") }
    
    fn reify(&self) -> Value<'t> { self.clone() }
    
    fn reflect(v: &Value<'t>) -> Self { v.clone() }
}

// TODO: when returning traits works, just make functions `Reifiable`
// TOUNDERSTAND: 'x also allows things to be owned instead?!?
pub fn reify_1ary_function<'t, A: Reifiable<'t> + 't, R: Reifiable<'t> + 't>(
        f: Rc<Box<(Fn(A) -> R) + 't>>) -> Value<'t> {
    let f_c = f.clone();
    Value::BuiltInFunction(::runtime::eval::BIF(Rc::new(
        move |args: Vec<Value<'t>>| ((*f_c)(A::reflect(&args[0]))).reify())))
}

pub fn reflect_1ary_function<'t, A: Reifiable<'t> + 't, R: Reifiable<'t> + 't>(
        f_v: Value<'t>) -> Rc<Box<(Fn(A) -> R) + 't>> {
    Rc::new(Box::new(move |a: A|
        extract!((&f_v)
            Value::BuiltInFunction = (ref bif) => R::reflect(&(*bif.0)(vec![a.reify()]));
            Value::Function = (ref closure) => {
                R::reflect(&::runtime::eval::eval(&closure.body,
                    closure.env.clone().set(closure.params[0], a.reify())).unwrap())
            })))
}

// I bet there's more of a need for reification than reflection for functions....
pub fn reify_2ary_function<'t, A: Reifiable<'t> + 'static, B: Reifiable<'t> + 'static, 
                           R: Reifiable<'t> + 'static>(
        f: Rc<(Fn(A, B) -> R)>) -> Value<'t> {
    let f_c = f.clone();
    Value::BuiltInFunction(::runtime::eval::BIF(Rc::new(
        move |args: Vec<Value<'t>>| (f_c(A::reflect(&args[0]), B::reflect(&args[1]))).reify())))
}

pub fn ty_of_1ary_function<'t, A: Reifiable<'t> + 'static, R: Reifiable<'t> + 'static>() 
         -> Ast<'t> {
    ast!( "TODO: generate type" )
}

macro_rules! reify_types {
    ( $($t:ty),* ) => {{
        let mut res = Assoc::new();
        $( 
           res = res.set(<$t as Reifiable>::ty_name(), ::ty::Ty(<$t as Reifiable>::ty()));    
        )*
        res
    }}
}

macro_rules! fake_reifiability {
    ( $underlying_type:ty ) => {
        impl<'t> Reifiable<'t> for $underlying_type {
            fn ty_name() -> Name<'static> { n(stringify!($underlying_type)) }
            fn reify(&self) -> Value<'t> { panic!() }
            fn reflect(_: &Value<'t>) -> Self { panic!() }
        }
    }
}

/*
 * This is unhygienic as heck, but the only way I've found to make `ty` make sense.
 * The problem is that, in Rust, there's no such thing as associated methods on
 *  `Assoc`, just `Assoc<K, V>` (not that would make sense anyways)
 * The other problem is that ihavenoideawhatimdoing.jpg
 */

struct K {}
fake_reifiability!(K);
struct V {}
fake_reifiability!(V);


pub fn make_reified_ty_env<'t>() -> Assoc<Name<'static>, ::ty::Ty<'static>> {
    reify_types!(Ast<'t>, Assoc<K, V>)
}


/*
impl<'t, A: Reifiable<'t>, R: Reifiable<'t>> Reifiable<'t> for Box<Fn(A) -> R> {
    fn ty() -> Ast<'static> { panic!("") }
    
    fn reify(&self) -> Value<'t> { panic!("") }
    
    fn reflect(v: &Value<'t>) -> Self { panic!("") }
}
*/



/* we can't add derive(), but we can `impl` these ourselves directly */ 

// This feels a little awkward, just dropping the `Rc`ness on the floor.
// But I think `Value` has enouch `Rc` inside that nothing can go wrong... right?
impl<'t, T: Reifiable<'t>> Reifiable<'t> for ::std::rc::Rc<T> {
    fn ty() -> Ast<'static> { T::ty() }
    
    fn ty_name() -> Name<'static> { T::ty_name() }
    
    fn ty_invocation() -> Ast<'static> { T::ty_invocation() }
    
    fn reify(&self) -> Value<'t> { (**self).reify() }
    
    fn reflect(v: &Value<'t>) -> Self { ::std::rc::Rc::new(T::reflect(v)) }
}

impl<'t, T: Reifiable<'t>> Reifiable<'t> for Vec<T> {
    fn ty() -> Ast<'static> { 
        panic!("TODO")
    }

    fn ty_name() -> Name<'static> { n("Sequence") }

    fn ty_invocation() -> Ast<'static> { 
        ast!({ "type" "type_apply" : 
            "type_name" => "Sequence",
            "arg" => [(, T::ty_invocation() )]
        })
    }
    
    fn reify(&self) -> Value<'t> {
        Value::Sequence(self.iter().map(|elt| Rc::new(elt.reify())).collect())
    }
    
    fn reflect(v: &Value<'t>) -> Self { 
        extract!((v) Value::Sequence = (ref s) => 
            s.iter().map(|elt| T::reflect(&elt)).collect()
        )
    }
}

impl<'t, T: Reifiable<'t>> Reifiable<'t> for ::std::boxed::Box<T> {
    fn ty() -> Ast<'static> { T::ty() }
    
    fn ty_name() -> Name<'static> { T::ty_name() }

    fn ty_invocation() -> Ast<'static> { T::ty_invocation() }
    
    fn reify(&self) -> Value<'t> { (**self).reify() }
    
    fn reflect(v: &Value<'t>) -> Self { ::std::boxed::Box::new(T::reflect(v)) }
}

// The roundtrip will de-alias the cell, sadly.
impl<'t, T: Reifiable<'t>> Reifiable<'t> for ::std::cell::RefCell<T> {
    fn ty_name() -> Name<'static> { n("rust_RefCell") }
    
    fn reify(&self) -> Value<'t> { self.borrow().reify() }
    
    fn reflect(v: &Value<'t>) -> Self { ::std::cell::RefCell::<T>::new(T::reflect(v)) }
}

// Hey, I know how to generate the implementation for this...
Reifiable! {
    () pub enum Option<T> {
        None,
        Some(T)
    }
}
Reifiable! {
    () pub enum Result<T, E> {
        Ok(T),
        Err(E),
    }
}


/* for testing */

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable, Clone)]
    struct BasicStruct {
        pub a: BigInt, // TODO: change to String to test heterogeneity
        b: BigInt
    }
}

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable, Clone)]
    struct NestedStruct {
        x: BasicStruct
    }
}


custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable(lifetime), Clone)]
    enum BasicLifetimeEnum<'t> {
        Only(Name<'t>)
    }
}


custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable, Clone)]
    enum BasicEnum {
        Jefferson(BigInt, BigInt), // TODO: change the first one to String
        Burr(BigInt)
    }
}

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable(lifetime), Clone)]
    struct ParameterizedLifetimeStruct<'t, T, S> {
        pub a: T, b: S, c: Name<'t>
    }     
}

// TODO: just write a macro that does a really faky custom_derive by calling `Reifiable!`
// around something and then putting down its definition.


#[test]
fn basic_reification() {
    assert_eq!(BigInt::from(1800).reify(), val!(i 1800));
}

#[test]
fn basic_reflection() {
    assert_eq!(BigInt::reflect(&val!(i 1800)), BigInt::from(1800));
}


#[test]
fn basic_r_and_r_roundtrip() {
    assert_eq!(BigInt::from(90), BigInt::reflect(&BigInt::from(90).reify()));
    
    let bsv = BasicStruct{ a: BigInt::from(4), b: BigInt::from(5) };
 
    assert_eq!(bsv, BasicStruct::reflect(&bsv.reify()));
    
    let nsv = NestedStruct{ x: bsv };
    
    assert_eq!(nsv, NestedStruct::reflect(&nsv.reify()));

    let bev0 = BasicEnum::Jefferson(BigInt::from(17), BigInt::from(1781));
    let bev1 = BasicEnum::Burr(BigInt::from(1781));
    
    assert_eq!(bev0, BasicEnum::reflect(&bev0.reify()));
    assert_eq!(bev1, BasicEnum::reflect(&bev1.reify()));

    //assert_eq!(None, Option::reflect(&None.reify()));
    assert_eq!(Some(BigInt::from(5)), Option::reflect(&Some(BigInt::from(5)).reify()));
    assert_eq!(Some(bev1.clone()), Option::reflect(&Some(bev1.clone()).reify()));
    
    assert_eq!(::std::rc::Rc::new(bev0.clone()), 
        ::std::rc::Rc::reflect(&::std::rc::Rc::new(bev0.clone()).reify()));

    assert_eq!(::std::boxed::Box::new(bev0.clone()), 
        ::std::boxed::Box::reflect(&::std::boxed::Box::new(bev0.clone()).reify()));
    
    let bleo = BasicLifetimeEnum::Only(n("AlexanderHamilton"));

    assert_eq!(bleo, BasicLifetimeEnum::reflect(&bleo.reify()));
    
    let pls = ParameterizedLifetimeStruct::<BigInt, bool>{ 
        a: BigInt::from(10),
        b: false,
        c: n("DuelCommandments")
    };
    
    assert_eq!(pls, ParameterizedLifetimeStruct::<BigInt, bool>::reflect(&pls.reify()));
}

#[test]
fn function_r_and_r_roundtrip() {
    let f = | a: BigInt | a + BigInt::from(1);
    
    let f2 = reflect_1ary_function::<BigInt, BigInt>(reify_1ary_function(Rc::new(Box::new(f))));
    
    assert_eq!((*f2)(BigInt::from(1776)), BigInt::from(1777));
}

struct T {}
fake_reifiability!(T);
struct S {}
fake_reifiability!(S);


#[test]
fn reified_types() {
    fn tbn(nm: &'static str) -> ::ast::Ast<'static> {
        ast!( { "type" "type_by_name" : "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }

    //"ParameterizedLifetimeStruct<[Option<[rust_usize]< integer]<"
    assert_eq!(
        ParameterizedLifetimeStruct::<'static, Option<usize>, BigInt>::ty_invocation(),
        ast!({"type" "type_apply" : 
            "type_name" => "ParameterizedLifetimeStruct",
            "arg" => [
                {"type" "type_apply" :
                    "type_name" => "Option",
                    "arg" => [ (, tbn("rust_usize")) ]
                },
                (, tbn("integer"))]
        }));
        
    
    assert_eq!(
        ParameterizedLifetimeStruct::<'static, T, S>::ty(),
        ast!({"type" "forall_type" :
            "param" => ["T", "S"],
            "body" => {"type" "mu_type" :
                "param" => "ParameterizedLifetimeStruct",
                "body" => {"type" "struct" :
                    // TODO: why did the order of fields get reversed?
                    "component_name" => [@"c" "c", "b", "a"],
                    "component" => [@"c" (, tbn("ident")), (, tbn("S")), (, tbn("T"))]
                    
            }
        }
    }))
}