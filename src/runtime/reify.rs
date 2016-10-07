#![macro_use]

// Designed for `use reify::*`
pub use ast::Ast;
pub use name::*;
pub use runtime::eval::Value;

use std::rc::Rc;
use num::bigint::BigInt;

/** This is for parts of this compiler that can also be represented as object-level values.
 * 
 * Since this language is extensible, we need to connect the Rust code in the compiler
 *  with the Unseemly code that actually gets evaluated.
 * This is where the magic happens.
 *
 * This is also where ICEs can happen, so make sure that ::ty() is consistent with ::reify().
 */

pub trait Reifiable<'t> {
    /// The Unseemly type that corresponds to Self.
    fn ty() -> Ast<'static>;
        
    /// The Unseemly value that corresponds to a value.
    fn reify(&self) -> Value<'t>;
    
    /// Get a value from an Unseemly value
    fn reflect(&Value<'t>) -> Self;
}

/* Core values */

macro_rules! basic_reifiability {
    ( $underlying_type:ty, $ty_name:tt, $value_name:ident ) => {
        impl<'t> Reifiable<'t> for $underlying_type {
            fn ty() -> Ast<'static> { ast!($ty_name) }

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


impl<'t> Reifiable<'t> for bool {
    fn ty() -> Ast<'static> { ast!("bool") }
    
    fn reify(&self) -> Value<'t> { Value::Bool(*self) }
    
    fn reflect(v: &Value<'t>) -> Self { extract!((v) Value::Bool = (i) => i) }
}

basic_reifiability!(Name<'t>, "ident", Ident);

// TODO: when returning traits works, just make functions `Reifiable`
// TODO: 'static also allows things to be owned instead?!?
pub fn reify_1ary_function<'t, A: Reifiable<'t> + 'static, R: Reifiable<'t> + 'static>(
        f: Rc<(Fn(A) -> R)>) -> Value<'t> {
    let f_c = f.clone();
    Value::BuiltInFunction(::runtime::eval::BIF(Rc::new(
        move |args: Vec<Value<'t>>| (f_c(A::reflect(&args[0]))).reify())))
}

pub fn reflect_1ary_function<'t, A: Reifiable<'t> + 'static, R: Reifiable<'t> + 'static>(
        f_v: Value<'t>) -> Rc<(Fn(A) -> R) + 't> {
    Rc::new(move |a: A|
        extract!((&f_v)
            Value::BuiltInFunction = (ref bif) => R::reflect(&(*bif.0)(vec![a.reify()]));
            Value::Function = (ref closure) => {
                R::reflect(&::runtime::eval::eval(&closure.body,
                    closure.env.clone().set(closure.params[0], a.reify())).unwrap())
            }))
}


// I bet there's more of a need for reification than reflection for functions....

pub fn reify_2ary_function<'t, A: Reifiable<'t> + 'static, B: Reifiable<'t> + 'static, 
                           R: Reifiable<'t> + 'static>(
        f: Rc<(Fn(A, B) -> R)>) -> Value<'t> {
    let f_c = f.clone();
    Value::BuiltInFunction(::runtime::eval::BIF(Rc::new(
        move |args: Vec<Value<'t>>| (f_c(A::reflect(&args[0]), B::reflect(&args[1]))).reify())))
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
    
    fn reify(&self) -> Value<'t> { (**self).reify() }
    
    fn reflect(v: &Value<'t>) -> Self { ::std::rc::Rc::new(T::reflect(v)) }
}

impl<'t, T: Reifiable<'t>> Reifiable<'t> for ::std::boxed::Box<T> {
    fn ty() -> Ast<'static> { T::ty() }
    
    fn reify(&self) -> Value<'t> { (**self).reify() }
    
    fn reflect(v: &Value<'t>) -> Self { ::std::boxed::Box::new(T::reflect(v)) }
}

// Hey, I know how to generate the implementation for this...
Reifiable!{
    () pub enum Option<T> {
        None,
        Some(T)
    }
}



/* for testing */

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable, Clone)]
    struct BasicStruct {
        a: BigInt, // TODO: change to String to test heterogeneity
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

#[test]
fn basic_reification() {
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
}

#[test]
fn function_reification() {
    let f = | a: BigInt | a + BigInt::from(1);
    
    let f2 = reflect_1ary_function::<BigInt, BigInt>(reify_1ary_function(Rc::new(f)));
    
    assert_eq!(f2(BigInt::from(1776)), BigInt::from(1777))
}