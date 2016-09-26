#![macro_use]

// Designed for `use reify::*`
pub use ast::Ast;
pub use name::*;
pub use runtime::eval::Value;


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
    
    /// What should Unseemly programmers call this type?
    fn type_name() -> Name<'static>;
    
    /// The Unseemly value that corresponds to a value.
    fn reify(&self) -> Value<'t>;
    
    /// Get a value from an Unseemly value
    fn reflect(&Value<'t>) -> Self;
}

impl<'t> Reifiable<'t> for String {
    fn ty() -> Ast<'static> { panic!("TODO") }
    
    fn type_name() -> Name<'static> { n("String") }
    
    fn reify(&self) -> Value<'t> { panic!("TODO") }
    
    fn reflect(v: &Value<'t>) -> Self { panic!("TODO") }
}

impl<'t> Reifiable<'t> for BigInt {
    fn ty() -> Ast<'static> { ast!("integer") }
    
    fn type_name() -> Name<'static> { n("Integer") }
    
    fn reify(&self) -> Value<'t> { Value::Int(self.clone()) }
    
    fn reflect(v: &Value<'t>) -> Self { extract!((v; Value::Int) (ref i) => i.clone()) }
}

impl<'t, T> Reifiable<'t> for Option<T> {
    fn ty() -> Ast<'static> { panic!("TODO") }
    
    fn type_name() -> Name<'static> { n("String") }
    
    fn reify(&self) -> Value<'t> { panic!("TODO") }
    
    fn reflect(v: &Value<'t>) -> Self { panic!("TODO") }    
}

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable)]
    struct BasicStruct {
        a: BigInt, // TODO: change to String to test heterogeneity
        b: BigInt
    }
}

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable)]
    struct NestedStruct {
        x: BasicStruct
    }
}

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable)]
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
}