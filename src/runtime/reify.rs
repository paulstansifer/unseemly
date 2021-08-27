// Designed for `use reify::*`
pub use crate::{ast::Ast, name::*, runtime::eval::Value};

use crate::runtime::eval;

use num::bigint::BigInt;
use std::rc::Rc;

/// This is for parts of this compiler that need to be represented as object-level values.
/// Almost all of it, turns out!
///
/// Since this language is extensible, we need to connect the Rust code in the compiler
///  with the Unseemly code that actually gets evaluated.
/// This is where the magic happens.
///
/// Suppose that `T` is a two-argument generic type.
/// Generally, we plan on executing code in an environment in which
///  `T::<Irr,Irr>::name()` is bound to `T::<Irr,Irr>::ty()`.
///   (The type arguments do not affect `name` and `ty`; `()` is convention.)
/// Then, we can use `T::<SomeActualArg, OtherActualArg>::ty_invocation()` in that environment.
///
/// This is also where ICPs can happen, so make sure that ::ty() is consistent with ::reify().

pub trait Reifiable {
    /// The Unseemly type that corresponds to to the `Reifiable` type.
    /// This leaves abstract the type parameters of `Self`; invoke like `Self::<Irr,Irr>::ty()`.
    /// e.g. `∀ A. Pair<A int>`
    /// TODO: rename to `generic_ty`
    fn ty() -> Ast {
        // By default, this is an opaque primitive.
        crate::core_type_forms::get__primitive_type(Self::ty_name())
    }

    /// A name for that type, so that recursive types are okay.
    /// Ignore the type parameters of `Self`; invoke like `Self::<Irr,Irr>::ty_name()`.
    /// e.g. `WithInteger`
    fn ty_name() -> Name;

    /// How to refer to this type, given an environment in which
    ///  `ty_name()` is defined to be `ty()`.
    /// Parameters will be concrete.
    /// e.g. `WithInteger<Float>`
    /// (Types using this type will use this, rather than `ty`)
    /// Don't override this.
    fn ty_invocation() -> Ast {
        let name_ref = ast!((vr Self::ty_name()));
        match Self::concrete_arguments() {
            None => name_ref,
            Some(args) => ast!({ "Type" "type_apply" :
                "type_rator" => (, name_ref),
                "arg" => (,seq args)
            }),
        }
    }

    // Override this to set the type arguments for invocation.
    fn concrete_arguments() -> Option<Vec<Ast>> { None }

    /// The Unseemly value that corresponds to a value.
    fn reify(&self) -> Value;

    /// Get a value from an Unseemly value
    fn reflect(_: &Value) -> Self;
}

// Core values

macro_rules! basic_reifiability {
    ( $underlying_type:ty, $ty_name:tt, $value_name:ident ) => {
        impl Reifiable for $underlying_type {
            fn ty_name() -> Name { n($ty_name) }

            // TODO: can we remove these clones? are they even bad?
            // They seem redundant in the `Name` case, at least
            fn reify(&self) -> Value { Value::$value_name(self.clone()) }

            fn reflect(v: &Value) -> Self {
                extract!((v) Value::$value_name = (ref i) => i.clone())
            }
        }
    }
}

/// Irr: the irrelevant type (like `!`). Satisfies a bunch of traits; can't be created.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum Irr {} // No values can be created.

impl std::fmt::Display for Irr {
    fn fmt(&self, _: &mut std::fmt::Formatter) -> std::fmt::Result { icp!() }
}

impl Default for Irr {
    fn default() -> Irr { icp!() }
}

impl Reifiable for Irr {
    fn ty_name() -> Name { icp!() }
    fn reify(&self) -> Value { icp!() }
    fn reflect(_: &Value) -> Self { icp!() }
}

impl crate::walk_mode::WalkElt for Irr {
    fn from_ast(_: &Ast) -> Self { icp!() }
    fn to_ast(&self) -> Ast { icp!() }
}

impl crate::walk_mode::WalkMode for Irr {
    fn name() -> &'static str { icp!() }
    type Elt = Irr;
    type Negated = NegIrr;
    type AsPositive = Irr;
    type AsNegative = NegIrr;
    type Err = Irr;
    type D = crate::walk_mode::Positive<Irr>;
    type ExtraInfo = Irr;

    fn get_walk_rule(_: &crate::form::Form) -> crate::ast_walk::WalkRule<Irr> { icp!() }
    fn automatically_extend_env() -> bool { icp!() }

    fn underspecified(_: Name) -> Irr { icp!() }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum NegIrr {}

impl Reifiable for NegIrr {
    fn ty_name() -> Name { icp!() }
    fn reify(&self) -> Value { icp!() }
    fn reflect(_: &Value) -> Self { icp!() }
}

impl crate::walk_mode::WalkMode for NegIrr {
    fn name() -> &'static str { icp!() }
    type Elt = Irr;
    type Negated = Irr;
    type AsPositive = Irr;
    type AsNegative = NegIrr;
    type Err = Irr;
    type D = crate::walk_mode::Negative<NegIrr>;
    type ExtraInfo = Irr;

    fn get_walk_rule(_: &crate::form::Form) -> crate::ast_walk::WalkRule<NegIrr> { icp!() }
    fn automatically_extend_env() -> bool { icp!() }

    fn underspecified(_: Name) -> Irr { icp!() }
}

impl crate::walk_mode::NegativeWalkMode for NegIrr {
    fn needs_pre_match() -> bool { panic!() }
}

basic_reifiability!(BigInt, "Int", Int);

impl Reifiable for bool {
    fn ty_name() -> Name { n("Bool") }

    fn reify(&self) -> Value { eval::Value::Enum(n(if *self { "True" } else { "False" }), vec![]) }

    fn reflect(v: &Value) -> Self {
        extract!((v) Value::Enum = (ref name, _) => name == &n("True"))
    }
}

// note: operations for these shouldn't have BigInt semantics!
impl Reifiable for usize {
    fn ty_name() -> Name { n("Rust_usize") }

    fn reify(&self) -> Value { Value::Int(BigInt::from(*self)) }

    fn reflect(v: &Value) -> Self {
        use num::ToPrimitive;
        extract!((v) Value::Int = (ref i) => i.to_usize().unwrap())
    }
}
impl Reifiable for i32 {
    fn ty_name() -> Name { n("Rust_i32") }

    fn reify(&self) -> Value { Value::Int(BigInt::from(*self)) }

    fn reflect(v: &Value) -> Self {
        use num::ToPrimitive;
        extract!((v) Value::Int = (ref i) => i.to_i32().unwrap())
    }
}
impl Reifiable for u8 {
    fn ty_name() -> Name { n("Rust_u8") }

    fn reify(&self) -> Value { Value::Int(BigInt::from(*self)) }

    fn reflect(v: &Value) -> Self {
        use num::ToPrimitive;
        extract!((v) Value::Int = (ref i) => i.to_u8().unwrap())
    }
}
impl Reifiable for () {
    fn ty_name() -> Name { n("Unit") }

    fn reify(&self) -> Value { Value::Int(BigInt::from(0)) }

    fn reflect(_: &Value) -> Self {}
}

impl<T0: Reifiable, T1: Reifiable> Reifiable for (T0, T1) {
    fn ty_name() -> Name { n("Tuple2") }

    fn concrete_arguments() -> Option<Vec<Ast>> {
        Some(vec![T0::ty_invocation(), T1::ty_invocation()])
    }

    fn reify(&self) -> Value {
        Value::Sequence(vec![Rc::new(self.0.reify()), Rc::new(self.1.reify())])
    }

    fn reflect(v: &Value) -> Self {
        extract!((v) Value::Sequence = (ref s) => (T0::reflect(&*s[0]), T1::reflect(&*s[1])))
    }
}

impl Reifiable for String {
    fn ty_name() -> Name { n("Rust_str") }

    fn reify(&self) -> Value { val!(ast (at self)) }

    fn reflect(v: &Value) -> Self {
        match v {
            eval::AbstractSyntax(at_ast) => at_ast.to_name().orig_sp(),
            _ => icp!(),
        }
    }
}

// This is right, right?
impl Reifiable for Value {
    fn ty_name() -> Name { n("any") }

    fn reify(&self) -> Value { self.clone() }

    fn reflect(v: &Value) -> Self { v.clone() }
}

// TODO: when returning traits works, just make functions `Reifiable`
// TOUNDERSTAND: 'x also allows things to be owned instead?!?
pub fn reify_1ary_function<A: Reifiable + 'static, R: Reifiable + 'static>(
    f: Rc<Box<(dyn Fn(A) -> R)>>,
) -> Value {
    Value::BuiltInFunction(eval::BIF(Rc::new(move |args: Vec<Value>| {
        ((*f)(A::reflect(&args[0]))).reify()
    })))
}

pub fn reflect_1ary_function<A: Reifiable + 'static, R: Reifiable + 'static>(
    f_v: Value,
) -> Rc<Box<(dyn Fn(A) -> R)>> {
    Rc::new(Box::new(move |a: A| {
        extract!((&f_v)
        Value::BuiltInFunction = (ref bif) => R::reflect(&(*bif.0)(vec![a.reify()]));
        Value::Function = (ref closure) => {
            R::reflect(&eval::eval(&closure.body,
                closure.env.clone().set(closure.params[0], a.reify())).unwrap())
        })
    }))
}

// I bet there's more of a need for reification than reflection for functions....
pub fn reify_2ary_function<
    A: Reifiable + 'static,
    B: Reifiable + 'static,
    R: Reifiable + 'static,
>(
    f: Rc<Box<(dyn Fn(A, B) -> R)>>,
) -> Value {
    Value::BuiltInFunction(eval::BIF(Rc::new(move |args: Vec<Value>| {
        ((*f)(A::reflect(&args[0]), B::reflect(&args[1]))).reify()
    })))
}

pub fn reflect_2ary_function<
    A: Reifiable + 'static,
    B: Reifiable + 'static,
    R: Reifiable + 'static,
>(
    f_v: Value,
) -> Rc<Box<(dyn Fn(A, B) -> R)>> {
    Rc::new(Box::new(move |a: A, b: B| {
        extract!((&f_v)
        Value::BuiltInFunction = (ref bif) =>
            R::reflect(&(*bif.0)(vec![a.reify(), b.reify()]));
        Value::Function = (ref closure) => {
            R::reflect(&eval::eval(&closure.body,
                closure.env.clone().set(closure.params[0], a.reify())
                                   .set(closure.params[1], b.reify())).unwrap())
        })
    }))
}

pub fn ty_of_1ary_function<A: Reifiable + 'static, R: Reifiable + 'static>() -> Ast {
    ast!("TODO: generate type")
}

macro_rules! reify_types {
    ( $($t:ty),* ) => {{
        let mut res = Assoc::new();
        $(
           res = res.set(<$t as Reifiable>::ty_name(), <$t as Reifiable>::ty());
        )*
        res
    }}
}

macro_rules! fake_reifiability {
    ( $underlying_type:ty ) => {
        impl Reifiable for $underlying_type {
            fn ty_name() -> Name { n(stringify!($underlying_type)) }
            fn reify(&self) -> Value { panic!() }
            fn reflect(_: &Value) -> Self { panic!() }
        }
    };
}

// impl<A: Reifiable, R: Reifiable> Reifiable for Box<Fn(A) -> R> {
//     fn ty() -> Ast { panic!("") }
//
//     fn reify(&self) -> Value { panic!("") }
//
//     fn reflect(v: &Value) -> Self { panic!("") }
// }

// We can't add derive() to existing types, but we can `impl` these ourselves directly

// This feels a little awkward, just dropping the `Rc`ness on the floor.
// But I think `Value` has enouch `Rc` inside that nothing can go wrong... right?
impl<T: Reifiable> Reifiable for Rc<T> {
    fn ty() -> Ast { T::ty() }

    fn ty_name() -> Name { T::ty_name() }

    fn concrete_arguments() -> Option<Vec<Ast>> { T::concrete_arguments() }

    fn reify(&self) -> Value { (**self).reify() }

    fn reflect(v: &Value) -> Self { Rc::new(T::reflect(v)) }
}

/// Takes the Unseemly type `T` to `Sequence<T>`
pub fn sequence_type__of(ty: &Ast) -> Ast {
    ast!({ "Type" "type_apply" :
        "type_rator" => (, crate::core_type_forms::get__primitive_type(n("Sequence"))),
        "arg" => [(, ty.clone()) ]})
}

/// Takes the Unseemly type `Sequence<T>` to `T`
pub fn un__sequence_type(ty: &Ast, loc: &Ast) -> Result<Ast, crate::ty::TypeError> {
    // This is a hack; `Sequence` is not a nonterminal!
    crate::core_type_forms::less_quoted_ty(ty, Some(n("Sequence")), loc)
}

impl<T: Reifiable> Reifiable for Vec<T> {
    fn ty_name() -> Name { n("Sequence") }

    fn concrete_arguments() -> Option<Vec<Ast>> { Some(vec![T::ty_invocation()]) }

    fn reify(&self) -> Value {
        Value::Sequence(self.iter().map(|elt| Rc::new(elt.reify())).collect())
    }

    fn reflect(v: &Value) -> Self {
        extract!((v) Value::Sequence = (ref s) =>
            s.iter().map(|elt| T::reflect(&elt)).collect()
        )
    }
}

impl<T: Reifiable> Reifiable for std::boxed::Box<T> {
    fn ty() -> Ast { T::ty() }

    fn ty_name() -> Name { T::ty_name() }

    fn concrete_arguments() -> Option<Vec<Ast>> { T::concrete_arguments() }

    fn reify(&self) -> Value { (**self).reify() }

    fn reflect(v: &Value) -> Self { std::boxed::Box::new(T::reflect(v)) }
}

// The roundtrip will de-alias the cell, sadly.
impl<T: Reifiable> Reifiable for std::cell::RefCell<T> {
    fn ty_name() -> Name { n("Rust_RefCell") }

    fn concrete_arguments() -> Option<Vec<Ast>> { Some(vec![T::ty_invocation()]) }

    fn reify(&self) -> Value { self.borrow().reify() }

    fn reflect(v: &Value) -> Self { std::cell::RefCell::<T>::new(T::reflect(v)) }
}

impl<T: Reifiable> Reifiable for std::marker::PhantomData<T> {
    fn ty_name() -> Name { n("PhantomData") }

    fn concrete_arguments() -> Option<Vec<Ast>> { Some(vec![T::ty_invocation()]) }

    fn reify(&self) -> Value { Value::Int(BigInt::from(0)) }

    fn reflect(_: &Value) -> Self { std::marker::PhantomData }
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

// for testing

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

#[derive(Debug, PartialEq, Eq, Clone)]
struct OldName<'t> {
    actual: Name,
    pd: std::marker::PhantomData<&'t u32>,
}
fn new_oldname<'t>(nm: Name) -> OldName<'t> { OldName { actual: nm, pd: std::marker::PhantomData } }

impl<'t> Reifiable for OldName<'t> {
    fn ty_name() -> Name { n("OldName") }

    fn reify(&self) -> Value { self.actual.reify() }

    fn reflect(v: &Value) -> Self { new_oldname(Name::reflect(v)) }
}

custom_derive! {
    #[derive(Debug, PartialEq, Eq, Reifiable(lifetime), Clone)]
    enum BasicLifetimeEnum<'t> {
        Only(OldName<'t>)
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
        pub a: T, b: S, c: OldName<'t>
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

    let bsv = BasicStruct { a: BigInt::from(4), b: BigInt::from(5) };

    assert_eq!(bsv, BasicStruct::reflect(&bsv.reify()));

    let nsv = NestedStruct { x: bsv };

    assert_eq!(nsv, NestedStruct::reflect(&nsv.reify()));

    let bev0 = BasicEnum::Jefferson(BigInt::from(17), BigInt::from(1781));
    let bev1 = BasicEnum::Burr(BigInt::from(1781));

    assert_eq!(bev0, BasicEnum::reflect(&bev0.reify()));
    assert_eq!(bev1, BasicEnum::reflect(&bev1.reify()));

    // assert_eq!(None, Option::reflect(&None.reify()));
    assert_eq!(Some(BigInt::from(5)), Option::reflect(&Some(BigInt::from(5)).reify()));
    assert_eq!(Some(bev1.clone()), Option::reflect(&Some(bev1.clone()).reify()));

    assert_eq!(Rc::new(bev0.clone()), Rc::reflect(&Rc::new(bev0.clone()).reify()));

    assert_eq!(
        std::boxed::Box::new(bev0.clone()),
        std::boxed::Box::reflect(&std::boxed::Box::new(bev0.clone()).reify())
    );

    let bleo = BasicLifetimeEnum::Only(new_oldname(n("AlexanderHamilton")));

    assert_eq!(bleo, BasicLifetimeEnum::reflect(&bleo.reify()));

    let pls = ParameterizedLifetimeStruct::<BigInt, bool> {
        a: BigInt::from(10),
        b: false,
        c: new_oldname(n("DuelCommandments")),
    };

    assert_eq!(pls, ParameterizedLifetimeStruct::<BigInt, bool>::reflect(&pls.reify()));
}

#[test]
fn function_r_and_r_roundtrip() {
    let f = |a: BigInt| a + BigInt::from(1);

    let f2 = reflect_1ary_function::<BigInt, BigInt>(reify_1ary_function(Rc::new(Box::new(f))));

    assert_eq!((*f2)(BigInt::from(1776)), BigInt::from(1777));
}

struct T {}
fake_reifiability!(T);
struct S {}
fake_reifiability!(S);

#[test]
fn reified_types() {
    //"ParameterizedLifetimeStruct<Option<Rust_usize> integer>"
    assert_eq!(
        ParameterizedLifetimeStruct::<'static, Option<usize>, BigInt>::ty_invocation(),
        ast!({"Type" "type_apply" :
            "type_rator" => (vr "ParameterizedLifetimeStruct"),
            "arg" => [
                {"Type" "type_apply" :
                    "type_rator" => (vr "Option"),
                    "arg" => [ (vr "Rust_usize") ]
                },
                (vr "Int")]
        })
    );

    assert_eq!(
        ParameterizedLifetimeStruct::<'static, T, S>::ty(),
        ast!({"Type" "forall_type" :
                "param" => ["T", "S"],
                "body" => (import [* [forall "param"]] {"Type" "mu_type" :
                    "param" => [(import [prot "param"] (vr "ParameterizedLifetimeStruct"))],
                    "body" => (import [* [prot "param"]] {"Type" "struct" :
                        // TODO: why did the order of fields get reversed?
                        "component_name" => [@"c" "c", "b", "a"],
                        "component" => [@"c" (vr "OldName"), (vr "S"), (vr "T")]

                })
            })
        })
    )
}
