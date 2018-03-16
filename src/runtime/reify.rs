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

pub trait Reifiable {
    /// The Unseemly type that corresponds to to the `Reifiable` type.
    /// Suitable for type definition, so any parameters will be abstract.
    /// e.g. `∀ A. Pair <[A int]<`
    /// TODO: this should return `Ty`
    fn ty() -> Ast {
        // By default, this is an opaque primitive.
        Ast::Node(Rc::new(::form::Form {
            name: Self::ty_name(),
            grammar: Rc::new(::parse::FormPat::Impossible),
            type_compare: ::form::Positive(::ast_walk::WalkRule::NotWalked),
            synth_type: ::form::Positive(::ast_walk::WalkRule::LiteralLike),
            quasiquote: ::form::Both(::ast_walk::WalkRule::LiteralLike,
                                     ::ast_walk::WalkRule::LiteralLike),
            eval: ::form::Positive(::ast_walk::WalkRule::NotWalked),
        }),
        ::util::mbe::EnvMBE::new(),
        ::beta::ExportBeta::Nothing)
    }

    /// A name for that type, so that recursive types are okay.
    /// e.g. `Annotated_with_int`
    fn ty_name() -> Name;

    /// How to refer to this type, given an environment in which
    ///  `ty_name()` is defined to be `ty()`.
    /// Parameters will be concrete.
    /// e.g. `Annotated_with_int<[nat]<`
    /// (Types using this type will use this, rather than `ty`)
    /// This must be customized if `ty` is, I think...
    fn ty_invocation() -> Ast { Ast::VariableReference(Self::ty_name()) }

    /// The Unseemly value that corresponds to a value.
    fn reify(&self) -> Value;

    /// Get a value from an Unseemly value
    fn reflect(&Value) -> Self;
}

/* Core values */

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

basic_reifiability!(BigInt, "Int", Int);

basic_reifiability!(Name, "Ident", Ident);

impl Reifiable for bool {
    fn ty_name() -> Name { n("Bool") }

    fn reify(&self) -> Value {
        ::runtime::eval::Value::Enum(n( if *self {"True"} else {"False"} ) , vec![])
    }

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
    fn ty_name() -> Name { n("unit") }

    fn reify(&self) -> Value { Value::Int(BigInt::from(0)) }

    fn reflect(_: &Value) -> Self { () }
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
        f: Rc<Box<(Fn(A) -> R)>>) -> Value {
    let f_c = f.clone();
    Value::BuiltInFunction(::runtime::eval::BIF(Rc::new(
        move |args: Vec<Value>| ((*f_c)(A::reflect(&args[0]))).reify())))
}

pub fn reflect_1ary_function<A: Reifiable + 'static, R: Reifiable + 'static>(
        f_v: Value) -> Rc<Box<(Fn(A) -> R)>> {
    Rc::new(Box::new(move |a: A|
        extract!((&f_v)
            Value::BuiltInFunction = (ref bif) => R::reflect(&(*bif.0)(vec![a.reify()]));
            Value::Function = (ref closure) => {
                R::reflect(&::runtime::eval::eval(&closure.body,
                    closure.env.clone().set(closure.params[0], a.reify())).unwrap())
            })))
}

// I bet there's more of a need for reification than reflection for functions....
pub fn reify_2ary_function<A: Reifiable + 'static, B: Reifiable + 'static,
                           R: Reifiable + 'static>(
        f: Rc<Box<(Fn(A, B) -> R)>>) -> Value {
    let f_c = f.clone();
    Value::BuiltInFunction(::runtime::eval::BIF(Rc::new(
        move |args: Vec<Value>| ((*f_c)(A::reflect(&args[0]), B::reflect(&args[1]))).reify())))
}

pub fn reflect_2ary_function<A: Reifiable + 'static, B: Reifiable + 'static,
                             R: Reifiable + 'static>(
        f_v: Value) -> Rc<Box<(Fn(A, B) -> R)>> {
    Rc::new(Box::new(move |a: A, b: B|
        extract!((&f_v)
            Value::BuiltInFunction = (ref bif) =>
                R::reflect(&(*bif.0)(vec![a.reify(), b.reify()]));
            Value::Function = (ref closure) => {
                R::reflect(&::runtime::eval::eval(&closure.body,
                    closure.env.clone().set(closure.params[0], a.reify())
                                       .set(closure.params[1], b.reify())).unwrap())
            })))
}


pub fn ty_of_1ary_function<A: Reifiable + 'static, R: Reifiable + 'static>()
         -> Ast {
    ast!( "TODO: generate type" )
}

macro_rules! reify_types {
    ( $($t:ty),* ) => {{
        let mut res = Assoc::new();
        $(
           res = res.set(<$t as Reifiable>::ty_name(), ::ty::Ty::new(<$t as Reifiable>::ty()));
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


pub fn make_reified_ty_env() -> Assoc<Name, ::ty::Ty> {
    reify_types!(Ast, Assoc<K, V>)
}


/*
impl<A: Reifiable, R: Reifiable> Reifiable for Box<Fn(A) -> R> {
    fn ty() -> Ast { panic!("") }

    fn reify(&self) -> Value { panic!("") }

    fn reflect(v: &Value) -> Self { panic!("") }
}
*/



/* we can't add derive(), but we can `impl` these ourselves directly */

// This feels a little awkward, just dropping the `Rc`ness on the floor.
// But I think `Value` has enouch `Rc` inside that nothing can go wrong... right?
impl<T: Reifiable> Reifiable for ::std::rc::Rc<T> {
    fn ty() -> Ast { T::ty() }

    fn ty_name() -> Name { T::ty_name() }

    fn ty_invocation() -> Ast { T::ty_invocation() }

    fn reify(&self) -> Value { (**self).reify() }

    fn reflect(v: &Value) -> Self { ::std::rc::Rc::new(T::reflect(v)) }
}

impl<T: Reifiable> Reifiable for Vec<T> {
    fn ty() -> Ast {
        panic!("TODO")
    }

    fn ty_name() -> Name { n("Sequence") }

    fn ty_invocation() -> Ast {
        ast!({ "Type" "type_apply" :
            "type_rator" => (vr "Sequence"),
            "arg" => [(, T::ty_invocation() )]
        })
    }

    fn reify(&self) -> Value {
        Value::Sequence(self.iter().map(|elt| Rc::new(elt.reify())).collect())
    }

    fn reflect(v: &Value) -> Self {
        extract!((v) Value::Sequence = (ref s) =>
            s.iter().map(|elt| T::reflect(&elt)).collect()
        )
    }
}

impl<T: Reifiable> Reifiable for ::std::boxed::Box<T> {
    fn ty() -> Ast { T::ty() }

    fn ty_name() -> Name { T::ty_name() }

    fn ty_invocation() -> Ast { T::ty_invocation() }

    fn reify(&self) -> Value { (**self).reify() }

    fn reflect(v: &Value) -> Self { ::std::boxed::Box::new(T::reflect(v)) }
}

// The roundtrip will de-alias the cell, sadly.
impl<T: Reifiable> Reifiable for ::std::cell::RefCell<T> {
    fn ty_name() -> Name { n("Rust_RefCell") }

    fn reify(&self) -> Value { self.borrow().reify() }

    fn reflect(v: &Value) -> Self { ::std::cell::RefCell::<T>::new(T::reflect(v)) }
}

impl<T> Reifiable for ::std::marker::PhantomData<T> {
    fn ty_name() -> Name { n("PhantomData") } // Do we need to distinguish different ones?

    fn reify(&self) -> Value { Value::Int(BigInt::from(0)) }

    fn reflect(_: &Value) -> Self { ::std::marker::PhantomData }
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

#[derive(Debug, PartialEq, Eq, Clone)]
struct OldName<'t> { actual: Name, pd: ::std::marker::PhantomData<&'t u32> }
fn new_oldname<'t>(nm: Name) -> OldName<'t> {
    OldName {
        actual: nm, pd: ::std::marker::PhantomData
    }
}

impl<'t> Reifiable for OldName<'t> {
    fn ty_name() -> Name { n("OldName") }

    fn reify(&self) -> Value { Value::Ident(self.actual) }

    fn reflect(v: &Value) -> Self {
        extract!((v) Value::Ident = (nm) => new_oldname(nm) )
    }
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

    let bleo = BasicLifetimeEnum::Only(new_oldname(n("AlexanderHamilton")));

    assert_eq!(bleo, BasicLifetimeEnum::reflect(&bleo.reify()));

    let pls = ParameterizedLifetimeStruct::<BigInt, bool>{
        a: BigInt::from(10),
        b: false,
        c: new_oldname(n("DuelCommandments"))
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
    fn tbn(nm: &'static str) -> ::ast::Ast {
        ast!( { "Type" "type_by_name" : "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }

    //"ParameterizedLifetimeStruct<[Option<[Rust_usize]< integer]<"
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
        }));


    assert_eq!(
        ParameterizedLifetimeStruct::<'static, T, S>::ty(),
        ast!({"Type" "forall_type" :
            "param" => ["T", "S"],
            "body" => (import [* [forall "param"]] {"Type" "mu_type" :
                "param" => [(vr "ParameterizedLifetimeStruct")],
                "body" => (import [* [prot "param"]] {"Type" "struct" :
                    // TODO: why did the order of fields get reversed?
                    "component_name" => [@"c" "c", "b", "a"],
                    "component" => [@"c" (vr "OldName"), (vr "S"), (vr "T")]

            })
        })
    }))
}
