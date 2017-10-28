/*
Type synthesis is a recursive traversal of an abstract syntax tree.
It is compositional,
 except for binding, which is indicated by ExtendTypeEnv nodes.
These nodes may depend on
 the result of type-synthesizing sibling AST nodes
 or the actual value of AST nodes corresponding to types
  (i.e., type annotations).
*/

use ast_walk::{walk, LazyWalkReses, WalkRule};
use ast_walk::WalkRule::*;
use walk_mode::WalkMode;
use form::Form;
use util::assoc::Assoc;
use ast::*;
use name::*;
use std::rc::Rc;


// TODO: we should validate that types don't have unexpected names in them
// (i.e. `∀ X. List<X>` is okay, but `X` is not a type; it's just syntax)
#[derive(PartialEq, Clone)]
pub struct Ty(pub Ast);

impl ::std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "[TYPE {:?}]", self.0)
    }
}

impl Ty {
    pub fn new(a: Ast) -> Ty { Ty(a) } // TODO: use `Ty()` instead of `Ty::new()`
    pub fn concrete(&self) -> Ast { // TODO: just use `Ty::to_ast()`; this name is obsolete
        self.0.clone()
    }

    // TODO: use this more
    pub fn destructure(&self, expd_form: Rc<Form>, loc: &Ast)
            -> Result<::util::mbe::EnvMBE<Ast>, TypeError> {
        match self.0 {
            Node(ref f, ref env, _) => {
                if f == &expd_form {
                    return Ok(env.clone());
                }
                ty_err!(UnableToDestructure(self.clone(), expd_form.name) at loc /*TODO*/);
            }
            _ => {
                ty_err!(UnableToDestructure(self.clone(), expd_form.name) at loc /*TODO*/);
            }
        }
    }
}

// this kinda belongs in core_forms.rs
impl ::std::fmt::Display for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ::runtime::reify::Reifiable for Ty {
    fn ty() -> Ast { Ast::ty() }

    fn ty_name() -> Name { n("Type") }

    fn ty_invocation() -> Ast { Ast::ty_invocation() }

    fn reify(&self) -> ::runtime::eval::Value { self.0.reify() }

    fn reflect(v: &::runtime::eval::Value) -> Self { Ty::new(Ast::reflect(v))}
}

impl ::walk_mode::WalkElt for Ty {
    fn from_ast(a: &Ast) -> Ty { Ty::new(a.clone()) }
    fn to_ast(&self) -> Ast { self.concrete() }
}

custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct SynthTy {}
}
custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct UnpackTy {}
}

impl WalkMode for SynthTy {
    type Elt = Ty;
    type Negated = UnpackTy;
    type Err = TypeError;
    type D = ::walk_mode::Positive<SynthTy>;

    fn get_walk_rule(f: &Form) -> &WalkRule<SynthTy> { f.synth_type.pos() }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(name: Name, parts: &::ast_walk::LazyWalkReses<SynthTy>) -> Result<Ty, TypeError> {
        match parts.env.find(&name) {
            None => Err(::util::err::sp(TyErr::UnboundName(name), parts.this_ast.clone())),
            // If name is protected, stop:
            Some(ty) if &Ty(VariableReference(name)) == ty => Ok(ty.clone()),
            Some(ty) => synth_type(&ty.concrete(), parts.env.clone())
        }
    }

    // Simply protect the name; don't try to unify it.
    fn underspecified(name: Name) -> Ty { Ty(VariableReference(name)) }
}

impl WalkMode for UnpackTy {
    type Elt = Ty;
    type Negated = SynthTy;
    type Err = TypeError;
    type D = ::walk_mode::Negative<UnpackTy>;

    fn get_walk_rule(f: &Form) -> &WalkRule<UnpackTy> { f.synth_type.neg() }
    fn automatically_extend_env() -> bool { true }
}

impl ::walk_mode::NegativeWalkMode for UnpackTy {
    fn needs_pre_match() -> bool { true }
}

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
        LengthMismatch(Vec<Ty>, usize),
        NtInterpMismatch(Name, Name),
        NonexistentEnumArm(Name, Ty),
        NonexistentStructField(Name, Ty),
        NonExhaustiveMatch(Ty),
        UnableToDestructure(Ty, Name),
        UnboundName(Name)
    }
}

impl ::std::fmt::Display for TyErr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use self::TyErr::*;
        match *self {
            Mismatch(ref got, ref exp) => {
                write!(f, "[Mismatch] got:\n  `{}`\n   expected:\n  `{}`\n", got, exp)
            }
            LengthMismatch(ref got, exp_len) => {
                try!(write!(f, "[LengthMismatch] got:\n  "));
                for g in got {
                    try!(write!(f, "{}, ", g))
                }
                write!(f, "\n  expected {} arguments.\n", exp_len)
            }
            NtInterpMismatch(got, exp) => {
                write!(f, "[NtInterpMismatch] expected the nonterminal `{:?}`, \
                           but `{:?}` was interpolated",
                       exp, got)
            }
            NonexistentEnumArm(got_name, ref ty) => {
                write!(f, "[NonexistentEnumArm] the enum `{}` doesn't have an arm named `{:?}`",
                       ty, got_name)
            }
            NonexistentStructField(got_name, ref ty) => {
                write!(f, "[NonexistentStructField] the struct `{}` doesn't have a \
                           field named `{:?}`",
                       ty, got_name)
            }
            NonExhaustiveMatch(ref ty) =>
                write!(f, "[NonExhaustiveMatch] non-exhaustive match of `{}`", ty),
            UnableToDestructure(ref ty, expected_name) => {
                write!(f, "[UnableToDestructure] expected a `{}` type, got `{}`", expected_name, ty)
            }
            UnboundName(name) => {
                write!(f, "[UnboundName] `{}` does not refer to a type", name)
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
    let int_ty = ty!({ ::core_forms::find_core_form("type", "Int") ; });
    let nat_ty = ty!({ ::core_forms::find_core_form("type", "Nat") ; });

    let simple_ty_env = mt_ty_env.set(n("x"), int_ty.clone());

    let body = basic_typed_form!(aat, Body(n("body")), NotWalked);
    let untypeable = basic_typed_form!(aat, NotWalked, NotWalked);

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
                aat,
                Custom(Rc::new(Box::new(
                    |_| Ok(ty!({ ::core_forms::find_core_form("type", "Nat") ; }))))),
                NotWalked) ; []}),
            simple_ty_env.clone()),
        Ok(nat_ty.clone()));


    let chained_ty_env
        = assoc_n!("a" => ty!((vr "B")), "B" => ty!((vr "C")), "C" => ty!({"type" "Int":}));

    assert_eq!(synth_type(&ast!((vr "a")), chained_ty_env), Ok(ty!({"type" "Int":})));
}


#[test]
fn type_specialization() {
    let nat_ty = ty!( { "type" "Nat" : });

    fn tbn(nm: &'static str) -> Ty {
        ty!( { "type" "type_by_name" : "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }

    let _para_ty_env = assoc_n!(
        "some_int" => ty!( { "type" "Int" : }),
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
        Ok(ty!( { "type" "Nat" : })));

    assert_eq!(synth_type(&ast!({ "expr" "apply" :
                "rator" => (vr "identity"),
                "rand" => [ (vr "some_int") ]
            }), para_ty_env.clone()),
        Ok(ty!( { "type" "Int" : })));
    */
    // TODO: test that ∀ X. ∀ Y. [ X → Y ] is a (sortof) sensible type (for transmogrify)
    //        and that ∀ X. [ X → ∀ Y . Y ] is ridiculously permissive
}
