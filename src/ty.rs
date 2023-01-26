// Type synthesis is a recursive traversal of an abstract syntax tree.
// It is compositional,
//  except for binding, which is indicated by ExtendTypeEnv nodes.
// These nodes may depend on
//  the result of type-synthesizing sibling AST nodes
//  or the actual value of AST nodes corresponding to types
//   (i.e., type annotations).

use crate::{
    ast::*,
    ast_walk::{
        walk, LazyWalkReses,
        WalkRule::{self},
    },
    form::Form,
    name::*,
    util::assoc::Assoc,
    walk_mode::WalkMode,
};
use std::{fmt, rc::Rc};

impl Ast {
    // TODO: use this more
    // TODO: make `expd_form` a reference
    pub fn ty_destructure(
        &self,
        expd_form: Rc<Form>,
        loc: &Ast,
    ) -> Result<crate::util::mbe::EnvMBE<Ast>, TypeError> {
        self.destructure(expd_form.clone())
            .ok_or(ty_err_val!(UnableToDestructure(self.clone(), expd_form.name) at loc /*TODO*/))
    }
}

custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct SynthTy {}
}
custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct UnpackTy {}
}

impl WalkMode for SynthTy {
    fn name() -> &'static str { "SynTy" }
    type Elt = Ast;
    type Negated = UnpackTy;
    type AsPositive = SynthTy;
    type AsNegative = UnpackTy;
    type Err = TypeError;
    type D = crate::walk_mode::Positive<SynthTy>;
    type ExtraInfo = ();

    fn get_walk_rule(f: &Form) -> WalkRule<SynthTy> { f.synth_type.pos().clone() }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(
        name: Name,
        parts: &crate::ast_walk::LazyWalkReses<SynthTy>,
    ) -> Result<Ast, TypeError> {
        match parts.env.find(&name) {
            None => Err(crate::util::err::sp(TyErr::UnboundName(name), parts.this_ast.clone())),
            // If name is protected, stop:
            Some(ty) if &VariableReference(name) == ty.c() => Ok(ty.clone()),
            Some(ref ty) => synth_type(ty, parts.env.clone()),
        }
    }

    // Simply protect the name; don't try to unify it.
    fn underspecified(name: Name) -> Ast { ast!((vr name)) }
}

impl WalkMode for UnpackTy {
    fn name() -> &'static str { "UnpTy" }
    type Elt = Ast;
    type Negated = SynthTy;
    type AsPositive = SynthTy;
    type AsNegative = UnpackTy;
    type Err = TypeError;
    type D = crate::walk_mode::Negative<UnpackTy>;
    type ExtraInfo = ();

    fn get_walk_rule(f: &Form) -> WalkRule<UnpackTy> { f.synth_type.neg().clone() }
    fn automatically_extend_env() -> bool { true }

    fn underspecified(name: Name) -> Ast { ast!((vr name)) }
}

impl crate::walk_mode::NegativeWalkMode for UnpackTy {
    fn needs_pre_match() -> bool { true }
}

pub fn synth_type_top(expr: &Ast) -> TypeResult {
    walk::<SynthTy>(expr, &LazyWalkReses::new_wrapper(Assoc::new()))
}

pub fn synth_type(expr: &Ast, env: Assoc<Name, Ast>) -> TypeResult {
    walk::<SynthTy>(expr, &LazyWalkReses::new_wrapper(env))
}

pub fn neg_synth_type(pat: &Ast, env: Assoc<Name, Ast>) -> Result<Assoc<Name, Ast>, TypeError> {
    walk::<UnpackTy>(pat, &LazyWalkReses::new_wrapper(env))
}

// TODO: Rename this. (Maybe `TypeComplaint`?)
custom_derive! {
    #[derive(Reifiable, Clone, PartialEq)]
    pub enum TyErr {
        Mismatch(Ast, Ast), // got, expected
        LengthMismatch(Vec<Ast>, usize),
        NtInterpMismatch(Name, Name),
        NonexistentEnumArm(Name, Ast),
        NonexistentStructField(Name, Ast),
        NonExhaustiveMatch(Ast),
        UnableToDestructure(Ast, Name),
        UnboundName(Name),
        // TODO: the reification macros can't handle empty `enum` cases. Fix that!
        AnnotationRequired(()),
        NeedsDriver(()),
        // TODO: replace all uses of `Other` with more specific errors:
        Other(String)
    }
}

impl fmt::Display for TyErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TyErr::*;
        match *self {
            Mismatch(ref got, ref exp) => {
                write!(f, "[Mismatch] got:\n  `{}`\n   expected:\n  `{}`\n", got, exp)
            }
            LengthMismatch(ref got, exp_len) => {
                write!(f, "[LengthMismatch] got:\n  ")?;
                for g in got {
                    write!(f, "{}, ", g)?;
                }
                write!(f, "\n  expected {} arguments.\n", exp_len)
            }
            NtInterpMismatch(got, exp) => write!(
                f,
                "[NtInterpMismatch] expected the nonterminal `{}`, but `{}` was interpolated",
                exp, got
            ),
            NonexistentEnumArm(got_name, ref ty) => write!(
                f,
                "[NonexistentEnumArm] the enum `{}` doesn't have an arm named `{}`",
                ty, got_name
            ),
            NonexistentStructField(got_name, ref ty) => write!(
                f,
                "[NonexistentStructField] the struct `{}` doesn't have a field named `{}`",
                ty, got_name
            ),
            NonExhaustiveMatch(ref ty) => {
                write!(f, "[NonExhaustiveMatch] non-exhaustive match of `{}`", ty)
            }
            UnableToDestructure(ref ty, expected_name) => {
                write!(f, "[UnableToDestructure] expected a `{}` type, got `{}`", expected_name, ty)
            }
            UnboundName(name) => write!(f, "[UnboundName] `{}` is not defined", name),
            AnnotationRequired(()) => write!(
                f,
                "[AnnotationRequired] Negative syntax (e.g. a pattern) inside positive syntax \
                 (e.g. an expression) requires a type annotation."
            ),
            NeedsDriver(()) => write!(f, "[NeedsDriver] Repetition needs a driver"),
            Other(ref s) => write!(f, "[Other] {}", s),
        }
    }
}

// temporary, until we get rid of `Debug` as the way of outputting errors
impl fmt::Debug for TyErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(self, f) }
}

// TODO: I hope I don't need this
// impl From<()> for TyErr {
//     fn from(_: ()) -> TyErr {
//         panic!("Tried to discard a type error");
//     }
// }

pub type TypeError = crate::util::err::Spanned<TyErr>;

pub type TypeResult = Result<Ast, TypeError>;

pub fn expect_type(expected: &Ast, got: &Ast, loc: &Ast) -> Result<(), TypeError> {
    if got != expected {
        Err(crate::util::err::Spanned {
            loc: loc.clone(),
            body: TyErr::Mismatch(expected.clone(), got.clone()),
        })
    } else {
        Ok(())
    }
}

#[test]
fn basic_type_synth() {
    use crate::ast_walk::WalkRule::*;

    let mt_ty_env = Assoc::new();
    let int_ty = ast!({
        crate::core_forms::find_core_form("Type", "Int");
    });
    let nat_ty = ast!({
        crate::core_forms::find_core_form("Type", "Nat");
    });

    let simple_ty_env = mt_ty_env.set(n("x"), int_ty.clone());

    let body = basic_typed_form!(atom, Body(n("body")), NotWalked);
    let untypeable = basic_typed_form!(atom, NotWalked, NotWalked);

    assert_eq!(synth_type(&ast!((vr "x")), simple_ty_env.clone()), Ok(int_ty.clone()));

    assert_eq!(
        synth_type(
            &ast!({body.clone() ;
                                     ["irrelevant" => {untypeable.clone() ; },
                                      "body" => (vr "x")]}),
            simple_ty_env.clone()
        ),
        Ok(int_ty.clone())
    );

    assert_eq!(
        synth_type(
            &ast!({body.clone() ;
                                     "type_of_new_var" => (, int_ty.clone()),
                                     "new_var" => "y",
                                     "body" => (import ["new_var" : "type_of_new_var"] (vr "y"))}),
            simple_ty_env.clone()
        ),
        Ok(int_ty.clone())
    );

    assert_eq!(
        synth_type(
            &ast!({
                basic_typed_form!(
                    atom,
                    Custom(Rc::new(Box::new(|_| Ok(ast!({
                        crate::core_forms::find_core_form("Type", "Nat");
                    }))))),
                    NotWalked
                );
                []
            }),
            simple_ty_env.clone()
        ),
        Ok(nat_ty.clone())
    );

    let chained_ty_env =
        assoc_n!("a" => ast!((vr "B")), "B" => ast!((vr "C")), "C" => ast!({"Type" "Int":}));

    assert_eq!(synth_type(&ast!((vr "a")), chained_ty_env), Ok(ast!({"Type" "Int":})));
}

#[test]
fn type_specialization() {
    let nat_ty = ast!( { "Type" "Nat" : });

    fn tbn(nm: &'static str) -> Ast { ast!((vr nm)) }

    let _para_ty_env = assoc_n!(
        "some_int" => ast!( { "Type" "Int" : }),
        "convert_to_nat" => ast!({ "Type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [ (, tbn("t") ) ],
                "ret" => (, nat_ty.clone() ) })}),
        "identity" => ast!({ "Type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [ (, tbn("t") ) ],
                "ret" => (, tbn("t") ) })}));

    // assert_eq!(synth_type(&ast!({ "Expr" "apply" :
    //             "rator" => (vr "convert_to_nat"),
    //             "rand" => [ (vr "some_int") ]
    //         }), para_ty_env.clone()),
    //     Ok(ast!( { "Type" "Nat" : })));

    // assert_eq!(synth_type(&ast!({ "Expr" "apply" :
    //             "rator" => (vr "identity"),
    //             "rand" => [ (vr "some_int") ]
    //         }), para_ty_env.clone()),
    //     Ok(ast!( { "Type" "Int" : })));
    // TODO: test that ∀ X. ∀ Y. [ X → Y ] is a (sortof) sensible type (for transmogrify)
    //        and that ∀ X. [ X → ∀ Y . Y ] is ridiculously permissive
}
