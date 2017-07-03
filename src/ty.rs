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
    pub fn destructure(&self, expected_form: Rc<Form>) -> Result<EnvMBE<Ast>, TypeError> {
        match self.0 {
            Node(ref f, ref env) => {
                if f == &expected_form {
                    return Ok(env.clone());
                }
                ty_err!(UnableToDestructure(self.clone(), expected_form.name) at Trivial /*TODO*/);
            }
            _ => {
                ty_err!(UnableToDestructure(self.clone(), expected_form.name) at Trivial /*TODO*/);
            }
        }
    }
}

// this kinda belongs in core_forms.rs
impl ::std::fmt::Display for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use core_forms::{find_core_form, ast_to_atom};
        let undet_form = ::ty_compare::underdetermined_form.with(|u_f| { u_f.clone() });

        match self.0 {
            // Not used, right? Maybe it should be...
            // Some(VariableReference(ref n)) => { write!(f, "{}", n) },
            Node(ref form, ref env) => {
                if form == &find_core_form("type", "ident") {
                    write!(f, "ident")
                } else if form == &find_core_form("type", "int") {
                    write!(f, "int")
                } else if form == &find_core_form("type", "nat") {
                    write!(f, "nat")
                } else if form == &find_core_form("type", "float") {
                    write!(f, "float")
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
                    try!(write!(f, "enum {{"));
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
                    try!(write!(f, "struct {{"));
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
                    try!(write!(f, "mu_type "));
                    for p in env.get_rep_leaf_or_panic(&n("param")) {
                        try!(write!(f, " {}", ast_to_atom(&p)))
                    }
                    write!(f, " . {}", Ty::new(env.get_leaf_or_panic(&n("body")).clone()))
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
                } else if form == &undet_form {
                    ::ty_compare::unification.with(|unif| {
                        let var = ast_to_atom(&env.get_leaf_or_panic(&n("id")));
                        let looked_up = unif.borrow().get(&var).map(|x| x.clone());
                        match looked_up {
                            Some(ref t) => write!(f, "{}", t),
                            None => write!(f, "¿{}?", var)
                        }
                    })
                } else {
                    panic!("{:?} is not a well-formed type", self.0);
                }
            }
            VariableReference(vr) => {
                write!(f, "{}", vr)
            }
            ExtendEnv(ref t, ref _beta) => {
                write!(f, "{}", Ty::new((**t).clone())) // the beta is clear from the form
            }
            ref other_ast => {
                write!(f, "(ill-formed type: {:?})", other_ast)
            }
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

impl ::ast_walk::WalkElt for Ty {
    fn from_ast(a: &Ast) -> Ty { Ty::new(a.clone()) }
    fn to_ast(&self) -> Ast { self.concrete() }

    fn underspecified() -> Ty { // This sorta belongs in ty_compare.rs ) :
        ::ty_compare::next_id.with(|id| {
            ::ty_compare::underdetermined_form.with(|u_f| {
                *id.borrow_mut() += 1;
                // TODO: we need `gensym`!
                let new_name = n(("⚁ ".to_string() + id.borrow().to_string().as_str()).as_str());

                ty!({ u_f.clone() ; "id" => (, ::ast::Atom(new_name))})
            })
        })

    }

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
    type D = ::ast_walk::Positive<SynthTy>;

    fn get_walk_rule(f: &Form) -> &WalkRule<SynthTy> { &f.synth_type.pos() }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(n: Name, parts: &::ast_walk::LazyWalkReses<SynthTy>) -> Result<Ty, TypeError> {
        match parts.env.find(&n) {
            None => Err(::util::err::sp(TyErr::UnboundName(n), parts.this_ast.clone())),
            Some(ty) => Ok(ty.clone())
        }
    }
}

impl WalkMode for UnpackTy {
    type Elt = Ty;
    type Negated = SynthTy;
    type Err = TypeError;
    type D = ::ast_walk::Negative<UnpackTy>;

    fn get_walk_rule(f: &Form) -> &WalkRule<UnpackTy> { &f.synth_type.neg() }
    fn automatically_extend_env() -> bool { true }
}

impl ::ast_walk::NegativeWalkMode for UnpackTy {}

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
        UnableToDestructure(Ty, Name),
        UnboundName(Name)
    }
}

impl ::std::fmt::Display for TyErr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        use self::TyErr::*;
        match *self {
            Mismatch(ref got, ref exp) => {
                write!(f, "[Mismatch] expected `{}`, found `{}`", exp, got)
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
    let int_ty = ty!({ ::core_forms::find_core_form("type", "int") ; });
    let nat_ty = ty!({ ::core_forms::find_core_form("type", "nat") ; });

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
                    |_| Ok(ty!({ ::core_forms::find_core_form("type", "nat") ; }))))),
                NotWalked) ; []}),
            simple_ty_env.clone()),
        Ok(nat_ty.clone()));
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
    // TODO: test that ∀ X. ∀ Y. [ X → Y ] is a (sortof) sensible type (for transmogrify)
    //        and that ∀ X. [ X → ∀ Y . Y ] is ridiculously permissive
}
