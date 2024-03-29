//! This abstract syntax tree is *really* abstract.
//! It makes binding explicit, but everything else about the language is hidden inside `Node`;
//!  Their meaning comes from `Form`.

#![macro_use]

use crate::{
    beta::{Beta, ExportBeta},
    form::Form,
    name::*,
    util::mbe::EnvMBE,
};
use std::{fmt, rc::Rc};

// TODO: This really ought to be an `Rc` around an `enum`
#[derive(Clone, PartialEq)]
pub enum AstContents {
    Trivial,
    /// Typically, a binder
    Atom(Name),
    VariableReference(Name),

    /// Shift environment to quote more (the `bool` indicates whether it's positive or negative)
    QuoteMore(Ast, bool),
    /// Shift environment to quote less (the `u8` indicates the number of steps out)
    QuoteLess(Ast, u8),

    /// A meaningful chunk of syntax, governed by a form, containing an environment,
    ///  potentially exporting some names.
    Node(std::rc::Rc<Form>, EnvMBE<Ast>, ExportBeta),

    /// For parsing purposes.
    IncompleteNode(EnvMBE<Ast>),
    /// For parsing purposes.
    Shape(Vec<Ast>),

    /// Variable binding
    ExtendEnv(Ast, Beta),
    /// Variable binding, affects all phases.
    /// This is weird, but needed for marcos, it seems.
    ExtendEnvPhaseless(Ast, Beta),
}

#[derive(Clone, PartialEq)]
pub struct LocatedAst {
    /// "contents"
    pub c: AstContents,
    pub file_id: usize,
    pub begin: usize,
    pub end: usize,
}

#[derive(Clone)]
pub struct Ast(pub Rc<LocatedAst>);

// For testing purposes, we want to ignore span information
impl PartialEq for Ast {
    fn eq(&self, other: &Ast) -> bool { self.c() == other.c() }
}

// Reification macros would totally work for this,
//  but it's worth having a special case in `Value` in order to make this faster.
impl crate::runtime::reify::Reifiable for Ast {
    fn ty_name() -> Name { n("Ast") }

    fn reify(&self) -> crate::runtime::eval::Value {
        crate::runtime::eval::Value::AbstractSyntax(self.clone())
    }

    fn reflect(v: &crate::runtime::eval::Value) -> Ast {
        extract!((v) crate::runtime::eval::Value::AbstractSyntax = (ref ast) => ast.clone())
    }
}

pub use self::AstContents::*;

impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{:#?}", self.c()) }
}

impl fmt::Debug for AstContents {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Trivial => write!(f, "⨉"),
            Atom(n) => write!(f, "∘{}∘", n.print()),
            VariableReference(v) => write!(f, "{}", v.print()),
            Shape(v) => {
                write!(f, "(")?;
                let mut first = true;
                for elt in v {
                    if !first {
                        write!(f, " ")?
                    }
                    elt.fmt(f)?;
                    first = false;
                }
                write!(f, ")")
            }
            Node(form, body, export) => {
                write!(f, "{{ ({}); {:#?}", form.name.sp(), body)?;
                match *export {
                    crate::beta::ExportBeta::Nothing => {}
                    _ => write!(f, " ⇑{:#?}", export)?,
                }
                write!(f, "}}")
            }
            QuoteMore(body, pos) => {
                if *pos {
                    write!(f, "pos``{:#?}``", body)
                } else {
                    write!(f, "neg``{:#?}``", body)
                }
            }
            QuoteLess(body, depth) => write!(f, ",,({}){:#?},,", depth, body),
            IncompleteNode(body) => write!(f, "{{ INCOMPLETE; {:#?} }}", body),
            ExtendEnv(body, beta) => write!(f, "{:#?}↓{:#?}", body, beta),
            ExtendEnvPhaseless(body, beta) => write!(f, "{:#?}±↓{:#?}", body, beta),
        }
    }
}

// Warning: this assumes the core language! To properly display an `Ast`, you need the `SynEnv`.
impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.c()) }
}

impl fmt::Display for AstContents {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom(ref n) => write!(f, "{}", n.print()),
            VariableReference(ref v) => write!(f, "{}", v.print()),
            Node(ref form, ref body, _) => {
                let s = crate::unparse::unparse_mbe(
                    &form.grammar,
                    self,
                    body,
                    &crate::core_forms::get_core_forms(),
                );
                write!(f, "{}", s)
            }
            Shape(ref v) => {
                write!(f, "(")?;
                let mut first = true;
                for elt in v {
                    if !first {
                        write!(f, " ")?
                    }
                    elt.fmt(f)?;
                    first = false;
                }
                write!(f, ")")
            }
            ExtendEnv(ref body, _) => write!(f, "{}↓", body),
            ExtendEnvPhaseless(ref body, _) => write!(f, "{}±↓", body),
            QuoteMore(body, _) => {
                write!(f, "``{}``", body)
            }
            QuoteLess(body, _) => write!(f, ",,{},,", body),
            _ => write!(f, "{:#?}", self),
        }
    }
}

impl Ast {
    /// "Contents". Ignore location information and get the interesting bits
    pub fn c(&self) -> &AstContents { &self.0.c }

    /// Replace the contents.
    pub fn c_map(&self, f: &dyn Fn(&AstContents) -> AstContents) -> Ast { self.with_c(f(self.c())) }

    /// Keep the location information, but replace the contents.
    pub fn with_c(&self, c: AstContents) -> Ast {
        Ast(Rc::new(LocatedAst {
            c: c,
            file_id: self.0.file_id,
            begin: self.0.begin,
            end: self.0.end,
        }))
    }

    // TODO: this ought to at least warn if we're losing anything other than `Shape`
    pub fn flatten(&self) -> EnvMBE<Ast> {
        match self.c() {
            Trivial | Atom(_) => EnvMBE::new(),
            VariableReference(_) => EnvMBE::new(),
            Shape(ref v) => {
                let mut accum = EnvMBE::new();
                for sub_a in v {
                    accum = accum.combine_overriding(&sub_a.flatten())
                }
                accum
            }
            IncompleteNode(ref env) => env.clone(),
            Node(ref _f, ref _body, ref _export) => {
                // TODO: think about what should happen when
                //  `Scope` contains a `Scope` without an intervening `Named`
                panic!("I don't know what to do with {:#?}!", self)
            }
            QuoteMore(ref body, _) => body.flatten(),
            QuoteLess(ref body, _) => body.flatten(),
            ExtendEnv(ref body, _) | ExtendEnvPhaseless(ref body, _) => body.flatten(),
        }
    }

    // TODO: use `Mode::context_match` whenever possible
    pub fn destructure(
        &self,
        expd_form: std::rc::Rc<Form>,
    ) -> Option<crate::util::mbe::EnvMBE<Ast>> {
        if let Node(ref f, ref parts, _) = self.c() {
            if f == &expd_form {
                return Some(parts.clone());
            }
        }
        None
    }

    pub fn is_node(&self) -> bool {
        match self.c() {
            Node(_, _, _) => true,
            _ => false,
        }
    }

    // TODO: I think we have a lot of places where we ought to use this function:
    pub fn node_parts(&self) -> &EnvMBE<Ast> {
        match self.c() {
            Node(_, ref body, _) => body,
            _ => icp!(),
        }
    }

    pub fn maybe_node_parts(&self) -> Option<&EnvMBE<Ast>> {
        match self.c() {
            Node(_, ref body, _) => Some(body),
            _ => None,
        }
    }

    pub fn node_form(&self) -> &Form {
        match self.c() {
            Node(ref form, _, _) => form,
            _ => icp!(),
        }
    }

    pub fn free_vrs(&self) -> Vec<Name> {
        match self.c() {
            Trivial | Atom(_) => vec![],
            VariableReference(v) => vec![*v],
            Shape(_) | IncompleteNode(_) => unimplemented!("TODO"),
            QuoteLess(_, _) | QuoteMore(_, _) => unimplemented!("TODO"),
            // This one is actually encounterable by real-world code
            //  (if a ∀ somehow ends up underneath a `*` in syntax.)
            // And we need to take a LazyWalkReses to do this right.
            ExtendEnv(_, _) | ExtendEnvPhaseless(_, _) => unimplemented!("TODO"),
            Node(_, ref body, _) => body.map_reduce(
                &|a| a.free_vrs(),
                &|v0, v1| {
                    let mut res = v0.clone();
                    res.append(&mut v1.clone());
                    res
                },
                vec![],
            ),
        }
    }

    pub fn to_name(&self) -> Name {
        match self.c() {
            Atom(n) => *n,
            _ => icp!("{:#?} is not an atom", self),
        }
    }

    pub fn vr_to_name(&self) -> Name {
        match self.c() {
            VariableReference(n) => *n,
            _ => icp!("{:#?} is not an atom", self),
        }
    }

    pub fn orig_str<'a, 'b>(&'a self, prog: &'b str) -> &'b str { &prog[self.0.begin..self.0.end] }
}

#[test]
fn star_construction() {
    let env = mbe!( "a" => ["1", "2"]);

    assert_eq!(
        ast!( { - "x" => [* env =>("a") env : (, env.get_leaf_or_panic(&n("a")).clone())]} ),
        ast!( { - "x" => ["1", "2"] })
    );

    let env = mbe!( "a" => [@"duo" "1", "2"], "b" => [@"duo" "11", "22"]);

    assert_eq!(
        ast!( { - "x" => [* env =>("a", "b") env :
                            ((, env.get_leaf_or_panic(&n("b")).clone())
                             (, env.get_leaf_or_panic(&n("a")).clone()))]} ),
        ast!( { - "x" => [("11" "1"), ("22" "2")] })
    );
}

#[test]
fn mbe_r_and_r_roundtrip() {
    use crate::runtime::reify::Reifiable;
    let mbe1 = mbe!( "a" => [@"duo" "1", "2"], "b" => [@"duo" "11", "22"]);
    assert_eq!(mbe1, EnvMBE::<Ast>::reflect(&mbe1.reify()));
}
