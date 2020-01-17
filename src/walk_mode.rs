use crate::{
    alpha::{freshen, freshen_with},
    ast::Ast::{self, *},
    ast_walk::{walk, Clo, LazyWalkReses, OutEnvHandle, WalkRule},
    form::Form,
    name::*,
    runtime::reify::Reifiable,
    util::{assoc::Assoc, mbe::EnvMBE},
};
use std::fmt::{Debug, Display};

/// This trait makes a type producable by positive and negative walks.
pub trait WalkElt: Clone + Debug + Display + Reifiable + PartialEq {
    fn from_ast(a: &Ast) -> Self;
    fn to_ast(&self) -> Ast;
}

// Abbreviation for Result<…::Out, …>
type Res<Mode> = Result<<<Mode as WalkMode>::D as Dir>::Out, <Mode as WalkMode>::Err>;

/// This trait exists to walk over `Ast`s in different ways.
/// `get_walk_rule` connects `Form`s to actual walk operations.
///
/// There are two kinds of walks over `Ast`s:
///  * Positive walks produce an element (a value or type, say) from an environment.
///    They are for expression-like terms.
///  * Negative walks produce an environment from an element.
///    They are for pattern-like terms.
///
/// Now, the whole environment is actually present in both cases,
///  and negative walks can actually use it
///   -- the special value they traverse is stored in the environment with a special name --
///  but they conceptually are mostly relying on the special value.
pub trait WalkMode: Debug + Copy + Reifiable {
    /// The object type for the environment to walk in.
    type Elt: Clone + Debug + Reifiable + WalkElt;

    type Err: Debug + Reifiable + Clone;

    type D: Dir<Mode = Self>;

    /// The negated version of this walk
    type Negated: WalkMode<
        Elt = Self::Elt,
        Err = Self::Err,
        ExtraInfo = Self::ExtraInfo,
        Negated = Self,
    >;

    /// If this walk is positive, `Self`; otherwise `Self::Negated`
    type AsPositive: WalkMode<
        Elt = Self::Elt,
        Err = Self::Err,
        ExtraInfo = Self::ExtraInfo,
        D = Positive<Self::AsPositive>,
    >;

    /// If this walk is positive, `Self::Negated`; otherwise `Self`
    type AsNegative: NegativeWalkMode
        + WalkMode<
            Elt = Self::Elt,
            Err = Self::Err,
            ExtraInfo = Self::ExtraInfo,
            D = Negative<Self::AsNegative>,
        >;

    /// Any extra information the walk needs
    type ExtraInfo: std::default::Default + Reifiable + Clone + Debug;

    fn get_walk_rule(form: &Form) -> WalkRule<Self>
    where Self: Sized;

    /// Should the walker extend the environment based on imports?
    /// Only `QQ` and `Expand` have this as false; it's not 100% clear what's special about them.
    /// (This evolved over time; it used to be false for `Eval`, because of lambda).
    /// It seems like the thing about those modes is
    ///  (a) they don't look at variables, so their environments are irrelevant,
    ///  (b) `SameAs` switching to the negated mode and doing `get_res` doesn't work.
    /// But what unites those two factors?
    fn automatically_extend_env() -> bool;

    /// Do we ever need to treat certain forms as though they were repetitions?
    fn needs__splice_healing() -> bool { false }

    /// A little like `get_walk_rule` always returning `Custom` for positive splicing
    fn perform_splice_positive(
        _: &Form,
        _: &LazyWalkReses<Self>,
    ) -> Result<Option<Vec<Ast>>, Self::Err>
    {
        icp!()
    }
    /// A little like `get_walk_rule` always returning `Custom` for negative splicing
    fn perform_splice_negative(
        _: &Form,
        _: &LazyWalkReses<Self>,
        _context_elts: &dyn Fn() -> Vec<Ast>,
    ) -> Result<Option<Vec<Ast>>, Self::Err>
    {
        icp!()
    }

    /// Walk over the structure of a node, not its meaning.
    /// This could be because we're inside a syntax-quote,
    ///  or it could be that we are a form (like written-out types or a literal)
    ///   that acts like a literal.
    /// Children are not necessarily walked quasiliterally
    ///  -- maybe they're an interpolation of some kind --
    ///   instead, the mode (=quotation depth) and form together decide what to do.
    /// If the walk is negative, the result might be MatchFailure
    fn walk_quasi_literally(expected: Ast, cnc: &LazyWalkReses<Self>) -> Res<Self> {
        Self::D::walk_quasi_literally(expected, cnc)
    }

    // TODO: these seem like a hack...
    // We need to dynamically do these if it's possible, for `env_from_beta`
    fn out_as_elt(o: <Self::D as Dir>::Out) -> Self::Elt { Self::D::out_as_elt(o) }
    fn out_as_env(o: <Self::D as Dir>::Out) -> Assoc<Name, Self::Elt> { Self::D::out_as_env(o) }
    fn env_as_out(e: Assoc<Name, Self::Elt>) -> <Self::D as Dir>::Out { Self::D::env_as_out(e) }

    fn walk_var(n: Name, cnc: &LazyWalkReses<Self>) -> Res<Self> { Self::D::walk_var(n, cnc) }

    fn walk_atom(n: Name, cnc: &LazyWalkReses<Self>) -> Res<Self> { Self::D::walk_atom(n, cnc) }

    /// When a DDDed subterm is matched, it matches against multiple `Elt`s.
    /// How should we represent that?
    fn collapse_repetition(_: Vec<Res<Self>>) -> Res<Self> { icp!("unexpected repetition") }

    /// Make up a special `Elt` that is currently "underspecified",
    ///  but which can be "unified" with some other `Elt`.
    /// If that happens, all copies of this `Elt` will act like that other one.
    ///
    /// Side-effects under the covers make this work.
    fn underspecified(_: Name) -> Self::Elt { icp!("no underspecified_elt") }

    fn name() -> &'static str;
}

pub trait Dir: Debug + Copy + Clone
where Self: std::marker::Sized
{
    type Mode: WalkMode;

    /// The output of the walking process.
    ///
    /// Negated walks produce an environment of Self::Elt, positive walks produce Self::Elt.
    type Out: Clone + Debug + Reifiable;

    /// Get ready to destructure a node.
    /// Includes freshening (including the context_elt, if necessary)
    ///  and and mode-specific leaf-processing
    fn pre_walk(node: Ast, cnc: LazyWalkReses<Self::Mode>) -> (Ast, LazyWalkReses<Self::Mode>);

    fn walk_quasi_literally(node: Ast, cnc: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode>;

    /// Look up variable in the environment!
    fn walk_var(name: Name, cnc: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode>;

    fn walk_atom(name: Name, cnc: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode>;

    fn out_as_elt(out: Self::Out) -> <Self::Mode as WalkMode>::Elt;
    fn out_as_env(out: Self::Out) -> Assoc<Name, <Self::Mode as WalkMode>::Elt>;
    fn env_as_out(env: Assoc<Name, <Self::Mode as WalkMode>::Elt>) -> Self::Out;

    /// For when we hackishly need to execute some code depending on the direction
    fn is_positive() -> bool;

    /// If necessary, prepare to smuggle results across more-quoted AST
    fn oeh_if_negative() -> Option<OutEnvHandle<Self::Mode>>;
}

#[derive(Copy, Clone, Debug)]
pub struct Positive<Mode: WalkMode> {
    md: Mode,
}

#[derive(Copy, Clone, Debug)]
pub struct Negative<Mode: WalkMode> {
    md: Mode,
}

impl<Mode: WalkMode<D = Self>> Dir for Positive<Mode> {
    type Out = <Self::Mode as WalkMode>::Elt;
    type Mode = Mode;

    fn pre_walk(node: Ast, cnc: LazyWalkReses<Self::Mode>) -> (Ast, LazyWalkReses<Self::Mode>) {
        (freshen(&node), cnc) // No-op
    }

    fn walk_quasi_literally(a: Ast, cnc: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode> {
        match a {
            Node(f, parts, exports) => {
                let mut walked: EnvMBE<Ast> = parts
                    .map_marched_against(
                        &mut |p: &Ast, cnc_m: &LazyWalkReses<Self::Mode>| {
                            match *p {
                                // Yes, `walk`, not `w_q_l`;
                                //  the mode is in charge of figuring things out.
                                Node(_, _, _)
                                | VariableReference(_)
                                | ExtendEnv(_, _)
                                | ExtendEnvPhaseless(_, _) => walk(p, cnc_m),
                                _ => Ok(<Self::Mode as WalkMode>::Elt::from_ast(&p.clone())),
                            }
                            .map(|e| <Self::Mode as WalkMode>::Elt::to_ast(&e))
                        },
                        cnc,
                    )
                    .lift_result()?;

                // HACK: recognize `Shape` as the output of `core_qq_forms::dotdotdot`:
                walked
                    .heal_splices::<()>(&|a| match a {
                        Shape(ref v) => Ok(Some(v.clone())),
                        _ => Ok(None),
                    })
                    .unwrap(); // Can't error

                // TODO: it should be a type error (or at least an obvious runtime error)
                // to put a splice (i.e. a `...[]...`) somewhere it can't be healed.

                Ok(<Self::Mode as WalkMode>::Elt::from_ast(&Node(f, walked, exports)))
            }
            orig => {
                // All this mess is to push `Shape` down past a wrapper (i.e. `ExtendEnv`),
                //  duplicating the wrapper around each element of `Shape`.
                // This is all for splicing the result of `dotdotdot`

                let body = match orig {
                    ExtendEnv(ref b, _)
                    | ExtendEnvPhaseless(ref b, _)
                    | QuoteMore(ref b, _)
                    | QuoteLess(ref b, _) => b,
                    _ => icp!(),
                };
                let sub_result = Mode::Elt::to_ast(&walk(&**body, cnc)?);

                fn handle_wrapper<Mode: WalkMode>(orig: &Ast, a: Ast) -> Ast {
                    let boxed = Box::new(a);
                    match orig {
                        // Environment extension is handled at `walk`
                        ExtendEnv(_, beta) => ExtendEnv(boxed, beta.clone()),
                        ExtendEnvPhaseless(_, beta) => ExtendEnvPhaseless(boxed, beta.clone()),
                        QuoteMore(_, pos) => QuoteMore(boxed, *pos),
                        QuoteLess(_, depth) => QuoteLess(boxed, *depth),
                        _ => icp!(),
                    }
                }

                let res: Ast = match sub_result {
                    Shape(sub_results) => Shape(
                        sub_results
                            .into_iter()
                            .map(|sub| handle_wrapper::<Self::Mode>(&orig, sub))
                            .collect(),
                    ),
                    sub_result => handle_wrapper::<Self::Mode>(&orig, sub_result),
                };

                Ok(Mode::Elt::from_ast(&res))
            }
        }
    }

    fn walk_var(n: Name, cnc: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode> {
        Ok(cnc.env.find_or_panic(&n).clone())
    }

    fn walk_atom(_: Name, _: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode> {
        icp!("Atoms are positively unwalkable");
    }

    fn out_as_elt(o: Self::Out) -> <Self::Mode as WalkMode>::Elt { o }
    fn out_as_env(_: Self::Out) -> Assoc<Name, <Self::Mode as WalkMode>::Elt> { icp!("out_as_env") }
    fn env_as_out(_: Assoc<Name, <Self::Mode as WalkMode>::Elt>) -> Self::Out { icp!("env_as_out") }

    fn oeh_if_negative() -> Option<OutEnvHandle<Mode>> { None }
    fn is_positive() -> bool { true }
}

impl<Mode: WalkMode<D = Self> + NegativeWalkMode> Dir for Negative<Mode> {
    type Out = Assoc<Name, <Self::Mode as WalkMode>::Elt>;
    type Mode = Mode;

    fn pre_walk(node: Ast, cnc: LazyWalkReses<Self::Mode>) -> (Ast, LazyWalkReses<Self::Mode>) {
        if !<Self::Mode as NegativeWalkMode>::needs_pre_match() {
            return (freshen(&node), cnc);
        }
        let node_ast = <Self::Mode as WalkMode>::Elt::from_ast(&node);
        // `pre_match` brings things together, which we want to do before attempting to co-freshen.
        match Mode::pre_match(node_ast, cnc.context_elt().clone(), &cnc.env) {
            Some((l_clo, r_clo)) => {
                // Closures; we need to unify their environments:
                let (l, r, new_env) = l_clo.env_merge(&r_clo);

                let (l_fresh, r_fresh) = freshen_with(
                    &<Self::Mode as WalkMode>::Elt::to_ast(&l),
                    &<Self::Mode as WalkMode>::Elt::to_ast(&r),
                );
                (
                    l_fresh,
                    cnc.with_environment(new_env)
                        .with_context(<Self::Mode as WalkMode>::Elt::from_ast(&r_fresh)),
                )
            }
            // HACK: force walking to automatically succeed, avoiding return type muckery
            None => (
                Atom(negative_ret_val()),
                cnc.with_context(<Self::Mode as WalkMode>::Elt::from_ast(&Trivial)),
            ),
        }
    }

    fn walk_quasi_literally(expected: Ast, cnc: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode> {
        let got = <Mode::Elt as WalkElt>::to_ast(&cnc.context_elt().clone());

        let parts_actual = Mode::context_match(&expected, &got, cnc.env.clone())?;

        let its_a_trivial_ast = EnvMBE::new(); // No more walking to do
        let expd_parts = match expected {
            Node(_, ref p, _) => p,
            _ => &its_a_trivial_ast,
        };

        // Continue the walk on subterms. (`context_match` does the freshening)
        // TODO: I fear that we need `map_collapse_reduce_with_marched_against`
        //  so that matching DDDed syntax won't go horribly wrong
        expd_parts.map_collapse_reduce_with(
            &parts_actual,
            &|model: &Ast, actual: &Ast| match *model {
                Node(_, _, _)
                | VariableReference(_)
                | ExtendEnv(_, _)
                | ExtendEnvPhaseless(_, _) => {
                    walk(model, &cnc.with_context(<Self::Mode as WalkMode>::Elt::from_ast(actual)))
                }
                _ => Ok(Assoc::new()),
            },
            &Mode::collapse_repetition,
            &|result, next| Ok(result.clone()?.set_assoc(&next.clone()?)),
            Ok(Assoc::new()),
        )
    }

    fn walk_var(n: Name, _: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode> {
        icp!("{} is a VarRef, which is negatively unwalkable", n)
    }

    /// Bind atom to the context!
    fn walk_atom(n: Name, cnc: &LazyWalkReses<Self::Mode>) -> Res<Self::Mode> {
        Ok(Assoc::new().set(n, cnc.context_elt().clone()))
    }

    fn out_as_elt(_: Self::Out) -> <Self::Mode as WalkMode>::Elt { icp!("out_as_elt") }
    fn out_as_env(o: Self::Out) -> Assoc<Name, <Self::Mode as WalkMode>::Elt> { o }
    fn env_as_out(e: Assoc<Name, <Self::Mode as WalkMode>::Elt>) -> Self::Out { e }

    fn oeh_if_negative() -> Option<OutEnvHandle<Self::Mode>> {
        Some(std::rc::Rc::new(std::cell::RefCell::new(
            Assoc::<Name, <Self::Mode as WalkMode>::Elt>::new(),
        )))
    }
    fn is_positive() -> bool { false }
}

pub trait NegativeWalkMode: WalkMode {
    /// What happens if destructuring fails?
    fn qlit_mismatch_error(l: Self::Elt, r: Self::Elt) -> Self::Err {
        panic!("match failure unimplemented: {} vs. {}", l, r)
    }

    // HACK: `Value`s can't survive the round-trip to `Ast`, so `pre_match`, as implemented,
    //  causes a panic in that case. So only pre_match if necessary.
    // HACK: This controls both whether `pre_match` is called,
    //  and whether we `freshen_with` the context_elt (as opposed to just `freshen`ing the value).
    // If something *can* round-trip to `Ast`, then it needs to be freshened, and `pre_match`
    fn needs_pre_match() -> bool;

    /// Before matching, possibly adjust the two `Elt`s to match better. (`None` is auto-match.)
    /// By default, a no-op.
    fn pre_match(
        expected: Self::Elt,
        got: Self::Elt,
        env: &Assoc<Name, Self::Elt>,
    ) -> Option<(Clo<Self::Elt>, Clo<Self::Elt>)>
    {
        Some((Clo { it: expected, env: env.clone() }, Clo { it: got, env: env.clone() }))
    }

    /// Match the context element against the current node.
    /// Note that this should come after `pre_match`,
    ///  so any remaining variables will be not be resolved.
    /// TODO: I should think about whether to use `Ast` or `Elt` during matches in `ast_walk`
    fn context_match(
        expected: &Ast,
        got: &Ast,
        _env: Assoc<Name, Self::Elt>,
    ) -> Result<EnvMBE<Ast>, <Self as WalkMode>::Err>
    {
        // break apart the node, and walk it element-wise
        match (expected, got) {
            // `pre_walk` has already freshened for us
            (&Node(ref f, _, _), &Node(ref f_actual, ref parts_actual, _)) if *f == *f_actual => {
                Ok(parts_actual.clone())
            }
            _ => {
                // TODO: wouldn't it be nice to have match failures that
                //  contained useful `diff`-like information for debugging,
                //   when a match was expected to succeed?
                // (I really like using pattern-matching in unit tests!)
                Err(Self::qlit_mismatch_error(
                    Self::Elt::from_ast(got),
                    Self::Elt::from_ast(expected),
                ))
            }
        }
    }
}

/// `var_to_out`, for positive walks where `Out` == `Elt`
pub fn var_lookup<Elt: Debug + Clone>(n: Name, env: &Assoc<Name, Elt>) -> Result<Elt, ()> {
    Ok((*env.find(&n).unwrap_or_else(|| panic!(format!("Name {:#?} unbound in {:#?}", n, env))))
        .clone())
}

/// `var_to_out`, for negative walks where `Out` == `Assoc<Name, Elt>``
pub fn var_bind<Elt: Debug + Clone>(
    n: Name,
    env: &Assoc<Name, Elt>,
) -> Result<Assoc<Name, Elt>, ()>
{
    Ok(Assoc::new().set(n, env.find(&negative_ret_val()).unwrap().clone()))
}
