// A lot of language implementation consists of walking an `Ast` while maintaining an environment.
//
// Our `Ast`s have baked-in information about
//  what should happen environment-wise,
//   so `walk` processes `ExtendEnv` and `VariableReference` on its own.
// When it reaches a `Node`, the `Form` of that node specifies what to do, using a `WalkRule`.
// The most interesting `WalkRule`, `Custom`,
//   specifies an arbitrary function on the results of walking its subterms,
//  but a lot of forms can use `Body`,
//   which means that the `Ast` structure already did all the work.
// Subterms are walked lazily, since not all of them are even evaluable/typeable,
//  and they might need to be walked in a specific order.

// There are different kinds of walks. Here are the major ones Unseemly needs so far:
//
// Evaluation produces a `Value` or an error.
// During evaluation, each `lambda` form may be processed many times,
//  with different values for its parameters.
//
// Typechecking produces `Ast` or an error.
// During typechecking, each `lambda` form is processed once,
//  using its parameters' declared types.
//
// Subtyping produces `Ast` (irrelevant) or an error.
// It only walks type Asts, so `lambda` is not walked,
//  but ∀ is a binding form that acts sort of like type-level lambda,
//   except we use unification instead of explicit "function" calls.
//
// Quasiquotation, typically a part of evaluation, produces a `Value::AbstractSyntax`.
// Typically, it is triggered by a specific quotative form,
//  and it's very simple to implement; it just reifies syntax
//   (until it hits a dotdotdot or unquote).
// Unseemly is special in that `lambda` even binds under quasiquotation,
//  despite the fact that it doesn't do anything until the reified syntax is evaluated.

// When we walk an `Ast`, we encounter many different forms.
//
// Some forms are positive, and some are negative.
//
// Positive forms (e.g. expressions and variable references)
//  are walked in an environment, and produce a "result" value.
//
// Negative forms (e.g. patterns and variable bindings)
//  still can access their environment,
//   but primarily they look at one special "context value" in it, and when they are walked,
//    they produce an environment from that context value.
//
// For example, suppose that `five` has type `nat` and `hello` has type `string`:
//   - the expression `struct{a: five, b: hello}` produces the type `struct{a: nat, b: string}`
//   - the pattern `struct{a: aa, b: bb}` produces
//      the envirnonment where `aa` is `nat` and `bb` is `string`.
//
// At runtime, something similar happens with values and value environments.
//
// Some forms are "ambidextrous".
// Everything should be ambidextrous under quasiquotation,
//  because all syntax should be constructable and matchable.

use crate::{
    ast::{Ast, AstContents::*},
    beta::*,
    name::*,
    runtime::{eval, reify},
    util::{assoc::Assoc, mbe::EnvMBE},
    walk_mode::{Dir, WalkElt, WalkMode},
};
use std::{cell::RefCell, rc::Rc};

/// A closed `Elt`; an `Elt` paired with an environment with which to interpret its free names.
#[derive(Clone, Debug, PartialEq)]
pub struct Clo<Elt: WalkElt> {
    pub it: Elt,
    pub env: Assoc<Name, Elt>,
}

impl<Elt: WalkElt> Clo<Elt> {
    pub fn env_merge(self, other: &Clo<Elt>) -> (Elt, Elt, Assoc<Name, Elt>) {
        // To reduce name churn (and keep environments from exploding in size),
        // we cut out the bits of the environments that are the same.
        let o_different_env = other.env.cut_common(&self.env);

        let o_renaming =
            o_different_env.keyed_map_borrow_f(&mut |name, _| ast!((vr name.freshen())));

        let mut fresh_o_env = Assoc::new();
        for (o_name, o_val) in o_different_env.iter_pairs() {
            fresh_o_env = fresh_o_env.set(
                o_renaming.find(o_name).unwrap().vr_to_name(), // HACK: VR -> Name
                Elt::from_ast(&crate::alpha::substitute(&Elt::to_ast(o_val), &o_renaming)),
            );
        }

        (
            self.it,
            Elt::from_ast(&crate::alpha::substitute(&Elt::to_ast(&other.it), &o_renaming)),
            self.env.set_assoc(&fresh_o_env),
        )
    }
}

thread_local! {
    // Tuple elements are (layers deep, number of steps taken).
    pub static ast_walk_layer: RefCell<(u32, u32)> = RefCell::new((0, 0));
    pub static ld_enabled: bool = std::env::var(&"UNSEEMLY_TRACE").map(|t| t == "full") == Ok(true);
}

/// Make a `<Mode::D as Dir>::Out` by walking `node` in the environment from `walk_ctxt`.
/// `walk_ctxt` is used as an environment,
///  and by betas to access other parts of the current node.
pub fn walk<Mode: WalkMode>(
    a: &Ast,
    walk_ctxt: &LazyWalkReses<Mode>,
) -> Result<<Mode::D as Dir>::Out, Mode::Err> {
    layer_watch! { ast_walk_layer :
        // TODO: can we get rid of the & in front of our arguments and save the cloning?
        // TODO: this has a lot of direction-specific runtime hackery.
        //  Maybe we want separate positive and negative versions?
        let (a, walk_ctxt) = match a.c() {
          // HACK: We want to process EE before pre_match before everything else.
          // This probably means we should find a way to get rid of pre_match.
          // But we can't just swap `a` and the ctxt when `a` is LiteralLike and the ctxt isn't.

          ExtendEnv(_,_) => { (a.clone(), walk_ctxt.clone()) }
          _ => Mode::D::pre_walk(a.clone(), walk_ctxt.clone())
        };

        ld!(ast_walk_layer, ld_enabled, "{} {}", Mode::name(), a);
        // lc!(ast_walk_layer, ld_enabled, "  from: {}", walk_ctxt.this_ast);
        // match walk_ctxt.env.find(&negative_ret_val()) {
        //     Some(ref ctxt) => lc!(ast_walk_layer, ld_enabled, "  ctxt: {}", ctxt), _ => {}};
        // lc!(ast_walk_layer, ld_enabled, " in: {}", walk_ctxt.env/*.map_borrow_f(&mut |_| "…")*/);

        let literally : Option<bool> = // If we're under a wrapper, `this_ast` might not be a Node
            match a.c() {
                QuoteMore(_,_) | QuoteLess(_,_) | ExtendEnv(_,_) | ExtendEnvPhaseless(_,_) => {
                    match walk_ctxt.this_ast.c() {
                        // `this_ast` might be `NotWalked` (and non-literal) if under `switch_mode`.
                        // It's weird, but seems to be the right thing
                        Node(f, _, _) => Some(Mode::get_walk_rule(f).is_literally()),
                        _ => None
                    }
                }
                _ => None
            };


        match a.c() {
            Node(f, parts, _) => {
                let mut new_walk_ctxt = walk_ctxt.switch_ast(parts, a.clone());
                heal__lwr_splices(&mut new_walk_ctxt)?;

                // certain walks only work on certain kinds of AST nodes
                match Mode::get_walk_rule(f) {
                    Custom(ref ts_fn) =>  ts_fn(new_walk_ctxt),
                    Body(n) =>            walk(parts.get_leaf(n).unwrap(), &new_walk_ctxt),
                    LiteralLike =>        Mode::walk_quasi_literally(a.clone(), &new_walk_ctxt),
                    NotWalked =>          icp!("{:#?} should not be walked at all!", a)
                }
            }
            IncompleteNode(parts) => { icp!("{:#?} isn't a complete node", parts)}

            VariableReference(n) => { Mode::walk_var(*n, &walk_ctxt) }
            Atom(n) => { Mode::walk_atom(*n, &walk_ctxt) }

            // TODO: we need to preserve these in LiteralLike contexts!!

            // So do we just set the context element at the wrong level and then grab it for the shift?
            // I guess so.
            QuoteMore(body, pos_inside) => {
                let oeh_m = Mode::D::oeh_if_negative();
                let old_ctxt_elt = walk_ctxt.maybe__context_elt();

                let currently_positive = oeh_m.is_none(); // kinda a hack for "Is `Mode` positive?"

                // Negative modes at quotation does some weird stuff. For example:
                // `match e { `[Expr | (add 5 ,[Expr<Nat> | a],)]` => ⋯}`
                //            ^--- `quote_more` here (`get_res` produces `Expr<Nat>`),
                //                 which we already knew.
                //                            ^--- `quote_less`, and we get {a => Expr<Nat>}
                // We need to smuggle out what we know at each `quote_less` (there might be many),
                //  so that `a` winds up bound to `Expr<Nat>` on the RHS.

                // If the quotation (outside) is negative, we need to unsquirrel no matter the inside.
                // If both are positive, return the result (so the form can do `Nat` → `Expr<Nat>`).
                // Otherwise, the context (expected type) is the result.

                if pos_inside == &currently_positive { // stay in the same mode?
                    let inner_walk_ctxt = walk_ctxt.quote_more(oeh_m.clone());
                    let res = maybe_literally__walk(&a, body, inner_walk_ctxt, old_ctxt_elt,
                                                    literally)?;

                    match oeh_m {
                        None => Ok(res), // positive walk, result is useful. Otherwise, unsquirrel:
                        Some(oeh) => { Ok( Mode::env_as_out((*oeh.borrow()).clone()) ) }
                    }
                } else {
                    let inner_walk_ctxt = walk_ctxt.clone()
                        .switch_mode::<Mode::Negated>().quote_more(oeh_m.clone());
                    let _ = maybe_literally__walk(&a, body, inner_walk_ctxt, old_ctxt_elt,
                                                  literally)?;

                    match oeh_m {
                        // HACK: just return the context element (and massage the type)
                        None => Mode::walk_var(negative_ret_val(), &walk_ctxt),
                        Some(oeh) => { Ok( Mode::env_as_out((*oeh.borrow()).clone()) ) }
                    }
                }
            }
            QuoteLess(body, depth) => {
                let old_ctxt_elt = walk_ctxt.maybe__context_elt();

                let mut oeh = None;
                let mut walk_ctxt = walk_ctxt;
                for _ in 0..*depth {
                    let (oeh_new, walk_ctxt_new) = walk_ctxt.quote_less();
                    oeh = oeh_new;
                    walk_ctxt = walk_ctxt_new;
                }

                let res = maybe_literally__walk(&a, body, walk_ctxt, old_ctxt_elt, literally)?;

                squirrel_away::<Mode>(oeh, res.clone());

                Ok(res)
            }

            Trivial | Shape(_) => {
                icp!("{:#?} is not a walkable AST in {}", a, Mode::name());
            }

            ExtendEnv(ref body, ref beta) | ExtendEnvPhaseless(ref body, ref beta) => {
                let phaseless = match a.c() { ExtendEnvPhaseless(_,_) => true, _ => false };

                fn extract__ee_body<Mode: WalkMode>(e: <Mode as WalkMode>::Elt)
                        -> <Mode as WalkMode>::Elt {
                    match e.to_ast().c() {
                        ExtendEnv(ref body, _) | ExtendEnvPhaseless(ref body, _) => {
                            <Mode as WalkMode>::Elt::from_ast(&*body)
                        }
                        _ => { e } // Match will fail
                    }
                }


                let new__walk_ctxt = if !Mode::automatically_extend_env() {
                    walk_ctxt.clone()
                } else if phaseless {
                    let extension = &env_from_beta(beta, &walk_ctxt)?;
                    LazyWalkReses {
                        env: walk_ctxt.env.set_assoc(extension),
                        prelude_env: walk_ctxt.prelude_env.set_assoc(extension),
                        more_quoted_env: walk_ctxt.more_quoted_env.iter().map(
                            |e| e.set_assoc(extension)).collect(),
                        less_quoted_env: walk_ctxt.less_quoted_env.iter().map(
                            |e| e.set_assoc(extension)).collect(),
                        .. walk_ctxt.clone()
                    }
                } else {
                    walk_ctxt.with_environment(walk_ctxt.env.set_assoc(&env_from_beta(beta, &walk_ctxt)?))
                };

                let new__walk_ctxt = // If the RHS is also binding, assume it's the same
                // TODO: we should make this only happen if we're actually negative.
                // The context element is sometimes leftover from a previous negative walk.
                    new__walk_ctxt.with_context(extract__ee_body::<Mode>(
                        walk_ctxt.env.find(&negative_ret_val()).unwrap_or(
                            &<Mode as WalkMode>::Elt::from_ast(&ast!((trivial)))).clone()));

                maybe_literally__walk(&a, body, new__walk_ctxt,
                    walk_ctxt.maybe__context_elt().map(extract__ee_body::<Mode>), literally)
            }
        }
    }
}

// This fixes up `walk_ctxt` based on splice healing.
// TODO #40: Its effects on the rest of the code are too complex:
//  * `extra_env` needs to be used in various places, but exactly where is fuzzy
//  * `walk_ctxt` goes out of sync with its `Ast`;
//      Negative::walk_quasi_literally was using the Ast but had to switch to using the `walk_ctxt`
fn heal__lwr_splices<Mode: WalkMode>(walk_ctxt: &mut LazyWalkReses<Mode>) -> Result<(), Mode::Err> {
    if !Mode::needs__splice_healing() {
        return Ok(()); // only do this once, at the top level
    }
    let orig_walk_ctxt = walk_ctxt.clone();

    if Mode::D::is_positive() {
        walk_ctxt.parts.heal_splices::<Mode::Err>(&|lwt: &Rc<LazilyWalkedTerm<Mode>>| {
            if let Node(sub_f, sub_parts, _) = lwt.term.c() {
                if let Some((envs, new_term)) = Mode::perform_splice_positive(
                    sub_f,
                    &orig_walk_ctxt.clone().switch_ast(&sub_parts, lwt.term.clone()),
                )? {
                    Ok(Some(
                        envs.into_iter()
                            .map(|env| {
                                Rc::new(LazilyWalkedTerm {
                                    term: new_term.clone(),
                                    res: lwt.res.clone(),
                                    extra_env: env,
                                })
                            })
                            .collect::<Vec<_>>(),
                    ))
                } else {
                    Ok(None)
                }
            } else {
                Ok(None)
            }
        })?;
    } else {
        let its_a_trivial_ast = EnvMBE::new();
        let context_ast = walk_ctxt.context_elt().to_ast();
        let other_parts = match (&context_ast.c(), &walk_ctxt.this_ast.c()) {
            (&Node(ref f, ref p, _), &Node(ref f_this, _, _)) => {
                if f != f_this {
                    // Mismatched ASTs; some subtyping rules allow this, but healing is nonsensical
                    return Ok(());
                }
                p
            }
            _ => &its_a_trivial_ast,
        };

        // Note that this is asymmetric:
        //  the walked Ast conforms itself to fit the context element.
        // In practice, that seems to be what subtyping wants.
        // Is this a coincidence?
        walk_ctxt.parts.heal_splices__with::<Mode::Err, Ast>(
            other_parts,
            &|lwt: &Rc<LazilyWalkedTerm<Mode>>, sub_other_thunk: &dyn Fn() -> Vec<Ast>| {
                if let Node(ref sub_f, ref sub_parts, _) = lwt.term.c() {
                    // TODO: negative
                    if let Some((envs, new_term)) = Mode::perform_splice_negative(
                        sub_f,
                        &orig_walk_ctxt.clone().switch_ast(&sub_parts, lwt.term.clone()),
                        sub_other_thunk,
                    )? {
                        Ok(Some(
                            envs.into_iter()
                                .map(|env| {
                                    Rc::new(LazilyWalkedTerm {
                                        term: new_term.clone(),
                                        res: lwt.res.clone(),
                                        extra_env: env,
                                    })
                                })
                                .collect::<Vec<_>>(),
                        ))
                    } else {
                        Ok(None)
                    }
                } else {
                    Ok(None)
                }
            },
        )?;
    }
    Ok(())
}

/// If a `Node` is `LiteralLike`, its imports and [un]quotes should be, too!
fn maybe_literally__walk<Mode: WalkMode>(
    a: &Ast,
    body: &Ast,
    walk_ctxt: LazyWalkReses<Mode>,
    ctxt_elt: Option<Mode::Elt>,
    literally: Option<bool>,
) -> Result<<Mode::D as Dir>::Out, Mode::Err> {
    let walk_ctxt = match ctxt_elt {
        Some(e) => walk_ctxt.with_context(e),
        None => walk_ctxt,
    };
    // It might be right to assume that it's true if the mode is quasiquotation
    if literally.expect("ICP: unable to determine literalness") {
        Mode::walk_quasi_literally(a.clone(), &walk_ctxt)
    } else {
        walk(&*body, &walk_ctxt)
    }
}

/// How do we walk a particular node? This is a super-abstract question, hence all the `<>`s.
#[derive(Clone)]
pub enum WalkRule<Mode: WalkMode> {
    /// A function from the types/values of the *parts* of this form
    ///  to the type/value of this form.
    /// The environment is accessible via the `LazyWalkReses`.
    /// Any of the other `WalkRule`s can be implemented as a simple `Custom`.
    Custom(Rc<Box<(dyn Fn(LazyWalkReses<Mode>) -> Result<<Mode::D as Dir>::Out, Mode::Err>)>>),
    /// "this form has the same type/value as one of its subforms".
    /// (useful for forms that only exist as wrapper s around other AST nodes)
    Body(Name),
    /// "traverse the subterms, and rebuild this syntax around them".
    /// Only valid in modes where `Ast`s can be converted to `::Elt`s.
    LiteralLike,
    /// "this form should not ever be walked".
    NotWalked,
}

impl<Mode: WalkMode> WalkRule<Mode> {
    fn is_literally(&self) -> bool {
        match self {
            LiteralLike => true,
            _ => false,
        }
    }
}

// trait bounds on parameters and functions are not yet supported by `Reifiable!`
impl<Mode: WalkMode + Copy + 'static> reify::Reifiable for WalkRule<Mode> {
    // Maybe there's some magic we can do somewhere to make this opaque?
    fn ty_name() -> Name { n("WalkRule") }

    fn concrete_arguments() -> Option<Vec<Ast>> { Some(vec![Mode::ty_invocation()]) }

    fn reify(&self) -> eval::Value {
        match *self {
            NotWalked => val!(enum "NotWalked",),
            Body(ref n) => val!(enum "Body", (, n.reify())),
            Custom(ref lwr_to_out) => val!(enum "Custom", (,
                reify::reify_1ary_function(lwr_to_out.clone()))),
            LiteralLike => val!(enum "LiteralLike",),
        }
    }

    fn reflect(v: &eval::Value) -> Self {
        extract!((v) eval::Value::Enum = (ref choice, ref parts) =>
        if choice.is("NotWalked") {
            WalkRule::NotWalked
        } else if choice.is("Body") {
            WalkRule::Body(Name::reflect(&parts[0]))
        } else if choice.is("Custom") {
            WalkRule::Custom(reify::reflect_1ary_function(parts[0].clone()))
        } else if choice.is("LiteralLike") {
            WalkRule::LiteralLike
        } else {
            icp!()
        })
    }
}

impl<Mode: WalkMode> std::fmt::Debug for WalkRule<Mode> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            NotWalked => write!(f, "NotWalked"),
            Body(ref n) => write!(f, "Body({})", n),
            Custom(_) => write!(f, "Custom(-)"),
            LiteralLike => write!(f, "LiteralLike"),
        }
    }
}

pub use self::WalkRule::*;

/// An environment of walked things.
pub type ResEnv<Elt> = Assoc<Name, Elt>;

/// A term where the results of walking subterms is memoized.
#[derive(Debug)]
pub struct LazilyWalkedTerm<Mode: WalkMode> {
    pub term: Ast,
    pub res: RefCell<Option<Result<<Mode::D as Dir>::Out, Mode::Err>>>,
    /// This is a hack; it's specifically for the dotdotdot type.
    /// Maybe it needs generalization in some direction.
    pub extra_env: Assoc<Name, Mode::Elt>,
}

// trait bounds on parameters are not yet supported by `Reifiable!`
impl<Mode: WalkMode> reify::Reifiable for LazilyWalkedTerm<Mode> {
    fn ty_name() -> Name { n("LazilyWalkedTerm") }

    fn concrete_arguments() -> Option<Vec<Ast>> { Some(vec![Mode::ty_invocation()]) }

    fn reify(&self) -> eval::Value {
        val!(struct "term" => (, self.term.reify()),
                    "res" => (, self.res.reify()),
                    "extra_env" => (, self.extra_env.reify()))
    }
    fn reflect(v: &eval::Value) -> Self {
        extract!((v) eval::Value::Struct = (ref contents) =>
        LazilyWalkedTerm {
            term: Ast::reflect(contents.find_or_panic(&n("term"))),
            res: RefCell::<Option<Result<<Mode::D as Dir>::Out, Mode::Err>>>::reflect(
                contents.find_or_panic(&n("res"))),
            extra_env: Assoc::<Name, Mode::Elt>::reflect(contents.find_or_panic(&n("extra_env")))
            })
    }
}

// We only implement this because lazy-rust is unstable
impl<Mode: WalkMode> LazilyWalkedTerm<Mode> {
    pub fn new(t: &Ast) -> Rc<LazilyWalkedTerm<Mode>> {
        Rc::new(LazilyWalkedTerm {
            term: t.clone(),
            res: RefCell::new(None),
            extra_env: Assoc::new(),
        })
    }

    /// Get the result of walking this term (memoized)
    fn get_res(
        &self,
        cur_node_contents: &LazyWalkReses<Mode>,
    ) -> Result<<Mode::D as Dir>::Out, Mode::Err> {
        self.memoized(&|| {
            // stab-in-the-dark optimization, but this function gets called a *lot*:
            if self.extra_env.empty() {
                walk::<Mode>(&self.term, cur_node_contents)
            } else {
                walk::<Mode>(
                    &self.term,
                    &cur_node_contents
                        .with_environment(cur_node_contents.env.set_assoc(&self.extra_env)),
                )
            }
        })
    }

    fn memoized(
        &self,
        f: &dyn Fn() -> Result<<Mode::D as Dir>::Out, Mode::Err>,
    ) -> Result<<Mode::D as Dir>::Out, Mode::Err> {
        let result = self.res.borrow_mut().take().unwrap_or_else(f);
        *self.res.borrow_mut() = Some(result.clone());
        result
    }

    fn clear_memo(&self) { *self.res.borrow_mut() = None; }
}

pub type OutEnvHandle<Mode> = Rc<RefCell<Assoc<Name, <Mode as WalkMode>::Elt>>>;

/// Only does anything if `Mode` is negative.
pub fn squirrel_away<Mode: WalkMode>(
    opt_oeh: Option<OutEnvHandle<Mode>>,
    more_env: <Mode::D as Dir>::Out,
) {
    if let Some(oeh) = opt_oeh {
        let new_env = oeh.borrow().set_assoc(&Mode::out_as_env(more_env));
        *oeh.borrow_mut() = new_env;
    }
}

/// Package containing enough information to walk the subforms of some form on-demand.
///
/// It is safe to have unwalkable subforms, as long as nothing ever refers to them.
///
/// Contents probably shouldn't be `pub`...
#[derive(Debug, Clone)]
pub struct LazyWalkReses<Mode: WalkMode> {
    /// Things that we have walked and that we might walk
    pub parts: EnvMBE<Rc<LazilyWalkedTerm<Mode>>>,
    /// The environment of the overall walk.
    pub env: ResEnv<Mode::Elt>,

    /// The environment to use when entering a new phase.
    /// It's like a prelude, except that it's affected by syntax extensions.
    pub prelude_env: ResEnv<Mode::Elt>,
    /// The environment for syntax quotation (deeper on the front, shallower on the back)
    pub more_quoted_env: Vec<ResEnv<Mode::Elt>>,
    /// The environment for interpolation (further out on the front, nearer on the back)
    pub less_quoted_env: Vec<ResEnv<Mode::Elt>>,
    /// For all the less-quoted walks ongoing whose direction is negative,
    ///  we need to smuggle out results.
    /// This is a stack of (optional, because not all walks are negative) mutable handles
    ///  to the environments being accumulated.
    pub less_quoted_out_env: Vec<Option<OutEnvHandle<Mode>>>,

    pub this_ast: Ast,

    pub extra_info: Mode::ExtraInfo,
}

// trait bounds on parameters are not yet supported by `Reifiable!`
impl<Mode: WalkMode> reify::Reifiable for LazyWalkReses<Mode> {
    fn ty_name() -> Name { n("LazyWalkedReses") }

    fn concrete_arguments() -> Option<Vec<Ast>> { Some(vec![Mode::ty_invocation()]) }

    fn reify(&self) -> eval::Value {
        val!(struct "parts" => (, self.parts.reify()), "env" => (, self.env.reify()),
                    "prelude_env" => (,self.prelude_env.reify()),
                    "more_quoted_env" => (,self.more_quoted_env.reify()),
                    "less_quoted_env" => (,self.less_quoted_env.reify()),
                    "less_quoted_out_env" => (,self.less_quoted_out_env.reify()),
                    "this_ast" => (, self.this_ast.reify()),
                    "extra_info" => (, self.extra_info.reify()))
    }
    fn reflect(v: &eval::Value) -> Self {
        extract!((v) eval::Value::Struct = (ref contents) =>
            LazyWalkReses { parts: EnvMBE::<Rc<LazilyWalkedTerm<Mode>>>::reflect(
                                contents.find_or_panic(&n("parts"))),
                            env: ResEnv::<Mode::Elt>::reflect(
                                contents.find_or_panic(&n("env"))),
                            prelude_env: ResEnv::<Mode::Elt>::reflect(
                                contents.find_or_panic(&n("prelude_env"))),
                            more_quoted_env: Vec::<ResEnv<Mode::Elt>>::reflect(
                                contents.find_or_panic(&n("more_quoted_env"))),
                            less_quoted_env: Vec::<ResEnv<Mode::Elt>>::reflect(
                                contents.find_or_panic(&n("less_quoted_env"))),
                            less_quoted_out_env:
                                Vec::<Option<Rc<RefCell<Assoc<Name,Mode::Elt>>>>>::reflect(
                                    contents.find_or_panic(&n("less_quoted_out_env"))),
                            this_ast: Ast::reflect(
                                contents.find_or_panic(&n("this_ast"))),
                            extra_info: Mode::ExtraInfo::reflect(
                                contents.find_or_panic(&n("extra_info")))})
    }
}

impl<Mode: WalkMode> LazyWalkReses<Mode> {
    pub fn new(
        env: ResEnv<Mode::Elt>,
        prelude_env: ResEnv<Mode::Elt>,
        this_ast: Ast,
    ) -> LazyWalkReses<Mode> {
        LazyWalkReses {
            env: env,
            prelude_env: prelude_env,
            more_quoted_env: vec![],
            less_quoted_env: vec![],
            less_quoted_out_env: vec![],
            parts: match this_ast.maybe_node_parts() {
                Some(parts_unwalked) => parts_unwalked.map(&mut LazilyWalkedTerm::new),
                None => EnvMBE::new()
            },
            this_ast: this_ast,
            extra_info: std::default::Default::default(),
        }
    }

    /// Slight hack: this is just to get a recursion started with some environment.
    /// Only use this in tests or at the top level; this discards any non-phase-0-environments!
    pub fn new_wrapper(env: ResEnv<Mode::Elt>) -> LazyWalkReses<Mode> {
        LazyWalkReses {
            env: env.clone(),
            prelude_env: env,
            more_quoted_env: vec![],
            less_quoted_env: vec![],
            less_quoted_out_env: vec![],
            parts: EnvMBE::new(),
            // TODO #46: This sets us up with a "default" value for `literally`.
            this_ast: ast!({
                crate::form::simple_form("wrapper", crate::grammar::FormPat::Impossible);
            }),
            extra_info: std::default::Default::default(),
        }
    }

    pub fn new_mq_wrapper(
        env: ResEnv<Mode::Elt>,
        mqe: Vec<ResEnv<Mode::Elt>>,
    ) -> LazyWalkReses<Mode> {
        LazyWalkReses {
            env: env,
            prelude_env: Assoc::new(),
            more_quoted_env: mqe,
            less_quoted_env: vec![],
            less_quoted_out_env: vec![], // If we want a `lqe`, we need to fill this in, too!
            parts: EnvMBE::new(),
            // TODO #46: This sets us up with a "default" value for `literally`.
            this_ast: ast!({
                crate::form::simple_form("wrapper", crate::grammar::FormPat::Impossible);
            }),
            extra_info: std::default::Default::default(),
        }
    }

    pub fn new_empty() -> LazyWalkReses<Mode> { Self::new_wrapper(Assoc::new()) }

    pub fn switch_ast(self, parts: &EnvMBE<Ast>, this_ast: Ast) -> LazyWalkReses<Mode> {
        LazyWalkReses { parts: parts.map(&mut LazilyWalkedTerm::new), this_ast: this_ast, ..self }
    }

    pub fn this_form(&self) -> Rc<crate::form::Form> {
        match self.this_ast.c() {
            Node(ref f, _, _) => f.clone(),
            _ => icp!(),
        }
    }

    /// The result of walking the subform named `part_name`. This is memoized.
    pub fn get_res(&self, part_name: Name) -> Result<<Mode::D as Dir>::Out, Mode::Err> {
        self.parts.get_leaf_or_panic(&part_name).get_res(self)
    }

    /// Will `get_res` or `get_term` panic?
    /// Rarely used, because a form typically knows which named subterms it has based on parsing.
    pub fn has(&self, part_name: Name) -> bool { self.parts.get_leaf(part_name).is_some() }

    /// Like `get_res`, but for subforms that are repeated at depth 1. Sort of a hack.
    pub fn get_rep_res(&self, part_name: Name) -> Result<Vec<<Mode::D as Dir>::Out>, Mode::Err> {
        self.parts.get_rep_leaf_or_panic(part_name).iter().map(|&lwt| lwt.get_res(self)).collect()
    }

    /// Like `get_res`, but with `depth` levels of repetition, and calling `f` to flatten the result
    pub fn flatten_res_at_depth(
        &self,
        part_name: Name,
        depth: u8,
        map: &dyn Fn(<Mode::D as Dir>::Out) -> <Mode::D as Dir>::Out,
        flatten: &dyn Fn(Vec<<Mode::D as Dir>::Out>) -> <Mode::D as Dir>::Out,
    ) -> Result<<Mode::D as Dir>::Out, Mode::Err> {
        self.parts.map_flatten_rep_leaf_or_panic(
            part_name,
            depth,
            &|lwt: &Rc<LazilyWalkedTerm<Mode>>| -> Result<<Mode::D as Dir>::Out, Mode::Err> {
                lwt.get_res(self).map(map)
            },
            &|v: Vec<Result<<Mode::D as Dir>::Out, Mode::Err>>| {
                let mut accum = vec![];
                for elt in v {
                    accum.push(elt?);
                }
                Ok(flatten(accum))
            },
        )
    }

    /// Like `flatten_res_at_depth`, but uses `leaf` instead of doing `get_res`
    /// TODO: this is used in only one place, and feels really awkward.
    pub fn flatten_generate_at_depth(
        &self,
        part_name: Name,
        depth: u8,
        generate: &dyn Fn() -> <Mode::D as Dir>::Out,
        flatten: &dyn Fn(Vec<<Mode::D as Dir>::Out>) -> <Mode::D as Dir>::Out,
    ) -> <Mode::D as Dir>::Out {
        self.parts.map_flatten_rep_leaf_or_panic(
            part_name,
            depth,
            &|_| -> <Mode::D as Dir>::Out { generate() },
            &|v: Vec<<Mode::D as Dir>::Out>| {
                let mut accum = vec![];
                for elt in v {
                    accum.push(elt);
                }
                flatten(accum)
            },
        )
    }

    /// Like `get_term`, but with `depth` levels of repetition, and calling `m` to map and `f` to
    /// flatten the result
    pub fn map_flatten_term_at_depth<S>(
        &self,
        part_name: Name,
        depth: u8,
        m: &dyn Fn(&Ast) -> S,
        f: &dyn Fn(Vec<S>) -> S,
    ) -> S {
        self.parts.map_flatten_rep_leaf_or_panic(
            part_name,
            depth,
            &|lwt: &Rc<LazilyWalkedTerm<Mode>>| -> S { return m(&lwt.term) },
            f,
        )
    }

    // /** Like `get_rep_res`, but doesn't panic if the name is absent. */
    // pub fn maybe_get_rep_res(&self, part_name: &Name) -> Option<Result<Vec<<Mode::D as Dir>::Out>, Mode::Err>> {
    //     self.parts.get_rep_leaf(part_name).map(|parts|
    //         parts.iter().map( |&lwt| lwt.get_res(self)).collect())
    // }

    /// The subform named `part_name`, without any processing.
    pub fn get_term(&self, part_name: Name) -> Ast {
        self.parts.get_leaf_or_panic(&part_name).term.clone()
    }

    /// Only needed if, for some reason, a form could occur with or without a particular term.
    /// (a hack involving "mu_type" and "opacity_for_different_phase" does this)
    pub fn maybe_get_term(&self, part_name: Name) -> Option<Ast> {
        self.parts.get_leaf(part_name).map(|x| x.term.clone())
    }

    // TODO: replace `get_term` with this
    pub fn get_term_ref(&self, part_name: Name) -> &Ast {
        &self.parts.get_leaf_or_panic(&part_name).term
    }

    pub fn get_rep_term(&self, part_name: Name) -> Vec<Ast> {
        self.parts.get_rep_leaf_or_panic(part_name).iter().map(|&lwt| lwt.term.clone()).collect()
    }

    /// Only sensible for negative walks
    pub fn context_elt(&self) -> &Mode::Elt { self.env.find(&negative_ret_val()).unwrap() }

    pub fn maybe__context_elt(&self) -> Option<Mode::Elt> {
        // Kind of a HACK; users might set the context_elt in a positive mode before a mode switch.
        self.env.find(&negative_ret_val()).map(Clone::clone)
    }

    /// Change the context (by editing the environment). Only sensible for negative walks.
    /// Don't do `.with_context(…).with_environment(…)`; it's the same as `.with_environment(…)`.
    pub fn with_context(&self, e: Mode::Elt) -> LazyWalkReses<Mode> {
        LazyWalkReses { env: self.env.set(negative_ret_val(), e), ..(*self).clone() }
    }

    /// Change the whole environment
    pub fn with_environment(&self, env: ResEnv<Mode::Elt>) -> LazyWalkReses<Mode> {
        LazyWalkReses { env: env, ..(*self).clone() }
    }

    /// Change the prelude environment
    pub fn with_prelude_environment(&self, prelude_env: ResEnv<Mode::Elt>) -> LazyWalkReses<Mode> {
        LazyWalkReses { prelude_env: prelude_env, ..(*self).clone() }
    }

    /// Clear the memo table; important if you're re-evaluating the same term,
    /// but have changed the environment
    pub fn clear_memo(&self) {
        self.parts.map(&mut |lwt: &Rc<LazilyWalkedTerm<Mode>>| lwt.clear_memo());
    }

    /// Switch to a different mode with the same `Elt` type.
    pub fn switch_mode<NewMode: WalkMode<Elt = Mode::Elt, ExtraInfo = Mode::ExtraInfo>>(
        &self,
    ) -> LazyWalkReses<NewMode> {
        let new_parts: EnvMBE<Rc<LazilyWalkedTerm<NewMode>>> =
            self.parts.map(&mut |part: &Rc<LazilyWalkedTerm<Mode>>| {
                LazilyWalkedTerm::<NewMode>::new(&part.term)
            });
        LazyWalkReses::<NewMode> {
            parts: new_parts,
            env: self.env.clone(),
            prelude_env: self.prelude_env.clone(),
            more_quoted_env: self.more_quoted_env.clone(),
            less_quoted_env: self.less_quoted_env.clone(),
            less_quoted_out_env: self.less_quoted_out_env.clone(),
            this_ast: self.this_ast.clone(),
            extra_info: self.extra_info.clone(),
        }
    }

    /// If `Mode` is positive, returns `self`.
    /// If `Mode` is negative, `switch_mode`s it to be positive
    pub fn switch_to_positive(&self) -> LazyWalkReses<<Mode as WalkMode>::AsPositive> {
        self.switch_mode::<<Mode as WalkMode>::AsPositive>()
    }

    /// If `Mode` is negative, returns `self`.
    /// If `Mode` is positive, `switch_mode`s it to be negative
    pub fn switch_to_negative(&self) -> LazyWalkReses<<Mode as WalkMode>::AsNegative> {
        self.switch_mode::<<Mode as WalkMode>::AsNegative>()
    }

    pub fn quote_more(mut self, oeh: Option<OutEnvHandle<Mode>>) -> LazyWalkReses<Mode> {
        let env = self.more_quoted_env.pop().unwrap_or_else(|| self.prelude_env.clone());
        let more_quoted_env = self.more_quoted_env;
        self.less_quoted_env.push(self.env);
        let less_quoted_env = self.less_quoted_env;

        self.less_quoted_out_env.push(oeh);
        let less_quoted_out_env = self.less_quoted_out_env;

        LazyWalkReses { env, more_quoted_env, less_quoted_env, less_quoted_out_env, ..self }
    }

    /// Shift to a less-quoted level. If the OEH is non-`None`, you need to call `squirrel_away`.
    pub fn quote_less(mut self) -> (Option<OutEnvHandle<Mode>>, LazyWalkReses<Mode>) {
        let env = self.less_quoted_env.pop().unwrap_or_else(|| self.prelude_env.clone());
        let less_quoted_env = self.less_quoted_env;

        let out_env: Option<OutEnvHandle<Mode>> =
            self.less_quoted_out_env.pop().unwrap_or_else(|| Mode::D::oeh_if_negative());
        let less_quoted_out_env = self.less_quoted_out_env;

        self.more_quoted_env.push(self.env);
        let more_quoted_env = self.more_quoted_env;

        let res =
            LazyWalkReses { env, less_quoted_env, more_quoted_env, less_quoted_out_env, ..self };

        (out_env, res)
    }

    /// March by example, turning a repeated set of part names into one LWR per repetition.
    /// Keeps the same environment.
    pub fn march_parts(&self, driving_names: &[Name]) -> Vec<LazyWalkReses<Mode>> {
        let marched = self.parts.march_all(driving_names);
        let mut res = vec![];
        for marched_parts in marched {
            res.push(LazyWalkReses { parts: marched_parts, ..self.clone() });
        }
        res
    }

    /// HACK: The `mbe_one_name!` macro expects a type with `march_all`
    ///  (it can accept both `LazyWalkReses` and `EnvMBE`).
    /// But, for `LazyWalkReses`, prefer `march_parts`, so don't use this ) :
    pub fn march_all(&self, driving_names: &[Name]) -> Vec<LazyWalkReses<Mode>> {
        self.march_parts(driving_names)
    }

    /// Combines `march_parts` and `with_context`. `new_contexts` should have the same length
    /// as the repetition marched.
    pub fn march_parts_with(
        &self,
        driving_names: &[Name],
        new_contexts: Vec<Mode::Elt>,
    ) -> Option<Vec<LazyWalkReses<Mode>>> {
        let marched = self.parts.march_all(driving_names);
        if marched.len() != new_contexts.len() {
            return None;
        }
        let mut res = vec![];
        for (marched_parts, ctx) in marched.into_iter().zip(new_contexts.into_iter()) {
            res.push(LazyWalkReses {
                env: self.env.set(negative_ret_val(), ctx),
                parts: marched_parts,
                ..self.clone()
            });
        }
        Some(res)
    }

    pub fn map_terms<F, E: Clone>(self, f: &mut F) -> Result<LazyWalkReses<Mode>, E>
    where F: FnMut(Name, &Ast) -> Result<Ast, E> {
        Ok(LazyWalkReses {
            parts: self
                .parts
                .named_map(&mut |n: &Name, lwt: &Rc<LazilyWalkedTerm<Mode>>| {
                    Ok(LazilyWalkedTerm::new(&f(*n, &lwt.term)?))
                })
                .lift_result()?,
            ..self
        })
    }

    /// Like `get_rep_res`, but with a different context for each repetition
    pub fn get_rep_res_with(
        &self,
        n: Name,
        new_contexts: Vec<Mode::Elt>,
    ) -> Result<Vec<<Mode::D as Dir>::Out>, Mode::Err> {
        if let Some(sub_parts) = self.march_parts_with(&[n], new_contexts) {
            // Some(sub_parts.iter().map(|sp| sp.get_res(n)).collect())
            let mut res = vec![];
            for sub_part in sub_parts {
                res.push(sub_part.get_res(n)?);
            }
            Ok(res)
        } else {
            icp!("[type error] Length mismatch")
            // Err(()) // TODO: Generate a mode-appropriate error
        }
    }
}

#[test]
fn quote_more_and_less() {
    let parts = LazyWalkReses::<crate::ty::UnpackTy>::new(
        assoc_n!("a" => ast!({"Type" "Nat" :})),
        Assoc::new(),
        // we'll pretend this is under an unquote or something:
        &mbe!("body" => "bind_me"),
        ast!("[ignored]"),
    );

    let parts = parts.with_context(ast!({"Type" "Int" :}));

    let interpolation_accumulator = Rc::new(RefCell::new(Assoc::<Name, Ast>::new()));

    assert_eq!(parts.env.find(&n("a")), Some(&ast!({"Type" "Nat" :})));

    let q_parts = parts.quote_more(Some(interpolation_accumulator.clone()));

    assert_eq!(q_parts.env.find(&n("a")), None);

    // process the binding for "bind_me" as if it were in an unquote
    let (squirreler, interpolation) = q_parts.quote_less();
    let res = interpolation.get_res(n("body")).unwrap();
    assert_eq!(res, assoc_n!("bind_me" => ast!({"Type" "Int" :})));

    // the other thing `unquote` needs to do; save the result for out-of-band retrieval
    squirrel_away::<crate::ty::UnpackTy>(squirreler, res);

    // check that we successfully squirreled it away:
    assert_eq!(*interpolation_accumulator.borrow(), assoc_n!("bind_me" => ast!({"Type" "Int" :})));
}
