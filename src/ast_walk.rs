
/*
We often need to walk an `Ast` while maintaining an environment.
This seems to be true at typecheck time and at runtime.

Our `Ast`s have information about
 what should happen environment-wise baked-in,
  so `walk` processes `ExtendEnv` and `VariableReference` on its own.
When it reaches a `Node`, the user has to specify
 (through the definition of the respective form)
  what to do, using a `WalkRule`.
The most interesting `WalkRule`, `Custom`,
 specifies an arbitrary function on the results of walking its subterms.
Subterms are walked lazily, since not all of them are even evaluable/typeable,
 and they might need to be walked in a specific order.
 
I may have committed some light type sorcery to make this happen.
 */

/*
There are different kinds of walks. Here are the ones Unseemly needs so far:

Evaluation prodcues a `Value` or an error.
During evaluation, each `lambda` form may be processed many times, 
 with different values for its parameters.

Typechecking produces `Ty` or an error.
During typechecking, each `lambda` form is processed once,
 using its parameters' declared types.
 
Subtyping produces `Ty` (irrelevant) or an error.
It only walks type Asts, so `lambda` is not walked,
 but ∀ is a binding form that acts sort of like type-level lambda,
  except we use unification instead of explicit "function" calls.

Quasiquotation, typically a part of evaluation, produces a `Value::AbstractSyntax`.
Typically, it is triggered by a specific quotative form, 
 and it's very simple to implement; it just reifies syntax.
Unseemly is special in that `lambda` even binds under quasiquotation,
 despite the fact that it doesn't do anything until the reified syntax is evaluated.

*/

/*
When we walk an `Ast`, we encounter many different forms.

Some forms are positive, and some are negative. 

Positive forms (e.g. expressions and variable references)
 are walked in an environment, and produce a "result" value.

Negative forms (e.g. patterns and variable bindings) 
 still can access their environment, 
  but primarily they look at one special "result" in it, and when they are walked, 
   they produce an environment from that special result.
  
For example, suppose that `five` has type `nat` and `hello` has type `string`:
  - the expression `struct{a: five, b: hello}` produces the type `struct{a: nat, b: string}`
  - the pattern `struct{a: aa, b: bb}` produces 
     the envirnonment where `aa` is `nat` and `bb` is `string`.

At runtime, something similar happens with values and value environments.

Some forms are "ambidextrous". 
Everything should be ambidextrous under quasiquotation,
 because all syntax should be constructable and matchable.

*/
use form::{Form, BiDiWR};
use std::rc::Rc; 
use std::cell::RefCell;
use name::*;
use util::assoc::Assoc;
use util::mbe::EnvMBE;
use ast::Ast;
use ast::Ast::*;
use beta::*;
use std::fmt::{Debug, Display};
use runtime::{reify, eval};
use runtime::reify::Reifiable;


pub enum WalkRule<Mode: WalkMode> {
    /** 
     * A function from the types/values of the *parts* of this form
     *  to the type/value of this form.
     * Note that the environment is not directly accessible! */
    Custom(Rc<Box<(Fn(LazyWalkReses<Mode>) -> Result<Mode::Out, Mode::Err>)>>),
    /** "this form has the same type/value as one of its subforms" */
    Body(Name),
    /** "traverse the subterms, and rebuild this syntax around them" */
    LiteralLike,
    /** this form should not ever be typed/evaluated */
    NotWalked 
}

// trait bounds on parameters and functions are not yet supported by `Reifiable!`
impl<Mode: WalkMode + Copy + 'static> reify::Reifiable for WalkRule<Mode> {
    // doesn't need to be parameterized because it will be opaque. I think!?
    fn ty_name() -> Name { n("walk_rule") }

    fn reify(&self) -> eval::Value { 
        match *self {
            NotWalked => val!(enum "NotWalked",),
            Body(ref n) => val!(enum "Body", (ident n.clone())),
            Custom(ref lwr_to_out) => val!(enum "Custom", (, 
                reify::reify_1ary_function(lwr_to_out.clone()))),
            LiteralLike => val!(enum "LiteralLike",)
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
                panic!("ICE in WalkRule reflection")
            })
    }
}


pub use self::WalkRule::*;

/** An environment of walked things. */
pub type ResEnv<Elt> = Assoc<Name, Elt>;

#[derive(Debug)]
pub struct LazilyWalkedTerm<Mode: WalkMode> {
    pub term: Ast,
    pub res: RefCell<Option<Result<Mode::Out, Mode::Err>>>
}

// trait bounds on parameters are not yet supported by `Reifiable!`
impl<Mode: WalkMode> reify::Reifiable for LazilyWalkedTerm<Mode> {
    // doesn't need to be parameterized because it will be opaque. I think!?
    fn ty_name() -> Name { n("lazily_walked_term") }

    fn reify(&self) -> eval::Value {
        val!(struct "term" => (, self.term.reify()), "res" => (, self.res.reify()))
    }
    fn reflect(v: &eval::Value) -> Self { 
        extract!((v) eval::Value::Struct = (ref contents) =>
            LazilyWalkedTerm { term: Ast::reflect(contents.find_or_panic(&n("term"))), 
                               res: RefCell::<Option<Result<Mode::Out, Mode::Err>>>::reflect(
                                   contents.find_or_panic(&n("res"))) })
    }
}




// We only implement this because lazy-rust is unstable 
impl<Mode: WalkMode> LazilyWalkedTerm<Mode> {
    pub fn new(t: &Ast) -> Rc<LazilyWalkedTerm<Mode>> {
        Rc::new(LazilyWalkedTerm { term: t.clone(), res: RefCell::new(None) }) 
    }
        
    /** Get the result of walking this term (memoized) */
    fn get_res<NewMode: WalkMode<Out=Mode::Out, Err=Mode::Err>>
            (&self, cur_node_contents: &LazyWalkReses<NewMode>)
            -> Result<Mode::Out, NewMode::Err> {
        self.memoized(&|| walk::<NewMode>(&self.term, cur_node_contents))
    }
    
    fn memoized(&self, f: &Fn() -> Result<Mode::Out, Mode::Err>) -> Result<Mode::Out, Mode::Err> {
        let result = self.res.borrow_mut().take().unwrap_or_else(f);
        * self.res.borrow_mut() = Some(result.clone());
        result
    }
}


/** 
 * Package containing enough information to walk the subforms of some form on-demand.
 *
 * It is safe to have unwalkable subforms, as long as nothing ever refers to them.
 * 
 * Contents probably shouldn't be `pub`...
 */
#[derive(Debug, Clone)]
pub struct LazyWalkReses<Mode: WalkMode> {
    /// Things that we have walked and that we might walk
    pub parts: EnvMBE<Rc<LazilyWalkedTerm<Mode>>>,
    /// The environment of the overall walk.
    pub env: ResEnv<Mode::Elt>,
    pub this_form: Rc<Form> // Seems to be needed to close a loop ) :
    //TODO: add the whole form for error reporting
}

// trait bounds on parameters are not yet supported by `Reifiable!`
impl<Mode: WalkMode> reify::Reifiable for LazyWalkReses<Mode> {
    // doesn't need to be parameterized because it will be opaque. I think!?
    fn ty_name() -> Name { n("lazy_walked_reses") }

    fn reify(&self) -> eval::Value {
        val!(struct "parts" => (, self.parts.reify()), "env" => (, self.env.reify()), 
                    "this_form" => (, self.this_form.reify()))
    }
    fn reflect(v: &eval::Value) -> Self { 
        extract!((v) eval::Value::Struct = (ref contents) =>
            LazyWalkReses { parts: EnvMBE::<Rc<LazilyWalkedTerm<Mode>>>::reflect(
                                contents.find_or_panic(&n("parts"))),
                            env: ResEnv::<Mode::Elt>::reflect(
                                contents.find_or_panic(&n("env"))),
                            this_form: Rc::<Form>::reflect(
                                contents.find_or_panic(&n("this_form")))})
    }
}



impl<Mode: WalkMode> LazyWalkReses<Mode> {
    pub fn new(env: ResEnv<Mode::Elt>, 
               parts_unwalked: EnvMBE<Ast>,
               this_form: Rc<Form>)
            -> LazyWalkReses<Mode> {
        LazyWalkReses {
            env: env,
            parts: parts_unwalked.map(&LazilyWalkedTerm::new),
            this_form: this_form
        }
    }
    
    /** Slight hack: this is just to get a recursion started with some environment. */
    pub fn new_wrapper(env: ResEnv<Mode::Elt>) -> LazyWalkReses<Mode> {
        LazyWalkReses {
            env: env,
            parts: EnvMBE::new(), this_form: ::form::simple_form("<wrapper>", form_pat!([]))
        }
    }
    
    // TODO: this should probably actually be stored, rather than reconstructed.
    pub fn as_ast(&self) -> Ast {
        Node(self.this_form.clone(),
             self.parts.clone().map(
                 &|x: &Rc<::ast_walk::LazilyWalkedTerm<Mode>>| x.term.clone()))
    }
    
    /** The result of walking the subform named `part_name`. This is memoized. */
    pub fn get_res(&self, part_name: &Name) -> Result<Mode::Out, Mode::Err> {
        self.parts.get_leaf_or_panic(part_name).get_res(self)
    }

    /** Like `get_res`, but for subforms that are repeated at depth 1. Sort of a hack. */
    pub fn get_rep_res(&self, part_name: &Name) -> Result<Vec<Mode::Out>, Mode::Err> {
        self.parts.get_rep_leaf_or_panic(part_name)
            .iter().map( |&lwt| lwt.get_res(self)).collect()
    }
    
    /*/** Like `get_rep_res`, but doesn't panic if the name is absent. */
    pub fn maybe_get_rep_res(&self, part_name: &Name) -> Option<Result<Vec<Mode::Out>, Mode::Err>> {
        self.parts.get_rep_leaf(part_name).map(|parts| 
            parts.iter().map( |&lwt| lwt.get_res(self)).collect())
    }*/
    
    /** The subform named `part_name`, without any processing. */
    pub fn get_term(&self, part_name: &Name) -> Ast {
        self.parts.get_leaf_or_panic(part_name).term.clone()
    }
    
    pub fn get_rep_term(&self, part_name: &Name) -> Vec<Ast> {
        self.parts.get_rep_leaf_or_panic(part_name)
            .iter().map( |&lwt| lwt.term.clone()).collect()
    }
    
    /** Only sensible for negative walks */
    pub fn context_elt(&self) -> &Mode::Elt {
        self.env.find(&negative_ret_val()).unwrap()
    }
    
    /** Change the context. Only sensible for negative walks. */
    pub fn with_context(&self, e: Mode::Elt) -> LazyWalkReses<Mode> {
        LazyWalkReses { env: self.env.set(negative_ret_val(), e), .. (*self).clone() }
    }
    
    /** Change the whole environment */
    pub fn with_environment(&self, env: ResEnv<Mode::Elt>) -> LazyWalkReses<Mode> {
        LazyWalkReses { env: env, .. (*self).clone() }
    }

    
    /** Switch to a different mode with the same `Elt` type. */
    pub fn switch_mode<NewMode: WalkMode<Elt=Mode::Elt>>(&self) -> LazyWalkReses<NewMode> {
        let new_parts: EnvMBE<Rc<LazilyWalkedTerm<NewMode>>> = 
            self.parts.map(
                &|part: &Rc<LazilyWalkedTerm<Mode>>| 
                    LazilyWalkedTerm::<NewMode>::new(&part.term));
        LazyWalkReses::<NewMode> { 
            env: self.env.clone(),
            parts: new_parts,
            this_form:  self.this_form.clone()
        }
    }
    
    /** March by example, turning a repeated set of part names into one LWR per repetition.
     * Keeps the same environment.
     */
    pub fn march_parts(&self, driving_names: &[Name]) -> Vec<LazyWalkReses<Mode>> {
        let marched  = self.parts.march_all(driving_names);
        let mut res = vec![];
        for marched_parts in marched {
            res.push(LazyWalkReses{
                env: self.env.clone(), parts: marched_parts, this_form: self.this_form.clone()
            });
        }
        res
    }
    
    /**
     * HACK: For the sake of `mbe_one_name`, we want to treat `LazyWalkReses` and `EnvMBE` 
     * the same way. But I don't like having the same interface for them in general; I find it
     * confusing. So don't use this ): 
     */
    pub fn march_all(&self, driving_names: &[Name]) -> Vec<LazyWalkReses<Mode>> {
        self.march_parts(driving_names)
    }
    
    /** Combines `march_parts` and `with_context`. `new_contexts` should have the same length
     * as the repetition marched. 
     */ 
    pub fn march_parts_with(&self, driving_names: &[Name], new_contexts: Vec<Mode::Elt>)
             -> Option<Vec<LazyWalkReses<Mode>>> {
        let marched  = self.parts.march_all(driving_names);
        if marched.len() != new_contexts.len() { return None; }
        let mut res = vec![];
        for (marched_parts, ctx) in marched.into_iter().zip(new_contexts.into_iter()) {
            res.push(LazyWalkReses{env: self.env.set(negative_ret_val(), ctx), 
                                   parts: marched_parts,
                                   this_form: self.this_form.clone()});
        }
        Some(res)
    }
    
    /** Like `get_rep_res`, but with a different context for each repetition */
    pub fn get_rep_res_with(&self, n: &Name, new_contexts: Vec<Mode::Elt>)
            -> Result<Vec<Mode::Out>, Mode::Err> {
        if let Some(sub_parts) = self.march_parts_with(&[*n], new_contexts) {
            //Some(sub_parts.iter().map(|sp| sp.get_res(n)).collect())
            let mut res = vec![];
            for sub_part in sub_parts {
                res.push(try!(sub_part.get_res(n)));
            }
            Ok(res)
        } else {
            panic!("Type error: Length mismatch")
            //Err(()) // TODO: When we actually start using results, emit something specific.
        }
    }
}

/**
 * Make a `Mode::Out` by walking `node` in the environment from `cur_node_contents`.
 * HACK: The parts in `cur_node_contents` are ignored; it's just an environment to us.
 */
pub fn walk<Mode: WalkMode>(node: &Ast, cur_node_contents: &LazyWalkReses<Mode>)
        -> Result<Mode::Out, Mode::Err> {
    print!("WALK: {:?}\n", node);
    match *node {
        Node(ref f, ref parts) => {
            // certain walks only work on certain kinds of AST nodes
            match *Mode::get_walk_rule(f) {
                Custom(ref ts_fn) => {
                    ts_fn(LazyWalkReses::new(
                        cur_node_contents.env.clone(), parts.clone(), f.clone()))
                }
                
                Body(n) => {
                    walk(parts.get_leaf(&n).unwrap(),
                         &LazyWalkReses::<Mode>::new(
                             cur_node_contents.env.clone(), parts.clone(), f.clone()))
                }
                
                LiteralLike => {
                    Mode::walk_quasi_literally(f, parts, cur_node_contents)
                }
                
                NotWalked => { panic!( "ICE: {:?} should not be walked at all!", node ) }
            }
        }
        IncompleteNode(ref parts) => { panic!("ICE: {:?} isn't a complete node", parts)}
        
        VariableReference(n) => { Ok(Mode::walk_var(n, &cur_node_contents)) }
        
        Trivial | Atom(_) | Shape(_) => {
            panic!("ICE: {:?} is not a walkable node", node);
        }
        
        ExtendEnv(ref body, ref beta) => {
            let new_env = cur_node_contents.env.set_assoc(
                &try!(env_from_beta(beta, cur_node_contents)));

            walk(&**body, &cur_node_contents.with_environment(new_env))
        }
    }
}

/**
 * This trait makes a type producable by positive and negative walks.
 * I'm not sure this information belongs on the type produced by the walk, 
 *  but there doesn't seem to be a better place to put it.
 */
 
 // The fact that we need this type parameter makes me unhappy. Is there any way around it?
pub trait WalkElt<Mode: WalkMode>: Clone + Debug + Reifiable {
    type Err : Debug /* TODO: use Display, when all errors are in place */ + Reifiable + Clone;
    
    fn get_bidi_walk_rule(f: &Form) -> &::form::BiDiWR<Mode, Mode::Negative>;
     
    fn automatically_extend_env() -> bool;
    
    fn underspecified() -> Self {
        panic!("underspecification not supported!")
    }
    
    fn mismatch_error(Self, Self) -> Self::Err {
        panic!("mismatch is not supported for all elements")
    }
    
    fn from_ast(a: &Ast) -> Self;
    fn to_ast(&self) -> Ast;
}

/**
 * This trait exists to connect `Form`s to different kinds of walks.
 *
 * There are two kinds of walks over `Ast`s:
 *  * Positive walks produce an element (a value or type, say) from an environment.
 *    They are for expression-like terms.
 *  * Negative walks produce an environment from an element.
 *    They are for pattern-like terms.
 *
 * Now, the whole environment is actually present in both cases, 
 *  and negative walks can actually use it 
 *   -- the special value they traverse is stored in the environment with a special name --
 *  but they conceptually are mostly relying on the special value.
 */

pub trait WalkMode : Debug + Copy + Reifiable {
    /** The object type for the environment to walk in. */
    type Elt : Clone + Debug + Reifiable;
    
    /** The output of the walking process.
     *
     * Negated walks produce an environment of Self::Elt, positive walks produce Self::Elt.
     */
    type Out : Clone + Debug + Reifiable;
    
    type Err : Debug /*Display*/ + Reifiable + Clone;
    
    /** The negated version of this walk */    
    type Negative : WalkMode<Elt=Self::Elt, Err=Self::Err, Negative=Self>;
    
    
    fn get_walk_rule(&Form) -> &WalkRule<Self> where Self: Sized ;

    /**
     Should the walker extend the environment based on imports?
    
     While `Beta`s are great for typechecking,
      evaluation sometimes extends environments
       in ways that they can't handle.
     (In particular, λ causes the `Ast` containing the `ExtendEnv`
       to be moved to a context where its `Beta`s are meaningless!
     If `!automatically_extend_env()`, the `Custom` implementation
      must extend the environment properly to be safe.
     */
    fn automatically_extend_env() -> bool;
    
    /** 
     (negative only)
     Make up a special `Elt` that is currently "underspecified",
      but which can be "unified" with some other `Elt`.
     If that happens, all copies of this `Elt` will act like that other one.
     
     Side-effects under the covers make this work.
     */
    fn underspecified_elt() -> Self::Elt;
    
    /**
     * (negative only) What happens if destructuring fails? 
     */
    fn qlit_mismatch_error(Self::Elt, Self::Elt) -> Self::Err;
    
    /**
     * (negative only) Possibly swap out a variable before matching.
     *
    fn pre_match(Self::Elt, Self::Elt) -> Self::Elt;
    */
    
    /**
     Walk over the structure of a node, not its meaning.
     This could be because we're inside a syntax-quote,
      or it could be that we are a form (like written-out types or a literal)
       that acts like a literal.
     Children are not necessarily walked quasiliterally
      -- maybe they're an interpolation of some kind --
       instead, the mode (=quotation depth) and form together decide what to do.
     If the walk is negative, the result might be MatchFailure
     */
    fn walk_quasi_literally(f: &Rc<Form>, parts: &EnvMBE<Ast>, 
                            cnc: &LazyWalkReses<Self>) 
        -> Result<Self::Out, Self::Err>;

    // We need to dynamically do these if it's possible, for `env_from_beta`        
    fn out_as_elt(Self::Out) -> Self::Elt;
    fn out_as_env(Self::Out) -> Assoc<Name, Self::Elt>;
    
    fn walk_var(Name, &LazyWalkReses<Self>) -> Self::Out;
}

custom_derive! {
    #[derive(Clone, Debug, Reifiable)]
    pub struct PositiveWalkMode<Elt, T> { pd: ::std::marker::PhantomData<Elt>, t: T }
}

impl<Elt: Clone, T: Copy> Copy for PositiveWalkMode<Elt, T> {}

impl<T: Copy + Debug + Reifiable, Elt: WalkElt<PositiveWalkMode<Elt, T>>>
        WalkMode for PositiveWalkMode<Elt, T> {
    type Out = Elt;
    type Elt = Elt;
    type Negative = NegativeWalkMode<Elt, T>;
    
    type Err = Elt::Err;

    // TODO: maybe remove, use Elt::get_walk_rule() directly   
    fn get_walk_rule(f: &Form) -> &WalkRule<Self> { 
        Self::Elt::get_bidi_walk_rule(f).pos()
    }
    
    // TODO: likewise
    fn automatically_extend_env() -> bool { Elt::automatically_extend_env() }

    // TODO: likewise    
    fn underspecified_elt() -> Self::Elt {
        Self::Elt::underspecified()
    }

    fn qlit_mismatch_error(_: Self::Elt, _: Self::Elt) -> Self::Err {
        panic!("can't happen; negative-only")
    }
        
    fn walk_quasi_literally(f: &Rc<Form>, parts: &EnvMBE<Ast>, 
                            cnc: &LazyWalkReses<Self>) 
            -> Result<Self::Out, Self::Err> {
        
        // TODO: I think we need a separate version of `walk` that doesn't panic on `MatchFailure`
        let walked : Result<EnvMBE<Ast>, Self::Err> = parts.map(
            &|p: &Ast| match *p {
                Node(_, _) => walk(p, cnc),
                _ => Ok(Elt::from_ast(&p.clone()))
            }.map(|e| Elt::to_ast(&e))).lift_result();

        walked.map(|out| Elt::from_ast(&Node(f.clone(), out)))      
        
        /*
        //panic!("TODO: I don't understand the code I wrote for this")
        
        let walked_subterms : Result<EnvMBE<Self::Out>, _> = parts.map(
            &|p: &Ast| -> Result<Self::Out, Self::Err> {
                match *p {
                    // Yes, `walk`, not `w_q_l`; the mode is in charge of figuring things out.
                    Node(_,_) => { walk(p, cnc) },
                    _ => Ok(Elt::from_ast(&p.clone()))
                }.map(|e:Elt| Elt::to_ast(&e))
            }).lift_result();
                
        Ok(Elt::from_ast(&Node(f.clone(), walked_subterms)))*/
    }
    
    /// Look up variable in the environment!
    fn walk_var(n: Name, cnc: &LazyWalkReses<Self>) -> Self::Out {
        cnc.env.find_or_panic(&n).clone()
    }
    
    fn out_as_elt(o: Self::Out) -> Self::Elt { o }
    fn out_as_env(_: Self::Out) -> Assoc<Name, Self::Elt> { panic!("ICE: out is not an env") }
}

custom_derive! {
    #[derive(Clone, Debug, Reifiable)]
    pub struct NegativeWalkMode<Elt, T> { pd: ::std::marker::PhantomData<Elt>, t: T }
}

impl<Elt: Clone, T: Copy> Copy for NegativeWalkMode<Elt, T> {}

impl<T: Copy + Debug + Reifiable, Elt: WalkElt<PositiveWalkMode<Elt, T>>>
        NegativeWalkMode<Elt, T> {
    // Match the context element against the current node
    pub fn context_match(f: &Rc<Form>, parts: &EnvMBE<Ast>, got: &Elt, env: Assoc<Name, Elt>)
            -> Result<EnvMBE<Ast>, <Self as WalkMode>::Err> {
        let ctxt = Elt::to_ast(got);

        //type Res = Result<Assoc<Name, Self::Elt>, ()>;

        // TODO Needs freshening (like what Romeo does)!
        // I only spent three years or so on hygenic destructuring, 
        //  so it's not surprising that I forgot that I'd need to do it.
        
        // break apart the node, and walk it element-wise
        if let Node(f_actual, parts_actual) = ctxt {
            // TODO: wouldn't it be nice to have match failures that 
            //  contained useful `diff`-like information for debugging,
            //   when a match was expected to succeed?
            // (I really like using pattern-matching in unit tests!)
            if **f != *f_actual { /* different form */
                let expd_elt = Elt::from_ast(&Node(f.clone(), parts.clone()));
                return Err(Self::qlit_mismatch_error(got.clone(), expd_elt));
            }

            Ok(parts_actual)
        } else { /* Didn't even get a form */
            let expd_elt = Elt::from_ast(&Node(f.clone(), parts.clone()));
            Err(Self::qlit_mismatch_error(got.clone(), expd_elt))
        }        
    }
}

impl<T: Copy + Debug + Reifiable, Elt: WalkElt<PositiveWalkMode<Elt, T>>> 
        WalkMode for NegativeWalkMode<Elt, T> {
    type Out = Assoc<Name, Elt>;
    type Elt = Elt;
    type Negative = PositiveWalkMode<Elt, T>;
    
    type Err = Elt::Err;

    // TODO: mabye remove, use Elt::get_walk_rule() directly   
    fn get_walk_rule(f: &Form) -> &WalkRule<Self> { 
        Self::Elt::get_bidi_walk_rule(f).neg()
    }
    
    // TODO: likewise
    fn automatically_extend_env() -> bool { Elt::automatically_extend_env() }
    
    // TODO: likewise    
    fn underspecified_elt() -> Self::Elt {
        Self::Elt::underspecified()
    }
    
    /*fn pre_match(got: Self::Elt, expd: Self::Elt) -> Self::Elt {
        panic!("not implemented for this mode")
    }*/

    // TODO: can we move this off Elt and onto the modes themselves?    
    fn qlit_mismatch_error(got: Self::Elt, expd: Self::Elt) -> Self::Err {
        Self::Elt::mismatch_error(got, expd)
    }
    
    fn walk_quasi_literally(f: &Rc<Form>, parts: &EnvMBE<Ast>, 
                            cnc: &LazyWalkReses<Self>) 
            -> Result<Self::Out, Self::Err> {

        let parts_actual = try!(Self::context_match(f, parts, cnc.context_elt(), cnc.env.clone()));
        
        parts.map_reduce_with(&parts_actual,
            &|model: &Ast, actual: &Ast| {
                walk(model, &cnc.with_context(Elt::from_ast(actual)))
            },
            &|result, next| { Ok(try!(result.clone()).set_assoc(&try!(next.clone()))) },
            Ok(cnc.env.clone()))
    }
    
    /// Bind variable to the context!
    fn walk_var(n: Name, cnc: &LazyWalkReses<Self>) -> Self::Out {
        Assoc::new().set(n, cnc.context_elt().clone())
    }

    fn out_as_elt(_: Self::Out) -> Self::Elt { panic!("ICE: Out ≠ Elt in negative walks") }
    fn out_as_env(o: Self::Out) -> Assoc<Name, Self::Elt> { o }
}



/** `var_to_out`, for positive walks where `Out` == `Elt` */
pub fn var_lookup<Elt: Debug + Clone>(n: &Name, env: &Assoc<Name, Elt>) 
        -> Result<Elt, ()> {
    Ok((*env.find(n).expect(format!("Name {:?} unbound in {:?}", n, env).as_str())).clone())
}

/** `var_to_out`, for negative walks where `Out` == `Assoc<Name, Elt>`` */
pub fn var_bind<Elt: Debug + Clone>(n: &Name, env: &Assoc<Name, Elt>) 
        -> Result<Assoc<Name, Elt>, ()> {
    Ok(Assoc::new().set(*n, env.find(&negative_ret_val()).unwrap().clone()))
}
