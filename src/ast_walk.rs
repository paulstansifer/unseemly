
/*
We often need to walk an `Ast` while maintaining an environment.
So far, this is used both for typechecking and for evaluation.

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
 */


/*
Some forms are positive, and some are negative. 
Positive forms (e.g. expressions) are walked in an environment, and produce a value.
Negative forms (e.g. patterns) still can access their environment, 
 but primarily they look at one special "result" in it, and when they are walked, 
  they produce an environment from that special result.
  
For example, suppose that `five` has type `nat` and `hello` has type `string`:
  - the expression `struct{a: five, b: hello}` produces the type `struct{a: nat, b: string}`
  - the pattern `struct{a: aa, b: bb}` produces 
     the envirnonment where `aa` is `nat` and `bb` is `string`.

At runtime, something similar happens with values and value environments.
*/
use form::Form;
use std::rc::Rc; 
use std::cell::RefCell;
use name::*;
use util::assoc::Assoc;
use util::mbe::EnvMBE;
use ast::Ast;
use ast::Ast::*;
use beta::*;
use std::fmt::Debug;
use runtime::{reify, eval};
use runtime::reify::Reifiable;


pub enum WalkRule<'t, Mode: WalkMode<'t>> {
    /** 
     * A function from the types/values of the *parts* of this form
     *  to the type/value of this form.
     * Note that the environment is not directly accessible! */
    Custom(Rc<Box<(Fn(LazyWalkReses<'t, Mode>) -> Result<Mode::Out, ()>) + 't>>),
    /** "this form has the same type/value as one of its subforms" */
    Body(Name),
    /** "traverse the subterms, and rebuild this syntax around them" */
    LiteralLike,
    /** this form should not ever be typed/evaluated */
    NotWalked 
}

// trait bounds on parameters and functions are not yet supported by `Reifiable!`
impl<'t, Mode: WalkMode<'t> + 't> reify::Reifiable<'t> for WalkRule<'t, Mode> {
    // doesn't need to be parameterized because it will be opaque. I think!?
    fn ty_name() -> Name { n("walk_rule") }

    fn reify(&self) -> eval::Value<'t> { 
        match self {
            &NotWalked => val!(enum "NotWalked",),
            &Body(ref n) => val!(enum "Body", (ident n.clone())),
            &Custom(ref lwr_to_out) => val!(enum "Custom", (, 
                reify::reify_1ary_function(lwr_to_out.clone()))),
            &LiteralLike => val!(enum "LiteralLike",)
        }
    }
    
    fn reflect(v: &eval::Value<'t>) -> Self { 
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
pub type ResEnv<'t, Elt> = Assoc<Name, Elt>;

#[derive(Debug)]
pub struct LazilyWalkedTerm<'t, Mode: WalkMode<'t>> {
    pub term: Ast<'t>,
    pub res: RefCell<Option<Result<Mode::Out, ()>>>
}

// trait bounds on parameters are not yet supported by `Reifiable!`
impl<'t, Mode: WalkMode<'t>> reify::Reifiable<'t> for LazilyWalkedTerm<'t, Mode> {
    // doesn't need to be parameterized because it will be opaque. I think!?
    fn ty_name() -> Name { n("lazily_walked_term") }

    fn reify(&self) -> eval::Value<'t> {
        val!(struct "term" => (, self.term.reify()), "res" => (, self.res.reify()))
    }
    fn reflect(v: &eval::Value<'t>) -> Self { 
        extract!((v) eval::Value::Struct = (ref contents) =>
            LazilyWalkedTerm { term: Ast::<'t>::reflect(contents.find_or_panic(&n("term"))), 
                               res: RefCell::<Option<Result<Mode::Out, ()>>>::reflect(
                                   contents.find_or_panic(&n("res"))) })
    }
}




// We only implement this because lazy-rust is unstable 
impl<'t, Mode : WalkMode<'t>> LazilyWalkedTerm<'t, Mode> {
    pub fn new(t: &Ast<'t>) -> Rc<LazilyWalkedTerm<'t, Mode>> {
        Rc::new(LazilyWalkedTerm { term: t.clone(), res: RefCell::new(None) }) 
    }
        
    /** Get the result of walking this term (memoized) */
    fn get_res(&self, cur_node_contents: &LazyWalkReses<'t, Mode>) -> Result<Mode::Out, ()> {
        self.memoized(&|| walk(&self.term, cur_node_contents))
    }
    
    fn memoized(&self, f: &Fn() -> Result<Mode::Out, ()>) -> Result<Mode::Out, ()> {
        let result = self.res.borrow_mut().take().unwrap_or_else(f);
        * self.res.borrow_mut() = Some(result.clone());
        result
    }
}


/** 
 * Package containing enough information to the subforms of some form on-demand.
 *
 * It is safe to have unwalkable subforms, as long as nothing ever refers to them.
 * 
 * Contents probably shouldn't be `pub`...
 */
#[derive(Debug, Clone)]
pub struct LazyWalkReses<'t, Mode: WalkMode<'t>> {
    /// Things that we have walked and that we might walk
    pub parts: EnvMBE<Rc<LazilyWalkedTerm<'t, Mode>>>,
    /// The environment of the overall walk.
    pub env: ResEnv<'t, Mode::Elt>,
    pub this_form: Rc<Form<'t>> // Seems to be needed to close a loop ) :
}

// trait bounds on parameters are not yet supported by `Reifiable!`
impl<'t, Mode: WalkMode<'t>> reify::Reifiable<'t> for LazyWalkReses<'t, Mode> {
    // doesn't need to be parameterized because it will be opaque. I think!?
    fn ty_name() -> Name { n("lazy_walked_reses") }

    fn reify(&self) -> eval::Value<'t> {
        val!(struct "parts" => (, self.parts.reify()), "env" => (, self.env.reify()), 
                    "this_form" => (, self.this_form.reify()))
    }
    fn reflect(v: &eval::Value<'t>) -> Self { 
        extract!((v) eval::Value::Struct = (ref contents) =>
            LazyWalkReses { parts: EnvMBE::<Rc<LazilyWalkedTerm<'t, Mode>>>::reflect(
                                contents.find_or_panic(&n("parts"))),
                            env: ResEnv::<'t, Mode::Elt>::reflect(
                                contents.find_or_panic(&n("env"))),
                            this_form: Rc::<Form<'t>>::reflect(
                                contents.find_or_panic(&n("this_form")))})
    }
}



impl<'t, Mode: WalkMode<'t>> LazyWalkReses<'t, Mode> {
    pub fn new(env: ResEnv<'t, Mode::Elt>, 
               parts_unwalked: EnvMBE<Ast<'t>>,
               this_form: Rc<Form<'t>>)
            -> LazyWalkReses<'t, Mode> {
        LazyWalkReses {
            env: env,
            parts: parts_unwalked.map(&LazilyWalkedTerm::new),
            this_form: this_form
        }
    }
    
    /** Slight hack: this is just to get a recursion started with some environment. */
    pub fn new_wrapper(env: ResEnv<'t, Mode::Elt>) -> LazyWalkReses<'t, Mode> {
        LazyWalkReses {
            env: env,
            parts: EnvMBE::new(), this_form: ::form::simple_form("<wrapper>", form_pat!([]))
        }
    }
    
    /** The result of walking the subform named `part_name`. This is memoized. */
    pub fn get_res(&self, part_name: &Name) -> Result<Mode::Out, ()> {
        self.parts.get_leaf_or_panic(part_name).get_res(self)
    }

    /** Like `get_res`, but for subforms that are repeated at depth 1. Sort of a hack. */
    pub fn get_rep_res(&self, part_name: &Name) -> Result<Vec<Mode::Out>, ()> {
        self.parts.get_rep_leaf_or_panic(part_name)
            .iter().map( |&lwt| lwt.get_res(self)).collect()
    }
    
    /*/** Like `get_rep_res`, but doesn't panic if the name is absent. */
    pub fn maybe_get_rep_res(&self, part_name: &Name) -> Option<Result<Vec<Mode::Out>, ()>> {
        self.parts.get_rep_leaf(part_name).map(|parts| 
            parts.iter().map( |&lwt| lwt.get_res(self)).collect())
    }*/
    
    /** The subform named `part_name`, without any processing. */
    pub fn get_term(&self, part_name: &Name) -> Ast<'t> {
        self.parts.get_leaf_or_panic(part_name).term.clone()
    }
    
    pub fn get_rep_term(&self, part_name: &Name) -> Vec<Ast<'t>> {
        self.parts.get_rep_leaf_or_panic(part_name)
            .iter().map( |&lwt| lwt.term.clone()).collect()
    }
    
    /** Only sensible for negative walks */
    pub fn context_elt<'f>(&'f self) -> &'f Mode::Elt {
        self.env.find(&negative_ret_val()).unwrap()
    }
    
    /** Change the context. Only sensible for negative walks. */
    pub fn with_context(&self, e: Mode::Elt) -> LazyWalkReses<'t, Mode> {
        LazyWalkReses { env: self.env.set(negative_ret_val(), e), .. (*self).clone() }
    }
    
    /** Change the whole environment */
    pub fn with_environment(&self, env: ResEnv<'t, Mode::Elt>) -> LazyWalkReses<'t, Mode> {
        LazyWalkReses { env: env, .. (*self).clone() }
    }
    
    /** Switch to a different mode with the same `Elt` type. */
    pub fn switch_mode<NewMode: WalkMode<'t, Elt=Mode::Elt>>(&self/*, new_mode: NewMode*/)
            -> LazyWalkReses<'t, NewMode> {
        LazyWalkReses::<'t, NewMode> { 
            env: self.env.clone(),
            parts: self.parts.map(
                &|part: &Rc<LazilyWalkedTerm<'t, Mode>>| 
                    LazilyWalkedTerm::<'t, NewMode>::new(&part.term)),
            this_form:  self.this_form.clone()
        }
    }
    
    /** March by example, turning a repeated set of part names into one LWR per repetition.
     * Keeps the same environment.
     */
    pub fn march_parts(&self, driving_names: &Vec<Name>) -> Vec<LazyWalkReses<'t, Mode>> {
        let marched  = self.parts.march_all(driving_names);
        let mut res = vec![];
        for marched_parts in marched.into_iter() {
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
    pub fn march_all(&self, driving_names: &Vec<Name>) -> Vec<LazyWalkReses<'t, Mode>> {
        self.march_parts(driving_names)
    }
    
    /** Combines `march_parts` and `with_context`. `new_contexts` should have the same length
     * as the repetition marched. 
     */ 
    pub fn march_parts_with(&self, driving_names: &Vec<Name>, new_contexts: Vec<Mode::Elt>)
             -> Option<Vec<LazyWalkReses<'t, Mode>>> {
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
            -> Result<Vec<Mode::Out>, ()> {
        if let Some(sub_parts) = self.march_parts_with(&vec![*n], new_contexts) {
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
 * Make a `Mode::Out` by walking `expr` in the environment from `cur_node_contents`.
 * HACK: The parts in `cur_node_contents` are ignored; it's just an environment to us.
 */
pub fn walk<'t, Mode: WalkMode<'t>>(expr: &Ast<'t>, cur_node_contents: &LazyWalkReses<'t, Mode>)
        -> Result<Mode::Out, ()> {
    match *expr {
        Node(ref f, ref parts) => {
            // certain walks only work on certain kinds of AST nodes
            match Mode::get_walk_rule(f) {
                &Custom(ref ts_fn) => {
                    let res = ts_fn(LazyWalkReses::new(
                        cur_node_contents.env.clone(), parts.clone(), f.clone()));
                    res
                }
                
                &Body(ref n) => {
                    walk(parts.get_leaf(n).unwrap(),
                         &LazyWalkReses::<Mode>::new(
                             cur_node_contents.env.clone(), parts.clone(), f.clone()))
                }
                
                &LiteralLike => {
                    if Mode::positive() {
                        // rebuild the node around a recursive descent
                        let rebuilt = Node(f.clone(),
                            try!(parts.map(
                                &|p| match *p {
                                    Node(_, _) => walk(p, cur_node_contents),
                                    _ => Ok(Mode::ast_to_out(p.clone()))
                                }.map(Mode::out_to_ast)).lift_result()));
                                
                        Ok(Mode::ast_to_out(rebuilt))
                    } else {
                        let ctxt = cur_node_contents.context_elt();
                        // HACK: I don't want to add yet another thing to all the modes:
                        let ctxt = Mode::out_to_ast(
                            Mode::var_to_out(&n("only"),
                                &assoc_n!("only" => ctxt.clone())).unwrap());
                                
                        //type Res<'t, Mode: WalkMode<'t>> = Result<Assoc<Name, Mode::Elt>, ()>;

                        // break apart the node, and walk it element-wise
                        if let Node(ref f_actual, ref parts_actual) = ctxt {
                            // TODO: wouldn't it be nice to have match failures that 
                            //  contained useful `diff`-like information for debugging,
                            //   when a match was expected to succeed?
                            // (I really like using pattern-matching in unit tests!)
                            if f != f_actual { return Err(()); /* match failure */ }
                            
                            fn combine<'t, 'f, Mode: WalkMode<'t>>(result: &'f Result<Assoc<Name, Mode::Elt>, ()>, next: &'f Result<Assoc<Name, Mode::Elt>, ()>) -> Result<Assoc<Name, Mode::Elt>, ()> {
                                Ok(try!(result.clone()).set_assoc(&try!(next.clone())))
                            }
                            
                            // TODO: this continues walking after a subterm fails to match;
                            //  it should bail out immediately
                            let res = parts.map_reduce_with::<Result<Assoc<Name, Mode::Elt>, ()>>(&parts_actual,
                                &|model: &Ast<'t>, actual: &Ast<'t>| {
                                    walk(model, 
                                        &cur_node_contents.with_context(
                                            Mode::ast_to_elt(actual.clone(), cur_node_contents)))
                                        .map(Mode::out_to_env)
                                },
                                &|result, next| {
                                    let r: Assoc<Name, Mode::Elt> = try!(result.clone());
                                    let n: Assoc<Name, Mode::Elt> = try!(next.clone());
                                    Ok(r.set_assoc(&n))
                                },
                                //panic!("I don't understand lifetimes enough to make this work!"),
                                Ok(cur_node_contents.env.clone()));
                            
                            res.map(Mode::env_to_out)
                        } else {
                            Err(()) /* match failure */
                        }
                    }
                }
                
                &NotWalked => { panic!( "{:?} should not be walked at all!", expr ) }
            }
        }
        IncompleteNode(ref parts) => { panic!("{:?} isn't a complete node", parts)}
        
        VariableReference(ref n) => { Mode::var_to_out(n, &cur_node_contents.env) }
        
        Trivial | Atom(_) | Shape(_) => {
            panic!("{:?} is not a walkable node", expr);
        }
        
        ExtendEnv(ref body, ref beta) => {
            let new_env = cur_node_contents.env.set_assoc(
                &try!(env_from_beta(beta, cur_node_contents)));

            walk(&**body, &cur_node_contents.with_environment(new_env))
        }
    }
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

pub trait WalkMode<'t> : Debug + Copy + Reifiable<'t> {
    /** The output of the walking process.
     *
     * Negated walks produce an environment of Self::Elt, positive walks produce Self::Elt.
     */
    type Out : Clone + Debug + Reifiable<'t>;
    
    /** The object type for the environment to walk in. */
    type Elt : Clone + Debug + Reifiable<'t>;
    
    type Negative : WalkMode<'t, Elt=Self::Elt>;
    
    fn get_walk_rule<'f>(&'f Form<'t>) -> &'f WalkRule<'t, Self> where Self: Sized ;

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

    fn automatically_extend_env() -> bool { false }
    
    fn ast_to_elt(a: Ast<'t>, _: &LazyWalkReses<'t, Self>) -> Self::Elt {
        panic!("not implemented: {:?} cannot be converted", a)
    }
    
    fn ast_to_out(a: Ast<'t>) -> Self::Out {
        panic!("not implemented: {:?} cannot be converted", a)
    }
    
    fn out_to_env(o: Self::Out) -> Assoc<Name, Self::Elt> {
        panic!("not implemented: {:?} cannot be converted", o)
    }
    
    fn env_to_out(e: Assoc<Name, Self::Elt>) -> Self::Out {
        panic!("not implemented: {:?} cannot be converted", e)        
    }
    
    fn out_to_elt(o: Self::Out) -> Self::Elt {
        panic!("not implemented: {:?} cannot be converted", o)
    }
    
    fn out_to_ast(o: Self::Out) -> Ast<'t> {
        panic!("not implemented: {:?} cannot be converted", o)
    }
    
    fn var_to_out(var: &Name, env: &ResEnv<'t, Self::Elt>) -> Result<Self::Out, ()>;
    
    fn positive() -> bool;
}

/** var_to_out, for positive walks where Out == Elt */
pub fn var_lookup<'t, Elt: Debug + Clone>(n: &Name, env: &Assoc<Name, Elt>) 
        -> Result<Elt, ()> {
    Ok((*env.find(n).expect(format!("Name {:?} unbound in {:?}", n, env).as_str())).clone())
}

/** var_to_out, for negative walks where Out == Assoc<Name, Elt> */
pub fn var_bind<'t, Elt: Debug + Clone>(n: &Name, env: &Assoc<Name, Elt>) 
        -> Result<Assoc<Name, Elt>, ()> {
    Ok(Assoc::new().set(n.clone(), env.find(&negative_ret_val()).unwrap().clone()))
}
