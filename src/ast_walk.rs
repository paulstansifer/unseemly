
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
TODO: generalize to handle patterns, which are negated expressions.
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
use parse::FormPat::AnyToken; // for making simple forms for testing
use std::fmt::Debug;


pub enum WalkRule<'t, Mode: WalkMode<'t>> {
    /** 
     * A function from the types/values of the *parts* of this form
     *  to the type/value of this form.
     * Note that the environment is not directly accessible! */
    Custom(Box<(Fn(LazyWalkReses<'t, Mode>) -> Result<Mode::Out, ()>) + 't>),
    /** "this form has the same type/value as one of its subforms" */
    Body(Name<'t>), 
    /** this form should not ever be typed/evaluated */
    NotWalked 
}

pub use self::WalkRule::*;

/** An environment of walked things. */
pub type ResEnv<'t, Out> = Assoc<Name<'t>, Out>;

#[derive(Debug)]
pub struct LazilyWalkedTerm<'t, Mode: WalkMode<'t>> {
    pub term: Ast<'t>,
    pub res: RefCell<Option<Result<Mode::Out, ()>>>
}

// We only implement this because lazy-rust is unstable 
impl<'t, Mode : WalkMode<'t>> LazilyWalkedTerm<'t, Mode> {
    pub fn new(t: Ast<'t>) -> Rc<LazilyWalkedTerm<'t, Mode>> {
        Rc::new(LazilyWalkedTerm { term: t, res: RefCell::new(None) }) 
    }
    
    fn get_res(&self, cur_node_contents: &LazyWalkReses<'t, Mode>) 
               -> Result<Mode::Out, ()> {
        let result = 
            self.res.borrow_mut().take().unwrap_or_else(
                || walk(&self.term, cur_node_contents.mode,
                        cur_node_contents.env.clone(),
                        cur_node_contents));
        
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
    pub parts: EnvMBE<'t, Rc<LazilyWalkedTerm<'t, Mode>>>,
    pub env: ResEnv<'t, Mode::Out>,
    mode: Mode
}

/*
impl<'t, Mode: WalkMode<'t>> Clone for LazyWalkReses<'t, Mode> {
    fn clone(&self) -> LazyWalkReses<'t, Mode> {
        LazyWalkReses {
            parts: self.parts.clone(), env: self.env.clone(), mode: self.mode
        }
    }
}
*/

impl<'t, Mode: WalkMode<'t>> LazyWalkReses<'t, Mode> {
    pub fn new(mode: Mode, 
               env: ResEnv<'t, Mode::Out>, 
               parts_unwalked: EnvMBE<'t, Ast<'t>>)
            -> LazyWalkReses<'t, Mode> {
        LazyWalkReses {
            env: env,
            parts: parts_unwalked.map(&LazilyWalkedTerm::new),
            mode: mode
        }
    }
    
    /** The result of walking the subform named `part_name`. This is memoized. */
    pub fn get_res(&self, part_name: &Name<'t>) -> Result<Mode::Out, ()> {
        self.parts.get_leaf_or_panic(part_name).get_res(self)
    }

    /** Like `get_res`, but for subforms that are repeated at depth 1. Sort of a hack. */
    pub fn get_rep_res(&self, part_name: &Name<'t>) -> Result<Vec<Mode::Out>, ()> {
        self.parts.get_rep_leaf_or_panic(part_name)
            .iter().map( |&lwt| lwt.get_res(self)).collect()
    }
    
    /** The subform named `part_name`, without any processing. */
    pub fn get_term(&self, part_name: &Name<'t>) -> Ast<'t> {
        self.parts.get_leaf_or_panic(part_name).term.clone()
    }
    
    pub fn get_rep_term(&self, part_name: &Name<'t>) -> Vec<Ast<'t>> {
        self.parts.get_rep_leaf_or_panic(part_name)
            .iter().map( |&lwt| lwt.term.clone()).collect()
    }
    
    /** March by example, turning a repeated set of part names into one LWR per repetition. */
    pub fn march_all(&self, driving_names: &Vec<Name<'t>>) -> Vec<LazyWalkReses<'t, Mode>> {
        let marched  = self.parts.march_all(driving_names);
        let mut res = vec![];
        for marched_parts in marched.into_iter() {
            res.push(LazyWalkReses{env: self.env.clone(), parts: marched_parts, mode: self.mode });
        }
        res
    }
}

/**
 * Make a `Mode::Out` by walking `expr` in the environment `env`.
 */
pub fn walk<'t, Mode: WalkMode<'t>>
    (expr: &Ast<'t>, mode: Mode, env: ResEnv<'t, Mode::Out>,
     cur_node_contents: &LazyWalkReses<'t, Mode>)
        -> Result<Mode::Out, ()> {
    match *expr {
        Node(ref f, ref parts) => {
            // certain walks only work on certain kinds of AST nodes
            match Mode::get_walk_rule(f) {
                &Custom(ref ts_fn) => {                    
                    ts_fn(LazyWalkReses::new(mode, env, parts.clone()))
                }
                
                &Body(ref n) => {
                    walk(parts.get_leaf(n).unwrap(), mode, env.clone(), 
                         &LazyWalkReses::new(mode, env.clone(), parts.clone()))
                }
                
                &NotWalked => { panic!( "{:?} should not have a type at all!", expr ) }
            }
        }
        IncompleteNode(ref parts) => { panic!("{:?} isn't a complete node", parts)}
        VariableReference(ref n) => {
            Ok(env.find(n).expect(format!("Name {:?} unbound in {:?}", n, env).as_str()).clone())
        }
        
        Trivial | Atom(_) | Shape(_) => {
            panic!("{:?} is not a typeable node", expr);
        }
        
        ExtendEnv(ref body, ref beta) => {
            let new_env = if Mode::automatically_extend_env() {
                env.set_assoc(&env_from_beta(beta, cur_node_contents))
            } else {
                env
            };

            walk(&**body, mode, new_env, cur_node_contents)
        }
    }
}

/**
 * This trait exists to connect `Form`s to different kinds of walks.
 */

pub trait WalkMode<'t> : Copy + Debug {
    type Out : Clone + Debug;
    
    fn get_walk_rule<'f>(&'f Form<'t>) -> &'f WalkRule<'t, Self>;

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
    
    fn ast_to_out(a: Ast<'t>) -> Self::Out {
        panic!("not implemented: {:?} cannot be converted", a);
    }
}

