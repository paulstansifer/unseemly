/*
 Our big asset is that we will have Γ available for type synthesis.

 But this means that introduced forms will be pretty restricted in design. Type-inferring `let`
 is possible, but `lambda` will have to be annotated with parameter types. Welp.

 We may eventually need various variations on `Type`.

*/


/*

Type synthesis is a recursive traversal of an abstract syntax tree. 
It is compositional,
 except for binding, which is indicated by ExtendResEnv nodes. 
These nodes  may depend on 
 the result of synthesizing sibling AST nodes
 or the actual value of AST nodes corresponding to types 
  (i.e., type annotations)

*/

use form::Form;
use std::rc::Rc; 
use std::cell::RefCell;
use name::*;
use util::assoc::Assoc;
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
    /** "this form is a var ref; look up its type/value in the environment" */
    VarRef, 
    /** this form should not ever be typed/evaluated */
    NotWalked 
}

pub use self::WalkRule::*;


pub type ResEnv<'t, Out> = Assoc<Name<'t>, Out>;

#[derive(Debug)]
pub struct LazilyWalkedTerm<'t, Mode: WalkMode<'t>> {
    pub term: Ast<'t>,
    pub res: RefCell<Option<Result<Mode::Out, ()>>>
}

// only because lazy-rust is unstable 

impl<'t, Mode : WalkMode<'t>> LazilyWalkedTerm<'t, Mode> {
    pub fn new(t: Ast<'t>) -> LazilyWalkedTerm<'t, Mode> {
         LazilyWalkedTerm { term: t, res: RefCell::new(None) } 
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
 * Package containing enough information to walk on-demand.
 * Contents probably shouldn't be `pub`...
 */
#[derive(Debug)]
pub struct LazyWalkReses<'t, Mode: WalkMode<'t>> {
    pub parts: Assoc<Name<'t>, LazilyWalkedTerm<'t, Mode>>,
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
               parts_unwalked: Assoc<Name<'t>, Ast<'t>>)
            -> LazyWalkReses<'t, Mode> {
        LazyWalkReses {
            env: env,
            parts: parts_unwalked.map(&LazilyWalkedTerm::new),
            mode: mode
        }
    }
    
    pub fn get_res(&self, part_name: &Name<'t>) -> Result<Mode::Out, ()> {
        self.parts.find(part_name).unwrap().get_res(self)
    }
    
    pub fn get_term(&self, part_name: &Name<'t>) -> Ast<'t> {
        self.parts.find(part_name).unwrap().term.clone()
    }
}

pub fn walk<'t, Mode: WalkMode<'t>>
    (expr: &Ast<'t>, mode: Mode, env: ResEnv<'t, Mode::Out>,
     cur_node_contents: &LazyWalkReses<'t, Mode>)
        -> Result<Mode::Out, ()> {
    match *expr {
        Node(ref f, ref body) => {
            // certain walks only work on certain kinds of AST nodes
            match (Mode::get_walk_rule(f), &**body) {
                (&Custom(ref ts_fn), &Env(ref parts)) => {                    
                    ts_fn(LazyWalkReses::new(mode, env, parts.clone()))
                }
                (&Custom(_), _) => { panic!("{:?} isn't an environment", body); }
                
                (&Body(ref n), &Env(ref parts)) => {
                    walk(parts.find(n).unwrap(), mode, env.clone(), 
                         &LazyWalkReses::new(mode, env.clone(), parts.clone()))
                }
                (&Body(_), _) => { panic!("{:?} cannot have Body type", body); }
                
                (&VarRef, &Atom(ref n)) => {
                    Ok(env.find(n).expect(format!("Name {:?} unbound in {:?}", n, env).as_str()).clone())
                }
                (&VarRef, _) => { panic!("{:?} is not a variable", body); }
                
                (&NotWalked, _) => { panic!( "{:?} should not have a type at all!", expr ) }
            }
        }
        Trivial | Atom(_) | Shape(_) | Env(_) => {
            panic!("{:?} is not a typeable node", expr);
        }
        
        ExtendEnv(ref body, ref beta) => {
            walk(&**body, mode,
                 if Mode::automatically_extend_env() {
                     env.set_assoc(&env_from_beta(beta, cur_node_contents))
                 } else {
                     env
                 },
                 cur_node_contents)
        }
    }
}

/**
 * This trait exists to connect `Form`s to different kinds of walks.
 */

pub trait WalkMode<'t> : Copy + Debug {
    type Out : Clone + Debug;
    
    fn get_walk_rule<'f>(&'f Form<'t>) -> &'f WalkRule<'t, Self>;

    /** should the walker extend the environment based on imports? */
    fn automatically_extend_env() -> bool { false }
    
    fn ast_to_out(a: Ast<'t>) -> Self::Out {
        panic!("not implemented: {:?} cannot be converted", a);
    }
}

