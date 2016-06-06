/*
 Our big asset is that we will have Γ available for type synthesis.

 But this means that introduced forms will be pretty restricted in design. Type-inferring `let`
 is possible, but `lambda` will have to be annotated with parameter types. Welp.

 We may eventually need various variations on `Type`.

*/


/*

Type synthesis is a recursive traversal of an abstract syntax tree. 
It is compositional,
 except for binding, which is indicated by ExtendTypeEnv nodes. 
These nodes  may depend on 
 the result of synthesizing sibling AST nodes
  
  
 the result of *parsing* sibling AST nodes corresponding to types 
  (i.e., type annotations, which 

*/

use form::Form;
use std::rc::Rc; // we expect to want to share a lot of structure
use name::*;
use util::assoc::Assoc;
use ast::Ast;
use ast::Ast::*;


pub enum TypeRule<'t> {
    /** A function from syntax to the (possible) types of that syntax.
    Note that the environment is not directly accessible! */
    Custom(Box<Fn(&Ast<'t>) -> Result<Ast<'t>, ()>>),
    Body(Name<'t>), /* this form has the same type as one of its subforms */
    VarRef, /* this form is a var ref; look up its type in the environment */
    NotTyped /* this form should not ever be typechecked */
}

pub use self::TypeRule::*;


pub type TyEnv<'t> = Assoc<Name<'t>, Ast<'t>>;

fn synth_type<'t>(expr: &Ast<'t>, env: TyEnv<'t>,
                  cur_node_contents: Assoc<Name<'t>, Ast<'t>>)
        -> Result<Ast<'t>, ()> {
    match *expr {
        Node(ref f, ref body) => {
            // certain type synthesizers only work on certain kinds of AST nodes
            match (&f.synth_type, &**body) {
                (&Custom(ref ts_fn), _) => ts_fn(&**body),
                
                (&Body(ref n), &Env(ref parts)) => {
                    synth_type(parts.find(n).unwrap(), env, parts.clone())
                }
                (&Body(_), _) => { panic!("{:?} cannot have Body type", body); }
                
                (&VarRef, &Atom(ref n)) => {
                    Ok(env.find(n).unwrap().clone())
                }
                (&VarRef, _) => { panic!("{:?} is not a variable", body); }
                
                (&NotTyped, _) => { panic!( "{:?} should not have a type at all!", expr ) }
            }
        }
        Trivial | Atom(_) | Shape(_) | Env(_) => {
            panic!("{:?} is not a typeable node", expr);
        }

        
        ExtendTypeEnv(ref _body, ref _beta) => {
            //synth_type(*body, env) 
            panic!("TODO");
        }
    }
}

/*

#[derive(Debug,Clone)]
pub enum Type<'t> {
    Function(Vec<Type<'t>>, Rc<Type<'t>>),
    Term(&'t Form<'t>, Rc<Type<'t>>),
    Struct(Assoc<Name<'t>, Type<'t>>),
    Enum(Vec<Type<'t>>),
    NamedType(Name<'t>, Vec<Type<'t>>),
    Number
}

*/


