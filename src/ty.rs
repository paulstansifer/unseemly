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
use beta::*;
use parse::FormPat::AnyToken; // for making simple forms for testing

pub enum TypeRule<'t> {
    /** A function from the types of the *parts* of this form
         to the (possible) type of this form.
    Note that the environment is not directly accessible! */
    Custom(Box<Fn(TyEnv<'t>) -> Result<Ast<'t>, ()>>),
    Body(Name<'t>), /* this form has the same type as one of its subforms */
    VarRef, /* this form is a var ref; look up its type in the environment */
    NotTyped /* this form should not ever be typechecked */
}

pub use self::TypeRule::*;


pub type TyEnv<'t> = Assoc<Name<'t>, Ast<'t>>;

// TODO: we really need to memoize to avoid recomputing 
//  (potentially exponentially!)
//  types of subterms.

fn synth_type<'t>(expr: &Ast<'t>, env: TyEnv<'t>,
                  cur_node_contents: Assoc<Name<'t>, Ast<'t>>)
        -> Result<Ast<'t>, ()> {
    match *expr {
        Node(ref f, ref body) => {
            // certain type synthesizers only work on certain kinds of AST nodes
            match (&f.synth_type, &**body) {
                // TODO: need to turn exprs into types before this point
                (&Custom(ref ts_fn), &Env(ref parts)) => {
                    let types_of_parts = parts.map(
                        &|part_expr| synth_type(&part_expr, env.clone(), 
                            cur_node_contents.clone()).unwrap());
                        
                    ts_fn(types_of_parts)
                }
                (&Custom(_), _) => { panic!("{:?} isn't an environment", body); }
                
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

        
        ExtendTypeEnv(ref body, ref beta) => {
            synth_type(&**body, 
                env.set_assoc(&env_from_beta(beta, cur_node_contents.clone())),
                cur_node_contents)
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


#[test]
fn test_type_synth() {
    let mt_parts = Assoc::new();
    let mt_ty_env = Assoc::new();
    let simple_ty_env = mt_ty_env.set(n("x"), ast_elt!("integer"));
    
    let var_ref = typed_form!(at, VarRef);
    let body = typed_form!(at, Body(n("body")));
    let untypeable = typed_form!(at, NotTyped);
    
    assert_eq!(synth_type(&ast_elt!({var_ref.clone() ; "x"}), 
               simple_ty_env.clone(), mt_parts.clone()),
               Ok(ast_elt!("integer")));
               
    assert_eq!(synth_type(&ast_elt!({body.clone() ; 
                                     ["irrelevant" => {untypeable.clone() ; "-"},
                                      "body" => {var_ref.clone() ; "x"}]}),
                          simple_ty_env.clone(),
                          mt_parts.clone()),
               Ok(ast_elt!("integer")));

    assert_eq!(synth_type(&ast_elt!({body.clone() ;
                                     ["type_of_new_var" => "integer",
                                      "new_var" => "y",
                                      "body" => (import ["new_var" : "type_of_new_var"]
                                                  {var_ref.clone() ; "y"})]}),
                          simple_ty_env.clone(),
                          mt_parts.clone()),
               Ok(ast_elt!("integer")));
               
    assert_eq!(synth_type(&ast_elt!(
            {typed_form!(at, Custom(Box::new(|_| Ok(ast_elt!("string"))))) ; []}),
            simple_ty_env.clone(),
            mt_parts.clone()),
        Ok(ast_elt!("string")));
}