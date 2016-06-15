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


pub enum TypeRule<'t> {
    /** A function from the types of the *parts* of this form
         to the (possible) type of this form.
    Note that the environment is not directly accessible! */
    Custom(Box<(Fn(LazyPartTypes<'t>) -> Result<Ast<'t>, ()>) + 't>),
    Body(Name<'t>), /* this form has the same type as one of its subforms */
    VarRef, /* this form is a var ref; look up its type in the environment */
    NotTyped /* this form should not ever be typechecked */
}

pub use self::TypeRule::*;


pub type TyEnv<'t> = Assoc<Name<'t>, Ast<'t>>;

#[derive(Clone, Debug)]
pub struct LazilyTypedTerm<'t> {
    pub term: Ast<'t>,
    pub ty: RefCell<Option<Result<Ast<'t>, ()>>>
}

// only because lazy-rust is unstable 

impl<'t> LazilyTypedTerm<'t> {
    pub fn new(t: Ast<'t>) -> LazilyTypedTerm<'t> {
         LazilyTypedTerm { term: t, ty: RefCell::new(None) } 
    }
    
    fn get_type(&self, cur_node_contents: &LazyPartTypes<'t>) 
               -> Result<Ast<'t>, ()> {
        let result = 
            self.ty.borrow_mut().take().unwrap_or_else(
                || synth_type(&self.term, cur_node_contents.env.clone(),
                              cur_node_contents));
        
        * self.ty.borrow_mut() = Some(result.clone());
        result
    }
}


/** Package containing enough information to figure out types on-demand */
#[derive(Clone, Debug)]
pub struct LazyPartTypes<'t> {
    pub parts: Assoc<Name<'t>, LazilyTypedTerm<'t>>,
    pub env: TyEnv<'t>
}

impl<'t> LazyPartTypes<'t> {
    pub fn new(env: TyEnv<'t>, parts_untyped: Assoc<Name<'t>, Ast<'t>>) 
            -> LazyPartTypes<'t> {
        LazyPartTypes {
            env: env,
            parts: parts_untyped.map(&LazilyTypedTerm::new)
        }
    }
    
    pub fn get_type(&self, part_name: &Name<'t>) -> Result<Ast<'t>, ()> {
        self.parts.find(part_name).unwrap().get_type(self)
    }
    
    pub fn get_term(&self, part_name: &Name<'t>) -> Ast<'t> {
        self.parts.find(part_name).unwrap().term.clone()
    }
}

pub fn synth_type<'t>(expr: &Ast<'t>, env: TyEnv<'t>,
                  cur_node_contents: &LazyPartTypes<'t>)
        -> Result<Ast<'t>, ()> {
    println!("synth: {:?} in {:?}", expr, env);
    match *expr {
        Node(ref f, ref body) => {
            // certain type synthesizers only work on certain kinds of AST nodes
            match (&f.synth_type, &**body) {
                (&Custom(ref ts_fn), &Env(ref parts)) => {                    
                    ts_fn(LazyPartTypes::new(env, parts.clone()))
                }
                (&Custom(_), _) => { panic!("{:?} isn't an environment", body); }
                
                (&Body(ref n), &Env(ref parts)) => {
                    synth_type(parts.find(n).unwrap(), env.clone(), 
                               &LazyPartTypes::new(env.clone(), parts.clone()))
                }
                (&Body(_), _) => { panic!("{:?} cannot have Body type", body); }
                
                (&VarRef, &Atom(ref n)) => {
                    Ok(env.find(n).expect(format!("Name {:?} unbound in {:?}", n, env).as_str()).clone())
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
    let mt_parts = LazyPartTypes::new(Assoc::new(), Assoc::new());
    let mt_ty_env = Assoc::new();
    let simple_ty_env = mt_ty_env.set(n("x"), ast_elt!("integer"));
    
    let var_ref = basic_typed_form!(at, VarRef);
    let body = basic_typed_form!(at, Body(n("body")));
    let untypeable = basic_typed_form!(at, NotTyped);
    
    assert_eq!(synth_type(&ast_elt!({var_ref.clone() ; "x"}), 
               simple_ty_env.clone(), &mt_parts),
               Ok(ast_elt!("integer")));
               
    assert_eq!(synth_type(&ast_elt!({body.clone() ; 
                                     ["irrelevant" => {untypeable.clone() ; "-"},
                                      "body" => {var_ref.clone() ; "x"}]}),
                          simple_ty_env.clone(),
                          &mt_parts),
               Ok(ast_elt!("integer")));

    assert_eq!(synth_type(&ast_elt!({body.clone() ;
                                     ["type_of_new_var" => "integer",
                                      "new_var" => "y",
                                      "body" => (import ["new_var" : "type_of_new_var"]
                                                  {var_ref.clone() ; "y"})]}),
                          simple_ty_env.clone(),
                          &mt_parts),
               Ok(ast_elt!("integer")));
               
    assert_eq!(synth_type(&ast_elt!(
            {basic_typed_form!(at, Custom(Box::new(|_| Ok(ast_elt!("string"))))) ; []}),
            simple_ty_env.clone(),
            &mt_parts),
        Ok(ast_elt!("string")));
}