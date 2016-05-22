use parse::FormPat;
use parse::FormPat::Scope;
use name::*;
use std::fmt::{Debug,Formatter,Error};
use ast::Ast;
use util::assoc::Assoc;
use std::rc::Rc;

pub type NMap<'t, T> = Assoc<Name<'t>, T>;

pub struct Form<'t> {
    pub name: Name<'t>,
    pub grammar: FormPat<'t>,
    pub synth_type: Box<Fn(Ast<'t>) -> Result<Ast<'t>,()>>,
    pub relative_phase: Assoc<Name<'t>, i32>, /* 2^31 macro phases ought to be enough for anybody */
}

impl<'t> PartialEq for Form<'t> {
    fn eq(&self, other: &Form<'t>) -> bool {
        self as *const Form == other as *const Form
    }
}

impl<'t> Debug for Form<'t> {
    fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
        formatter.write_str(format!("[FORM {:?}]", self.grammar).as_str())
    }
}


pub fn simple_form<'t>(form_name: &'t str, p: FormPat<'t>) -> Rc<Form<'t>> {
    Rc::new(Form {
            name: n(form_name),
            grammar: Scope(Box::new(p)),
            relative_phase: Assoc::new(),
            synth_type: Box::new(|_| Result::Ok(Ast::Trivial))
        })
}

macro_rules! typed_form {
    ( $p:tt, $gen_type:expr ) => {
        Form {
            grammar: form_pat!($p),
            relative_phase: Assoc::new(),
            synth_type: Box::new($gen_type)
        }
    }
}