#![macro_use]

use parse::FormPat;
use parse::FormPat::Scope;
use name::*;
use std::fmt::{Debug,Formatter,Error};
use ast::Ast;
use util::assoc::Assoc;
use std::rc::Rc;
use ast_walk::WalkRule;
use ty::SynthesizeType;
use runtime::eval::Evaluate;

pub type NMap<'t, T> = Assoc<Name<'t>, T>;

/// Unseemly language form
pub struct Form<'t> {
    /// The name of the form. Mainly for internal use.
    pub name: Name<'t>,
    /** The grammar the programmer should use to invoke this form. 
     * This contains information about bindings and syntax extension; this is where it belongs!
     */
    pub grammar: FormPat<'t>,
    /** From a type environment, construct the type of this term. */
    pub synth_type: WalkRule<'t, SynthesizeType>,
    /** From a value environment, evaluate this term.*/
    pub eval: WalkRule<'t, Evaluate>,
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
            grammar: p,
            relative_phase: Assoc::new(), 
            synth_type: WalkRule::NotWalked,
            eval: WalkRule::NotWalked
        })
}

macro_rules! basic_typed_form {
    ( $p:tt, $gen_type:expr, $eval:expr ) => {
        Rc::new(Form {
            name: n("unnamed form"),
            grammar: form_pat!($p),
            relative_phase: Assoc::new(),
            synth_type: $gen_type,
            eval: $eval
        })
    }
}

macro_rules! typed_form {
    ( $name:expr, $p:tt, $gen_type:expr, $eval:expr ) => {
        Rc::new(Form {
            name: n($name),
            grammar: form_pat!($p),
            relative_phase: Assoc::new(),
            synth_type: $gen_type,
            eval: $eval
        })
    }
}