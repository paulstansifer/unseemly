use parse::FormPat;
use ty::Type;
use std::collections::HashMap;
use name::*;
use std::fmt::{Debug,Formatter,Error};

pub type NMap<'t, T> = HashMap<Name<'t>, T>;

#[derive(Clone)]
pub struct Form<'t> {
    pub grammar: FormPat<'t>,
    //synth_type: Box<Fn(/*child_types*/ &NMap<Type>, /*type_env*/ &NMap<Type>) -> Type<'t>>,
    pub relative_phase: NMap<'t, i32>, /* 2^31 macro phases ought to be enough for anybody */
}


impl<'t> Debug for Form<'t> {
    fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
        formatter.write_str(format!("[FORM {:?}]", self.grammar).as_str())
    }
}


pub fn simple_form<'t>(p: FormPat<'t>) -> Form<'t> {
    Form {
        grammar: p,
        relative_phase: HashMap::new()
    }
}