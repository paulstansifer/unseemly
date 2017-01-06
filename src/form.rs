#![macro_use]

use parse::FormPat;
use name::*;
use std::fmt::{Debug,Formatter,Error};
use util::assoc::Assoc;
use std::rc::Rc;
use ast_walk::WalkRule;
use ty::{SynthesizeType, NegativeSynthesizeType};
use runtime::eval::{Evaluate, NegativeEvaluate, Quasiquote, NegativeQuasiquote};

pub type NMap<T> = Assoc<Name, T>;


// `Form` appears to be invariant (rather than covariant) over its lifetime parameter
//  because the function inside WalkRule is invariant over it. ) :
custom_derive! {
    /// Unseemly language form
    #[derive(Reifiable)]
    pub struct Form {
        /// The name of the form. Mainly for internal use.
        pub name: Name,
        /** The grammar the programmer should use to invoke this form. 
         * This contains information about bindings and syntax extension; this is where it belongs!
         */
        pub grammar: FormPat,
        /** From a type environment, construct the type of this term. */
        pub synth_type: EitherPN<WalkRule<SynthesizeType>, WalkRule<NegativeSynthesizeType>>,
        /** From a value environment, evaluate this term.*/
        pub eval: EitherPN<WalkRule<Evaluate>, WalkRule<NegativeEvaluate>>,
        /** Treat everything as quoted except `unquote`s */
        pub quasiquote: EitherPN<WalkRule<Quasiquote>, WalkRule<NegativeQuasiquote>>,
        pub relative_phase: Assoc<Name, i32> /* 2^31 macro phases ought to be enough for anybody */
    }
}

custom_derive! {
    /**
     * The distinction between `Form`s with positive and negative walks is documented at `Mode`.
     */
    #[derive(Reifiable)]
    pub enum EitherPN<L, R> {
        Positive(L),
        Negative(R),
        Both(L, R)
        // Maybe instead of WalkRule::NotWalked, we need EitherPN::Neither
    }
}
pub use self::EitherPN::*;

impl<L, R> EitherPN<L, R> {
    pub fn pos(&self) -> &L {
        match self { 
            &Positive(ref l) => l, 
            &Negative(_) => panic!("ICE: wanted positive walk"),
            &Both(ref l, _) => l
        }
    }
    pub fn neg(&self) -> &R {
        match self {
            &Negative(ref r) => r, 
            &Positive(_) => panic!("ICE: wanted negative walk"),
            &Both(_, ref r) => r
        }
    }
    pub fn is_pos(&self) -> bool { match self { &Negative(_) => false, _ => true }}
    pub fn is_neg(&self) -> bool { match self { &Positive(_) => false, _ => true }}
}


impl PartialEq for Form {
    /// pointer equality on the underlying structure!
    fn eq(&self, other: &Form) -> bool { 
        self as *const Form == other as *const Form
    }
}

// HACK: I think this means that we need to just get rid of the pervasive lifetime parameters
pub fn same_form(a: &Rc<Form>, b: &Rc<Form>) -> bool {
    a.name.is_name(&b.name)
}


impl Debug for Form {
    fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
        formatter.write_str(format!("[FORM {:?}]", self.name).as_str())
    }
}


pub fn simple_form(form_name: &str, p: FormPat) -> Rc<Form> {
    Rc::new(Form {
            name: n(form_name),
            grammar: p,
            relative_phase: Assoc::new(), 
            synth_type: ::form::Positive(WalkRule::NotWalked),
            eval: ::form::Positive(WalkRule::NotWalked),
            quasiquote: ::form::Both(WalkRule::LiteralLike, WalkRule::LiteralLike)
        })
}
