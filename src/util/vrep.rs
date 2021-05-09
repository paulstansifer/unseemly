use crate::name::{Name, n};
use crate::runtime::reify::Reifiable;


custom_derive! {
    #[derive(Clone, PartialEq, Eq, Debug, Reifiable)]
    pub enum VRepElt<T> {
        Single(T),
        Rep(T, Vec<Name>),
    }
}

use VRepElt::*;

#[derive(Debug, PartialEq, Eq)]
pub enum VRepLen {
    Exactly(usize),
    AtLeast(usize),
}

#[derive(Clone, PartialEq, Eq)]
pub struct VRep<T>(Vec<VRepElt<T>>);
pub struct SRep<'a, T>(&'a [VRepElt<T>]);

impl<T> VRep<T> {
    fn expand_reps<F>(&self, mut f: F) -> Vec<T>
    where
        F: FnMut(&T, &Vec<Name>) -> Vec<T>,
        T: Clone,
    {
        let mut res = vec![];
        for elt in &self.0 {
            match elt {
                Single(e) => res.push(e.clone()),
                Rep(es, names) => {
                    let mut expanded = f(es, names);
                    res.append(&mut expanded)
                }
            }
        }
        res
    }

    fn concrete(&self) -> bool {
        for elt in &self.0 {
            match elt {
                Rep(_, _) => return false,
                Single(_) => {}
            }
        }
        return true;
    }

    fn len(&self) -> VRepLen {
        let mut min_len: usize = 0;
        let mut exact: bool = true;
        for elt in &self.0 {
            match elt {
                Single(_) => min_len += 1,
                Rep(_, _) => exact = false,
            }
        }
        if exact {
            VRepLen::Exactly(min_len)
        } else {
            VRepLen::AtLeast(min_len)
        }
    }
}

// Only needed because our custom_derive! doesn't support newtype-style structs:
impl<T: Clone + Reifiable> Reifiable for VRep<T> {
    fn ty_name() -> Name { n("VRep") }

    fn concrete_arguments() -> Option<Vec<crate::ast::Ast>> {
        Some(vec![T::ty_invocation()])
    }

    fn reify(&self) -> crate::runtime::eval::Value {
        let res: Vec<_> = self.0.iter().map(|e| std::rc::Rc::new(e.reify())).collect();

        crate::runtime::eval::Value::Sequence(res)
    }

    fn reflect(v: &crate::runtime::eval::Value) -> Self {
        let mut res = vec![];

        extract!((v) crate::runtime::eval::Value::Sequence = (ref parts) => {
            for part in parts {
                res.push(<VRepElt<T>>::reflect(&**part));
            }
        });
        VRep(res)
    }
}

// Turns a plain Vec into a VRep without repetitions
impl<T> From<Vec<T>> for VRep<T> {
    fn from(flat: Vec<T>) -> Self { VRep(flat.into_iter().map(Single).collect()) }
}

impl<T: std::fmt::Debug> std::fmt::Debug for VRep<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[")?;
        let mut first = false;
        for elt in &self.0 {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            match elt {
                Single(e) => write!(f, "{:?}", e)?,
                Rep(e, names) => write!(f, "{:?} ...({:?})", e, names)?,
            }
        }
        write!(f, "]")
    }
}

macro_rules! vrep {
    ( $( $contents:tt )*) => {
        vrep_accum![ ( $( $contents )* , ) ]
    };
}

macro_rules! vrep_accum {
    // For ease of parsing, expects a trailing comma!
    (($elt:expr, $($rest:tt)*)  $($accum:tt)* ) => {
        // ... and produces a leading comma
        vrep_accum!(($($rest)*)  $($accum)* , crate::util::vrep::VRepElt::Single($elt))
    };
    (($elt:expr => ( $( $driver:expr),* ), $($rest:tt)*)  $($accum:tt)* ) => {
        vrep_accum!(($($rest)*)
                    $($accum)* ,
                    crate::util::vrep::VRepElt::Rep($elt,
                        vec![ $( crate::name::n(stringify!($driver)) ),* ])
                )
    };
    // Expect the leading comma:
    (() , $($accum:tt)* ) => {
        crate::util::vrep::VRep(vec![ $( $accum )* ])
    };
}

#[test]
fn vrep_basics() {
    assert_eq!(vrep![1, 2, 3, 4, 5], VRep::from(vec![1, 2, 3, 4, 5]));

    assert_eq!(vrep![1, 2, 3, 4, 5].len(), VRepLen::Exactly(5));

    let with_rep = vrep![1, 2 => (a, b, c), 3];
    assert_eq!(with_rep.len(), VRepLen::AtLeast(2));

    assert_eq!(with_rep.expand_reps(|_, _| vec![7, 7, 7]), vec![1, 7, 7, 7, 3]);

    // Reification roundtrip:
    assert_eq!(with_rep, <VRep<i32>>::reflect(&with_rep.reify()))
}
