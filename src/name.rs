#![macro_use]

#![allow(non_upper_case_globals)]

use std::fmt;

#[derive(PartialEq,Eq,Clone,Copy,Hash)]
pub struct Name<'t> {
    orig: &'t str
}

/// Special name for negative `ast_walk`ing
// TODO: this should be gensymmed, effectively
// This has to be here for `orig` to be private.
// And then this gets included in `name::*`; very sad.
pub const negative_ret_val : Name<'static> = Name { orig: "⋅" };

impl<'t> fmt::Debug for Name<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "«{}»", self.orig)
    }
}

impl<'t> Name<'t> {
    pub fn is(&self, s: &'t str) -> bool {
        self.orig == s
    }
}

pub fn n<'t>(s: &'t str) -> Name<'t> {
    Name{ orig: s }
}

macro_rules! expr_ify {
    ($e:expr) => {$e};
}

macro_rules! assoc_n {
    () => { Assoc::new() };
    ( $k:tt => $v:expr $(, $k_cdr:tt => $v_cdr:expr)* ) => {
        assoc_n!( $( $k_cdr => $v_cdr ),* ).set(n(expr_ify!($k)), $v)
    };
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ContainedName {
    orig: String
}

