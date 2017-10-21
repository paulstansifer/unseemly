#![macro_use]

extern crate lalrpop_intern;

use std::fmt;
use std::string::String;

#[derive(PartialEq,Eq,Clone,Copy,Hash)]
pub struct Name {
    id: lalrpop_intern::InternedString
}

// only available on nightly:
// impl !Send for Name {}

impl Name {
    pub fn sp(&self) -> String { self.id.to_string() }
}

/// Special name for negative `ast_walk`ing
// TODO: move to `ast_walk`
// TODO: this interner doesn't support `gensym`...
pub fn negative_ret_val() -> Name {
    Name { id: lalrpop_intern::intern("⋄") }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "«{}»", self.sp())
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.sp())
    }
}

impl Name {
    pub fn is(&self, s: &str) -> bool {
        self.sp() == s
    }

    pub fn is_name(&self, n: &Name) -> bool {
        self.sp() == n.sp()
    }
}

pub fn n(s: &str) -> Name {
    Name{ id: lalrpop_intern::intern(s) }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ContainedName {
    spelling: String
}

impl ContainedName {
    pub fn from_name(n: &Name) -> ContainedName {
        ContainedName {
            spelling: n.sp()
        }
    }
}
