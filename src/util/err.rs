use std::fmt::{Display, Debug, Result, Formatter};

custom_derive! {
    #[derive(Reifiable, Clone, PartialEq)]
    pub struct Spanned<T> {
        pub loc: ::ast::Ast, // TODO: implement spans!
        pub body: T
    }
}

pub fn sp<T>(t: T, a: ::ast::Ast) -> Spanned<T> {
    Spanned { loc: a, body: t }
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{} at {:#?}", self.body, self.loc)
    }
}

impl<T: Debug> Debug for Spanned<T> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{:#?} at {:#?}", self.body, self.loc)
    }
}

/*
impl<T: From<()>> From<()> for Spanned<T> {
    fn from(_: ()) -> Spanned<T> {
        Spanned { loc: ::ast::Ast::Trivial, body: T::from(()) }
    }
}
*/
