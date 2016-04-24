

#[derive(PartialEq,Eq,Clone,Copy,Debug,Hash)]
pub struct Name<'t> {
    orig: &'t str
}

impl<'t> Name<'t> {
    pub fn is(&self, s: &'t str) -> bool {
        self.orig == s
    }
}

pub fn n<'t>(s: &'t str) -> Name<'t> {
    Name{ orig: s }
}
