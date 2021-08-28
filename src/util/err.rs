use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    term::termcolor::{Ansi, ColorChoice, StandardStream, WriteColor},
};
use std::fmt::{Debug, Display, Formatter, Result};

custom_derive! {
    #[derive(Reifiable, Clone, PartialEq)]
    pub struct Spanned<T> {
        // The actual contents are ignored; only the span information is used.
        pub loc: crate::ast::Ast,
        pub body: T
    }
}

pub fn sp<T>(t: T, a: crate::ast::Ast) -> Spanned<T> { Spanned { loc: a, body: t } }

impl<T: Display> Spanned<T> {
    pub fn emit_to_writer(&self, mut writer: &mut dyn WriteColor) {
        let diagnostic =
            Diagnostic::error().with_message(format!("{}", self.body)).with_labels(vec![
                Label::primary(self.loc.0.file_id, self.loc.0.begin..self.loc.0.end),
            ]);

        let config = codespan_reporting::term::Config::default();

        crate::earley::files.with(|f| {
            codespan_reporting::term::emit(&mut writer, &config, &*f.borrow(), &diagnostic).unwrap()
        });
    }

    pub fn emit(&self) {
        let mut writer = StandardStream::stderr(ColorChoice::Always);
        self.emit_to_writer(&mut writer);
    }
}

// Temporary HACK: capture the ANSI terminal output in a string,
//  assuming we'll get printed to a terminal.
impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let mut writer = Ansi::new(Vec::<u8>::new());

        self.emit_to_writer(&mut writer);

        write!(f, "{}", std::str::from_utf8(&writer.into_inner()).unwrap())
    }
}

// Force pretty version
impl<T: Display> Debug for Spanned<T> {
    fn fmt(&self, f: &mut Formatter) -> Result { write!(f, "{}", self) }
}
