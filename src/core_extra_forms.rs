use crate::{ast_walk::WalkRule::*, form::Form, grammar::FormPat, name::*};
use std::rc::Rc;

/// These forms are theoretically implementable as macros from other forms,
///  but for performance and debugability reasons, they are a part of Unseemly.
/// Stored as a `FormPat` instead of a `SynEnv`
///  because we need to merge this with the rest of the "Expr"s.
pub fn make_core_extra_forms() -> FormPat {
    // I think we want to have "Stmt" separate from "Expr", once #4 is complete.
    // Should "Item"s be valid "Stmt"s? Let's do whatever Rust does.

    forms_to_form_pat![typed_form!("block",
    (delim "-{", "{", [(star [(named "effect", (call "Expr")), (lit ";")]),
                       (named "result", (call "Expr"))]),
    /* type */
    Body(n("result")),
    /* evaluation */
    cust_rc_box!( move | part_values | {
        for effect_values in part_values.march_all(&[n("effect")]) {
            let _ = effect_values.get_res(n("effect"))?;
        }
        part_values.get_res(n("result"))
    }))]
}
