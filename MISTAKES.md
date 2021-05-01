If I had to do it all over again...

* There should be one primary macro for defining language forms,
  which would also define a destructuring macro for that form.
  (And maybe it could make flimsy_syntax.rs simpler or nonexistent.)
* This may overlap with the purpose of the previous,
  but there should be something like `Ast`, except with binding and quotation omitted.
  It would represent syntax "as written"
  and be nice for making, e.g., syntax-aware `diff`-like tools.
* Names for "parts" would appear as barewords, not strings, in macros. Maybe. Not sure about this.
* There are so many variations on maps and reduces in mbe.rs,
  and pretty much all of them are used once.
  I think something visitor-pattern-like might be able to unify them?
* I think `FormPat` is more like a language than I realized.
  It seems to have positive and negative forms, mediated by `Scope` and `Named`.
  There might need to be more structure, to enforce what can go where,
  as well as, uh, possibly some scoped way to define names *internal* to the grammar.
  Also, `FormPat` is a bad name.
* The walk_mode.rs/ast_walk.rs distinction isn't great; I never know what's where.
* It would probably have been simpler to add a few more cases (or one `Any` case) to `Value`
    and build some primitive operations on them
   than it was to build all those reification macros.
* In examples and tests, `Int` and `Nat` are frequently used,
  and the user is supposed to assume that neither is a subtype of the other.
  That's unintuitive!
  Also, they are a little similar-looking.

  Former mistakes:
  * There used to be a `Ty` type that was just a wrapper around `Ast` (in the
    distant past, it had had additional functionality). (Issue #30)
