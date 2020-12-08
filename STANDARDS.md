1. Use `cargo +nightly fmt` before comitting for consistency.
   It enforces 100-character lines, and some other stuf that's
    .. perhaps a bit on the agressively terse side.

2. It's okay for comments to ask questions
    that the author of the code ought to have known the answer to.

3. Everything else on this list is a little weird, and shouldn't be taken too seriously.

4. Text in comments (and, where possible, in other natural-language prose)
    is formatted in a hierarchical fashion.
   Ending a sentence ends the line that it's on.
   Manually-word wrap by inserting line-breaks at major breaks in thought
     (often, it's after a comma or a where one would pause when reading aloud),
    and indent successive lines of that sentence
     in a way that communicates the grammatical hierarchy.

5. If a variable name has more than two underscores in it,
    consider doubling (or, *shudder* tripling) some of them
     to indicate how they relate to each other.
   For example, `maybe_literally__walk` is a function that walks, and might do so literally.
   If it were named `maybe__literally_walk`, then it might literally walk, but might do nothing.

TODO: Change `EnvMBE` to `EnvMbe` to follow [Rust naming style].

[Rust naming style]: https://rust-lang.github.io/api-guidelines/naming.html
