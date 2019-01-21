### ≉

In Unseemly, typechecking occurs entirely prior to macro expansion.

Error messages are the user interface of a compiler.
In languages where code resulting from macro expansion is typechecked,
 (pretty much all existing languages with types and macros)
 the programmer must think about the internals of each macro they use
  in order to make sense of type errors.
Informally, Unseemly guarantees that,
 no matter how many macros you use,
  type errors will be expressed
   entirely in terms of code you directly wrote.

Unseemly has a bare minimum of forms
 necessary to bootstrap the implementation of practical languages.

## How to use it

Install Rust:

    curl https://sh.rustup.rs -sSf | sh

(Recommended) Get the default prelude for the unseemly REPL:

    cp src/examples/.unseemly_prelude ~/

Start the REPL:

    cargo run


Run an example programs:

    cargo run src/examples/sum_list.≉

## Documentation

Look at core_language_basics.txt for documentation of the language.

## Related work

### FreshML / Romeo

Unseemly is sort of a descendant of FreshML and Romeo
 (but without the parts of Romeo corresponding to Pure FreshML).
Romeo allowed for manipulation of syntax types with complex binding information,
 but (a) syntax was otherwise untyped
     (b) there was no macro system (so the syntax manipulation was pointless!)
     (c) it was more of a core calculus

### SugarJ / SoundX



### Wyvern

### Terra
