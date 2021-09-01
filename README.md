# ≉ [![Build Status](https://travis-ci.com/paulstansifer/unseemly.svg?branch=master)](https://travis-ci.com/paulstansifer/unseemly) [![Coverage Status](https://coveralls.io/repos/github/paulstansifer/unseemly/badge.svg)](https://coveralls.io/github/paulstansifer/unseemly)

Unseemly typechecks the code that you wrote, not the code your macros wrote.
This makes macros feel like part of the language, not something tacked-on.

For a more complete pitch, see http://unseemly.github.io

Unseemly has a bare minimum of forms
 necessary to bootstrap the implementation of practical languages.

Unseemly is still pretty early-stage, so, while all of the features below exist,
 there are still a number of things that are janky or incomplete.

## Features

### From the ML family
 * Algebraic types (i.e., supports structs and (rich) enums)
 * Typesafe destructuring with `match`.
 * Generic types (or parametric types) (e.g. `List<T>`)
 * Recursive types
### From the Scheme family
 * Syntax quasiquotation
    (`'[Expr | … ]'` quotes an expression,
      but inside that, `,[Expr | … ],` evaluates its contents and interpolates them)
 * Pretty-printing respects macro invocations and quoted syntax
    (the pretty-printer is rather limited at the moment, though)
 * Hygenic macros (all operations respect α-equivalence)
 * Macro By Example (easily implement n-ary forms without writing boilerplate loops).
### Unusual features
 * Typechecking under syntax quotation
   (so `'[Expr | (plus one ,[e1],)]'` is a type error if `e1` has the type `Expr<String>`)
 * No type errors in generated code
   (if a macro invocation typechecks, the code it expands to doesn't need typechecking)†.
 * Extensible parsing and lexing (write real SQL or real regexes inline, not strings).

† Except that there are [known soundness bugs](https://github.com/paulstansifer/unseemly/issues?q=is%3Aissue+is%3Aopen+label%3Asoundness).
### Other features
 * Full-featured REPL, with persistent command history and line editing (courtesy of `rustyline`).


## How to use it

Install Rust, if you haven't already:

    curl https://sh.rustup.rs -sSf | sh

From your Unseemly repository directory, run an example program:

    cargo run --release examples/sum_list.unseemly

(Recommended) Get the default prelude for the Unseemly REPL:

    cp examples/.unseemly_prelude ~/

Start the REPL:

    cargo run --release

## Documentation

Look at core_language_basics.md for documentation of the language.

## Related work

### Research projects
#### [FreshML](https://www.cl.cam.ac.uk/~amp12/freshml/) / [Romeo](https://repository.library.northeastern.edu/files/neu:cj82mb52h)

Unseemly is most closely based on Romeo, which descends from FreshML.
 (Romeo is closer to Pure FreshML, but the "Pure" part is not present in Unseemly.)
Romeo allowed for manipulation of syntax types with complex binding information, but
  * syntax was otherwise untyped
  * there was no macro system (so the syntax manipulation was pointless!)
  * it is just a core calculus

#### [SugarJ](https://github.com/sugar-lang) / [SoundX](https://github.com/florenzen/soundx)

SoundX is a language with syntax extensions in which typechecking occurs before expansion.
It provides sound language extensions, but
  * it doesn't support binding annotations
    (in practice, this means that syntax extension authors wind up writing specifications
     that contain logic-y things like `x ∉ dom(E)`.)
  * the language extensions aren't macros (they're not themselves part of the language)
  * it is just a core calculus

(TODO: are the extensions themselves statically verified to be type-preserving?
 I think so, but I don't remember for sure.)

### Practical languages
#### [Scala](https://www.scala-lang.org/)

If I understand correctly, Scala's blackbox macros are typechecked before expansion,
 but they can't do everything that whitebox macros can.
Unseemly macros are typechecked before expansion, but are the only macro system needed,
 because they can (in particular) define new binding forms safely.
(TODO: learn more about Scala's macro system)

#### [Wyvern](http://wyvernlang.github.io/)

Wyvern's primary motivating example
 (write SQL, not strings containing SQL, in your general-purpose code)
 is a lot like Unseemly's vision of inline syntax extension.
Wyvern is a full-fledged language, not a core language.
I believe that writing new embedded languages is not as easy as macro definition.

Wyvern also includes a number of features that are outside the scope of Unseemly.

(TODO: learn more about Wyvern)

#### [Terra](http://terralang.org/)

Terra, from a quick glance (TODO: learn more),
 appears to be a language with a close relationship to Lua,
  similar to the relationship that Unseemly-based languages would have.

In this case, it looks like the goal is to marry a high-level and low-level language together,
 without an FFI and with inline embedding.

#### [MetaOCaml](http://okmij.org/ftp/ML/MetaOCaml.html)

MetaOCaml is an extension to OCaml that supports type-safe syntax quotation.
Though Unseemly uses "quasiquotation" to describe syntax quotation,
 it is more similar to [MetaOCaml's bracket](http://okmij.org/ftp/meta-programming/implementations.html#meta-scheme)
   than to Scheme's quasiquotation,
  because it respects alpha-equivalence.


Unlike Unseemly, MetaOCaml doesn't use its safe syntax quotation to implement a macro system.

#### [Rust](http://rust-lang.org) and [SweetJS](https://www.sweetjs.org/)

Rust and SweetJS are non-S-expression-based languages with macro systems that allow rich syntax.

Unseemly is implemented in Rust, and it uses *lots* of macros.
