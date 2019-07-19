# ≉ [![Build Status](https://travis-ci.com/paulstansifer/unseemly.svg?branch=master)](https://travis-ci.com/paulstansifer/unseemly) [![Coverage Status](https://coveralls.io/repos/github/paulstansifer/unseemly/badge.svg)](https://coveralls.io/github/paulstansifer/unseemly)

Unseemly typechecks the code that you wrote, not the code your macros wrote.
This makes macros feel like part of the language, not something tacked-on.

For a more complete pitch, see http://unseemly.github.io

Unseemly has a bare minimum of forms
 necessary to bootstrap the implementation of practical languages.

## Features

### From the ML family
 * Algebraic types (i.e., supports structs and (rich) enums)
 * Typesafe destructuring with `match`.
 * Generic types (or parametric types) (e.g. `List <[T]<` (Unseemly's syntax is weird))
 * Recursive types
### From the Scheme family
 * Syntax quasiquotation
    (`'[Expr | … ]'` quotes an expression,
      but inside that, `,[Expr | … ],` evaluates its contents and interpolates them)
 * Pretty-printing respects macro invocations and quoted syntax
    (the pretty-printer is rather limited at the moment, though)
 * Hygenic macros (all operations respect α-equivalence)
### Unique features
 * Typechecking under syntax quotation
   (so `'[Expr | (plus one ,[Expr | e1],)]'` is a type error
     if `e1` has the type `Expr <[String]<`)
 * No type errors in generated code
   (if a macro invocation typechecks, the code it expands to doesn't need typechecking).
 * Extensible parsing (write real SQL or real regexes inline, not strings).
### Other features
 * Full-featured REPL, with command history and line editing (courtesy of `rustyline`).


## How to use it

Install Rust, if you haven't already:

    curl https://sh.rustup.rs -sSf | sh

From your Unseemly repository directory, run an example program:

    cargo run src/examples/sum_list.≉

(Recommended) Get the default prelude for the unseemly REPL:

    cp src/examples/.unseemly_prelude ~/

Start the REPL:

    cargo run

## Documentation

Look at core_language_basics.md for documentation of the language.

## Related work

### FreshML / Romeo

Unseemly is sort of a descendant of FreshML and Romeo
 (but without the parts of Romeo corresponding to Pure FreshML).
Romeo allowed for manipulation of syntax types with complex binding information, but
  * syntax was otherwise untyped
  * there was no macro system (so the syntax manipulation was pointless!)
  * it is just a core calculus

### SugarJ / SoundX

SoundX is a language with syntax extensions in which typechecking occurs before expansion.
It provides sound language extensions, but
  * it doesn't support binding annotations
    (in practice, this means that syntax extension authors wind up writing specifications
     that contain logic-y things like `x ∉ dom(E)`.)
  * the language extensions aren't macros (they're not themselves part of the language)
  * it is just a core calculus

(TODO: are the extensions themselves statically verified to be type-preserving?
 I think so, but I don't remember for sure.)

### Wyvern

Wyvern's primary motivating example
 (write SQL, not strings containing SQL, in your general-purpose code)
 is a lot like Unseemly's vision of inline syntax extension.
Wyvern is an engineered programming language, not a core calculus.

Wyvern also includes a number of features that are outside the scope of Unseemly.

(TODO: learn more about Wyvern)

### Terra

Terra, from a quick glance (TODO: learn more),
 appears to be a language with a close relationship to Lua,
  similar to the relationship that Unseemly-based languages would have.

In this case, it looks like the goal is to marry a high-level and low-level language together,
 without an FFI and with inline embedding.

### Rust and SweetJS

Rust and SweetJS are non-S-expression-based languages with macro systems that allow rich syntax.