The Unseemly core language is not intended to be ergonomic,
but to support the bare minimum of an algebraic type system and a procedural macro system.

The file extension for Unseemly source code is `.≉`.

## Low-level structure
The default Unseemly tokenizer is very simple.
Tokens are only separated by whitespace and the *inside edges* of `([{}])`.
You'll tend to see constructs like, `.[ ].`, `'[ ]'`, and `hi[ ]hi`.
You need to leave more spaces than you're used to in normal languages.
Probably, there's a reason that they have tokenizers
 that can't be described in five sentences.


## Expressions
* `(expr expr ⋯)` is function application.

* `.[ x: Type  ⋯ . expr ].` is lambda.

* `match expr { pat => expr  ⋯ }` is a pattern match.

* `+[Choice expr ⋯]+ : Type` constructs an enumerated value.
    The type annotation is weird, but it helps keep the typechecker simple.

* `*[component : expr ⋯]*` constructs a structure value.

* `forall X ⋯ . expr` abstracts over a type. It is typically used around lambdas.

* `unfold expr` pulls one layer of `mu` off a recursively-typed value.
    It is almost exclusively used for the scrutinee in `match`.

* `fold expr : Type` adds one layer of `mu` to recursively-typed value.
    It is almost exclusively used right after constructing an enum or struct.
    `Type` is the type you want after adding the `mu`.

* `[Nonterminal<Type> | whatever_that_nonterminal_represents ]` is syntax quotation.
    For example, `[Expr | (plus one one) ]`.
    (The `<Type>` annotation is usually optional†).

    * Inside a quotation, `,[Nonterminal<Type> | expr ],` is an unquotation.
        For example `[Expr | (plus ,[syn_for_number], one)]` is the syntax for
         adding one to whatever `syn_for_number` represents.
        (The whole `Nt<Type> |` annotation is usually optional†).
    * Inside a quotation `...[x ⋯ >> whatever_that_nonterminal_represents ]...`
       is an abstract repetition;
       it's only valid at parts of the grammar that accept an arbitrary number of something.
      `x` must have been parsed under some kind of repetition; this expands `x` to its components,
       duplicating everything else.
      It will usually contain an unquotation immediately inside it.
* `extend_syntax expr in extended_expr` is syntax extension.
    `expr` should define a function from the current syntax enviroment to a new syntax environment.
    `extended_expr` is an expression in that new environment.

†The rule for when you need a type annotation is a little weird.
Honestly, it's probably best to leave off type annotations unless the typechecker complains.
But the rule is this:
 you only need an annotation if the outside of the quotation/unquotation is an expression,
  and the inside is a pattern.
The confusing part is that *whether* it's a quotation or unquotation is irrelevant!
 (Except that when an unquotation doesn't need an annotation, it needs no `Nonterminal` at all.)

## Pre-defined values
* `zero` through `ten` are integers. (What are these "literals" you speak of?)
* `plus`, `minus`, `times`, and `equal?` are binary functions.
* `zero?` is a unary function.
* `true` and `false` are boolean values.
* `fix` is the fixpoint function. A simple way to run forever, calculating the largest number:
    `(fix .[again: [ -> [Int -> Int]] . .[ n: Int . ((again) (plus n one))]. ].)`


## Patterns
* `+[Choice pat ⋯]+` deconstructs an enumerated value.

* `*[component: pat  ⋯]*` deconstructs a structure value.

* Quotation and unquotation are also useful as patterns.
  The type annotation is always optional starting from a pattern.


## Types
* `[Type ⋯  -> Type]` is the function type.

* `enum { Choice (Type ⋯) ⋯ }` is the enumeration type.

* `struct { component: Type  ⋯ }` is the structure type.

* `**[Type ⋯]**` is a tuple type.

* `forall X ⋯ . Type` is the abstracted type.

* `mu_type X ⋯ . Type` protects a recursive type from being infinitely large.
    It is typically used inside the definition of X.

* `Type<Type ⋯>` applies an abstracted type.
    For example, `List<Int>` is a list of integers.
    The technical term for this operator is "Fish X-ray".

* `:::[, T , >> Type]:::` requires `T` to refer to a tuple type. Suppose `T` is `**[A B Int]**`:
    `:::[, T , >> [T -> X]]:::` is `**[[A -> X] [B -> X] [Int -> X]]**`.

## Pre-defined types
* `Int` is a built-in type.
* `Bool` is defined as `enum { True () False () }`.


## Example unseemly programs
*(in `src/examples/`)*

*  `fact.≉` takes 5 factorial
    Demonstrates recursion with `fix`

*  `sum_list.≉` sums the list "1, 2, 3"
    Demonstrates `let_type`, `match`, `fold`, `unfold`, and the need for a macro system.

*  `if_macro.≉` introduces `if expr then expr else expr` to the language.

*  `.unseemly_prelude` is intended to be copied to your home directory.
    It's automatically loaded by the REPL.
    You can add to it with `:s` commands from the REPL.
    It has comments, too! You have to add those manually.

There are also some examples in the unit tests in `src/main.rs`.
