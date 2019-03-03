The Unseemly core language is not intended to be ergonomic,
but to support the bare minimum of an algebraic type system and a procedural macro system.

The file extension for Unseemly source code is `.≉`.

## Low-level structure
The Unseemly tokenizer is very simple.
Tokens are only separated by whitespace and the *inside edges* of `([{}])`.
Furthermore, groupers are named. Thus `[]`, `.[ ].`, `hi[ ]hi` are all legal,
 but `x[ ]` is not.
You need to leave more spaces than you're used to in normal languages.
Probably, there's a reason that they have tokenizers
 that can't be described in five sentences.


## Expressions
* `(expr expr ⋯)` is function application.

* `.[ x : Type  ⋯ . expr ].` is lambda.

* `match expr { pat => expr  ⋯ }` is a pattern match.

* `+[Choice expr ⋯]+ : Type` constructs an enumerated value.
    The type annotation is weird, but it helps keep the typechecker simple.

* `*[component : expr ⋯]*` constructs a structure value.

* `foall X ⋯ . expr` abstracts over a type. It is typically used around lambdas.

* `unfold expr` pulls one layer of `mu` off a recursively-typed value.
    It is almost exclusively used for the scrutinee in `match`.

* `fold expr : Type` adds one layer of `mu` to recursively-typed value.
    It is almost exclusively used right after constructing an enum or struct.
    `Type` is the type you want after adding the `mu`.

* `[Nonterminal <[Type]< | whatever_that_nonterminal_represents ]` is syntax quotation.
    For example, `[Expr | (plus one one) ]`.
    (The `<[Type]<` annotation is usually optional, but you need it for `Pat`).

    * Inside a quotation, `,[Nonterminal <[Type]< | expr ],` is an unquotation.
        For example `[Expr | (plus ,[Expr | syn_for_number], one)]` is the syntax for
        adding one to whatever `syn_for_number` represents.
        (The `<[Type]<` annotation is usually optional, but you need it for `Pat`).

## Pre-defined values
* `zero` through `ten` are integers. (What are these "literals" you speak of?)
* `plus`, `minus`, `times`, and `equal?` are binary functions.
* `zero?` is a unary function.
* `true` and `false` are boolean values.
* `fix` is the fixpoint function. A simple way to run forever, calculating the largest number:
    `(fix .[again : [ -> [Int -> Int]] . .[ n : Int . ((again) (plus n one))]. ].)`


## Patterns
* `+[Choice pat ⋯]+` deconstructs an enumerated value.

* `*[component : pat  ⋯]*` deconstructs a structure value.

* Quotation and unquotation are also useful as patterns.
  The `<[Type]<` annotation is always optional starting from a pattern.


## Types
* `[Type ⋯  -> Type]` is the function type.

* `enum { Choice (Type ⋯) ⋯ }` is the enumeration type.

* `struct { component : Type  ⋯ }` is the structure type.

* `forall X ⋯ . Type` is the abstracted type.

* `mu_type X ⋯ . Type` protects a recursive type from being infinitely large.
    It is typically used inside the definition of X.

* `Type <[Type ⋯]<` applies an abstracted type.
    For example, `List <[Int]<` is a list of integers.
    The technical term for this operator is "Fish X-ray".

## Pre-defined types
* `Int` is a built-in type.
* `Bool` is defined as `enum { True () False () }`.


## Example unseemly programs
*(in `src/examples/`)*

*  fact.≉ takes 5 factorial
    Demonstrates recursion with `fix`
*  sum_list.≉ sums the list "1, 2, 3"
    Demonstrates `let_type`, `match`, `fold`, `unfold`, and the need for a macro system.

*  .unseemly_prelude is intended to be copied to your home directory.
    It's automatically loaded by the REPL.
    You can add to it with `:s` commands from the REPL.
    It has comments, too! You have to add those manually.
