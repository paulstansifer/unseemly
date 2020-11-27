The Unseemly core language is not intended to be ergonomic,
but to support the bare minimum of an algebraic type system and a procedural macro system.

The typical file extension for Unseemly source code is `.≉`.

## Low-level structure
The default Unseemly tokenizer is very simple.
Names start with a letter, and contain letters, numbers, and `?` and `_`.
Non-name tokens are typically separated by whitespace and the *inside edges* of `([{}])`.
You'll tend to see constructs like `.[ ].`, `'[ ]'`, and `hi[ ]hi`.

## Expressions
* `(expr expr ⋯)` is function application.
  ```
  (plus one eight)   # 9
  ```

* `.[ x: Type  ⋯ . expr ].` is lambda.
  ```
  .[lhs: Int  rhs: Int . (equal? (plus lhs one) rhs)].
  # function that determines if `lhs` is one less than `rhs`
  ```

* `match expr { pat => expr  ⋯ }` is a pattern match.
  ```
  match (lookup x some_table) {
      +[Some result]+ => result
      +[None]+ => zero          # default value
  }
  ```

* `+[Choice expr ⋯]+ : Type` constructs an enumerated value.
    The type annotation is weird, but it helps keep the typechecker simple.
   ```
   +[Some eight]+ : { +[Some Int]+  +[None]+ }
   # Equivalent to `Some(8)` in a normal language
   ```
* `*[component: expr ⋯]*` constructs a structure value.
   ```
   *[x: two  y: seven]*  # coordinates
   ```
* `forall X ⋯ . expr` abstracts over a type. It is typically used around lambdas.
   ```
   forall T . .[ opt: Option<T> .
       match opt {
           +[Some thing]+ => true
           +[Nil]+ => false
        }
   ].  # Does this option contain a value?
   ```

* `unfold expr` pulls one layer of `mu` off a recursively-typed value.
    It is almost exclusively used for the scrutinee in `match`.
   ```
   # Is `list` nonempty?
   # Assume `List` is defined as `forall T . mu_type List . { +[Nil]+ +[Cons T List<T> ]+ }`
   # `List` is recursive, so we need to peel off the `mu` to examine it:
   forall T . .[ list: List<T> .
       match unfold list {
           +[Cons car cdr]+ => true
           +[Nil]+ => false
        }
   ].
   ```

* `fold expr: Type` adds one layer of `mu` to recursively-typed value.
    It is almost exclusively used right after constructing an enum or struct.
    `Type` is the type you want after adding the `mu`.
    ```
    fold +[Cons eight my_list]+ : List<Int>
    # Normal languages make `fold` and `unfold` implicit.
    ```

* `[Nonterminal<Type> | whatever_that_nonterminal_represents ]` is syntax quotation.
   ```
   `[Expr | (plus one one) ]`  # syntax for adding 1 to 1
   ```
    (The `<Type>` annotation is usually optional†).

    * Inside a quotation, `,[Nonterminal<Type> | expr ],` is an unquotation.
        ```
        `[Expr | (plus ,[syn_for_number], one)]`
        # Syntax for adding 1 to whatever `syn_for_number` represents.
        ```
        (The whole `Nt<Type> |` annotation is usually optional†).
    * Inside a quotation `...[,x, ⋯ >> whatever_that_nonterminal_represents ]...`
       is an abstract repetition;
       it's only valid at parts of the grammar that accept an arbitrary number of something.
      `x` must have been parsed under some kind of repetition; this expands `x` to its components,
       duplicating everything else.
      It will often contain an unquotation immediately inside it.
      ```
      `[Expr | (my_fn ...[,arg_syn, >> ,[arg_syn],]...)]`
      # Syntax for invoking `my_fn` on an arbitrary number of arguments
      ```
    † The rule for when you need a type annotation is a little weird.
    Honestly, it's probably best to leave off type annotations unless the typechecker complains.
    But the rule is this:
    you only need an annotation if the outside of the quotation/unquotation is an expression,
      and the inside is a pattern.
    The confusing part is that *whether* it's a quotation or unquotation is irrelevant!
    (Except that when an unquotation doesn't need an annotation, it needs no `Nonterminal` at all.)

* `extend_syntax nt_ext ⋯ in extended_expr` is syntax extension.
    `nt_ext` is `Nt ::= grammar ;` or `Nt ::=also grammar ;`
    (`::=` replaces the current definition of that `Nt`, `::=also` extends it).
    `grammar` is defined in the section "Syntax" below.
    `extended_expr` is an expression in the new language.
   ```
   extend_syntax
     Expr ::=also forall T . '{
         [
             lit ,{ DefaultToken }, = 'if'
             cond := ( ,{ Expr< Bool > }, )
             lit ,{ DefaultToken }, = 'then'
             then_e := ( ,{ Expr< T > }, )
             lit ,{ DefaultToken }, = 'else'
             else_e := ( ,{ Expr< T > }, )
         ]
     }' conditional -> .{
         '[Expr | match ,[cond], {
                     +[True]+ => ,[then_e],
                     +[False]+ => ,[else_e], } ]' }. ;
     in
         if (zero? five) then eight else two
   ```


### Pre-defined values
* `zero` through `ten` are integers. (What are these "literals" you speak of?)
* `plus`, `minus`, `times`, and `equal?` are binary functions.
* `zero?` is a unary function.
* `true` and `false` are boolean values.
* `fix` is the fixpoint function. A simple way to run forever, calculating the largest number:
    `(fix .[again: [ -> [Int -> Int]] . .[ n: Int . ((again) (plus n one))]. ].)`

## Patterns
* `+[Choice pat ⋯]+` deconstructs an enumerated value.

* `*[component: pat  ⋯]*` deconstructs a structure value.

* Quotation (with unquotation) is a valid pattern.
  The type annotation is always optional starting from a pattern.


## Types
* `[Type ⋯  -> Type]` is the function type.

* `{+[Choice Type ⋯]+  ⋯}` is the enumeration type.

* `*[component: Type  ⋯]*` is the structure type.

* `**[Type ⋯]**` is a tuple type.

* `forall X ⋯ . Type` is the abstracted type.

* `mu_type X ⋯ . Type` protects a recursive type from being infinitely large.
    It is typically used inside the definition of X.

* `Type<Type ⋯>` applies an abstracted type.
    For example, `List<Int>` is a list of integers.
    Currently, you'll want to leave a space between the angle brackets and any punctuation
     (the definition of `DefaultToken` needs revision to handle this).

* `:::[,T, >> Type]:::` is a type-level "splicing map". It requires `T` to refer to a tuple type. 
    Suppose `T` is `**[A B Int]**`. Then
    `[:::[,T, >> [T -> X]]::: -> Bool]` is `[ [A -> X] [B -> X] [Int -> X] -> Bool]`.

### Pre-defined types
* `Int` is a built-in type.
* `Bool` is defined as `{ +[True]+  +[False]+ }`.

## Syntax
* `lit ,{ Nt }, = 'arbitrary string'` is syntax for the exact text `arbitrary string`,
   where `Nt` is a lexer (usually useful so that surrounding whitespace gets discarded properly).
* `/regex/` is a lexer, which matches a [regex](https://docs.rs/regex/1.3.3/regex/).
   Be sure to have a capturing group around everything except for (e.g.) the whitespace to discard!
* `my_named_subterm := ( ,{Nt<Type>}, ) ` binds `my_named_subterm` to an `Nt` with the type `Type`.
  ```
  scrutinee := ( ,{Expr<T>}, )
  ```
* `[Syntax …]` is a sequence.
  ```
  [/abc/  skip_a_few := ( ,{ Expr<T>}, )  /xyz/]
  ```
* `Syntax *` is a zero-or-more repetition; `Syntax +` is a one-or-more repetition
  ```
  argument := ( ,{Expr<T>}, ) *
  # You'll want to use `...[,argument, >>    ]...` to handle the repetition correctly
  ```
* `forall T ⋯ . '{ Syntax }'  macro_name -> .{ Expr }.` defines a macro.
  `macro_name` must be unique, but is otherwise ignored (this problem should be fixed)
  ```
  forall T S . '{ [
      lit ,{ DefaultToken }, = 'let'
      [
          pat := ( ,{ Pat<S> }, )
          lit ,{ DefaultToken }, = '='
          value := ( ,{ Expr<S> }, )
          lit ,{ DefaultToken }, = ';'
      ] *
      lit ,{ DefaultToken }, = 'in'
      body := ( ,{ Expr<T> }, <-- ...[pat = value]... )
  ] }' let_macro -> .{
      '[Expr |
          match **[...[,value, >> ,[value], ]... ]**
              { **[...[,pat, >> ,[pat],]... ]** => ,[body], } ]'
  }.
  # introduces a `let` macro
  ```
* `Syntax <-- Beta` binds according to `Beta`'s specification.
  ```
  body := ( ,{Expr<T>}, ) <-- pat = value
  ```
TODO: there's more syntax than this

### Pre-defined nonterminals
These are defined in `core_forms.rs`, and their definitions are relatively short.
* `DefaultSeparator` matches whitespace. Redefine it to allow comments!
  ```
  DefaultSeparator ::= /((?s:\s|#[^\n]*)*)/ ;
  # Adds Python-style comments to the language
  ```
* `DafaultToken` is a `DefaultSeparator` followed by a token.
* `DafaultWord` is a `DefaultSeparator` followed by an identifier.
* `DefaultAtom` is a `DefaultWord`, except it doesn't match reserved words.
* `DefaultReference` is a `DefaultAtom`, except that it produces variable references,
    rather than atoms (which are binding-introducers).
* `Expr`, `Pat`, and `Type` are expressions, patterns, and types.

## Beta
* `term_name = term_name` binds the names in the left `term_name`
  to be equal to the contents of the right `term_name`.
* `term_name : term_name` binds the names in the left `term_name`
  to have the type from right `term_name` (which must be a `Type` term).
* `prot term_name` "protects" the names in `term_name`.
  This is what `mu_type` does.
* `forall term_name` abstracts over the names in `term_name`.
  This is what the type also named `forall` does.
* `...[Beta]...`, assuming all of the term names inside `Beta` are repeated,
  binds `Beta` for each repetition, shadowing left-to-right.
* `[Beta o> Beta]` does left-to-right shadowing between two `Beta`s

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
