Unseemly is the first typed macro language.

I like to divide the design of programming languages into two main threads.
There are other, equally-valid, ways of looking at them,
 but this one appeals to me.

One thread, the family of typed languages
 includes the MLs and Haskell, as well as C++, Java, Rust, and so on.
Programmers in those languages use type systems
 to both describe data they are interested in and to express invariants.

The other, smaller, thread is macro languages.
These are mostly direct descendants of Lisp: Scheme, and Racket, etc.
If you squint, the dynamic metaprogramming systems of Ruby and JavaScript
 make them cousins of this family, too.
Programmers in those languages use metaprogramming to
 abstract over surface syntax, control flow, and binding,
 and to construct lightweight DSLs that integrate with the main language well.

But if you write in a typed language,
 you almost certainly hear the advice to use the macro system sparingly,
  if at all.
And the macro languages all lack type systems.
Why?
If you don't follow that advice, you will discover that
 type errors in macro-generated code
  are incredibly difficult to understand.

This is no small issue.
Type errors are the user interface of a typed language;
 the primary purpose of types is to produce useful error messages.
