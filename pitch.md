## Philosophical pitch

Unseemly is the first language that can safely typecheck all macros before expansion.

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
It's because type errors in macro-generated code are incredibly difficult to understand.

This is no small issue.
Type errors are the user interface of a typed language;
 the primary purpose of types is to produce useful error messages.

Macros in Unseemly have types.
This means that typechecking happens on code with macros in it,
 as opposed to code with all the macros expanded away.

So, just like a true Scheme, in Unseemly you don't know
 whether something is part of the language or whether it's a macro.
And, just like a true ML, Unseemly's type errors are concise and useful.


## Simple, comparative-PL pitch

Unseemly is a language with ML-like types and Scheme-like macros.
 In a sense, it's the first one.

It's very small, and the syntax is weird,
 but you can build a bigger, better language with the macros.
The macros are typechecked before expansion,
 so the programmer won't care what is a macro, and what's part of the core language.

To my knowledge, Unseemly is the first language
 where macros that bind names can be safely typechecked without expanding them.
(Modulo one thing that still needs to be designed and implemented)