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
