## Changelog

## Current version
### Fixed
 - Macro type parameters can now be used in defining the macro.

## 0.0.3 - 2021-12-02
### Added
 - Added a Web IDE, with automatically-generated syntax-highlighting.
### Fixed
 - Improved the parser somewhat.

## 0.0.2 - 2021-08-22
### Added
 - Added more builtin functions, and the `Option<T>` type.
 - Added `common` and `reserving` to the syntax for grammars.
### Fixed
 - Fixed an erratic bug where `Form` identity was lost.
 - Improved display of parse ambiguities.

## 0.0.1 - 2021-08-20
### Added
- Added rudimentary multi-file program support.
  * To define a library, introduce the syntax and values that should be exposed,
     and write `capture_language` as the program body
  * To use a library write `import \[library_definition.unseemly]\`.
    This overwrites the current syntactic environment and extends the runtime environment.
    (So, only the most recent `import` provides macros.)
  * You interpret a file in a specific language with
    `unseemly language_definition.unseemly program.lang`
- Introduced string literals and the `String` type.
- Introduced sequence literals.
- Introduced the `Cell` type for side-effects.
- Introduced some basic operations on `Sequence<T>`, `String`, and `Cell` types.
- Introduced value and type "prefabs".
  * `(prefab v)` produces (imaginary) syntax for an expression that returns `v`.
  * `prefab_type T` produces (imaginary) syntax for the type `T`.
- Added support for `UNSEEMLY_FRESHEN_WATCH
### Fixed
- Display of multiline error messages now uses newlines instead of "\n".
- Macros can now be *used* in the implementation of other macros, not just expanded-to.
- Values can be captured in macro definitions.

## 0.0.0 - 2020-02-02
### Added
- Implemented the Unseemly programming language. Usage is described in `core_language_basics.md`.
  It's a bit buggy at the moment, and it's missing some features.