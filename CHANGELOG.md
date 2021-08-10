## Changelog

## Current
### Added
- Added rudimentary multi-file program support.
  * To define a library, introduce the syntax and values that should be exposed,
     and write `capture_language` as the program body
  * To use a library write `import \[library_definition.unseemly]\`.
    This overwrites the current syntactic environment and extends the runtime environment.
    (So, only the most recent `import` provides macros.)
- Introduced string literals and the `String` type.
- Introduced some basic operations on `Sequence` and `String` types.
### Fixed
- Display of multiline error messages now uses newlines instead of "\n".

## 0.0.0 - 2020-02-02
### Added
- Implemented the Unseemly programming language. Usage is described in `core_language_basics.md`.
  It's a bit buggy at the moment, and it's missing some features.