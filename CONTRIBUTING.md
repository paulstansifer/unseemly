Ways you can contribute:
 * You can write code in Unseemly! It needs testing! You can add examples to `src/examples`, and
   file bugs in the [issue  tracker] when things don't work.
 * You can fix a bug. There are some in the [issue tracker]. Issues that don't require much
   context about the language and are on the smaller side are marked ["good first issue"].
 * You can fix a TODO. There are [a lot of TODOs] in the codebase. Some of them are simple
   refactorings, some are self-contained design issues, others are more complex.
 * You can file a bug. If you find a problem or want a feature, the [issue tracker] is the place to
   go. Many of the TODOs should be given associated issues (e.g. `// TODO #7832`).
 * You can write tests. [Test coverage] is decent, but could be better. (You can get the list of
   all files sorted by number of missed lines to look for low-hanging fruit.) Even writing tests
   for low-priority things (like `impl Debug`s) to get the numbers up helps focus attention on
   existing gaps. Also of interest: what's test coverage without end-to-end tests?
 * If you're ambitious, you can pick something in MISTAKES.md and fix it!

[issue tracker]: https://github.com/paulstansifer/unseemly/issues
["good first issue"]: https://github.com/paulstansifer/unseemly/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22
[a lot of TODOs]: https://github.com/paulstansifer/unseemly/search?q=TODO&unscoped_q=TODO
[Test coverage]: https://coveralls.io/github/paulstansifer/unseemly

Things to know about developing Unseemly:
  * Try setting the `UNSEEMLY_TRACE` environment variable to `full` for a complete view of all
    `Ast`-walking.
    So if you get test failures, try `UNSEEMLY_TRACE=full cargo test`
  * Appended carrots (🥕) distinguish variable names that "look" the same, but differ due to
    freshening. (If you see tomatoes; they serve a similar purpose, but for debug-printing.)
  * To observe freshening, try `UNSEEMLY_FRESHEN_WATCH=variable_name`; it will show what's happening
    each time that name is freshened.
  * In the REPL (`cargo run --release`), use ctrl-R to search your REPL history.
    Add commonly-used definitions to your `~/.unseemly_prelude` file.
