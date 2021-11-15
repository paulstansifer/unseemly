## The Web IDE for Unseemly

The Unseemly Web IDE is totally client-side;
 you can host it as a set of static files.
It's not hard to set up!

To build the Wasm version of the compiler,
 first switch to the root of where you checked out the Unseemly repo
  (or change the `--out-dir` argument below).
Then:

```
cargo install wasm-pack
wasm-pack build --target no-modules --out-dir web_ide/wasm/ --no-typescript --release
```

This will create files in `web_ide/wasm/`, but they will be `.gitignore`d.

To test that it worked, load `ide.html`.
You can't use a `file://` URL;
 you'll need to use a local webserver like
  the Live Server extension in VS Code
  or `python3 -m http.server`.
  or `npm i local-web-server` and then `ws`.

Then, edit `config.js` to configure the IDE.
For example,
 `base_language = "newlang.unseemly"` and `starter_file = "example.newlang"`
  to make an IDE for the language defined in `newlang.unseemly`.
(Files that you reference need to be in this directory.)

To publish, host the files together (you can delete the `.gitignore` and the human-readable files).
One option is to use [GitHub Pages](https://pages.github.com/).