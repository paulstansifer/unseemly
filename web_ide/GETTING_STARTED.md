## The Web IDE for Unseemly

To build the Wasm version of the compiler,
 first switch to the root of where you checked out the Unseemly repo
  (or change the `--out-dir` argument below).
Then:

```
cargo install wasm-pack
wasm-pack build --target no-modules --out-dir web_ide/ --no-typescript --release
```

This will create files in `web_ide/` (this directory), but they will be `.gitignore`d.

To test that it worked, load `ide.html`.
You can't use a `file://` URL;
 you'll need to use a local webserver like
  the Live Server extension in VS Code
  or `python3 -m http.server`.
  or `npm i local-web-server` and then `ws`.

To publish, host the files together (deleting the `.gitignore` and the human-readable files).
One option is to use [GitHub Pages](https://pages.github.com/).