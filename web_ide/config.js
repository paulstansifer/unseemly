
// Dynamic Highlighting attempts to respect in-file syntax extensions.
// It's janky and slow
//  (it's implemented by, every few seconds, re-parsing the file (while involves running phase-1+ code),
//    and finding long lines in the syntax extension to mark where the language changes),
//  but it makes for a cool demo!
dynamic_highlighting = true;

// [not supported yet]
// Each of these (possibly relative) URLs will be opened in a tab.
open_files = ["example.unseemly"];

// [not supported yet]
// If empty, Unseemly. Otherwise, the URL of the language to use for execution and syntax-highlighting purposes.
base_language = "";