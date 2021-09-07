#![allow(non_snake_case)]

use std::{fs::File, io::Read, path::Path};

use libunseemly::{
    ast,
    ast::Ast,
    core_forms, expand, grammar,
    name::{n, Name},
    runtime::{core_values, eval, eval::Value},
    ty, ty_compare,
    util::assoc::Assoc,
};
use std::{borrow::Cow, cell::RefCell, io::BufRead};

thread_local! {
    pub static TY_ENV : RefCell<Assoc<Name, Ast>> = RefCell::new(core_values::core_types());
    pub static VAL_ENV : RefCell<Assoc<Name, Value>> = RefCell::new(core_values::core_values());
}

#[cfg_attr(tarpaulin, skip)]
fn main() {
    let arguments: Vec<String> = std::env::args().collect();

    if arguments.len() == 1 {
        repl();
    } else if arguments.len() == 2 {
        let filename = Path::new(&arguments[1]);

        let mut raw_input = String::new();
        File::open(&filename)
            .expect("Error opening file")
            .read_to_string(&mut raw_input)
            .expect("Error reading file");

        // So the file can import (etc.) relative to its own location:
        if let Some(dir) = filename.parent() {
            if dir.is_dir() {
                std::env::set_current_dir(dir).unwrap();
            }
        }
        libunseemly::terminal_display(libunseemly::eval_unseemly_program_top(&raw_input));
    } else if arguments.len() == 3 {
        let lang = libunseemly::language_from_file(&std::path::Path::new(&arguments[1]));

        // Run the second program in the language defined by the first:
        let mut second_program = String::new();
        File::open(&Path::new(&arguments[2]))
            .expect("Error opening file")
            .read_to_string(&mut second_program)
            .expect("Error reading file");

        if let Some(dir) = Path::new(&arguments[2]).parent() {
            if dir.is_dir() {
                std::env::set_current_dir(dir).unwrap();
            }
        }
        libunseemly::terminal_display(libunseemly::eval_program(&second_program, lang));
    }
}

struct LineHelper {
    highlighter: rustyline::highlight::MatchingBracketHighlighter,
    // Braket-matching isn't exactly right,
    //  but running the whole parser to decide whether more lines are needed is probably ... bad.
    validator: rustyline::validate::MatchingBracketValidator,
}

impl LineHelper {
    fn new() -> LineHelper {
        LineHelper {
            highlighter: rustyline::highlight::MatchingBracketHighlighter::new(),
            validator: rustyline::validate::MatchingBracketValidator::new(),
        }
    }
}

impl rustyline::completion::Completer for LineHelper {
    type Candidate = String;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctxt: &rustyline::Context,
    ) -> Result<(usize, Vec<String>), rustyline::error::ReadlineError> {
        let mut res = vec![];
        let (start, word_so_far) = rustyline::completion::extract_word(line, pos, None, b"[({ })]");
        VAL_ENV.with(|vals| {
            let vals = vals.borrow();
            for k in vals.iter_keys() {
                if k.sp().starts_with(word_so_far) {
                    res.push(k.sp());
                }
            }
        });
        Ok((start, res))
    }
}

impl rustyline::hint::Hinter for LineHelper {
    type Hint = String;
    fn hint(&self, _line: &str, _pos: usize, _ctxt: &rustyline::Context) -> Option<String> { None }
}

impl rustyline::highlight::Highlighter for LineHelper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        self.highlighter.highlight_prompt(prompt, default)
    }
    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        self.highlighter.highlight_hint(hint)
    }
    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: rustyline::config::CompletionType,
    ) -> Cow<'c, str> {
        self.highlighter.highlight_candidate(candidate, completion)
    }
    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl rustyline::validate::Validator for LineHelper {
    fn validate(
        &self,
        ctx: &mut rustyline::validate::ValidationContext,
    ) -> rustyline::Result<rustyline::validate::ValidationResult> {
        self.validator.validate(ctx)
    }

    fn validate_while_typing(&self) -> bool { self.validator.validate_while_typing() }
}

impl rustyline::Helper for LineHelper {}

pub fn repl() {
    let prelude_filename = dirs::home_dir().unwrap().join(".unseemly_prelude");
    let history_filename = dirs::home_dir().unwrap().join(".unseemly_history");

    let mut rl = rustyline::Editor::<LineHelper>::new();
    rl.set_helper(Some(LineHelper::new()));

    let quit = regex::Regex::new(r"\s*quit\s*").unwrap();
    let just_parse = regex::Regex::new(r"^:p (.*)$").unwrap();
    let just_parse_debug_print = regex::Regex::new(r"^:pd (.*)$").unwrap();
    let just_type = regex::Regex::new(r"^:t (.*)$").unwrap();
    let just_eval = regex::Regex::new(r"^:e (.*)$").unwrap();
    let type_and_expand = regex::Regex::new(r"^:x (.*)$").unwrap();
    let canon_type = regex::Regex::new(r"^:tt (.*)$").unwrap();
    let subtype = regex::Regex::new(r"^:sub (.*)\s*<:\s*(.*)$").unwrap();
    let assign_value = regex::Regex::new(r"^(\w+)\s*:=(.*)$").unwrap();
    let save_value = regex::Regex::new(r"^:s +((\w+)\s*:=(.*))$").unwrap();
    let assign_type = regex::Regex::new(r"^(\w+)\s*t=(.*)$").unwrap();
    let save_type = regex::Regex::new(r"^:s +((\w+)\s*t=(.*))$").unwrap();
    let comment = regex::Regex::new(r"^#").unwrap();

    println!();
    println!("                    \x1b[1;38mUnseemly\x1b[0m");
    println!("    `<expr>` to (typecheck and expand and) evaluate `<expr>`.");
    println!("    `:x <expr>` to (typecheck and) expand `<expr>`.");
    println!("    `:e <expr>` to (expand and) evaluate `<expr>` without typechecking.");
    println!("    `<name> := <expr>` to bind a name for this session.");
    println!("    `:t <expr>` to synthesize the type of <expr>.");
    println!("    `:tt <type>` to canonicalize <type>.");
    println!("    `:sub <type_a> <: <type_b>` to check that `<type_a>` is a subtype of `<type_b>`");
    println!("    `<name> t= <type>` to bind a type for this session.");
    println!("    `:s <name> := <expr>` to save a binding to the prelude for the future.");
    println!("    `:s <name> t= <expr>` to save a type binding to the prelude.");
    println!("    `:p <expr>` to parse `<expr>` and pretty-print its AST output.");
    println!("    `:pd <expr>` to parse `<expr>` and debug-print its AST output.");
    println!("    Command history is saved over sessions.");
    println!("    Tab-completion works on variables, and lots of Bash-isms work.");
    if let Ok(prelude_file) = File::open(&prelude_filename) {
        let prelude = std::io::BufReader::new(prelude_file);
        for line in prelude.lines() {
            let line = line.unwrap();
            if comment.captures(&line).is_some() {
                // comment
            } else if let Some(caps) = assign_value.captures(&line) {
                if let Err(e) = assign_variable(&caps[1], &caps[2]) {
                    println!("    Error in prelude line: {}\n    {}", line, e);
                }
            } else if let Some(caps) = assign_type.captures(&line) {
                if let Err(e) = assign_t_var(&caps[1], &caps[2]) {
                    println!("    Error in prelude line: {}\n    {}", line, e);
                }
            }
        }
        println!("    [prelude loaded from {}]", prelude_filename.display());
    }
    println!();
    println!("This virtual machine kills cyber-fascists.");

    let _ = rl.load_history(&history_filename);
    while let Ok(line) = rl.readline("\x1b[1;36m≫\x1b[0m ") {
        // TODO: count delimiters, and allow line continuation!
        rl.add_history_entry(line.clone());

        if quit.captures(&line).is_some() {
            break;
        }

        let result = if let Some(caps) = just_parse.captures(&line) {
            parse_unseemly_program(&caps[1], true)
        } else if let Some(caps) = just_parse_debug_print.captures(&line) {
            parse_unseemly_program(&caps[1], false)
        } else if let Some(caps) = just_type.captures(&line) {
            type_unseemly_program(&caps[1]).map(|x| format!("{}", x))
        } else if let Some(caps) = just_eval.captures(&line) {
            eval_unseemly_program_without_typechecking(&caps[1]).map(|x| format!("{}", x))
        } else if let Some(caps) = type_and_expand.captures(&line) {
            type_and_expand_unseemly_program(&caps[1]).map(|x| format!("{}", x))
        } else if let Some(caps) = canon_type.captures(&line) {
            canonicalize_type(&caps[1]).map(|x| format!("{}", x))
        } else if let Some(caps) = subtype.captures(&line) {
            check_subtype(&caps[1], &caps[2]).map(|x| format!("{}", x))
        } else if let Some(caps) = assign_value.captures(&line) {
            assign_variable(&caps[1], &caps[2]).map(|x| format!("{}", x))
        } else if let Some(caps) = save_value.captures(&line) {
            match assign_variable(&caps[2], &caps[3]) {
                Ok(_) => {
                    use std::io::Write;
                    let mut prel_file = std::fs::OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open(&prelude_filename)
                        .unwrap();
                    writeln!(prel_file, "{}", &caps[1]).unwrap();
                    Ok(format!("[saved to {}]", &prelude_filename.display()))
                }
                Err(e) => Err(e),
            }
        } else if let Some(caps) = assign_type.captures(&line) {
            assign_t_var(&caps[1], &caps[2]).map(|x| format!("{}", x))
        } else if let Some(caps) = save_type.captures(&line) {
            match assign_t_var(&caps[2], &caps[3]) {
                Ok(_) => {
                    use std::io::Write;
                    let mut prel_file = std::fs::OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open(&prelude_filename)
                        .unwrap();
                    writeln!(prel_file, "{}", &caps[1]).unwrap();
                    Ok(format!("[saved to {}]", &prelude_filename.display()))
                }
                Err(e) => Err(e),
            }
        } else {
            eval_unseemly_program(&line).map(|x| format!("{}", x))
        };

        match result {
            Ok(v) => println!("\x1b[1;32m≉\x1b[0m {}", v),
            Err(s) => println!("\x1b[1;31m✘\x1b[0m {}", s),
        }
    }
    println!("Bye! Saving history to {}", &history_filename.display());
    rl.save_history(&history_filename).unwrap();
}

fn assign_variable(name: &str, expr: &str) -> Result<Value, String> {
    let res = eval_unseemly_program(expr);

    if let Ok(ref v) = res {
        let ty = type_unseemly_program(expr).unwrap();
        TY_ENV.with(|tys| {
            VAL_ENV.with(|vals| {
                let new_tys = tys.borrow().set(n(name), ty);
                let new_vals = vals.borrow().set(n(name), v.clone());
                *tys.borrow_mut() = new_tys;
                *vals.borrow_mut() = new_vals;
            })
        })
    }
    res
}

fn assign_t_var(name: &str, t: &str) -> Result<Ast, String> {
    let ast = grammar::parse(
        &grammar::FormPat::Call(n("Type")),
        core_forms::outermost__parse_context(),
        t,
    )
    .map_err(|e| e.msg)?;

    let res =
        TY_ENV.with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)));

    if let Ok(ref t) = res {
        TY_ENV.with(|tys| {
            let new_tys = tys.borrow().set(n(name), t.clone());
            *tys.borrow_mut() = new_tys;
        })
    }

    res
}

fn canonicalize_type(t: &str) -> Result<Ast, String> {
    let ast = grammar::parse(
        &grammar::FormPat::Call(n("Type")),
        core_forms::outermost__parse_context(),
        t,
    )
    .map_err(|e| e.msg)?;

    TY_ENV.with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)))
}

fn check_subtype(t_a: &str, t_b: &str) -> Result<Ast, String> {
    let ast_a = grammar::parse(
        &grammar::FormPat::Call(n("Type")),
        core_forms::outermost__parse_context(),
        t_a,
    )
    .map_err(|e| e.msg)?;

    let ast_b = grammar::parse(
        &grammar::FormPat::Call(n("Type")),
        core_forms::outermost__parse_context(),
        t_b,
    )
    .map_err(|e| e.msg)?;

    TY_ENV.with(|tys| {
        ty_compare::must_subtype(&ast_a, &ast_b, tys.borrow().clone())
            .map(
                // TODO: just figure out how to import `ast!` instead:
                |env| {
                    ast::Ast(std::rc::Rc::new(ast::LocatedAst {
                        c: ast::Atom(n(&format!("OK, under this environment: {}", env))),
                        begin: 0,
                        end: 0,
                        file_id: 0,
                    }))
                },
            )
            .map_err(|e| format!("{}", e))
    })
}

fn parse_unseemly_program(program: &str, pretty: bool) -> Result<String, String> {
    let ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        program,
    )
    .map_err(|e| e.msg)?;

    if pretty {
        Ok(format!("{}", ast))
    } else {
        Ok(format!("{:#?}", ast))
    }
}

fn type_unseemly_program(program: &str) -> Result<Ast, String> {
    let ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        program,
    )
    .map_err(|e| e.msg)?;

    TY_ENV.with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)))
}

fn eval_unseemly_program_without_typechecking(program: &str) -> Result<Value, String> {
    let ast: Ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        program,
    )
    .map_err(|e| e.msg)?;

    let core_ast = expand::expand(&ast).map_err(|_| "error".to_owned())?;

    VAL_ENV.with(|vals| eval::eval(&core_ast, vals.borrow().clone()).map_err(|_| "???".to_string()))
}

fn eval_unseemly_program(program: &str) -> Result<Value, String> {
    let ast: Ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        program,
    )
    .map_err(|e| e.msg)?;

    let _type = TY_ENV
        .with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)))?;

    let core_ast = expand::expand(&ast).map_err(|_| "error".to_owned())?;

    VAL_ENV.with(|vals| eval::eval(&core_ast, vals.borrow().clone()).map_err(|_| "???".to_string()))
}

fn type_and_expand_unseemly_program(program: &str) -> Result<ast::Ast, String> {
    let ast: Ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        program,
    )
    .map_err(|e| e.msg)?;

    let _type = TY_ENV
        .with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)))?;

    expand::expand(&ast).map_err(|_| "error".to_owned())
}
