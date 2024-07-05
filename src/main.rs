use std::fmt::Debug;
use std::fs::read_to_string;
use std::io::Write;
use std::path::Path;
use std::process::exit;
use std::rc::Rc;
use std::{env, io};

use thiserror::Error;

use repl::MultilineInput;

use crate::interpreter::{Interpreter, LoxEnvironment};
use crate::parser::parse;
use crate::resolver::VariableResolver;
use crate::scanner::{tokenize, ScanningError};

mod ast;
mod environment;
mod interpreter;
mod parser;
mod repl;
mod resolver;
mod scanner;
mod test_helpers;
mod token;

#[derive(Debug, Error)]
enum CLIError {
    #[error(transparent)]
    IoError(#[from] std::io::Error),
    #[error("file does not seem to exist {0}")]
    FileDoesNotExist(String),
}

fn main() -> Result<(), color_eyre::eyre::Error> {
    color_eyre::install()?;

    let args: Vec<String> = env::args().collect();
    if args.len() > 2 {
        println!("Too many arguments received ({})", args.len());
        println!("Usage: rlox [script]");
        exit(64);
    }
    if args.len() == 2 {
        let file_path = &args[1];
        run_file(file_path)?;
    } else {
        run_repl()?;
    }
    Ok(())
}

fn run_file(path_string: &String) -> Result<(), CLIError> {
    let path = Path::new(path_string);
    let exists = path.try_exists().expect(&format!(
        "unable to check existence of {:?}, check ",
        path_string
    ));
    if !exists {
        return Err(CLIError::FileDoesNotExist(String::to_string(path_string)));
    }
    let self_content = read_to_string(path)?;
    run(None, self_content, true);
    return Ok(());
}

fn run_repl() -> Result<(), CLIError> {
    fn prompt() {
        // I ran into a weird behavior where the prompt is not shown in past commands.
        // looks like it is caused by `rlwrap`, if I run the program directly there is no issue.
        print!("> ");
        io::stdout().flush().unwrap();
    }

    let repl_env = Rc::new(LoxEnvironment::new(None));

    let lines = io::stdin().lines();
    prompt();
    let inputs = MultilineInput::new(lines);
    for input in inputs {
        run(Some(repl_env.clone()), input, false);
        prompt();
    }
    Ok(())
}

fn run(environment: Option<Rc<LoxEnvironment>>, source: String, exit_on_error: bool) {
    // passing a 'handle error' callback to stick to the book. Did not follow this pattern for the rest (parser, etc).
    let mut scanner_error_handler = ScannerErrorHandler::new();
    let tokens = tokenize(source, |err| scanner_error_handler.handle(err));

    for err in &scanner_error_handler.errors {
        // print scanning errors but don't exit/return: we want to run the parser too.
        // this is to make official tests pass. I guess maybe this is done in the book to report relevant errors to the user in one pass?
        let line = err.get_line();
        eprintln!("[line {line}] Error: {err}");
    }

    // println!("{:#?}", tokens);
    let parsed = parse(tokens.into_iter());
    // println!("{:#?}", parsed);
    let stdout_binding = std::io::stdout();
    let mut interpreter = Interpreter::new(stdout_binding);

    let mut resolver_ = VariableResolver::new();
    match parsed {
        Err(errors) => {
            for err in errors {
                eprintln!("{err}");
            }
            if exit_on_error {
                exit(65);
            }
        }
        Ok(mut statements) => {
            // don't run code that didn't pass scanning
            if scanner_error_handler.errors.len() > 0 {
                if exit_on_error {
                    exit(65);
                }
                return;
            }
            if let Err(errors) = resolver_.resolve_program(&mut statements) {
                for err in errors {
                    eprintln!("{err}");
                }
                if exit_on_error {
                    exit(65);
                }
            }
            // println!("{:#?}", statements);
            let interpreted = match environment {
                None => interpreter.interpret_program(&statements),
                Some(env) => interpreter.interpret_program_with_env(&statements, env),
            };
            match interpreted {
                Ok(_) => {}
                Err(err) => {
                    // making the format of what we print consistent with what the Java version does
                    // so the tests from the official repo can be run without modification.
                    // first line is a runtime error, then it's a stacktrace (only the first line of the stacktrace is checked).
                    eprintln!(
                        "{}",
                        err.to_string()
                            .strip_prefix("[line ")
                            .unwrap()
                            .trim_start_matches(|c: char| c.is_digit(10))
                            .strip_prefix("] runtime error: ")
                            .unwrap()
                    );
                    eprintln!("{err}");
                    if exit_on_error {
                        exit(70);
                    }
                }
            }
        }
    }
}

struct ScannerErrorHandler {
    pub errors: Vec<ScanningError>,
}

impl ScannerErrorHandler {
    fn new() -> ScannerErrorHandler {
        ScannerErrorHandler { errors: vec![] }
    }
    fn handle(&mut self, error: ScanningError) {
        self.errors.push(error);
    }
}
