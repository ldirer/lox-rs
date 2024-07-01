use std::fmt::Debug;
use std::fs::read_to_string;
use std::io::Write;
use std::path::Path;
use std::process::exit;
use std::{env, io};

use thiserror::Error;

use crate::interpreter::Interpreter;
use crate::parser::parse;
use crate::resolver::VariableResolver;
use crate::scanner::{tokenize, ScanningError};

mod ast;
mod environment;
mod interpreter;
mod parser;
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
    //     TODO need to add a 'catch all' error if I want to return interpreter/parser/scanning errors?
    // handling them is all well and nice but this means we don't have a stacktrace...
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
        run_prompt()?;
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
    run(self_content);
    return Ok(());
}

fn run_prompt() -> Result<(), CLIError> {
    fn prompt() {
        print!("> ");
        io::stdout().flush().unwrap();
    }

    let lines = io::stdin().lines();
    prompt();
    for line in lines {
        // TODO reset error status somehow
        run(line.unwrap());
        prompt();
    }
    Ok(())
}

fn run(source: String) {
    // passing a 'handle error' callback to stick to the book.
    let tokens = tokenize(source, scanner_error);
    // println!("{:#?}", tokens);
    let mut parsed = parse(tokens.into_iter());
    // println!("{:#?}", parsed);
    let stdout_binding = std::io::stdout();
    let mut interpreter = Interpreter::new(stdout_binding);

    let mut resolver_ = VariableResolver::new();
    match parsed {
        Err(err) => {
            eprintln!("{err}");
            exit(65)
        }
        Ok(mut statements) => {
            if let Err(err) = resolver_.resolve_program(&mut statements) {
                eprintln!("{err}");
                exit(65)
            }
            match interpreter.interpret_program(&statements) {
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
                    exit(70)
                }
            }
        }
    }
}

fn scanner_error(err: ScanningError) {
    match err {
        ScanningError::UnexpectedCharacter { line, character: _ } => {
            report(line, "", &format!("Scanner error: {err}"))
        }
        ScanningError::UnterminatedString {
            line,
            string_start: _,
        } => report(line, "", &format!("Scanner error: {err}")),
        ScanningError::UnterminatedBlockComment {
            line,
            comment_start: _,
        } => report(line, "", &format!("Scanner error: {err}")),
    }
}

fn report(line: usize, location: &str, message: &str) {
    eprintln!("[line {line}] Error {location}: {message}");
    exit(65)
    //     TODO had_error = true
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_scanner() {
        assert_eq!(2, 1 + 1)
    }
}
