use std::fmt::Debug;
use std::fs::read_to_string;
use std::io::Write;
use std::path::Path;
use std::process::exit;
use std::{env, error, io};

use thiserror::Error;

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
    dbg!(args.join(" "));
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
    println!("FILE CONTENT {self_content}");
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
        run(line.unwrap());
        prompt();
    }
    Ok(())
}

fn run(source: String) {
    println!("{source}")
}
