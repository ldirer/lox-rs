use color_eyre::eyre;
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::fs::read_to_string;
use std::io::Error;
use std::path::Path;
use std::process::exit;
use std::{env, error};

#[derive(Debug)]
enum CLIError {
    IoError(std::io::Error),
    FileDoesNotExist(String),
}

impl From<std::io::Error> for CLIError {
    fn from(value: Error) -> Self {
        Self::IoError(value)
    }
}

impl fmt::Display for CLIError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            CLIError::IoError(e) => {
                write!(f, "{}", e)
            }
            CLIError::FileDoesNotExist(filename) => {
                write!(f, "{}", filename)
            }
        }
    }
}

impl error::Error for CLIError {}

fn main() -> Result<(), color_eyre::eyre::Error> {
    color_eyre::install()?;

    let args: Vec<String> = env::args().collect();
    dbg!(args.join(" "));
    if args.len() > 2 {
        println!("Too many arguments received ({})", args.len());
        println!("Usage: rlox [script]");
        exit(64);
    }

    let file_path = &args[1];
    run_file(file_path)
}

fn run_file(path_string: &String) -> Result<(), color_eyre::eyre::Error> {
    let path = Path::new(path_string);
    let exists = path.try_exists().expect(&format!(
        "unable to check existence of {:?}, check ",
        path_string
    ));
    if !exists {
        return Err(color_eyre::eyre::eyre!("file does not exist {:?}", path));
    }
    let self_content = read_to_string(path)?;
    println!("FILE CONTENT {self_content}");
    return Ok(());
}
