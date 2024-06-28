use crate::ast::{Expr, Statement};
use crate::parser::{Parser, ParserError};
use crate::scanner::tokenize;

// Unfortunately to have these functions here I had to make a lot of things 'public'.
// Not a huge deal but does not feel very clean.

pub fn parse_expr(code: &str) -> Result<Expr, ParserError> {
    let tokens = tokenize(code.to_string(), |error| panic!("{}", error));
    let mut parser = Parser::new(tokens.into_iter());
    parser.parse_expression()
}

pub fn parse_statement(code: &str) -> Result<Statement, ParserError> {
    let tokens = tokenize(code.to_string(), |error| panic!("{}", error));
    let mut parser = Parser::new(tokens.into_iter());
    parser.parse_statement()
}

pub fn parse_program(code: &str) -> Result<Vec<Statement>, ParserError> {
    let tokens = tokenize(code.to_string(), |error| panic!("{}", error));
    let mut parser = Parser::new(tokens.into_iter());
    parser.parse_program()
}
