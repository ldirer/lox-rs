use crate::ast::{Expr, Statement};
use crate::parser::{parse, Parser, ParserError};
use crate::resolver::{VariableResolver, VariableResolverError};
use crate::scanner::tokenize;

// Unfortunately to have these functions here I had to make a lot of things 'public'.
// Not a huge deal but does not feel very clean.

#[allow(dead_code)]
pub fn parse_expr(code: &str) -> Result<Expr, ParserError> {
    let tokens = tokenize(code.to_string(), |error| panic!("{}", error));
    let mut parser = Parser::new(tokens.into_iter());
    parser.parse_expression()
}

#[allow(dead_code)]
pub fn parse_statement(code: &str) -> Result<Statement, ParserError> {
    let tokens = tokenize(code.to_string(), |error| panic!("{}", error));
    let mut parser = Parser::new(tokens.into_iter());
    parser.parse_statement()
}

#[allow(dead_code)]
pub fn parse_program(code: &str) -> Result<Vec<Statement>, Vec<ParserError>> {
    let tokens = tokenize(code.to_string(), |error| panic!("{}", error));
    parse(tokens.into_iter())
}

#[allow(dead_code)]
pub fn parse_and_resolve_program(code: &str) -> Result<Vec<Statement>, Vec<VariableResolverError>> {
    let tokens = tokenize(code.to_string(), |error| panic!("{}", error));
    let mut program = parse(tokens.into_iter()).unwrap();

    let mut resolver = VariableResolver::new();
    resolver.resolve_program(&mut program)?;
    Ok(program)
}
