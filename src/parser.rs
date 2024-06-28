use std::iter::Peekable;

use thiserror::Error;

use crate::ast::Statement::WhileStatement;
use crate::ast::{BinaryLogicalOperator, BinaryOperator, Expr, Literal, Statement, UnaryOperator};
use crate::token::{Token, TokenType};

#[derive(Debug, Error, PartialEq)]
pub enum ParserError {
    #[error("line: {line}. Expected ')' after expression.")]
    UnmatchedParenthesis { line: usize },
    #[error("line: {line}. Unexpected token {lexeme}.")]
    UnexpectedToken { line: usize, lexeme: String },
    // line is not implemented yet for missing tokens
    #[error("line: {line}. Expected ';' after value.")]
    MissingSemicolonPrint { line: usize },
    #[error("line: {line}. Expected ';' after expression.")]
    MissingSemicolonExpressionStatement { line: usize },
    #[error("line: {line}. invalid syntax for variable declaration.")]
    InvalidSyntaxVarDeclaration { line: usize },
    #[error("line: {line}. Expected ';' after variable declaration.")]
    MissingSemicolonVariableDeclaration { line: usize },
    #[error("line: {line}. Invalid assignment target.")]
    InvalidAssignmentTarget { line: usize },
    #[error("line: {line}. Unclosed block, expected '}}'.")]
    UnclosedBlock { line: usize },
    // these dedicated error types... dont feel very useful.
    #[error("line: {line}. Missing '(' after 'while'.")]
    MissingOpeningParenthesisWhile { line: usize },
    #[error("line: {line}. Missing ')' after condition.")]
    MissingClosingParenthesisCondition { line: usize },
    #[error("line: {line}. Missing '(' after 'if'.")]
    MissingOpeningParenthesisIf { line: i32 },
}
pub struct Parser<T: Iterator<Item = Token>> {
    tokens: Peekable<T>,
}

pub fn parse<T>(tokens: T) -> Result<Vec<Statement>, ParserError>
where
    T: Iterator<Item = Token>,
{
    let mut parser = Parser::new(tokens);
    parser.parse_program()
}

impl<T: Iterator<Item = Token>> Parser<T> {
    pub(crate) fn new(tokens: T) -> Self {
        let tokens = tokens.peekable();
        Parser { tokens }
    }

    // clean error handling not the focus yet
    pub fn parse_program(&mut self) -> Result<Vec<Statement>, ParserError> {
        let mut statements: Vec<Statement> = vec![];
        while !self.is_at_end() {
            statements.push(self.parse_declaration()?);
        }
        Ok(statements)
    }

    pub fn parse_declaration(&mut self) -> Result<Statement, ParserError> {
        match self.match_current(&vec![TokenType::Var]) {
            Some(_) => self.parse_var_declaration(),
            None => self.parse_statement(),
        }
    }

    fn parse_var_declaration(&mut self) -> Result<Statement, ParserError> {
        match self.match_current(&vec![TokenType::Identifier]) {
            None => return Err(ParserError::InvalidSyntaxVarDeclaration { line: 0 }),
            Some(Token {
                r#type: TokenType::Identifier,
                lexeme: name,
                ..
            }) => {
                let mut initializer = Expr::Literal(Literal::Nil);
                if self.match_current(&vec![TokenType::Equal]).is_some() {
                    initializer = self.parse_expression()?;
                }

                let line = self.tokens.peek().unwrap().line;
                self.consume(
                    TokenType::Semicolon,
                    ParserError::MissingSemicolonVariableDeclaration { line },
                )?;

                Ok(Statement::VarDeclaration { initializer, name })
            }
            Some(t) => unreachable!("unexpected token type for {:?}", t),
        }
    }

    pub(crate) fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        if self.match_current(&vec![TokenType::Print]).is_some() {
            return self.parse_print_statement();
        }
        if self.match_current(&vec![TokenType::If]).is_some() {
            return self.parse_if_statement();
        }

        if self.match_current(&vec![TokenType::While]).is_some() {
            return self.parse_while_statement();
        }
        if self.match_current(&vec![TokenType::LeftBrace]).is_some() {
            return Ok(Statement::Block {
                statements: self.parse_block()?,
            });
        }
        self.parse_expression_statement()
    }

    fn parse_if_statement(&mut self) -> Result<Statement, ParserError> {
        self.consume(
            TokenType::LeftParen,
            ParserError::MissingOpeningParenthesisIf { line: 0 },
        )?;
        let condition = self.parse_expression()?;
        self.consume(
            TokenType::RightParen,
            ParserError::MissingClosingParenthesisCondition { line: 0 },
        )?;
        let then_branch = self.parse_statement()?;

        let mut else_branch_box = None;
        if self.match_current(&vec![TokenType::Else]).is_some() {
            else_branch_box = Some(Box::new(self.parse_statement()?));
        }
        Ok(Statement::IfStatement {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: else_branch_box,
        })
    }
    fn parse_while_statement(&mut self) -> Result<Statement, ParserError> {
        self.consume(
            TokenType::LeftParen,
            ParserError::MissingOpeningParenthesisWhile { line: 0 },
        )?;
        let condition = self.parse_expression()?;
        self.consume(
            TokenType::RightParen,
            ParserError::MissingClosingParenthesisCondition { line: 0 },
        )?;
        let body = self.parse_statement()?;
        Ok(Statement::WhileStatement {
            condition,
            body: Box::new(body),
        })
    }

    fn parse_block(&mut self) -> Result<Vec<Statement>, ParserError> {
        let mut statements = vec![];
        while !self.is_at_end()
            && !self
                .tokens
                .peek()
                .is_some_and(|t| t.r#type == TokenType::RightBrace)
        {
            statements.push(self.parse_declaration()?);
        }
        let line = self.tokens.peek().unwrap().line;
        self.consume(TokenType::RightBrace, ParserError::UnclosedBlock { line })?;
        Ok(statements)
    }

    fn parse_print_statement(&mut self) -> Result<Statement, ParserError> {
        let expr = self.parse_expression()?;
        let token_match = self.match_current(&vec![TokenType::Semicolon]);
        match token_match {
            // todo grab the line somehow? on the previous token. '.previous' that I removed would be useful here.
            None => Err(ParserError::MissingSemicolonPrint { line: 0 }),
            Some(_) => Ok(Statement::PrintStatement { expression: expr }),
        }
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, ParserError> {
        let expr = self.parse_expression()?;
        let token_match = self.match_current(&vec![TokenType::Semicolon]);
        match token_match {
            None => Err(ParserError::MissingSemicolonExpressionStatement { line: 0 }),
            Some(_) => Ok(Statement::ExprStatement { expression: expr }),
        }
    }

    /// parsing functions encode grammar rules. This code should be read with the grammar.
    /// in particular, the grammar used here (from the book) encodes precedence rules.
    pub(crate) fn parse_expression(&mut self) -> Result<Expr, ParserError> {
        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParserError> {
        let expr = self.parse_logical_or()?;
        match (self.match_current(&vec![TokenType::Equal]), &expr) {
            (None, _) => Ok(expr),
            (Some(_), Expr::Variable { name }) => {
                let value = self.parse_assignment()?;
                Ok(Expr::Assign {
                    name: name.clone(),
                    value: Box::new(value),
                })
            }
            (Some(token), _) => Err(ParserError::InvalidAssignmentTarget { line: token.line }),
        }
    }

    fn parse_logical_or(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_logical_and()?;
        while let Some(token) = self.match_current(&vec![TokenType::Or]) {
            let right = self.parse_logical_and()?;
            expr = Expr::BinaryLogical {
                operator: BinaryLogicalOperator::Or,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }
    fn parse_logical_and(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_equality()?;
        while let Some(token) = self.match_current(&vec![TokenType::And]) {
            let right = self.parse_equality()?;
            expr = Expr::BinaryLogical {
                operator: BinaryLogicalOperator::And,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_equality(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_comparison()?;
        while let Some(token) =
            self.match_current(&vec![TokenType::BangEqual, TokenType::EqualEqual])
        {
            let operator = token_to_binary(token);
            let right = self.parse_comparison()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }

        return Ok(expr);
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_term()?;
        while let Some(token) = self.match_current(&vec![
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let operator = token_to_binary(token);
            let right = self.parse_term()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_term(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_factor()?;
        while let Some(token) = self.match_current(&vec![TokenType::Plus, TokenType::Minus]) {
            let operator = token_to_binary(token);
            let right = self.parse_factor()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }
    fn parse_factor(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_unary()?;
        while let Some(token) = self.match_current(&vec![TokenType::Slash, TokenType::Star]) {
            let operator = token_to_binary(token);
            let right = self.parse_unary()?;
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, ParserError> {
        while let Some(token) = self.match_current(&vec![TokenType::Bang, TokenType::Minus]) {
            let operator = token_to_unary(token);
            let operand = self.parse_unary()?;
            return Ok(Expr::Unary {
                operator,
                expression: Box::new(operand),
            });
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<Expr, ParserError> {
        let token = self.advance();

        if token.is_none() {
            panic!("unfinished business?")
        }
        let token = token.unwrap();
        match token.r#type {
            TokenType::Identifier => Ok(Expr::Variable { name: token.lexeme }),
            TokenType::False => Ok(Expr::Literal(Literal::False)),
            TokenType::True => Ok(Expr::Literal(Literal::True)),
            TokenType::Nil => Ok(Expr::Literal(Literal::Nil)),
            TokenType::Number => Ok(Expr::Literal(Literal::Number(
                token.lexeme.parse().unwrap(),
            ))),
            // remove quotes from string
            TokenType::String => Ok(Expr::Literal(Literal::String(
                token.lexeme[1..token.lexeme.len() - 1].to_string(),
            ))),
            TokenType::LeftParen => {
                let expr = self.parse_expression()?;
                match self.match_current(&vec![TokenType::RightParen]) {
                    None => Err(ParserError::UnmatchedParenthesis { line: token.line }),
                    Some(_) => Ok(Expr::Grouping(Box::new(expr))),
                }
            }
            _ => Err(ParserError::UnexpectedToken {
                line: token.line,
                lexeme: if token.r#type == TokenType::EOF {
                    "End Of File".to_string()
                } else {
                    token.lexeme
                },
            }),
        }
    }

    /// a better api for this might be to return an Option<Token>
    fn match_current(&mut self, token_types: &Vec<TokenType>) -> Option<Token> {
        for token_type in token_types {
            let matched = self.tokens.next_if(|t| t.r#type == *token_type);
            if matched.is_some() {
                return matched;
            }
        }
        None
    }

    fn advance(&mut self) -> Option<Token> {
        let token = self.tokens.next();
        token
    }

    fn consume(&mut self, token_type: TokenType, err: ParserError) -> Result<(), ParserError> {
        match self.match_current(&vec![token_type]) {
            None => Err(err),
            Some(_) => Ok(()),
        }
    }

    #[allow(clippy::wrong_self_convention)]
    fn is_at_end(&mut self) -> bool {
        // we check two things. Does not feel clean.
        self.tokens.peek().is_none()
            || self
                .tokens
                .peek()
                .is_some_and(|t| t.r#type == TokenType::EOF)
    }

    /// 'synchronize' in the book. Not used yet.
    /// The idea is that when there's an error, we don't want to show many 'cascading errors'.
    /// So we use 'anchor points' in tokens where it's likely we are back to a clean state.
    fn recover(&mut self) {
        while let Some(token) = self.advance() {
            // I think there's something nice about having an explicit match statement here: if we
            // make additions to the language, it lets us know we need to consider what we want to
            // do with the new token type here.
            match token.r#type {
                TokenType::Semicolon => return,
                TokenType::Class => return,
                TokenType::Fun => return,
                TokenType::For => return,
                TokenType::If => return,
                TokenType::Print => return,
                TokenType::Return => return,
                TokenType::Var => return,
                TokenType::While => return,
                TokenType::LeftParen => {}
                TokenType::RightParen => {}
                TokenType::LeftBrace => {}
                TokenType::RightBrace => {}
                TokenType::Comma => {}
                TokenType::Dot => {}
                TokenType::Minus => {}
                TokenType::Plus => {}
                TokenType::Slash => {}
                TokenType::Star => {}
                TokenType::Bang => {}
                TokenType::BangEqual => {}
                TokenType::Equal => {}
                TokenType::EqualEqual => {}
                TokenType::Greater => {}
                TokenType::GreaterEqual => {}
                TokenType::Less => {}
                TokenType::LessEqual => {}
                TokenType::And => {}
                TokenType::Else => {}
                TokenType::False => {}
                TokenType::Nil => {}
                TokenType::Or => {}
                TokenType::Super => {}
                TokenType::This => {}
                TokenType::True => {}
                TokenType::Identifier => {}
                TokenType::String => {}
                TokenType::Number => {}
                TokenType::EOF => {}
            }
        }
    }
}

// TODO these conversion functions are okay... But not great.
// 1. we panic.
// 2. Nothing tells us if we forgot one operator. Ideally I'd like to know that all UnaryOperators/BinaryOperators can be produced by these functions.
fn token_to_unary(token: Token) -> UnaryOperator {
    match token.r#type {
        TokenType::Minus => UnaryOperator::Minus,
        TokenType::Bang => UnaryOperator::Not,
        _ => panic!("unable to parse token into unary operator: {:?}", token),
    }
}

fn token_to_binary(token: Token) -> BinaryOperator {
    match token.r#type {
        TokenType::Plus => BinaryOperator::Plus,
        TokenType::Minus => BinaryOperator::Minus,
        TokenType::Star => BinaryOperator::Multiply,
        TokenType::Slash => BinaryOperator::Divide,
        TokenType::EqualEqual => BinaryOperator::Eq,
        TokenType::BangEqual => BinaryOperator::Neq,
        TokenType::Greater => BinaryOperator::Gt,
        TokenType::GreaterEqual => BinaryOperator::Gte,
        TokenType::Less => BinaryOperator::Lt,
        TokenType::LessEqual => BinaryOperator::Lte,
        _ => panic!("unable to parse token into binary operator: {:?}", token),
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Literal::Number;
    use crate::ast::Statement::ExprStatement;
    use crate::ast::{
        format_lisp_like, BinaryLogicalOperator, BinaryOperator, Expr, Literal, Statement,
        UnaryOperator,
    };
    use crate::parser::{Parser, ParserError};
    use crate::test_helpers::{parse_expr, parse_program, parse_statement};
    use crate::token::{Token, TokenType};

    #[test]
    fn test_match_current() {
        let tokens = vec![Token {
            r#type: TokenType::Plus,
            lexeme: "+".to_string(),
            line: 1,
        }];
        let mut parser = Parser::new(tokens.into_iter());
        let matched = parser.match_current(&vec![TokenType::Plus]);
        assert!(matched.is_some());
        // cursor should have moved
        let matched_again = parser.match_current(&vec![TokenType::Plus]);
        assert!(matched_again.is_none());
    }

    #[test]
    fn test_binary_simple() {
        let expr = parse_expr("1 + 2").unwrap();
        assert_eq!(
            expr,
            Expr::Binary {
                operator: BinaryOperator::Plus,
                left: Box::new(Expr::Literal(Literal::Number(1.),)),
                right: Box::new(Expr::Literal(Literal::Number(2.),))
            }
        )
    }

    #[test]
    fn test_binary_logical() {
        let expr = parse_expr("1 or 2").unwrap();
        assert_eq!(
            expr,
            Expr::BinaryLogical {
                operator: BinaryLogicalOperator::Or,
                left: Box::new(Expr::Literal(Literal::Number(1.),)),
                right: Box::new(Expr::Literal(Literal::Number(2.),))
            }
        )
    }

    #[test]
    fn test_unary_simple() {
        let expr = parse_expr("-2").unwrap();
        assert_eq!(
            expr,
            Expr::Unary {
                operator: UnaryOperator::Minus,
                expression: Box::new(Expr::Literal(Literal::Number(2.)))
            }
        )
    }

    #[test]
    fn test_precedence() {
        let expr = parse_expr("3 + 2 * (-2 + 3) == 5").unwrap();

        // I'd use RPN but I don't understand it :)
        // "3 2 2 - 3 + * + 5 =="
        assert_eq!(
            format_lisp_like(&expr),
            "(== (+ 3 (* 2 (group (+ (- 2) 3)))) 5)"
        )
    }

    #[test]
    fn test_unmatched_parenthesis() {
        let expr = parse_expr("\n((1 + 2) / 1");
        assert!(expr.is_err());
        let err = expr.err().unwrap();
        assert_eq!(err, ParserError::UnmatchedParenthesis { line: 2 });
    }
    #[test]
    fn test_unfinished_expression() {
        let expr = parse_expr("1 + ");
        assert!(expr.is_err());
        let err = expr.err().unwrap();
        assert_eq!(
            err,
            ParserError::UnexpectedToken {
                line: 1,
                lexeme: "End Of File".to_string()
            }
        );
    }

    #[test]
    fn test_print_statement() {
        let statement = parse_statement("print 1;").unwrap();
        assert_eq!(
            statement,
            Statement::PrintStatement {
                expression: Expr::Literal(Number(1.))
            }
        )
    }

    #[test]
    fn test_statement_missing_semicolon() {
        [
            (
                "1 + 3",
                ParserError::MissingSemicolonExpressionStatement { line: 0 },
            ),
            (
                "print 1 + 3",
                ParserError::MissingSemicolonPrint { line: 0 },
            ),
        ]
        .into_iter()
        .for_each(|(code, expected_error)| {
            let err = parse_statement(code).unwrap_err();
            assert_eq!(err, expected_error);
        })
    }

    #[test]
    fn test_variable_declaration() {
        let parsed = parse_program("var a = 1;").unwrap();
        assert_eq!(parsed.len(), 1);
    }
    #[test]
    fn test_variable_declaration_no_initializer() {
        let parsed = parse_program("var a;").unwrap();
        assert_eq!(parsed.len(), 1);
    }
    #[test]
    fn test_variable_expression() {
        // this is valid at this stage, the parser allows undefined variables (interpreter would throw a runtime error)
        let parsed = parse_program("a + b == 3;").unwrap();
        assert_eq!(parsed.len(), 1);
    }
    #[test]
    fn test_variable_assignment() {
        let parsed = parse_program("a = 3;").unwrap();
        assert_eq!(parsed.len(), 1);
        assert_eq!(
            parsed[0],
            ExprStatement {
                expression: Expr::Assign {
                    value: Box::from(Expr::Literal(Number(3.))),
                    name: "a".to_string()
                }
            }
        );
    }

    #[test]
    fn test_program() {
        // let parsed = parse_program("print 2;").unwrap();
        let parsed = parse_program("// hello comment\nprint 1;\nprint 2;\n").unwrap();
        assert_eq!(parsed.len(), 2);
    }
}
