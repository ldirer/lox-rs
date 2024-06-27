use std::iter::Peekable;

use thiserror::Error;

use crate::ast::{BinaryOperator, Expr, Literal, Statement, UnaryOperator};
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
    fn parse_program(&mut self) -> Result<Vec<Statement>, ParserError> {
        let mut statements: Vec<Statement> = vec![];
        while !self.is_at_end() {
            statements.push(self.parse_statement()?);
        }
        Ok(statements)
    }

    pub(crate) fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        match self.match_current(&vec![TokenType::Print]) {
            Some(_) => self.parse_print_statement(),
            None => self.parse_expression_statement(),
        }
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
        self.parse_equality()
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
            TokenType::False => Ok(Expr::Literal(Literal::False)),
            TokenType::True => Ok(Expr::Literal(Literal::True)),
            TokenType::Nil => Ok(Expr::Literal(Literal::Nil)),
            TokenType::Number(value) => Ok(Expr::Literal(Literal::Number(value))),
            TokenType::String(value) => Ok(Expr::Literal(Literal::String(value))),
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

    #[allow(clippy::wrong_self_convention)]
    fn is_at_end(&mut self) -> bool {
        self.tokens.peek().is_none()
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
                TokenType::Identifier(_) => {}
                TokenType::String(_) => {}
                TokenType::Number(_) => {}
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
    use crate::ast::{format_lisp_like, BinaryOperator, Expr, Literal, Statement, UnaryOperator};
    use crate::parser::{Parser, ParserError};
    use crate::test_helpers::{parse_expr, parse_statement};
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
}
