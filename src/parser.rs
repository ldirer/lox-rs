use crate::ast::{BinaryOperator, Expr, Literal, UnaryOperator};
use crate::token::{Token, TokenType};
use std::iter::Peekable;
use thiserror::Error;

#[derive(Debug, Error)]
enum ParserError {}
struct Parser<T: Iterator<Item = Token>> {
    tokens: Peekable<T>,
    current: usize,
    previous: Option<Token>,
}

fn parse<T>(tokens: T) -> Result<Expr, ParserError>
where
    T: Iterator<Item = Token>,
{
    let mut parser = Parser::new(tokens);
    Ok(parser.expression())
}

impl<T: Iterator<Item = Token>> Parser<T> {
    fn new(tokens: T) -> Self {
        let tokens = tokens.peekable();
        Parser {
            tokens,
            current: 0,
            previous: None,
        }
    }

    fn expression(&mut self) -> Expr {
        self.equality()
    }
    fn equality(&mut self) -> Expr {
        let mut expr = self.comparison();
        while self.match_current(&vec![TokenType::BangEqual, TokenType::EqualEqual]) {
            let token = self.previous();
            let operator = token_to_binary(token);
            let right = self.comparison();
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }

        return expr;
    }

    /// a better api for this might be to return an Option<Token>
    fn match_current(&mut self, token_types: &Vec<TokenType>) -> bool {
        for token_type in token_types {
            let matched = self.tokens.next_if(|t| t.r#type == *token_type);
            if let Some(token) = matched {
                self.previous = Some(token);
                return true;
            }
        }
        false
    }
    fn previous(&mut self) -> Token {
        // TODO unwrap. Any way around it?
        self.previous.clone().unwrap()
    }

    fn comparison(&mut self) -> Expr {
        let mut expr = self.term();
        while self.match_current(&vec![
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let token = self.previous();
            let operator = token_to_binary(token);
            let right = self.term();
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        expr
    }

    fn term(&mut self) -> Expr {
        let mut expr = self.factor();
        while self.match_current(&vec![TokenType::Plus, TokenType::Minus]) {
            let token = self.previous();
            let operator = token_to_binary(token);
            let right = self.factor();
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        expr
    }
    fn factor(&mut self) -> Expr {
        let mut expr = self.unary();
        while self.match_current(&vec![TokenType::Slash, TokenType::Star]) {
            let token = self.previous();
            let operator = token_to_binary(token);
            let right = self.unary();
            expr = Expr::Binary {
                operator,
                left: Box::new(expr),
                right: Box::new(right),
            };
        }
        expr
    }

    fn unary(&mut self) -> Expr {
        while self.match_current(&vec![TokenType::Bang, TokenType::Minus]) {
            let token = self.previous();
            let operator = token_to_unary(token);
            let operand = self.unary();
            return Expr::Unary {
                operator,
                expression: Box::new(operand),
            };
        }
        self.primary()
    }

    fn primary(&mut self) -> Expr {
        // TODO not great to hand-manage next and previous here I think
        let token = self.tokens.next();
        self.previous = token.clone();

        if token.is_none() {
            panic!("unfinished business?")
        }
        let token = token.unwrap();
        match token.r#type {
            TokenType::False => Expr::Literal(Literal::False),
            TokenType::True => Expr::Literal(Literal::True),
            TokenType::Nil => Expr::Literal(Literal::Nil),
            TokenType::Number(value) => Expr::Literal(Literal::Number(value)),
            TokenType::String(value) => Expr::Literal(Literal::String(value)),
            TokenType::LeftParen => {
                let expr = self.expression();
                self.consume(TokenType::RightParen)
                    .expect("Expect ')' after expression.");
                Expr::Grouping(Box::new(expr))
            }
            _ => {
                panic!("unexpected token {token:?}");
            }
        }
    }

    fn consume(&mut self, token_type: TokenType) -> Option<Token> {
        let matched = self.tokens.next_if(|t| t.r#type == token_type);
        self.previous = matched.clone();
        matched
    }

    fn peek(&mut self) -> Option<&Token> {
        self.tokens.peek()
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
    use crate::ast::{
        format_lisp_like, format_reverse_polish_notation, BinaryOperator, Expr, Literal,
        UnaryOperator,
    };
    use crate::parser::{parse, Parser};
    use crate::scanner::tokenize;
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
        assert!(matched);
        // cursor should have moved
        let matched_again = parser.match_current(&vec![TokenType::Plus]);
        assert!(!matched_again);
    }

    #[test]
    fn test_binary_simple() {
        let tokens = tokenize("1 + 2".to_string(), |error| panic!("{}", error));
        println!("tokens: {tokens:#?}");
        let expr = parse(tokens.into_iter()).unwrap();
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
        let tokens = tokenize("-2".to_string(), |error| panic!("{}", error));
        let expr = parse(tokens.into_iter()).unwrap();
        assert_eq!(
            expr,
            Expr::Unary {
                operator: UnaryOperator::Minus,
                expression: Box::new(Expr::Literal(Literal::Number(2.)))
            }
        )
    }

    #[test]
    fn test_precedence_1() {
        let tokens = tokenize("3 + 2 * (-2 + 3) == 5".to_string(), |error| {
            panic!("{}", error)
        });
        let expr = parse(tokens.into_iter()).unwrap();

        // I'd use RPN but I don't understand it :)
        // "3 2 2 - 3 + * + 5 =="
        assert_eq!(
            format_lisp_like(&expr),
            "(== (+ 3 (* 2 (group (+ (- 2) 3)))) 5)"
        )
    }
}
