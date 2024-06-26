use crate::token::{Token, TokenType};
use std::iter::Peekable;
use thiserror::Error;

#[derive(Debug, PartialEq)]
enum Expr {
    Literal(Token),
    Unary {
        operator: Token,
        expression: Box<Expr>,
    },
    Binary {
        operator: Token,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Grouping(Box<Expr>),
}

fn format_lisp_like(expr: &Expr) -> String {
    match expr {
        Expr::Literal(ref token) => {
            format!("{}", token.lexeme)
        }
        Expr::Unary {
            expression,
            ref operator,
        } => {
            format!("({} {})", operator.lexeme, format_lisp_like(expression))
        }
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            format!(
                "({} {} {})",
                operator.lexeme,
                format_lisp_like(left),
                format_lisp_like(right)
            )
        }
        Expr::Grouping(expr) => {
            format!("(group {})", format_lisp_like(expr))
        }
    }
}

fn format_reverse_polish_notation(expr: &Expr) -> String {
    match expr {
        Expr::Literal(ref token) => {
            format!("{}", token.lexeme)
        }
        Expr::Unary {
            expression,
            ref operator,
        } => {
            format!(
                "{} {}",
                format_reverse_polish_notation(expression),
                operator.lexeme,
            )
        }
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            format!(
                "{} {} {}",
                format_reverse_polish_notation(left),
                format_reverse_polish_notation(right),
                operator.lexeme,
            )
        }
        Expr::Grouping(expr) => {
            format!("{}", format_reverse_polish_notation(expr))
        }
    }
}

#[derive(Debug, Error)]
enum ParserError {}
struct Parser {
    tokens: Peekable<Box<dyn Iterator<Item = Token>>>,
    current: usize,
    previous: Option<Token>,
}

fn parse(tokens: Box<dyn Iterator<Item = Token>>) -> Result<Expr, ParserError> {
    let tokens = tokens.peekable();
    // for token in tokens {}
    let mut parser = Parser {
        tokens,
        current: 0,
        previous: None,
    };
    Ok(parser.expression())
}

impl Parser {
    fn equality(&mut self) -> Expr {
        let mut expr = self.comparison();
        while self.match_current(&vec![TokenType::BangEqual, TokenType::EqualEqual]) {
            let operator: Token = self.previous();
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
            let operator: Token = self.previous();
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
            let operator: Token = self.previous();
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
            let operator: Token = self.previous();
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
            let operator: Token = self.previous();
            let operand = self.unary();
            return Expr::Unary {
                operator,
                expression: Box::new(operand),
            };
        }
        self.primary()
    }

    fn primary(&mut self) -> Expr {
        let token = self.peek();
        if token.is_none() {
            panic!("unfinished business?")
        }
        let token = token.unwrap();
        match token {
            // deviating from the book: I'm storing a token in Expr::Literal. the book uses a value (false, true, null...) and discards the rest of the token information.
            // I guess that makes sense... But that's not what we do with other expressions? I don't know, will see later maybe.
            Token {
                r#type:
                    TokenType::False
                    | TokenType::True
                    | TokenType::Nil
                    | TokenType::Number(_)
                    | TokenType::String(_),
                ..
            } => Expr::Literal(token.clone()),
            Token {
                r#type: TokenType::LeftParen,
                ..
            } => {
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
        self.tokens.next_if(|t| t.r#type == token_type)
    }

    fn expression(&mut self) -> Expr {
        self.equality()
    }

    fn peek(&mut self) -> Option<&Token> {
        self.tokens.peek()
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{format_lisp_like, format_reverse_polish_notation, Expr};
    use crate::token::{Token, TokenType};

    fn get_test_expr() -> Expr {
        // Expression used in the chapter 5 of the book: -123 * (45.67)
        // let tokens = tokenize("-123 * (45.67)".to_string(), |err| panic!("{}", err));
        // println!("{tokens:#?}");
        Expr::Binary {
            operator: Token {
                r#type: TokenType::Star,
                lexeme: "*".to_string(),
                line: 1,
            },
            left: Box::new(Expr::Unary {
                expression: Box::new(Expr::Literal(Token {
                    r#type: TokenType::Number(123.0),
                    lexeme: "123".to_string(),
                    line: 1,
                })),
                operator: Token {
                    r#type: TokenType::Minus,
                    lexeme: "-".to_string(),
                    line: 1,
                },
            }),
            right: Box::new(Expr::Grouping(Box::new(Expr::Literal(Token {
                r#type: TokenType::Number(45.67),
                lexeme: "45.67".to_string(),
                line: 1,
            })))),
        }
    }

    fn build_binary(operator: Token, a: f64, b: f64) -> Expr {
        return Expr::Binary {
            operator,
            left: Box::new(Expr::Literal(Token {
                r#type: TokenType::Number(a),
                lexeme: a.to_string(),
                line: 1,
            })),
            right: Box::new(Expr::Literal(Token {
                r#type: TokenType::Number(b),
                lexeme: b.to_string(),
                line: 1,
            })),
        };
    }

    /// tedious to write fixtures like this...
    fn get_test_expr_reverse_polish_notation() -> Expr {
        let left = build_binary(
            Token {
                r#type: TokenType::Plus,
                lexeme: "+".to_string(),
                line: 1,
            },
            1.,
            2.,
        );
        let right = build_binary(
            Token {
                r#type: TokenType::Minus,
                lexeme: "-".to_string(),
                line: 1,
            },
            4.,
            3.,
        );
        return Expr::Binary {
            operator: Token {
                r#type: TokenType::Star,
                lexeme: "*".to_string(),
                line: 1,
            },
            left: Box::new(Expr::Grouping(Box::new(left))),
            right: Box::new(Expr::Grouping(Box::new(right))),
        };
    }

    #[test]
    fn test_format_expression_lisp_like() {
        let expr = get_test_expr();
        assert_eq!(
            format_lisp_like(&expr),
            "(* (- 123) (group 45.67))".to_string()
        );
    }
    #[test]
    fn test_format_expression_reverse_polish_notation_1() {
        let expr = get_test_expr();
        assert_eq!(
            format_reverse_polish_notation(&expr),
            "123 - 45.67 *".to_string()
        );
    }
    #[test]
    fn test_format_expression_reverse_polish_notation_2() {
        let expr = get_test_expr_reverse_polish_notation();
        assert_eq!(
            format_reverse_polish_notation(&expr),
            "1 2 + 4 3 - *".to_string()
        );
    }
}
