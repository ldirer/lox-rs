use crate::token::Token;

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

fn parse(tokens: Box<dyn Iterator<Item = Token>>) {
    for token in tokens {}
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
