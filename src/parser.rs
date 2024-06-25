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

fn pretty_print_lisp_like(expr: &Expr) -> String {
    match expr {
        Expr::Literal(ref token) => {
            format!("{}", token.lexeme)
        }
        Expr::Unary {
            expression,
            ref operator,
        } => {
            format!(
                "({} {})",
                operator.lexeme,
                pretty_print_lisp_like(expression)
            )
        }
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            format!(
                "({} {} {})",
                operator.lexeme,
                pretty_print_lisp_like(left),
                pretty_print_lisp_like(right)
            )
        }
        Expr::Grouping(expr) => {
            format!("(group {})", pretty_print_lisp_like(expr))
        }
    }
}

fn parse(tokens: Box<dyn Iterator<Item = Token>>) {
    for token in tokens {}
}

#[cfg(test)]
mod tests {
    use crate::parser::{pretty_print_lisp_like, Expr};
    use crate::scanner::tokenize;
    use crate::token::{Token, TokenType};

    #[test]
    fn test_print_expression_lisp_like() {
        let tokens = tokenize("-123 * (45.67)".to_string(), |err| panic!("{}", err));
        println!("{tokens:#?}");
        let expr = Expr::Binary {
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
        };
        assert_eq!(
            pretty_print_lisp_like(&expr),
            "(* (- 123) (group 45.67))".to_string()
        );
    }
}
