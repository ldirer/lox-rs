use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq)]
pub enum Expr {
    Literal(Literal),
    Unary {
        operator: UnaryOperator,
        expression: Box<Expr>,
    },
    Binary {
        operator: BinaryOperator,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Grouping(Box<Expr>),
}
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum UnaryOperator {
    Minus,
    Not,
}
impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Minus => write!(f, "-"),
            UnaryOperator::Not => write!(f, "!"),
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum BinaryOperator {
    Plus,
    Minus,
    Multiply,
    Divide,
    Eq,
    Neq,
    Gt,
    Gte,
    Lt,
    Lte,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Plus => write!(f, "+"),
            BinaryOperator::Minus => write!(f, "-"),
            BinaryOperator::Multiply => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/"),
            BinaryOperator::Eq => write!(f, "=="),
            BinaryOperator::Neq => write!(f, "!="),
            BinaryOperator::Gt => write!(f, ">"),
            BinaryOperator::Gte => write!(f, ">="),
            BinaryOperator::Lt => write!(f, "<"),
            BinaryOperator::Lte => write!(f, "<="),
        }
    }
}
#[derive(Debug, PartialEq)]
pub enum Literal {
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Number(n) => write!(f, "{n}"),
            Literal::String(s) => write!(f, "{s}"),
            Literal::True => write!(f, "true"),
            Literal::False => write!(f, "false"),
            Literal::Nil => write!(f, "nil"),
        }
    }
}

pub fn format_lisp_like(expr: &Expr) -> String {
    match expr {
        Expr::Literal(ref literal) => {
            format!("{}", literal)
        }
        Expr::Unary {
            expression,
            ref operator,
        } => {
            format!("({} {})", operator, format_lisp_like(expression))
        }
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            format!(
                "({} {} {})",
                operator,
                format_lisp_like(left),
                format_lisp_like(right)
            )
        }
        Expr::Grouping(expr) => {
            format!("(group {})", format_lisp_like(expr))
        }
    }
}

pub fn format_reverse_polish_notation(expr: &Expr) -> String {
    match expr {
        Expr::Literal(ref lit) => {
            format!("{}", lit)
        }
        Expr::Unary {
            expression,
            ref operator,
        } => {
            format!(
                "{} {}",
                format_reverse_polish_notation(expression),
                operator,
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
                operator,
            )
        }
        Expr::Grouping(expr) => {
            format!("{}", format_reverse_polish_notation(expr))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Literal::Number;
    use crate::ast::{
        format_lisp_like, format_reverse_polish_notation, BinaryOperator, Expr, UnaryOperator,
    };

    fn get_test_expr() -> Expr {
        // Expression used in the chapter 5 of the book: -123 * (45.67)
        // let tokens = tokenize("-123 * (45.67)".to_string(), |err| panic!("{}", err));
        // println!("{tokens:#?}");
        Expr::Binary {
            operator: BinaryOperator::Multiply,
            left: Box::new(Expr::Unary {
                expression: Box::new(Expr::Literal(Number(123.0))),
                operator: UnaryOperator::Minus,
            }),
            right: Box::new(Expr::Grouping(Box::new(Expr::Literal(Number(45.67))))),
        }
    }

    fn build_binary(operator: BinaryOperator, a: f64, b: f64) -> Expr {
        return Expr::Binary {
            operator,
            left: Box::new(Expr::Literal(Number(a))),
            right: Box::new(Expr::Literal(Number(b))),
        };
    }

    /// tedious to write fixtures like this...
    fn get_test_expr_reverse_polish_notation() -> Expr {
        let left = build_binary(BinaryOperator::Plus, 1., 2.);
        let right = build_binary(BinaryOperator::Minus, 4., 3.);
        return Expr::Binary {
            operator: BinaryOperator::Multiply,
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
