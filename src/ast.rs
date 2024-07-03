use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    IfStatement {
        condition: Expr,
        then_branch: Box<Statement>,
        else_branch: Option<Box<Statement>>,
    },
    WhileStatement {
        condition: Expr,
        body: Box<Statement>,
    },
    VarDeclaration {
        name: String,
        initializer: Expr,
        line: usize,
    },
    ClassDeclaration {
        name: String,
        // methods should contain only FunctionDeclaration objects
        methods: Vec<Statement>,
        line: usize,
    },
    FunctionDeclaration {
        name: String,
        parameters: Vec<String>,
        body: Vec<Statement>,
        line: usize,
    },
    ReturnStatement {
        expression: Expr,
    },
    Block {
        statements: Vec<Statement>,
    },
    ExprStatement {
        expression: Expr,
    },
    // reminder that this is a statement (and not a library function) so that we can get some lox
    // code running before our interpreter handles functions (comes later in the book).
    PrintStatement {
        expression: Expr,
    },
}
#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Set {
        object: Box<Expr>,
        name: String,
        value: Box<Expr>,
        line: usize,
    },
    Assign {
        location: Box<Expr>,
        value: Box<Expr>,
    },
    BinaryLogical {
        operator: BinaryLogicalOperator,
        left: Box<Expr>,
        right: Box<Expr>,
    },
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
    Variable {
        // depth is ignored by the parser and populated later by the resolver
        depth: Option<usize>,
        line: usize,
        name: String,
    },
    FunctionCall {
        line: usize,
        callee: Box<Expr>,
        arguments: Vec<Expr>,
    },
    PropertyAccess {
        object: Box<Expr>,
        name: String,
        line: usize,
    },
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub struct UnaryOperator {
    pub(crate) type_: UnaryOperatorType,
    pub(crate) line: usize,
}
impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.type_)
    }
}
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum UnaryOperatorType {
    Minus,
    Not,
}
impl Display for UnaryOperatorType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperatorType::Minus => write!(f, "-"),
            UnaryOperatorType::Not => write!(f, "!"),
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub struct BinaryLogicalOperator {
    pub(crate) type_: BinaryLogicalOperatorType,
    pub(crate) line: usize,
}
impl Display for crate::ast::BinaryLogicalOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.type_)
    }
}
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum BinaryLogicalOperatorType {
    Or,
    And,
}
impl Display for BinaryLogicalOperatorType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryLogicalOperatorType::Or => write!(f, "or"),
            BinaryLogicalOperatorType::And => write!(f, "and"),
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub struct BinaryOperator {
    pub(crate) type_: BinaryOperatorType,
    pub(crate) line: usize,
}
impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.type_)
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum BinaryOperatorType {
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

impl Display for BinaryOperatorType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperatorType::Plus => write!(f, "+"),
            BinaryOperatorType::Minus => write!(f, "-"),
            BinaryOperatorType::Multiply => write!(f, "*"),
            BinaryOperatorType::Divide => write!(f, "/"),
            BinaryOperatorType::Eq => write!(f, "=="),
            BinaryOperatorType::Neq => write!(f, "!="),
            BinaryOperatorType::Gt => write!(f, ">"),
            BinaryOperatorType::Gte => write!(f, ">="),
            BinaryOperatorType::Lt => write!(f, "<"),
            BinaryOperatorType::Lte => write!(f, "<="),
        }
    }
}
#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum FunctionType {
    Function,
    Method,
}

impl Display for FunctionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionType::Function => write!(f, "function"),
            FunctionType::Method => write!(f, "method"),
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
        Expr::Variable { name, .. } => {
            format!("{name}")
        }
        Expr::Assign { .. } => {
            panic!("Assign not supported")
        }
        Expr::BinaryLogical {
            operator,
            left,
            right,
        } => format!(
            "({} {} {})",
            operator,
            format_reverse_polish_notation(left),
            format_reverse_polish_notation(right),
        ),
        // tired of having to come here and change this code that I don't use much, so adding a default case.
        _ => {
            panic!("not supported {expr:?}")
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
        Expr::BinaryLogical {
            operator,
            left,
            right,
        } => format!(
            "{} {} {}",
            format_reverse_polish_notation(left),
            format_reverse_polish_notation(right),
            operator
        ),
        Expr::Grouping(expr) => {
            format!("{}", format_reverse_polish_notation(expr))
        }
        Expr::Variable { name, .. } => {
            format!("{}", name)
        }
        Expr::Assign { .. } => {
            panic!("Assign not supported")
        }
        _ => {
            panic!("not supported {expr:?}")
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Literal::Number;
    use crate::ast::{
        format_lisp_like, format_reverse_polish_notation, BinaryOperator, BinaryOperatorType, Expr,
        UnaryOperator, UnaryOperatorType,
    };

    fn get_test_expr() -> Expr {
        // Expression used in the chapter 5 of the book: -123 * (45.67)
        // let tokens = tokenize("-123 * (45.67)".to_string(), |err| panic!("{}", err));
        // println!("{tokens:#?}");
        Expr::Binary {
            operator: BinaryOperator {
                type_: BinaryOperatorType::Multiply,
                line: 1,
            },
            left: Box::new(Expr::Unary {
                expression: Box::new(Expr::Literal(Number(123.0))),
                operator: UnaryOperator {
                    type_: UnaryOperatorType::Minus,
                    line: 1,
                },
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
        let left = build_binary(
            BinaryOperator {
                type_: BinaryOperatorType::Plus,
                line: 1,
            },
            1.,
            2.,
        );
        let right = build_binary(
            BinaryOperator {
                type_: BinaryOperatorType::Minus,
                line: 1,
            },
            4.,
            3.,
        );
        return Expr::Binary {
            operator: BinaryOperator {
                type_: BinaryOperatorType::Multiply,
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
