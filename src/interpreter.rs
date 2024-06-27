use crate::ast::{BinaryOperator, Expr, Literal, Statement, UnaryOperator};
use crate::interpreter::LoxValue::*;
use std::io::Write;
use thiserror::Error;
use BinaryOperator::*;

#[derive(Debug, PartialEq, Error)]
pub enum InterpreterError {
    // TODO having dedicated types for the AST was nice, but line numbers in errors are even nicer.
    // need to get them somehow.
    #[error("operation {operator} not supported between {left:?} and {right:?}")]
    BinaryOperationNotSupported {
        operator: BinaryOperator,
        left: LoxValue,
        right: LoxValue,
    },
    #[error("operation {operator} not supported on {operand:?}")]
    UnaryOperationNotSupported {
        operator: UnaryOperator,
        operand: LoxValue,
    },
}

#[derive(Debug, PartialEq, Clone)]
enum LoxValue {
    LString(String),
    LNumber(f64),
    LBool(bool),
    LNil,
}

enum Command {
    Print { value: LoxValue },
}

pub fn interpret_program(program: &Vec<Statement>) -> Result<(), InterpreterError> {
    for statement in program {
        let command = interpret_statement(statement)?;
        if let Some(c) = command {
            execute_command(c);
        }
    }
    Ok(())
}

fn execute_command(command: Command) {
    match command {
        Command::Print { value } => println!("{:?}", value),
    }
}

fn interpret_statement(statement: &Statement) -> Result<Option<Command>, InterpreterError> {
    match statement {
        Statement::ExprStatement { expression } => {
            interpret_expression(expression)?;
            Ok(None)
        }
        Statement::PrintStatement { expression } => {
            let value = interpret_expression(expression)?;
            Ok(Some(Command::Print { value }))
        }
    }
}

fn interpret_expression(expr: &Expr) -> Result<LoxValue, InterpreterError> {
    match expr {
        Expr::Literal(literal) => Ok(interpret_literal(literal)),
        Expr::Unary {
            operator,
            expression,
        } => {
            let lox_operand = interpret_expression(expression)?;
            interpret_unary(operator, lox_operand)
        }
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            let lox_left_value = interpret_expression(left)?;
            let lox_right_value = interpret_expression(right)?;
            interpret_binary(operator, lox_left_value, lox_right_value)
        }
        Expr::Grouping(grouped_expr) => interpret_expression(grouped_expr),
    }
}

fn interpret_binary(
    op: &BinaryOperator,
    lox_left: LoxValue,
    lox_right: LoxValue,
) -> Result<LoxValue, InterpreterError> {
    match (lox_left, op, lox_right) {
        (LNumber(left), Plus, LNumber(right)) => Ok(LNumber(left + right)),
        (LNumber(left), Minus, LNumber(right)) => Ok(LNumber(left - right)),
        (LNumber(left), Multiply, LNumber(right)) => Ok(LNumber(left * right)),
        (LNumber(left), Divide, LNumber(right)) => Ok(LNumber(left / right)),
        (LNumber(left), Gt, LNumber(right)) => Ok(LBool(left > right)),
        (LNumber(left), Gte, LNumber(right)) => Ok(LBool(left >= right)),
        (LNumber(left), Lt, LNumber(right)) => Ok(LBool(left < right)),
        (LNumber(left), Lte, LNumber(right)) => Ok(LBool(left <= right)),
        (LString(left), Plus, LString(right)) => Ok(LString(format!("{left}{right}"))),

        (lox_left, Eq, lox_right) => Ok(LBool(is_equal(lox_left, lox_right))),
        (lox_left, Neq, lox_right) => Ok(LBool(!is_equal(lox_left, lox_right))),

        (a, _, b) => Err(InterpreterError::BinaryOperationNotSupported {
            operator: *op,
            left: a,
            right: b,
        }),
    }
}

fn is_equal(left: LoxValue, right: LoxValue) -> bool {
    match (left, right) {
        (LNil, LNil) => true,
        (LBool(l), LBool(r)) => l == r,
        (LNumber(l), LNumber(r)) => l == r,
        (LString(l), LString(r)) => l == r,
        (_, _) => false,
    }
}

fn interpret_unary(op: &UnaryOperator, operand: LoxValue) -> Result<LoxValue, InterpreterError> {
    match (op, operand) {
        (UnaryOperator::Minus, LNumber(num)) => Ok(LNumber(-num)),
        (UnaryOperator::Not, lox_value) => Ok(LBool(!truthy(lox_value))),
        (_, operand) => Err(InterpreterError::UnaryOperationNotSupported {
            operator: *op,
            operand,
        }),
    }
}

fn truthy(v: LoxValue) -> bool {
    match v {
        LNil => false,
        LBool(value) => value,
        _ => true,
    }
}

fn interpret_literal(literal: &Literal) -> LoxValue {
    match literal {
        Literal::Number(num) => LNumber(*num),
        Literal::String(s) => LString(s.clone()),
        Literal::True => LBool(true),
        Literal::False => LBool(false),
        Literal::Nil => LNil,
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::BinaryOperator::Plus;
    use crate::interpreter::{interpret_expression, InterpreterError, LoxValue};
    use crate::test_helpers::{parse_expr, parse_statement};

    ///assumes success
    fn get_lox_value(code: &str) -> LoxValue {
        let expr = parse_expr(code).expect("error in test setup");
        interpret_expression(&expr).unwrap()
    }

    fn get_lox_error(code: &str) -> InterpreterError {
        let expr = parse_expr(code).expect("error in test setup");
        let lox_value = interpret_expression(&expr);
        assert!(lox_value.is_err());
        lox_value.err().unwrap()
    }

    #[test]
    fn test_interpret_expression_simple() {
        let lox_value = get_lox_value("1 + 1");
        assert_eq!(lox_value, LoxValue::LNumber(2.0))
    }
    #[test]
    fn test_interpret_expression_unary() {
        let lox_value = get_lox_value("3 * -1");
        assert_eq!(lox_value, LoxValue::LNumber(-3.0))
    }

    #[test]
    fn test_unary_not() {
        let input_and_expected: Vec<(&str, LoxValue)> = vec![
            ("!true", LoxValue::LBool(false)),
            ("!false", LoxValue::LBool(true)),
            ("!4", LoxValue::LBool(false)),
            ("!nil", LoxValue::LBool(true)),
            ("!!nil", LoxValue::LBool(false)),
            ("!\"abc\"", LoxValue::LBool(false)),
        ];
        input_and_expected.into_iter().for_each(|(code, expected)| {
            dbg!(code, &expected);
            assert_eq!(get_lox_value(code), expected)
        })
    }

    #[test]
    fn test_comparison() {
        let input_and_expected: Vec<(&str, LoxValue)> = vec![
            ("true == true", LoxValue::LBool(true)),
            ("true == \"ok\"", LoxValue::LBool(false)),
            ("3 != \"ok\"", LoxValue::LBool(true)),
            ("nil == false", LoxValue::LBool(false)),
            ("nil == nil", LoxValue::LBool(true)),
            ("3 == 3.", LoxValue::LBool(true)),
            ("3 == 4.", LoxValue::LBool(false)),
        ];
        input_and_expected.into_iter().for_each(|(code, expected)| {
            dbg!(code, &expected);
            assert_eq!(get_lox_value(code), expected)
        })
    }

    #[test]
    fn test_interpret_expression_groups() {
        let lox_value = get_lox_value("(1 + 2) * (4 - 2)");
        assert_eq!(lox_value, LoxValue::LNumber(6.0))
    }
    #[test]
    fn test_interpret_expression_string_concatenation() {
        let lox_value = get_lox_value("\"Hello\" + \", \" + \"World!\"");
        assert_eq!(lox_value, LoxValue::LString("Hello, World!".to_string()))
    }
    #[test]
    fn test_interpret_expression_invalid_operation() {
        let lox_error = get_lox_error("true + 1");
        assert_eq!(
            lox_error,
            InterpreterError::BinaryOperationNotSupported {
                operator: Plus,
                left: LoxValue::LBool(true),
                right: LoxValue::LNumber(1.)
            }
        );
    }

    #[test]
    fn test_interpret_statement() {}
}
