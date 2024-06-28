use crate::ast::{BinaryLogicalOperator, BinaryOperator, Expr, Literal, Statement, UnaryOperator};
use crate::environment::Environment;
use crate::interpreter::LoxValue::*;
use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;
use thiserror::Error;
use BinaryOperator::*;

type LoxEnvironment = Environment<LoxValue>;
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

/// this enum is an effort to keep functions pure (no actual printing) so we can test them.
/// I don't know whether extending it to variable assignment is a good idea. Seems like it might backfire.
#[derive(Debug, PartialEq)]
enum Command {
    Print { value: LoxValue },
}

// now I added a generic write type it's a mix of two patterns to achieve testability.
// I think only the write redirection will be useful. Messy :)
fn execute_command<W: Write>(command: Command, writer: &mut W) -> Result<(), std::io::Error> {
    match command {
        Command::Print { value } => writeln!(writer, "{:?}", value),
    }
}

pub fn interpret_program<W: Write>(
    program: &Vec<Statement>,
    writer: &mut W,
) -> Result<(), InterpreterError> {
    let environment = Rc::new(RefCell::new(LoxEnvironment::new(None)));
    interpret_program_with_env(program, writer, environment)
}

pub fn interpret_program_with_env<W: Write>(
    program: &Vec<Statement>,
    writer: &mut W,
    environment: Rc<RefCell<LoxEnvironment>>,
) -> Result<(), InterpreterError> {
    for statement in program {
        let commands = interpret_statement(statement, environment.clone())?;
        for c in commands {
            execute_command(c, writer).unwrap();
        }
    }
    Ok(())
}
fn interpret_statement(
    statement: &Statement,
    environment: Rc<RefCell<LoxEnvironment>>,
) -> Result<Vec<Command>, InterpreterError> {
    match statement {
        Statement::ExprStatement { expression } => {
            interpret_expression(expression, environment.clone())?;
            Ok(vec![])
        }
        Statement::PrintStatement { expression } => {
            let value = interpret_expression(expression, environment.clone())?;
            Ok(vec![Command::Print { value }])
        }
        Statement::VarDeclaration { name, initializer } => {
            environment.borrow_mut().define(
                name.clone(),
                interpret_expression(initializer, environment.clone())?,
            );
            Ok(vec![])
        }
        Statement::Block { statements } => {
            let mut child_env = LoxEnvironment::new(None);
            child_env.parent = Some(environment.clone());
            let child_env = Rc::new(RefCell::new(child_env));
            let mut commands = vec![];
            for statement in statements {
                commands.extend(interpret_statement(statement, child_env.clone())?);
            }
            Ok(commands)
        }
        Statement::IfStatement {
            condition,
            then_branch,
            else_branch,
        } => {
            let cond = interpret_expression(condition, environment.clone())?;
            if is_truthy(&cond) {
                return interpret_statement(then_branch, environment.clone());
            } else {
                if let Some(branch) = else_branch {
                    return interpret_statement(branch, environment.clone());
                }
                Ok(vec![])
            }
        }
        Statement::WhileStatement { condition, body } => {
            // it's weird to gather all commands before evaluating them... Creates a delay we don't really want!!
            let mut commands = vec![];
            while is_truthy(&interpret_expression(condition, environment.clone())?) {
                commands.extend(interpret_statement(body, environment.clone())?);
            }
            Ok(commands)
        }
        Statement::FunctionDeclaration { .. } => {
            todo!()
        }
    }
}

fn interpret_expression(
    expr: &Expr,
    environment: Rc<RefCell<LoxEnvironment>>,
) -> Result<LoxValue, InterpreterError> {
    match expr {
        Expr::Literal(literal) => Ok(interpret_literal(literal)),
        Expr::Unary {
            operator,
            expression,
        } => {
            let lox_operand = interpret_expression(expression, environment.clone())?;
            interpret_unary(operator, lox_operand)
        }
        Expr::Binary {
            operator,
            left,
            right,
        } => {
            let lox_left_value = interpret_expression(left, environment.clone())?;
            let lox_right_value = interpret_expression(right, environment.clone())?;
            interpret_binary(operator, lox_left_value, lox_right_value)
        }
        Expr::Grouping(grouped_expr) => interpret_expression(grouped_expr, environment.clone()),
        Expr::Variable { name } => Ok(environment.borrow().lookup(name.clone())),
        Expr::Assign { name, value } => {
            let left_hand_side = interpret_expression(value, environment.clone())?;
            environment
                .borrow_mut()
                .assign(name.clone(), left_hand_side.clone());
            // there's probably something wrong here about cloning if the value is mutable.
            Ok(left_hand_side)
        }
        Expr::BinaryLogical {
            operator: BinaryLogicalOperator::Or,
            left,
            right,
        } => {
            let lox_left_value = interpret_expression(left, environment.clone())?;
            if is_truthy(&lox_left_value) {
                return Ok(lox_left_value);
            }
            let lox_right_value = interpret_expression(right, environment.clone())?;
            return Ok(lox_right_value);
        }
        Expr::BinaryLogical {
            operator: BinaryLogicalOperator::And,
            left,
            right,
        } => {
            let lox_left_value = interpret_expression(left, environment.clone())?;
            if !is_truthy(&lox_left_value) {
                return Ok(lox_left_value);
            }
            let lox_right_value = interpret_expression(right, environment.clone())?;
            return Ok(lox_right_value);
        }
        Expr::FunctionCall { .. } => {
            todo!()
        }
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
        (UnaryOperator::Not, lox_value) => Ok(LBool(!is_truthy(&lox_value))),
        (_, operand) => Err(InterpreterError::UnaryOperationNotSupported {
            operator: *op,
            operand,
        }),
    }
}

fn is_truthy(v: &LoxValue) -> bool {
    match v {
        LNil => false,
        LBool(value) => *value,
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
    use crate::interpreter::{
        interpret_expression, interpret_program, interpret_statement, Command, InterpreterError,
        LoxEnvironment, LoxValue,
    };
    use crate::test_helpers::{parse_expr, parse_program, parse_statement};
    use std::cell::RefCell;
    use std::rc::Rc;

    ///assumes success
    fn get_lox_value(code: &str) -> LoxValue {
        let expr = parse_expr(code).expect("error in test setup");
        let env = LoxEnvironment::new(None);
        interpret_expression(&expr, Rc::new(RefCell::new(env))).unwrap()
    }

    fn get_lox_error(code: &str) -> InterpreterError {
        let expr = parse_expr(code).expect("error in test setup");
        let env = LoxEnvironment::new(None);
        let lox_value = interpret_expression(&expr, Rc::new(RefCell::new(env)));
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
    fn test_interpret_expression_logical_operations() {
        let lox_value = get_lox_value("nil or \"Hello\"");
        assert_eq!(lox_value, LoxValue::LString("Hello".to_string()));

        let lox_value = get_lox_value("\"Hello\" or 2");
        assert_eq!(lox_value, LoxValue::LString("Hello".to_string()));

        let lox_value = get_lox_value("\"Hello\" and 2");
        assert_eq!(lox_value, LoxValue::LNumber(2.));

        let lox_value = get_lox_value("false and 2");
        assert_eq!(lox_value, LoxValue::LBool(false));
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
    fn test_interpret_statement() {
        let statement = parse_statement("print \"Hello\";").expect("error in test setup");
        let env = LoxEnvironment::new(None);
        let commands = interpret_statement(&statement, Rc::new(RefCell::new(env))).unwrap();
        assert_eq!(
            commands,
            vec![Command::Print {
                value: LoxValue::LString("Hello".to_string())
            }]
        )
    }

    #[test]
    fn test_if_without_else() {
        let statement = parse_statement("if (1) print \"Hello\";").expect("error in test setup");
        let env = LoxEnvironment::new(None);
        let commands = interpret_statement(&statement, Rc::new(RefCell::new(env))).unwrap();
        assert_eq!(
            commands,
            vec![Command::Print {
                value: LoxValue::LString("Hello".to_string())
            }]
        )
    }
    #[test]
    fn test_if_with_else() {
        let statement =
            parse_statement("if (1) print \"Hello\"; else print \"should not be printed\";")
                .expect("error in test setup");
        let env = LoxEnvironment::new(None);
        let commands = interpret_statement(&statement, Rc::new(RefCell::new(env))).unwrap();
        assert_eq!(
            commands,
            vec![Command::Print {
                value: LoxValue::LString("Hello".to_string())
            }]
        )
    }

    #[test]
    fn test_interpret_variables() {
        let program = parse_program("var a = 1;\nprint a;").expect("error in test setup");
        let env = LoxEnvironment::new(None);
        let mut mock_writer: Vec<u8> = Vec::new();

        interpret_program(&program, &mut mock_writer).expect("error! test failed.");

        let written = String::from_utf8(mock_writer).unwrap();
        assert_eq!(written, format!("{:?}\n", LoxValue::LNumber(1.)));
    }
}
