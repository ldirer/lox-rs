use std::cell::RefCell;
use std::fmt::{Debug, Display, Formatter, Pointer};
use std::io::Write;
use std::iter::zip;
use std::rc::Rc;

use thiserror::Error;

use BinaryOperator::*;

use crate::ast::{BinaryLogicalOperator, BinaryOperator, Expr, Literal, Statement, UnaryOperator};
use crate::environment::Environment;
use crate::interpreter::LoxValue::*;

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
    LFunc(LoxFunction),
    LString(String),
    LNumber(f64),
    LBool(bool),
    LNil,
}

impl Display for LoxValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LFunc(func) => write!(f, "fun {}\n", func.name),
            LString(s) => write!(f, "{}", s),
            LNumber(n) => write!(f, "{}", n),
            LBool(b) => write!(f, "{}", b),
            LNil => write!(f, "nil"),
        }
    }
}

#[derive(Clone)]
struct LoxFunction {
    name: String,
    parameters: Vec<String>,
    body: Vec<Statement>,
    environment: Rc<RefCell<LoxEnvironment>>,
}

impl Debug for LoxFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LoxFunction")
            .field("name", &self.name)
            .field("parameters", &self.parameters)
            .field("body", &self.body)
            .finish()
    }
}

/// For testing convenience. Because LoxFunction is used in an enum for which I want PartialEq.
impl PartialEq for LoxFunction {
    fn eq(&self, other: &LoxFunction) -> bool {
        self.name == other.name && self.parameters == other.parameters && self.body == other.body
    }
}

pub struct Interpreter<W: Write> {
    // having this means our interpreter has to be mutable. This is a bit unfortunate.
    // maybe putting this in a `Cell` would allow 'hiding' the mutability.
    writer: W,
}

impl<W: Write> Interpreter<W> {
    pub(crate) fn new(writer: W) -> Interpreter<W> {
        Interpreter { writer }
    }
}

impl<W: Write> Interpreter<W> {
    pub fn interpret_program(&mut self, program: &Vec<Statement>) -> Result<(), InterpreterError> {
        let environment = Rc::new(RefCell::new(LoxEnvironment::new(None)));
        self.interpret_program_with_env(program, environment)
    }

    pub fn interpret_program_with_env(
        &mut self,
        program: &Vec<Statement>,
        environment: Rc<RefCell<LoxEnvironment>>,
    ) -> Result<(), InterpreterError> {
        for statement in program {
            self.interpret_statement(statement, environment.clone())?;
        }
        Ok(())
    }

    /// Ok(Some(value)) signals the return of a function, so we know to stop executing the current
    /// function body.
    fn interpret_statement(
        &mut self,
        statement: &Statement,
        environment: Rc<RefCell<LoxEnvironment>>,
    ) -> Result<Option<LoxValue>, InterpreterError> {
        match statement {
            Statement::ExprStatement { expression } => {
                self.interpret_expression(expression, environment.clone())?;
                Ok(None)
            }
            Statement::PrintStatement { expression } => {
                let value = self.interpret_expression(expression, environment.clone())?;
                writeln!(self.writer, "{}", value).unwrap();
                Ok(None)
            }
            Statement::VarDeclaration { name, initializer } => {
                let value = self.interpret_expression(initializer, environment.clone())?;
                environment.borrow_mut().define(name.clone(), value);
                Ok(None)
            }
            Statement::Block { statements } => {
                let mut child_env = LoxEnvironment::new(None);
                child_env.parent = Some(environment.clone());
                let child_env = Rc::new(RefCell::new(child_env));
                for statement in statements {
                    let return_value = self.interpret_statement(statement, child_env.clone())?;
                    if !return_value.is_none() {
                        return Ok(return_value);
                    }
                }
                Ok(None)
            }
            Statement::IfStatement {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond = self.interpret_expression(condition, environment.clone())?;
                if is_truthy(&cond) {
                    return self.interpret_statement(then_branch, environment.clone());
                } else {
                    if let Some(branch) = else_branch {
                        return self.interpret_statement(branch, environment.clone());
                    }
                    Ok(None)
                }
            }
            Statement::WhileStatement { condition, body } => {
                while is_truthy(&self.interpret_expression(condition, environment.clone())?) {
                    let return_value = self.interpret_statement(body, environment.clone())?;
                    if !return_value.is_none() {
                        return Ok(return_value);
                    }
                }
                Ok(None)
            }
            Statement::FunctionDeclaration {
                name,
                parameters,
                body,
            } => {
                environment.borrow_mut().define(
                    name.clone(),
                    LoxValue::LFunc(LoxFunction {
                        name: name.clone(),
                        parameters: parameters.clone(),
                        body: body.clone(),
                        environment: environment.clone(),
                    }),
                );
                Ok(None)
            }
            Statement::ReturnStatement { expression } => {
                let lox_value = self.interpret_expression(expression, environment.clone())?;
                Ok(Some(lox_value))
            }
        }
    }

    fn interpret_expression(
        &mut self,
        expr: &Expr,
        environment: Rc<RefCell<LoxEnvironment>>,
    ) -> Result<LoxValue, InterpreterError> {
        match expr {
            Expr::Literal(literal) => Ok(self.interpret_literal(literal)),
            Expr::Unary {
                operator,
                expression,
            } => {
                let lox_operand = self.interpret_expression(expression, environment.clone())?;
                self.interpret_unary(operator, lox_operand)
            }
            Expr::Binary {
                operator,
                left,
                right,
            } => {
                let lox_left_value = self.interpret_expression(left, environment.clone())?;
                let lox_right_value = self.interpret_expression(right, environment.clone())?;
                self.interpret_binary(operator, lox_left_value, lox_right_value)
            }
            Expr::Grouping(grouped_expr) => {
                self.interpret_expression(grouped_expr, environment.clone())
            }
            Expr::Variable { name } => Ok(environment.borrow().lookup(name.clone())),
            Expr::Assign { name, value } => {
                let left_hand_side = self.interpret_expression(value, environment.clone())?;
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
                let lox_left_value = self.interpret_expression(left, environment.clone())?;
                if is_truthy(&lox_left_value) {
                    return Ok(lox_left_value);
                }
                let lox_right_value = self.interpret_expression(right, environment.clone())?;
                return Ok(lox_right_value);
            }
            Expr::BinaryLogical {
                operator: BinaryLogicalOperator::And,
                left,
                right,
            } => {
                let lox_left_value = self.interpret_expression(left, environment.clone())?;
                if !is_truthy(&lox_left_value) {
                    return Ok(lox_left_value);
                }
                let lox_right_value = self.interpret_expression(right, environment.clone())?;
                return Ok(lox_right_value);
            }
            Expr::FunctionCall { callee, arguments } => {
                let lox_func = self.interpret_expression(callee, environment.clone())?;
                let args: Result<Vec<LoxValue>, InterpreterError> = arguments
                    .into_iter()
                    .map(|arg| self.interpret_expression(arg, environment.clone()))
                    .collect();
                if let Err(err) = args {
                    return Err(err);
                }
                self.interpret_call(&lox_func, args.unwrap())
            }
        }
    }

    fn interpret_binary(
        &self,
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

    fn interpret_call(
        &mut self,
        value: &LoxValue,
        arguments: Vec<LoxValue>,
    ) -> Result<LoxValue, InterpreterError> {
        match value {
            LFunc(lox_function) => self.interpret_function_call(lox_function, arguments),
            _ => panic!("cannot call this value {:?}", value),
        }
    }

    fn interpret_function_call(
        &mut self,
        lox_func: &LoxFunction,
        arguments: Vec<LoxValue>,
    ) -> Result<LoxValue, InterpreterError> {
        if lox_func.parameters.len() != arguments.len() {
            panic!("lox interpreter: number of arguments did not match number of parameters for function {:?}", lox_func.name);
        }

        // copy-pasta, this could be factored out. I wonder if I should be reusing the block interpretation too
        let mut child_env = LoxEnvironment::new(Some(
            zip(&lox_func.parameters, arguments)
                .into_iter()
                .map(|(name, value)| (name.clone(), value))
                .collect(),
        ));
        child_env.parent = Some(lox_func.environment.clone());
        let child_env = Rc::new(RefCell::new(child_env));

        // let mut child_env = lox_func.environment.clone();
        // TODO understand why this WAS required (before init on env::new). Looks like the mutable reference stays alive into
        // the interpret statement calls.
        // erm... adding a block to make sure the mutable reference 'expires'.
        // {
        //     let mut mut_ref = child_env.borrow_mut();
        //     for (name, value) in zip(&lox_func.parameters, arguments) {
        //         mut_ref.define(name.clone(), value);
        //     }
        // }

        for statement in &lox_func.body {
            let return_value = self.interpret_statement(statement, child_env.clone())?;
            if let Some(v) = return_value {
                return Ok(v);
            }
        }
        // implicit returned value is nil
        Ok(LoxValue::LNil)
    }

    fn interpret_unary(
        &self,
        op: &UnaryOperator,
        operand: LoxValue,
    ) -> Result<LoxValue, InterpreterError> {
        match (op, operand) {
            (UnaryOperator::Minus, LNumber(num)) => Ok(LNumber(-num)),
            (UnaryOperator::Not, lox_value) => Ok(LBool(!is_truthy(&lox_value))),
            (_, operand) => Err(InterpreterError::UnaryOperationNotSupported {
                operator: *op,
                operand,
            }),
        }
    }
    fn interpret_literal(&self, literal: &Literal) -> LoxValue {
        match literal {
            Literal::Number(num) => LNumber(*num),
            Literal::String(s) => LString(s.clone()),
            Literal::True => LBool(true),
            Literal::False => LBool(false),
            Literal::Nil => LNil,
        }
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

fn is_truthy(v: &LoxValue) -> bool {
    match v {
        LNil => false,
        LBool(value) => *value,
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use crate::ast::BinaryOperator::Plus;
    use crate::interpreter::{Interpreter, InterpreterError, LoxEnvironment, LoxValue};
    use crate::test_helpers::{parse_expr, parse_program, parse_statement};

    ///assumes success
    fn get_lox_value(code: &str) -> LoxValue {
        let mock_writer: Vec<u8> = Vec::new();
        let mut interpreter = Interpreter::new(mock_writer);
        let expr = parse_expr(code).expect("error in test setup");
        let env = LoxEnvironment::new(None);
        interpreter
            .interpret_expression(&expr, Rc::new(RefCell::new(env)))
            .unwrap()
    }

    fn get_lox_error(code: &str) -> InterpreterError {
        let mock_writer: Vec<u8> = Vec::new();
        let mut interpreter = Interpreter::new(mock_writer);
        let expr = parse_expr(code).expect("error in test setup");
        let env = LoxEnvironment::new(None);
        let lox_value = interpreter.interpret_expression(&expr, Rc::new(RefCell::new(env)));
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
        let mock_writer: Vec<u8> = Vec::new();
        let mut interpreter = Interpreter::new(mock_writer);
        let statement = parse_statement("print \"Hello\";").expect("error in test setup");
        let env = LoxEnvironment::new(None);

        interpreter
            .interpret_statement(&statement, Rc::new(RefCell::new(env)))
            .unwrap();
        assert_eq!(
            String::from_utf8(interpreter.writer).unwrap(),
            format!("{:}\n", LoxValue::LString("Hello".to_string()))
        )
    }

    #[test]
    fn test_interpret_return_statement() {
        let mock_writer: Vec<u8> = Vec::new();
        let mut interpreter = Interpreter::new(mock_writer);
        let program = parse_program("fun f() { return \"Hello\";} \nprint f();")
            .expect("error in test setup");
        let env = LoxEnvironment::new(None);

        interpreter.interpret_program(&program).unwrap();
        assert_eq!(
            String::from_utf8(interpreter.writer).unwrap(),
            format!("{:}\n", LoxValue::LString("Hello".to_string()))
        );
    }

    #[test]
    fn test_if_without_else() {
        let mock_writer = vec![];
        let mut interpreter = Interpreter::new(mock_writer);
        let statement = parse_statement("if (1) print \"Hello\";").expect("error in test setup");
        let env = LoxEnvironment::new(None);
        interpreter
            .interpret_statement(&statement, Rc::new(RefCell::new(env)))
            .unwrap();
        assert_eq!(
            String::from_utf8(interpreter.writer).unwrap(),
            format!("{:}\n", LoxValue::LString("Hello".to_string()))
        );
    }
    #[test]
    fn test_if_with_else() {
        let mock_writer = vec![];
        let mut interpreter = Interpreter::new(mock_writer);
        let statement =
            parse_statement("if (1) print \"Hello\"; else print \"should not be printed\";")
                .expect("error in test setup");
        let env = LoxEnvironment::new(None);
        interpreter
            .interpret_statement(&statement, Rc::new(RefCell::new(env)))
            .unwrap();
        assert_eq!(
            String::from_utf8(interpreter.writer).unwrap(),
            format!("{:}\n", LoxValue::LString("Hello".to_string()))
        );
    }

    #[test]
    fn test_interpret_variables() {
        let mock_writer = vec![];
        let mut interpreter = Interpreter::new(mock_writer);
        let program = parse_program("var a = 1;\nprint a;").expect("error in test setup");

        interpreter
            .interpret_program(&program)
            .expect("error! test failed.");

        let written = String::from_utf8(interpreter.writer).unwrap();
        assert_eq!(written, format!("{:}\n", LoxValue::LNumber(1.)));
    }
}
