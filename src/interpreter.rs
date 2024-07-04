use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::io::Write;
use std::iter::zip;
use std::rc::Rc;

use thiserror::Error;

use BinaryOperatorType::*;

use crate::ast::{
    BinaryLogicalOperator, BinaryLogicalOperatorType, BinaryOperator, BinaryOperatorType, Expr,
    Literal, Statement, UnaryOperator, UnaryOperatorType,
};
use crate::environment::{Environment, EnvironmentError};
use crate::interpreter::InterpreterError::UndefinedVariable;
use crate::interpreter::LoxValue::*;

type LoxEnvironment = Environment<LoxValue>;
#[derive(Debug, PartialEq, Error)]
pub enum InterpreterError {
    #[error("[line {line}] runtime error: Operands must be two numbers or two strings.")]
    BinaryAdditionNotSupported { line: usize },
    #[error("[line {line}] runtime error: Operands must be numbers.")]
    BinarySubtractionNotSupported { line: usize },
    #[error("[line {line}] runtime error: Operands must be numbers.")]
    BinaryDivisionNotSupported { line: usize },
    #[error("[line {line}] runtime error: Operands must be numbers.")]
    BinaryMultiplicationNotSupported { line: usize },
    #[error("[line {line}] runtime error: Operands must be numbers.")]
    BinaryComparisonNotSupported { line: usize },
    #[error("[line {line}] runtime error: Operand must be a number.")]
    UnaryNegateNotSupported { line: usize },

    #[error("[line {line}] runtime error: Can only call functions and classes.")]
    CannotCall { line: usize },
    #[error("[line {line}] runtime error: Expected {parameters} arguments but got {arguments}.")]
    WrongNumberOfArguments {
        parameters: usize,
        arguments: usize,
        line: usize,
    },
    #[error("[line {line}] runtime error: Undefined property '{name}'.")]
    UndefinedProperty { name: String, line: usize },
    #[error("[line {line}] runtime error: Only instances have properties.")]
    OnlyInstancesHaveProperties { line: usize, name: String },
    #[error("[line {line}] runtime error: Only instances have fields.")]
    SetPropertyOnlyWorksOnInstances { line: usize, lexeme: String },

    #[error("[line {line}] runtime error: Undefined variable '{name}'.")]
    UndefinedVariable { line: usize, name: String },
}

impl InterpreterError {
    fn from_environment_error(value: EnvironmentError, line: usize) -> Self {
        match value {
            EnvironmentError::VariableNotFound { name } => UndefinedVariable { name, line },
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum LoxValue {
    LString(String),
    LNumber(f64),
    LBool(bool),
    LNil,
    LFunc(Rc<LoxFunction>),
    LClass(Rc<LoxClass>),
    LInstance(Rc<LoxInstance>),
}

impl Display for LoxValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LFunc(func) => write!(f, "<fn {}>\n", func.name),
            LString(s) => write!(f, "{}", s),
            LNumber(n) => write!(f, "{}", n),
            LBool(b) => write!(f, "{}", b),
            LNil => write!(f, "nil"),
            LClass(class) => write!(f, "{}", class.name),
            LInstance(instance) => write!(f, "{} instance", instance.class.name),
        }
    }
}

#[derive(Clone)]
struct LoxFunction {
    name: String,
    parameters: Vec<String>,
    body: Vec<Statement>,
    environment: Rc<LoxEnvironment>,
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

/// We compare environments by pointer to match the book.
impl PartialEq for LoxFunction {
    fn eq(&self, other: &LoxFunction) -> bool {
        self.name == other.name
            && self.parameters == other.parameters
            && self.body == other.body
            && std::ptr::eq(&self.environment, &other.environment)
    }
}

#[derive(Clone)]
struct LoxClass {
    name: String,
    environment: Rc<LoxEnvironment>,
    methods: HashMap<String, Rc<LoxFunction>>,
}

impl Debug for LoxClass {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LoxClass")
            .field("name", &self.name)
            .finish()
    }
}

impl PartialEq for LoxClass {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
#[derive(Clone, PartialEq, Debug)]
struct LoxInstance {
    class: Rc<LoxClass>,
    fields: RefCell<HashMap<String, LoxValue>>,
}

impl LoxInstance {
    fn new(class: Rc<LoxClass>) -> LoxInstance {
        LoxInstance {
            class,
            fields: RefCell::new(HashMap::new()),
        }
    }

    pub(crate) fn set_field(&self, name: String, value: LoxValue) {
        self.fields.borrow_mut().insert(name, value);
    }
    pub(crate) fn get_field_or_method(
        &self,
        name: &String,
        line: usize,
        self_rc: Rc<LoxInstance>,
    ) -> Result<LoxValue, InterpreterError> {
        if let Some(value) = self.fields.borrow().get(name) {
            return Ok(value.clone());
        }

        if let Some(value) = self.class.methods.get(name) {
            // Add "this" to the environment so the function returned is a "bound method"
            let mut closure_env = LoxEnvironment::new(None);
            closure_env.parent = Some(value.environment.clone());
            closure_env.define("this".to_string(), LInstance(self_rc.clone()));
            return Ok(LFunc(Rc::new(LoxFunction {
                environment: Rc::new(closure_env),
                name: value.name.clone(),
                parameters: value.parameters.clone(),
                body: value.body.clone(),
            })));
        }

        return Err(InterpreterError::UndefinedProperty {
            name: name.clone(),
            line,
        });
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
        let environment = Rc::new(LoxEnvironment::new(None));
        self.interpret_program_with_env(program, environment)
    }

    fn interpret_program_with_env(
        &mut self,
        program: &Vec<Statement>,
        environment: Rc<LoxEnvironment>,
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
        environment: Rc<LoxEnvironment>,
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
            Statement::VarDeclaration {
                name, initializer, ..
            } => {
                let value = self.interpret_expression(initializer, environment.clone())?;
                environment.define(name.clone(), value);
                Ok(None)
            }
            Statement::Block { statements } => {
                let mut child_env = LoxEnvironment::new(None);
                child_env.parent = Some(environment.clone());
                let child_env = Rc::new(child_env);
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
                ..
            } => {
                environment.define(
                    name.clone(),
                    LoxValue::LFunc(Rc::new(LoxFunction {
                        name: name.clone(),
                        parameters: parameters.clone(),
                        body: body.clone(),
                        environment: environment.clone(),
                    })),
                );
                Ok(None)
            }
            Statement::ClassDeclaration {
                name,
                methods,
                line,
            } => {
                // defining first so the name exists and methods can refer to it.
                environment.define(name.clone(), LoxValue::LNil);
                let mut lox_methods = HashMap::new();
                for statement in methods {
                    match statement {
                        Statement::FunctionDeclaration { name, parameters, body, line } => {
                            let method = LoxFunction{name: name.clone(), parameters: parameters.clone(), body: body.clone(), environment: environment.clone() };
                            lox_methods.insert(name.clone(), Rc::new(method));
                        }
                        _ => panic!("internal error: interpreter expects only function declarations in a class declaration node")
                    };
                }

                let class = LoxValue::LClass(Rc::from(LoxClass {
                    name: name.clone(),
                    environment: environment.clone(),
                    methods: lox_methods,
                }));
                environment
                    .assign(name.clone(), class, 0)
                    .map_err(|err| InterpreterError::from_environment_error(err, *line))?;

                Ok(None)
            }
            Statement::ReturnStatement { expression, .. } => {
                let lox_value = self.interpret_expression(expression, environment.clone())?;
                Ok(Some(lox_value))
            }
        }
    }

    fn interpret_expression(
        &mut self,
        expr: &Expr,
        environment: Rc<LoxEnvironment>,
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
            Expr::Variable { name, depth, line } => Ok(environment
                .lookup(name.clone(), depth.unwrap())
                .map_err(|err| InterpreterError::from_environment_error(err, *line))?),
            Expr::This(variable) => self.interpret_expression(variable, environment.clone()),
            Expr::Assign { location, value } => {
                let right_hand_side = self.interpret_expression(&value, environment.clone())?;
                match location.as_ref() {
                    Expr::Variable { depth, line, name } => environment
                        .assign(name.clone(), right_hand_side.clone(), depth.unwrap())
                        .map_err(|err| InterpreterError::from_environment_error(err, *line))?,
                    _ => panic!("assignment to location of this type not handled ({location:?})"),
                }
                Ok(right_hand_side)
            }
            Expr::BinaryLogical {
                operator:
                    BinaryLogicalOperator {
                        type_: BinaryLogicalOperatorType::Or,
                        ..
                    },
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
                operator:
                    BinaryLogicalOperator {
                        type_: BinaryLogicalOperatorType::And,
                        ..
                    },
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
            Expr::FunctionCall {
                callee,
                arguments,
                line,
            } => {
                let lox_func = self.interpret_expression(callee, environment.clone())?;
                let args: Result<Vec<LoxValue>, InterpreterError> = arguments
                    .into_iter()
                    .map(|arg| self.interpret_expression(arg, environment.clone()))
                    .collect();
                if let Err(err) = args {
                    return Err(err);
                }
                self.interpret_call(&lox_func, args.unwrap(), *line)
            }
            Expr::PropertyAccess { object, name, line } => {
                let lox_obj = self.interpret_expression(object, environment.clone())?;
                match lox_obj {
                    LInstance(lox_instance) => {
                        lox_instance.get_field_or_method(name, *line, lox_instance.clone())
                    }
                    _ => Err(InterpreterError::OnlyInstancesHaveProperties {
                        line: *line,
                        name: name.clone(),
                    }),
                }
            }
            Expr::Set {
                object,
                name,
                value,
                line,
            } => {
                let lox_object = self.interpret_expression(object, environment.clone())?;
                let lox_value = self.interpret_expression(value, environment.clone())?;
                match lox_object {
                    LInstance(mut lox_instance) => {
                        // TODO at some point add a test where we have an instance and put it as field on another instance.
                        // then change the field instance. Does it change the other one? It should (I think).
                        lox_instance.set_field(name.clone(), lox_value.clone());
                        Ok(lox_value)
                    }
                    _ => Err(InterpreterError::SetPropertyOnlyWorksOnInstances {
                        line: *line,
                        lexeme: name.clone(),
                    }),
                }
            }
        }
    }

    fn interpret_binary(
        &self,
        op: &BinaryOperator,
        lox_left: LoxValue,
        lox_right: LoxValue,
    ) -> Result<LoxValue, InterpreterError> {
        match (lox_left, op.type_, lox_right) {
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
            (_, Plus, _) => Err(InterpreterError::BinaryAdditionNotSupported { line: op.line }),
            (_, Minus, _) => Err(InterpreterError::BinarySubtractionNotSupported { line: op.line }),
            (_, Divide, _) => Err(InterpreterError::BinaryDivisionNotSupported { line: op.line }),
            (_, Multiply, _) => {
                Err(InterpreterError::BinaryMultiplicationNotSupported { line: op.line })
            }
            (_, Gt | Gte | Lt | Lte, _) => {
                Err(InterpreterError::BinaryComparisonNotSupported { line: op.line })
            }
        }
    }

    fn interpret_call(
        &mut self,
        value: &LoxValue,
        arguments: Vec<LoxValue>,
        line: usize,
    ) -> Result<LoxValue, InterpreterError> {
        match value {
            LFunc(lox_function) => self.interpret_function_call(lox_function, arguments, line),
            LClass(lox_class) => self.interpret_class_call(lox_class.clone(), arguments, line),
            _ => return Err(InterpreterError::CannotCall { line }),
        }
    }

    fn interpret_function_call(
        &mut self,
        lox_func: &LoxFunction,
        arguments: Vec<LoxValue>,
        line: usize,
    ) -> Result<LoxValue, InterpreterError> {
        if lox_func.parameters.len() != arguments.len() {
            return Err(InterpreterError::WrongNumberOfArguments {
                line,
                parameters: lox_func.parameters.len(),
                arguments: arguments.len(),
            });
        }

        // copy-pasta, this could be factored out. I wonder if I should be reusing the block interpretation too
        let mut child_env = LoxEnvironment::new(Some(
            zip(&lox_func.parameters, arguments)
                .into_iter()
                .map(|(name, value)| (name.clone(), value))
                .collect(),
        ));
        child_env.parent = Some(lox_func.environment.clone());
        let child_env = Rc::new(child_env);

        for statement in &lox_func.body {
            let return_value = self.interpret_statement(statement, child_env.clone())?;
            if let Some(v) = return_value {
                return Ok(v);
            }
        }
        // implicit returned value is nil
        Ok(LoxValue::LNil)
    }

    fn interpret_class_call(
        &mut self,
        lox_class: Rc<LoxClass>,
        arguments: Vec<LoxValue>,
        line: usize,
    ) -> Result<LoxValue, InterpreterError> {
        Ok(LoxValue::LInstance(Rc::new(LoxInstance::new(
            lox_class.clone(),
        ))))
    }

    fn interpret_unary(
        &self,
        op: &UnaryOperator,
        operand: LoxValue,
    ) -> Result<LoxValue, InterpreterError> {
        match (op.type_, operand) {
            (UnaryOperatorType::Minus, LNumber(num)) => Ok(LNumber(-num)),
            (UnaryOperatorType::Not, lox_value) => Ok(LBool(!is_truthy(&lox_value))),
            (UnaryOperatorType::Minus, _) => {
                Err(InterpreterError::UnaryNegateNotSupported { line: op.line })
            }
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
        (LFunc(l), LFunc(r)) => l == r,
        (LClass(l), LClass(r)) => l == r,
        (LInstance(l), LInstance(r)) => l == r,
        // this 'catch all' arm is a bit unfortunate: nothing tells us we are forgetting to add cases if we add a variant to LoxValue
        // not sure how to do differently though, don't want to enumerate all cases explicitly.
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
    use std::rc::Rc;

    use crate::interpreter::{Interpreter, InterpreterError, LoxEnvironment, LoxValue};
    use crate::test_helpers::{
        parse_and_resolve_program, parse_expr, parse_program, parse_statement,
    };

    ///assumes success
    fn get_lox_value(code: &str) -> LoxValue {
        let mock_writer: Vec<u8> = Vec::new();
        let mut interpreter = Interpreter::new(mock_writer);
        let expr = parse_expr(code).expect("error in test setup");
        let env = LoxEnvironment::new(None);
        interpreter
            .interpret_expression(&expr, Rc::new(env))
            .unwrap()
    }

    fn get_lox_error(code: &str) -> InterpreterError {
        let mock_writer: Vec<u8> = Vec::new();
        let mut interpreter = Interpreter::new(mock_writer);
        let expr = parse_expr(code).expect("error in test setup");
        let env = LoxEnvironment::new(None);
        let lox_value = interpreter.interpret_expression(&expr, Rc::new(env));
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
            ("3 == 3.0", LoxValue::LBool(true)),
            ("3 == 4.0", LoxValue::LBool(false)),
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
            InterpreterError::BinaryAdditionNotSupported { line: 1 }
        );
    }

    #[test]
    fn test_interpret_statement() {
        let mock_writer: Vec<u8> = Vec::new();
        let mut interpreter = Interpreter::new(mock_writer);
        let statement = parse_statement("print \"Hello\";").expect("error in test setup");
        let env = LoxEnvironment::new(None);

        interpreter
            .interpret_statement(&statement, Rc::new(env))
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
        let program = parse_and_resolve_program("fun f() { return \"Hello\";} \nprint f();")
            .expect("error in test setup");

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
            .interpret_statement(&statement, Rc::new(env))
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
            .interpret_statement(&statement, Rc::new(env))
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
        let program =
            parse_and_resolve_program("var a = 1;\nprint a;").expect("error in test setup");

        interpreter
            .interpret_program(&program)
            .expect("error! test failed.");

        let written = String::from_utf8(interpreter.writer).unwrap();
        assert_eq!(written, format!("{:}\n", LoxValue::LNumber(1.)));
    }
}
