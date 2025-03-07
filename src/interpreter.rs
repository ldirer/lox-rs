use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::io::Write;
use std::iter::zip;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};
use thiserror::Error;

use BinaryOperatorType::*;

use crate::ast::{
    BinaryLogicalOperator, BinaryLogicalOperatorType, BinaryOperator, BinaryOperatorType, Expr,
    Literal, Statement, UnaryOperator, UnaryOperatorType,
};
use crate::environment::{Environment, EnvironmentError};
use crate::interpreter::InterpreterError::UndefinedVariable;
use crate::interpreter::LoxValue::*;
const CONSTRUCTOR_RESERVED_NAME: &str = "init";
pub type LoxEnvironment = Environment<LoxValue>;
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
    #[error("[line {line}] runtime error: Superclass must be a class.")]
    SuperclassMustBeAClass { line: usize, name: String },
}

impl InterpreterError {
    fn from_environment_error(value: EnvironmentError, line: usize) -> Self {
        match value {
            EnvironmentError::VariableNotFound { name } => UndefinedVariable { name, line },
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum LoxValue {
    LString(String),
    LNumber(f64),
    LBool(bool),
    LNil,
    LFunc(Rc<LoxFunction>),
    LNativeFunc(Rc<LoxNativeFunction>),
    LClass(Rc<LoxClass>),
    LInstance(Rc<LoxInstance>),
}

impl Display for LoxValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LFunc(func) => write!(f, "<fn {}>", func.name),
            LString(s) => write!(f, "{}", s),
            LNumber(n) => write!(f, "{}", n),
            LBool(b) => write!(f, "{}", b),
            LNil => write!(f, "nil"),
            LClass(class) => write!(f, "{}", class.name),
            LInstance(instance) => write!(f, "{} instance", instance.class.name),
            LNativeFunc(_) => write!(f, "<native fn>"),
        }
    }
}

#[derive(Clone)]
pub struct LoxFunction {
    name: String,
    parameters: Vec<String>,
    body: Vec<Statement>,
    environment: Rc<LoxEnvironment>,
    is_initializer: bool,
}

impl LoxFunction {
    fn bind(&self, instance: Rc<LoxInstance>) -> Rc<LoxFunction> {
        // Add "this" to the environment so the function returned is a "bound method"
        let closure_env = LoxEnvironment::new_with_parent(self.environment.clone());
        closure_env.define("this".to_string(), LInstance(instance.clone()));
        return Rc::new(LoxFunction {
            environment: Rc::new(closure_env),
            name: self.name.clone(),
            parameters: self.parameters.clone(),
            body: self.body.clone(),
            is_initializer: self.is_initializer,
        });
    }
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

#[derive(Clone, Debug)]
pub struct LoxNativeFunction {
    name: String,
    parameters: Vec<String>,
    environment: Rc<LoxEnvironment>,
    call: fn(Rc<LoxEnvironment>, Vec<LoxValue>) -> Result<LoxValue, InterpreterError>,
}
impl PartialEq for LoxNativeFunction {
    fn eq(&self, other: &LoxNativeFunction) -> bool {
        self.name == other.name
            && self.parameters == other.parameters
            && std::ptr::eq(&self.environment, &other.environment)
    }
}

#[derive(Clone)]
pub struct LoxClass {
    name: String,
    superclass: Option<Rc<LoxClass>>,
    methods: HashMap<String, Rc<LoxFunction>>,
}

impl LoxClass {
    fn find_method(&self, name: &String) -> Option<Rc<LoxFunction>> {
        return self.methods.get(name).map(|m| m.clone()).or_else(|| {
            self.superclass
                .clone()
                .and_then(|cls| cls.find_method(name))
        });
    }
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
pub struct LoxInstance {
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

        if let Some(value) = self.class.find_method(name) {
            return Ok(LFunc(value.bind(self_rc.clone())));
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

    pub fn interpret_program_with_env(
        &mut self,
        program: &Vec<Statement>,
        environment: Rc<LoxEnvironment>,
    ) -> Result<(), InterpreterError> {
        let globals = get_globals(environment.clone());
        for (name, lox_value) in globals {
            environment.define(name, lox_value);
        }

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
                let child_env = Rc::new(LoxEnvironment::new_with_parent(environment));

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
                        parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                        body: body.clone(),
                        environment: environment.clone(),
                        is_initializer: false,
                    })),
                );
                Ok(None)
            }
            Statement::ClassDeclaration {
                name,
                methods,
                line,
                superclass,
            } => {
                // defining first so the name exists and methods can refer to it.
                environment.define(name.clone(), LoxValue::LNil);

                let mut lox_superclass = None;
                if let Some(super_var) = superclass {
                    lox_superclass = Some(
                        self.interpret_superclass_declaration(super_var, environment.clone())?,
                    );
                }

                let mut lox_methods = HashMap::new();
                for statement in methods {
                    match statement {
                        Statement::FunctionDeclaration { name, parameters, body, line: _ } => {
                            let mut method_env = environment.clone();
                            if let Some(superclass) = &lox_superclass {
                                method_env = Rc::new(LoxEnvironment::new_with_parent(method_env));
                                method_env.define("super".to_string(), LoxValue::LClass(superclass.clone()));
                            }
                            let method = LoxFunction{name: name.clone(), parameters: parameters.iter().map(|p|p.name.clone()).collect(), body: body.clone(), environment: method_env, is_initializer: name == CONSTRUCTOR_RESERVED_NAME };
                            lox_methods.insert(name.clone(), Rc::new(method));
                        }
                        _ => panic!("internal error: interpreter expects only function declarations in a class declaration node")
                    };
                }

                let class = LoxValue::LClass(Rc::from(LoxClass {
                    name: name.clone(),
                    superclass: lox_superclass,
                    methods: lox_methods,
                }));
                environment
                    .assign(name.clone(), class, 0)
                    .map_err(|err| InterpreterError::from_environment_error(err, *line))?;

                Ok(None)
            }
            Statement::ReturnStatement { expression, .. } => match expression {
                // we would not want to return Ok(None) here because we use the return value elsewhere (function call) to know if there was a return.
                None => Ok(Some(LoxValue::LNil)),
                Some(value_expr) => {
                    let lox_value = self.interpret_expression(value_expr, environment.clone())?;
                    Ok(Some(lox_value))
                }
            },
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
                    LInstance(lox_instance) => {
                        lox_instance.set_field(name.clone(), lox_value.clone());
                        Ok(lox_value)
                    }
                    _ => Err(InterpreterError::SetPropertyOnlyWorksOnInstances {
                        line: *line,
                        lexeme: name.clone(),
                    }),
                }
            }
            Expr::Super {
                line,
                method,
                variable,
            } => {
                // get the method on the superclass and bind this to the current 'this' (based on environment)
                let this_depth: usize;
                if let Expr::Variable { depth, .. } = variable.as_ref() {
                    // hack. Following the book though.
                    this_depth = depth.unwrap() - 1;
                } else {
                    unreachable!("interpreter expects super to store a Variable node");
                }
                let lox_superclass = self.interpret_expression(variable, environment.clone())?;
                match lox_superclass {
                    LClass(class) => {
                        let lox_method = class.find_method(method);
                        match lox_method {
                            None => {
                                return Err(InterpreterError::UndefinedProperty {
                                    name: method.clone(),
                                    line: *line,
                                });
                            }
                            Some(lox_function) => {
                                match environment.lookup("this".to_string(), this_depth).unwrap() {
                                    LInstance(lox_instance_this) => Ok(LoxValue::LFunc(
                                        lox_function.clone().bind(lox_instance_this),
                                    )),
                                    _ => unreachable!(
                                        "implementation error, 'this' should refer to an instance"
                                    ),
                                }
                            }
                        }
                    }
                    _ => {
                        unreachable!("internal error, expected super to evaluate to a class object")
                    }
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
            LNativeFunc(lox_native_function) => {
                self.interpret_native_function_call(lox_native_function, arguments)
            }
            LClass(lox_class) => self.interpret_class_call(lox_class.clone(), arguments, line),
            _ => return Err(InterpreterError::CannotCall { line }),
        }
    }

    fn interpret_native_function_call(
        &self,
        lox_native_function: &Rc<LoxNativeFunction>,
        arguments: Vec<LoxValue>,
    ) -> Result<LoxValue, InterpreterError> {
        (lox_native_function.call)(lox_native_function.environment.clone(), arguments)
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
        let child_env = Rc::new(LoxEnvironment::new_with_parent(
            lox_func.environment.clone(),
        ));
        for (name, value) in zip(&lox_func.parameters, arguments) {
            child_env.define(name.clone(), value);
        }

        for statement in &lox_func.body {
            let return_value = self.interpret_statement(statement, child_env.clone())?;
            if let Some(v) = return_value {
                if lox_func.is_initializer {
                    // bypass return value. resolver should only allow empty returns anyway
                    // unwrapping because it's an implementation bug if the variable isn't there.
                    return Ok(lox_func.environment.lookup("this".to_string(), 0).unwrap());
                }
                return Ok(v);
            }
        }
        // implicit returned value is nil, unless we're in an initializer
        if lox_func.is_initializer {
            return Ok(lox_func.environment.lookup("this".to_string(), 0).unwrap());
        }
        Ok(LoxValue::LNil)
    }

    fn interpret_class_call(
        &mut self,
        lox_class: Rc<LoxClass>,
        arguments: Vec<LoxValue>,
        line: usize,
    ) -> Result<LoxValue, InterpreterError> {
        let instance = Rc::new(LoxInstance::new(lox_class.clone()));
        if let Some(constructor) = lox_class.find_method(&CONSTRUCTOR_RESERVED_NAME.to_string()) {
            let bound_method = constructor.bind(instance.clone());
            self.interpret_function_call(&bound_method, arguments, line)?;
        } else if arguments.len() > 0 {
            return Err(InterpreterError::WrongNumberOfArguments {
                arguments: arguments.len(),
                parameters: 0,
                line,
            });
        };

        Ok(LoxValue::LInstance(instance))
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

    fn interpret_superclass_declaration(
        &mut self,
        superclass_var: &Expr,
        environment: Rc<LoxEnvironment>,
    ) -> Result<Rc<LoxClass>, InterpreterError> {
        match superclass_var {
            Expr::Variable { line, name, .. } => {
                let super_value = self.interpret_expression(superclass_var, environment.clone())?;
                return match super_value {
                    LClass(lox_superclass) => Ok(lox_superclass),
                    _ => Err(InterpreterError::SuperclassMustBeAClass {
                        line: *line,
                        name: name.clone(),
                    }),
                };
            }
            _ => unreachable!("this interpreter expects superclass to be a variable"),
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

pub fn get_globals(environment: Rc<LoxEnvironment>) -> HashMap<String, LoxValue> {
    let clock = LNativeFunc(Rc::new(LoxNativeFunction {
        name: "clock".to_string(),
        parameters: vec![],
        environment: environment.clone(),
        call: |_env, _args| {
            let start = SystemTime::now();
            return Ok(LoxValue::LNumber(
                // conversion isn't safe but it does not matter here.
                start
                    .duration_since(UNIX_EPOCH)
                    .expect("time went backwards")
                    .as_secs() as f64,
            ));
        },
    }));
    return HashMap::from([("clock".to_string(), clock)]);
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::interpreter::{Interpreter, InterpreterError, LoxEnvironment, LoxValue};
    use crate::test_helpers::{parse_and_resolve_program, parse_expr, parse_statement};

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
