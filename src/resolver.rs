use std::collections::HashMap;

use thiserror::Error;

use crate::ast::{Expr, FunctionType, Statement};

#[derive(Debug, PartialEq, Copy, Clone)]
enum VariableStatus {
    Unknown,
    Declared,
    Defined,
}

#[derive(Debug, Error, PartialEq)]
pub enum VariableResolverError {
    // var a = a + 1: not allowed. Almost certainly a user mistake.
    #[error("[line {line}] Error at '{name}': Can't read local variable in its own initializer.")]
    LocalVariableSelfReferencedInInitializer { line: usize, name: String },
    #[error("[line {line}] Error at '{name}': Already a variable with this name in this scope.")]
    LocalVariableRedeclaredInScope { line: usize, name: String },
    #[error("[line {line}] Error at 'return': Can't return from top-level code.")]
    ReturnNotAllowed { line: usize },
    #[error("[line {line}] Error at 'this': Can't use 'this' outside of a class.")]
    ThisNotAllowed { line: usize },
}
#[derive(Debug, Copy, Clone, PartialEq)]
enum ClassNestingStatus {
    None,
    InClass,
}

/// an example of a 'semantic analysis' pass
pub struct VariableResolver {
    scope_stack: Vec<HashMap<String, VariableStatus>>,
    in_function: bool,
    current_class: ClassNestingStatus,
}

impl VariableResolver {
    pub fn new() -> VariableResolver {
        VariableResolver {
            // start with one item for globals
            scope_stack: vec![HashMap::new()],
            in_function: false,
            current_class: ClassNestingStatus::None,
        }
    }

    fn begin_scope(&mut self) {
        self.scope_stack.push(HashMap::new());
    }
    fn end_scope(&mut self) {
        self.scope_stack.pop();
    }

    fn declare(&mut self, name: String) -> Result<(), String> {
        let is_global = self.scope_stack.len() == 1;
        let mut scope = self.scope_stack.last_mut().unwrap();
        // it's ok to re-declare a global variable.
        if scope.get(&name).unwrap_or(&VariableStatus::Unknown) != &VariableStatus::Unknown
            && !is_global
        {
            return Err("variable redeclared!".to_string());
        }
        scope.insert(name, VariableStatus::Declared);
        Ok(())
    }
    fn define(&mut self, name: String) {
        self.scope_stack
            .last_mut()
            .unwrap()
            .insert(name, VariableStatus::Defined);
    }

    fn find_variable(&self, name: String) -> Option<usize> {
        for (idx, scope) in self.scope_stack.iter().rev().enumerate() {
            let var_status = scope.get(&name).unwrap_or(&VariableStatus::Unknown);
            match var_status {
                VariableStatus::Unknown => {
                    continue;
                }
                VariableStatus::Declared => {
                    // this is an error!
                    return None;
                }
                VariableStatus::Defined => {
                    return Some(idx);
                }
            }
        }
        // variable not defined anywhere. We can assume it's a global variable, that will be defined later.
        // global variables don't play by the same rules as regular variables.
        // if there's an error, it will happen at runtime.
        return Some(self.scope_stack.len() - 1);
    }

    pub fn resolve_program(
        &mut self,
        program: &mut Vec<Statement>,
    ) -> Result<(), VariableResolverError> {
        for statement in program {
            self.resolve_statement(statement)?;
        }
        Ok(())
    }

    fn resolve_statement(
        &mut self,
        statement: &mut Statement,
    ) -> Result<(), VariableResolverError> {
        match statement {
            Statement::IfStatement {
                condition,
                then_branch,
                else_branch,
            } => {
                self.resolve_expr(condition)?;
                self.resolve_statement(then_branch)?;
                if let Some(branch) = else_branch {
                    self.resolve_statement(branch)?;
                }
            }
            Statement::WhileStatement { condition, body } => {
                self.resolve_expr(condition)?;
                self.resolve_statement(body)?;
            }
            Statement::VarDeclaration {
                name,
                initializer,
                line,
            } => {
                if let Err(_) = self.declare(name.clone()) {
                    return Err(VariableResolverError::LocalVariableRedeclaredInScope {
                        name: name.clone(),
                        line: *line,
                    });
                }
                self.resolve_expr(initializer)?;
                self.define(name.clone());
            }
            Statement::FunctionDeclaration {
                name,
                parameters,
                body,
                line,
            } => {
                self.resolve_function_declaration(
                    name,
                    parameters,
                    body,
                    line,
                    FunctionType::Function,
                )?;
            }
            Statement::Block { statements } => {
                self.begin_scope();
                for statement in statements {
                    self.resolve_statement(statement)?;
                }
                self.end_scope();
            }
            Statement::ExprStatement { expression } | Statement::PrintStatement { expression } => {
                self.resolve_expr(expression)?;
            }

            Statement::ReturnStatement { expression, line } => {
                if !self.in_function {
                    return Err(VariableResolverError::ReturnNotAllowed { line: *line });
                }
                self.resolve_expr(expression)?;
            }
            Statement::ClassDeclaration {
                name,
                methods,
                line,
            } => {
                let previous_current_class = self.current_class;
                self.current_class = ClassNestingStatus::InClass;
                if let Err(_) = self.declare(name.clone()) {
                    return Err(VariableResolverError::LocalVariableRedeclaredInScope {
                        name: name.clone(),
                        line: *line,
                    });
                }
                self.define(name.clone());
                for statement in methods {
                    match statement {
                        Statement::FunctionDeclaration { name, parameters, body, line } => {
                            self.resolve_function_declaration(name, parameters, body, line, FunctionType::Method)?;
                        }
                        _ => unreachable!("internal error: resolver expects methods to be FunctionDeclaration nodes"),
                    }
                }

                self.current_class = previous_current_class;
            }
        }
        Ok(())
    }

    fn resolve_function_declaration(
        &mut self,
        name: &String,
        parameters: &Vec<String>,
        body: &mut Vec<Statement>,
        line: &usize,
        function_type: FunctionType,
    ) -> Result<(), VariableResolverError> {
        let previous_in_function = self.in_function;
        self.in_function = true;
        match function_type {
            // only functions are defined as variables
            FunctionType::Function => {
                if let Err(_) = self.declare(name.clone()) {
                    return Err(VariableResolverError::LocalVariableRedeclaredInScope {
                        name: name.clone(),
                        line: *line,
                    });
                }

                self.define(name.clone())
            }
            FunctionType::Method => {
                self.begin_scope();
                self.define("this".to_string());
            }
        }
        if function_type == FunctionType::Method {
        } else {
            self.define(name.clone());
        }

        self.begin_scope();

        for parameter in parameters {
            // mark as defined because they will be when the function runs.
            self.define(parameter.clone());
        }
        for statement in body {
            self.resolve_statement(statement)?;
        }
        self.end_scope();
        self.in_function = previous_in_function;

        if function_type == FunctionType::Method {
            self.end_scope();
        }

        Ok(())
    }

    fn resolve_expr(&self, expr: &mut Expr) -> Result<(), VariableResolverError> {
        match expr {
            Expr::This(variable) => {
                match &**variable {
                    Expr::Variable { line, .. } => {
                        if self.current_class == ClassNestingStatus::None {
                            return Err(VariableResolverError::ThisNotAllowed { line: *line });
                        }
                    }
                    _ => unreachable!(
                        "this resolver assumes 'This' nodes can only contain Variable nodes."
                    ),
                }
                self.resolve_expr(variable)?;
            }
            Expr::Literal(_) => {
                return Ok(());
            }
            Expr::Assign { location, value } => {
                // interestingly, there isn't much to do here.
                self.resolve_expr(location)?;
                self.resolve_expr(value)?;
            }
            Expr::BinaryLogical { left, right, .. } | Expr::Binary { left, right, .. } => {
                self.resolve_expr(left)?;
                self.resolve_expr(right)?;
            }
            Expr::Unary { expression, .. } => self.resolve_expr(expression)?,
            Expr::Grouping(expr) => self.resolve_expr(expr)?,
            Expr::Variable { depth, line, name } => {
                let new_depth = self.find_variable(name.clone());
                match new_depth {
                    None => {
                        return Err(
                            VariableResolverError::LocalVariableSelfReferencedInInitializer {
                                line: *line,
                                name: name.clone(),
                            },
                        );
                    }
                    Some(_) => {
                        *depth = new_depth;
                    }
                }
            }
            Expr::FunctionCall {
                callee, arguments, ..
            } => {
                self.resolve_expr(callee)?;
                for argument in arguments {
                    self.resolve_expr(argument)?;
                }
            }
            Expr::PropertyAccess { object, .. } => {
                self.resolve_expr(object)?;
            }
            Expr::Set { object, value, .. } => {
                self.resolve_expr(object)?;
                self.resolve_expr(value)?;
            }
        };
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_helpers::parse_program;

    use super::*;

    #[test]
    fn test_invalid_variable_use_passes_if_global() {
        // this should not crash. That's about it.
        let mut program = parse_program("fun f() { print x; }").unwrap();
        let mut resolver = VariableResolver::new();
        resolver.resolve_program(&mut program).unwrap();
    }

    #[test]
    fn test_local_same_scope_variable_redefinition_errors() {
        let mut program = parse_program("{ var a = 1; var a = 2; }").unwrap();
        let mut resolver = VariableResolver::new();
        let maybe_error = resolver.resolve_program(&mut program);
        assert!(maybe_error.is_err());
        assert!(maybe_error.is_err_and(|err| err
            == VariableResolverError::LocalVariableRedeclaredInScope {
                line: 1,
                name: "a".to_string()
            }));
    }

    #[test]
    fn test_variable_depth_correct() {
        let mut program =
            parse_program("{var a = 1;\n{fun f() { print x; }\nprint a;\n}}").unwrap();
        let mut resolver = VariableResolver::new();
        resolver.resolve_program(&mut program).unwrap();
        println!("{:#?}", program);

        // that is one lousy test :)
        match &program[0] {
            Statement::Block { statements } => {
                match &statements[1] {
                    Statement::Block { statements } => {
                        match &statements[1] {
                            Statement::PrintStatement {
                                expression:
                                    Expr::Variable {
                                        depth: Some(d),
                                        name,
                                        ..
                                    },
                            } => {
                                // sanity check we're looking at the right variable
                                assert_eq!(*name, "a".to_string());
                                assert_eq!(*d, 1);
                            }
                            _ => panic!("test failed 1"),
                        }
                    }
                    _ => panic!("test failed 2"),
                }
            }
            _ => unreachable!("should have been a block"),
        }
    }
}
