use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum EnvironmentError {
    #[error("Undefined variable '{name}'.")]
    VariableNotFound { name: String },
}

#[derive(Debug, PartialEq)]
pub struct Environment<T: Clone> {
    // rust book: "interior mutability pattern"
    pub(crate) parent: Option<Rc<Environment<T>>>,
    bindings: RefCell<HashMap<String, T>>,
}

impl<T: Clone> Environment<T> {
    pub fn new(bindings: Option<HashMap<String, T>>) -> Environment<T> {
        Environment {
            parent: None,
            bindings: RefCell::new(bindings.unwrap_or(HashMap::new())),
        }
    }

    pub fn new_with_parent(parent: Rc<Environment<T>>) -> Environment<T> {
        let mut child_env = Environment::new(None);
        child_env.parent = Some(parent.clone());
        child_env
    }
    pub fn define(&self, name: String, value: T) {
        let is_global_environment = self.parent.is_none();
        // it's fine to redefine a global variable, but not a local one (Lox spec).
        if self.bindings.borrow().contains_key(&name) && !is_global_environment {
            panic!(
                "a variable with this name ({}) already exists in this scope",
                name
            );
        }
        self.bindings.borrow_mut().insert(name, value);
    }

    pub fn assign(&self, name: String, value: T, depth: usize) -> Result<(), EnvironmentError> {
        if depth == 0 {
            if self.bindings.borrow().contains_key(&name) {
                // overwrite existing value
                self.bindings.borrow_mut().insert(name, value);
                return Ok(());
            }
            return Err(EnvironmentError::VariableNotFound { name });
        }

        match &self.parent {
            None => unreachable!("assign failed for {name}! Implementation bug, we should have a parent or depth should be zero (not {depth})"),
            Some(parent_env) => parent_env.assign(name, value, depth - 1),
        }
    }

    pub fn lookup(&self, name: String, depth: usize) -> Result<T, EnvironmentError> {
        if depth == 0 {
            if let Some(value) = self.bindings.borrow().get(&name) {
                return Ok(value.clone());
            }
            return Err(EnvironmentError::VariableNotFound { name: name.clone() });
        }

        match &self.parent {
            None => {
                self.debug(depth);
                unreachable!("lookup failed for {name}! Implementation bug, we should have a parent or depth should be zero (not {depth})")
            }
            Some(parent_env) => parent_env.lookup(name, depth - 1),
        }
    }

    #[allow(dead_code)]
    fn debug(&self, depth: usize) {
        eprintln!(
            "What's in scope - depth {depth}: {:#?}",
            self.bindings.borrow().keys()
        );
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::rc::Rc;

    use crate::environment::Environment;

    #[test]
    fn test_lookup() {
        let environment = Environment::<i32>::new(Some(HashMap::from([
            ("a".to_string(), 1),
            ("b".to_string(), 2),
        ])));
        let value = environment.lookup("a".to_string(), 0).unwrap();
        assert_eq!(value, 1)
    }

    #[test]
    fn test_define_and_assign() {
        let environment = Environment::<i32>::new(None);
        environment.define("a".to_string(), 1);
        assert_eq!(environment.lookup("a".to_string(), 0).unwrap(), 1);
        // change value
        environment.assign("a".to_string(), 3, 0).unwrap();
        assert_eq!(environment.lookup("a".to_string(), 0).unwrap(), 3);
    }

    #[test]
    fn test_redefine_global() {
        let environment = Environment::<i32>::new(None);
        environment.define("a".to_string(), 1);
        assert_eq!(environment.lookup("a".to_string(), 0).unwrap(), 1);
        // redefine
        environment.define("a".to_string(), 2);
        assert_eq!(environment.lookup("a".to_string(), 0).unwrap(), 2);
    }
    #[test]
    #[should_panic]
    fn test_redefine_local() {
        let root_env = Environment::<i32>::new(Some(HashMap::from([("a".to_string(), 1)])));
        let mut env = Environment::<i32>::new(None);
        env.parent = Some(Rc::new(root_env));
        env.define("a".to_string(), 1);
        env.define("a".to_string(), 2);
    }
    #[test]
    fn test_assign_variable_from_parent_environment() {
        let root_env = Environment::<i32>::new(Some(HashMap::from([("a".to_string(), 1)])));

        let mut env = Environment::<i32>::new(None);
        env.parent = Some(Rc::new(root_env));
        assert_eq!(env.lookup("a".to_string(), 1).unwrap(), 1);

        env.assign("a".to_string(), 2, 1).unwrap();
        assert_eq!(env.lookup("a".to_string(), 1).unwrap(), 2);
    }

    #[test]
    fn test_multiple_environments_one_parent_does_not_panic() {
        let root_env = Environment::<i32>::new(Some(HashMap::from([("a".to_string(), 1)])));
        let mut child_1 = Environment::<i32>::new(None);
        let mut child_2 = Environment::<i32>::new(None);
        let shared_parent_env = Rc::new(root_env);
        child_1.parent = Some(shared_parent_env.clone());
        child_2.parent = Some(shared_parent_env.clone());

        assert_eq!(child_1.lookup("a".to_string(), 1).unwrap(), 1);
        assert_eq!(child_2.lookup("a".to_string(), 1).unwrap(), 1);

        child_1.assign("a".to_string(), 2, 1).unwrap();
        assert_eq!(shared_parent_env.lookup("a".to_string(), 0).unwrap(), 2);
        child_2.assign("a".to_string(), 3, 1).unwrap();
        assert_eq!(shared_parent_env.lookup("a".to_string(), 0).unwrap(), 3);
    }
}
