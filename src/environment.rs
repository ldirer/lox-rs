use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

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

    pub fn assign(&self, name: String, value: T, depth: usize) {
        if depth == 0 {
            if self.bindings.borrow().contains_key(&name) {
                // overwrite existing value
                self.bindings.borrow_mut().insert(name, value);
                return;
            }
            panic!("variable {name} not defined in current scope");
        }

        match &self.parent {
            None => unreachable!("assign failed for {name}! Implementation bug, we should have a parent or depth should be zero (not {depth})"),
            Some(parent_env) => parent_env.assign(name, value, depth - 1),
        }
    }

    pub fn lookup(&self, name: String, depth: usize) -> T {
        // todo error handling
        if depth == 0 {
            if let Some(value) = self.bindings.borrow().get(&name) {
                return value.clone();
            }
            panic!(
                "oh no lookup failed :o! Variable {} not found in scope. \nHere's all we got: {:#?}",
                name,
                self.bindings.borrow().keys()
            );
        }

        match &self.parent {
            None => {
                eprintln!("Here's what we got: {:#?}", self.bindings.borrow().keys());
                unreachable!("lookup failed for {name}! Implementation bug, we should have a parent or depth should be zero (not {depth})")
            }
            Some(parent_env) => parent_env.lookup(name, depth - 1),
        }
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
        let value = environment.lookup("a".to_string(), 0);
        assert_eq!(value, 1)
    }

    #[test]
    fn test_define_and_assign() {
        let environment = Environment::<i32>::new(None);
        environment.define("a".to_string(), 1);
        assert_eq!(environment.lookup("a".to_string(), 0), 1);
        // change value
        environment.assign("a".to_string(), 3, 0);
        assert_eq!(environment.lookup("a".to_string(), 0), 3);
    }

    #[test]
    fn test_redefine_global() {
        let environment = Environment::<i32>::new(None);
        environment.define("a".to_string(), 1);
        assert_eq!(environment.lookup("a".to_string(), 0), 1);
        // redefine
        environment.define("a".to_string(), 2);
        assert_eq!(environment.lookup("a".to_string(), 0), 2);
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
        assert_eq!(env.lookup("a".to_string(), 1), 1);

        env.assign("a".to_string(), 2, 1);
        assert_eq!(env.lookup("a".to_string(), 1), 2);
    }

    #[test]
    fn test_multiple_environments_one_parent_does_not_panic() {
        let root_env = Environment::<i32>::new(Some(HashMap::from([("a".to_string(), 1)])));
        let mut child_1 = Environment::<i32>::new(None);
        let mut child_2 = Environment::<i32>::new(None);
        let shared_parent_env = Rc::new(root_env);
        child_1.parent = Some(shared_parent_env.clone());
        child_2.parent = Some(shared_parent_env.clone());

        assert_eq!(child_1.lookup("a".to_string(), 1), 1);
        assert_eq!(child_2.lookup("a".to_string(), 1), 1);

        child_1.assign("a".to_string(), 2, 1);
        assert_eq!(shared_parent_env.lookup("a".to_string(), 0), 2);
        child_2.assign("a".to_string(), 3, 1);
        assert_eq!(shared_parent_env.lookup("a".to_string(), 0), 3);
    }
}
