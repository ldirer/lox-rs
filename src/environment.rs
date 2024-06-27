use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Environment<T: Clone> {
    // rust book: "interior mutability pattern"
    pub(crate) parent: Option<Rc<RefCell<Environment<T>>>>,
    bindings: HashMap<String, T>,
}

impl<T: Clone> Environment<T> {
    pub fn new(bindings: Option<HashMap<String, T>>) -> Environment<T> {
        Environment {
            parent: None,
            bindings: bindings.unwrap_or(HashMap::new()),
        }
    }
    pub fn define(&mut self, name: String, value: T) {
        // Lox allows redefining a variable
        self.bindings.insert(name, value);
    }

    pub fn assign(&mut self, name: String, value: T) {
        if self.bindings.contains_key(&name) {
            // overwrite existing value
            self.bindings.insert(name, value);
            return;
        }

        match &self.parent {
            None => panic!("variable {name} not defined in current scope"),
            Some(parent_env) => parent_env.borrow_mut().assign(name, value),
        }
    }

    pub fn lookup(&self, name: String) -> T {
        // todo error handling
        if let Some(value) = self.bindings.get(&name) {
            return value.clone();
        }
        match &self.parent {
            None => panic!("oh no lookup failed :o!"),
            Some(parent_env) => parent_env.borrow().lookup(name),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::environment::Environment;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    #[test]
    fn test_lookup() {
        let environment = Environment::<i32>::new(Some(HashMap::from([
            ("a".to_string(), 1),
            ("b".to_string(), 2),
        ])));
        let value = environment.lookup("a".to_string());
        assert_eq!(value, 1)
    }

    #[test]
    fn test_define_and_assign() {
        let mut environment = Environment::<i32>::new(None);
        environment.define("a".to_string(), 1);
        assert_eq!(environment.lookup("a".to_string()), 1);
        // redefine
        environment.define("a".to_string(), 2);
        assert_eq!(environment.lookup("a".to_string()), 2);
        // change value
        environment.assign("a".to_string(), 3);
        assert_eq!(environment.lookup("a".to_string()), 3);
    }

    #[test]
    fn test_assign_variable_from_parent_environment() {
        let root_env = Environment::<i32>::new(Some(HashMap::from([("a".to_string(), 1)])));

        let mut env = Environment::<i32>::new(None);
        env.parent = Some(Rc::new(RefCell::new(root_env)));
        assert_eq!(env.lookup("a".to_string()), 1);

        env.assign("a".to_string(), 2);
        assert_eq!(env.lookup("a".to_string()), 2);
    }

    #[test]
    fn test_multiple_environments_one_parent_does_not_panic() {
        let root_env = Environment::<i32>::new(Some(HashMap::from([("a".to_string(), 1)])));
        let mut child_1 = Environment::<i32>::new(None);
        let mut child_2 = Environment::<i32>::new(None);
        let shared_parent_env = Rc::new(RefCell::new(root_env));
        child_1.parent = Some(shared_parent_env.clone());
        child_2.parent = Some(shared_parent_env.clone());

        assert_eq!(child_1.lookup("a".to_string()), 1);
        assert_eq!(child_2.lookup("a".to_string()), 1);

        child_1.assign("a".to_string(), 2);
        assert_eq!(shared_parent_env.borrow().lookup("a".to_string()), 2);
        child_2.assign("a".to_string(), 3);
        assert_eq!(shared_parent_env.borrow().lookup("a".to_string()), 3);
    }
}
