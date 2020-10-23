use crate::object;
use std::collections::HashMap;

pub(crate) struct Env<'a> {
    bindings: HashMap<String, object::Word>,
    parent: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    pub(crate) fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    pub(crate) fn bind(&mut self, name: String, value: object::Word) {
        self.bindings.insert(name, value);
    }

    pub(crate) fn find(&self, name: &str) -> Option<object::Word> {
        self.bindings
            .get(name)
            .copied()
            .or_else(|| self.parent.and_then(|p| p.find(name)))
    }

    pub(crate) fn extend(&self) -> Env {
        Env {
            bindings: HashMap::new(),
            parent: Some(self),
        }
    }
}
