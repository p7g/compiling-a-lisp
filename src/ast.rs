use crate::object;

#[derive(Debug, PartialEq)]
pub(crate) enum ASTNode {
    Integer(object::Word),
    Char(char),
    Bool(bool),
    Nil,
    Pair(Box<Pair>),
    Symbol(Symbol),
}

impl ASTNode {
    pub(crate) fn list1(item0: ASTNode) -> Self {
        Self::Pair(Box::new(Pair::new(item0, Self::Nil)))
    }

    pub(crate) fn list2(item0: ASTNode, item1: ASTNode) -> Self {
        Self::Pair(Box::new(Pair::new(item0, Self::list1(item1))))
    }

    pub(crate) fn new_unary_call(name: String, arg: ASTNode) -> Self {
        Self::list2(Self::Symbol(Symbol::new(name)), arg)
    }

    pub(crate) fn new_binary_call(name: String, arg1: ASTNode, arg2: ASTNode) -> Self {
        Self::Pair(Box::new(Pair::new(
            Self::Symbol(Symbol::new(name)),
            Self::list2(arg1, arg2),
        )))
    }
}

#[derive(Debug, PartialEq)]
pub(crate) struct Pair {
    pub(crate) car: ASTNode,
    pub(crate) cdr: ASTNode,
}

impl Pair {
    pub(crate) fn new(car: ASTNode, cdr: ASTNode) -> Self {
        Self { car, cdr }
    }
}

#[derive(Debug, PartialEq)]
pub(crate) struct Symbol(String);

impl Symbol {
    pub(crate) fn new(sym: String) -> Self {
        Self(sym)
    }

    pub(crate) fn name(&self) -> &str {
        &self.0
    }
}
