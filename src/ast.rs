use crate::object;

pub(crate) enum ASTNode {
    Integer(object::Word),
    Char(char),
    Bool(bool),
    Nil,
}
