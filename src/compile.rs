use crate::ast::ASTNode;
use crate::buffer::Buffer;
use crate::emit::{Emit, Register};
use crate::object;
use std::convert::TryInto;
use std::num::TryFromIntError;

#[derive(Debug)]
pub(crate) enum Error {
    ObjectError(object::Error),
    ConversionError(TryFromIntError),
    IOError(std::io::Error),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

pub(crate) struct Compiler {
    emit: Emit,
}

impl Compiler {
    pub(crate) fn new(emit: Emit) -> Self {
        Self { emit }
    }

    pub(crate) fn finish(self) -> Buffer {
        self.emit.finish()
    }

    pub(crate) fn compile_expr(&mut self, node: &ASTNode) -> Result<(), Error> {
        match node {
            ASTNode::Integer(w) => self.emit.mov_reg_imm32(
                Register::RAX,
                object::encode_integer(*w)
                    .map_err(Error::ObjectError)?
                    .try_into()
                    .map_err(Error::ConversionError)?,
            ),
            ASTNode::Char(c) => self.emit.mov_reg_imm32(
                Register::RAX,
                object::encode_char(*c)
                    .try_into()
                    .map_err(Error::ConversionError)?,
            ),
            ASTNode::Bool(b) => self.emit.mov_reg_imm32(
                Register::RAX,
                object::encode_bool(*b)
                    .try_into()
                    .map_err(Error::ConversionError)?,
            ),
            ASTNode::Nil => self.emit.mov_reg_imm32(
                Register::RAX,
                object::nil().try_into().map_err(Error::ConversionError)?,
            ),
        }
        .map_err(Error::IOError)
    }

    pub(crate) fn compile_function(&mut self, node: &ASTNode) -> Result<(), Error> {
        self.compile_expr(node)?;
        self.emit.ret().map_err(Error::IOError)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result = std::result::Result<(), Box<dyn std::error::Error>>;

    #[test]
    fn compile_positive_integer() -> Result {
        let value: object::Word = 123;
        let node = ASTNode::Integer(value);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0xc3];
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(value)?.try_into()?
        );
        Ok(())
    }

    #[test]
    fn compile_negative_integer() -> Result {
        let value: object::Word = -123;
        let node = ASTNode::Integer(value);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0x14, 0xfe, 0xff, 0xff, 0xc3];
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(value)?.try_into()?
        );
        Ok(())
    }

    #[test]
    fn compile_char() -> Result {
        let value = 'a';
        let node = ASTNode::Char(value);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00, 0xc3];
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_char(value).try_into()?
        );
        Ok(())
    }

    #[test]
    fn compile_bool() -> Result {
        for value in &[true, false] {
            let node = ASTNode::Bool(*value);
            let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
            compiler.compile_function(&node)?;
            let buf = compiler.finish();
            let expected = &[
                0x48,
                0xc7,
                0xc0,
                if *value { 0x9f } else { 0x1f },
                0x00,
                0x00,
                0x00,
                0xc3,
            ];
            assert_eq!(expected, buf.code());
            assert_eq!(
                buf.make_executable()?.exec(),
                object::encode_bool(*value).try_into()?
            );
        }
        Ok(())
    }

    #[test]
    fn compile_nil() -> Result {
        let node = ASTNode::Nil;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00, 0xc3];
        assert_eq!(expected, buf.code());
        assert_eq!(buf.make_executable()?.exec(), object::nil().try_into()?);
        Ok(())
    }
}
