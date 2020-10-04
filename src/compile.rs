use crate::ast::{ASTNode, Pair};
use crate::buffer::Buffer;
use crate::emit::{Condition, Emit, Register, RegisterPiece};
use crate::object;
use std::convert::TryInto;
use std::num::TryFromIntError;

#[derive(Debug)]
pub(crate) enum Error {
    ObjectError(object::Error),
    ConversionError(TryFromIntError),
    IOError(std::io::Error),
    NotImplemented(String),
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
            ASTNode::Char(c) => self
                .emit
                .mov_reg_imm32(Register::RAX, object::encode_char(*c) as i32),
            ASTNode::Bool(b) => self
                .emit
                .mov_reg_imm32(Register::RAX, object::encode_bool(*b) as i32),
            ASTNode::Nil => self.emit.mov_reg_imm32(Register::RAX, object::nil() as i32),
            ASTNode::Pair(p) => Ok(self.compile_call(&*p)?),
            _ => unimplemented!(),
        }
        .map_err(Error::IOError)
    }

    pub(crate) fn compile_function(&mut self, node: &ASTNode) -> Result<(), Error> {
        self.compile_expr(node)?;
        self.emit.ret().map_err(Error::IOError)?;
        Ok(())
    }

    pub(crate) fn compile_call(&mut self, pair: &Pair) -> Result<(), Error> {
        let Pair {
            car: callable,
            cdr: args,
        } = pair;
        if let (ASTNode::Symbol(sym), ASTNode::Pair(p)) = (callable, args) {
            let p: &Pair = p;
            if let Pair {
                car: arg,
                cdr: ASTNode::Nil,
            } = p
            {
                match sym.name() {
                    "add1" => {
                        self.compile_expr(arg)?;
                        self.emit
                            .add_reg_imm32(
                                Register::RAX,
                                object::encode_integer(1).map_err(Error::ObjectError)? as i32,
                            )
                            .map_err(Error::IOError)?;
                    }
                    "sub1" => {
                        self.compile_expr(arg)?;
                        self.emit
                            .sub_reg_imm32(
                                Register::RAX,
                                object::encode_integer(1).map_err(Error::ObjectError)? as i32,
                            )
                            .map_err(Error::IOError)?;
                    }
                    "integer->char" => {
                        self.compile_expr(arg)?;
                        self.emit
                            .shl_reg_imm8(
                                Register::RAX,
                                (object::CHAR_SHIFT - object::INTEGER_SHIFT) as i8,
                            )
                            .map_err(Error::IOError)?;
                        self.emit
                            .or_reg_imm8(Register::RAX, object::CHAR_TAG as u8)
                            .map_err(Error::IOError)?;
                    }
                    "char->integer" => {
                        self.compile_expr(arg)?;
                        self.emit
                            .shr_reg_imm8(
                                Register::RAX,
                                (object::CHAR_SHIFT - object::INTEGER_SHIFT) as i8,
                            )
                            .map_err(Error::IOError)?;
                    }
                    "nil?" => {
                        self.compile_expr(arg)?;
                        self.compile_compare_imm32(object::nil() as i32)?;
                    }
                    "zero?" => {
                        self.compile_expr(arg)?;
                        self.compile_compare_imm32(
                            object::encode_integer(0).map_err(Error::ObjectError)? as i32,
                        )?;
                    }
                    "not" => {
                        self.compile_expr(arg)?;
                        self.compile_compare_imm32(object::encode_bool(false) as i32)?;
                    }
                    "integer?" => {
                        self.compile_expr(arg)?;
                        self.emit
                            .and_reg_imm8(Register::RAX, object::INTEGER_TAG_MASK as u8)
                            .map_err(Error::IOError)?;
                        self.compile_compare_imm32(object::INTEGER_TAG as i32)?;
                    }
                    "boolean?" => {
                        self.compile_expr(arg)?;
                        self.emit
                            .and_reg_imm8(Register::RAX, object::IMMEDIATE_TAG_MASK as u8)
                            .map_err(Error::IOError)?;
                        self.compile_compare_imm32(object::BOOL_TAG as i32)?;
                    }
                    name => return Err(Error::NotImplemented(name.to_string())),
                }

                Ok(())
            } else {
                Err(Error::NotImplemented(
                    "non-unary function calls".to_string(),
                ))
            }
        } else {
            Err(Error::NotImplemented("non-symbol functions".to_string()))
        }
    }

    fn compile_compare_imm32(&mut self, value: i32) -> Result<(), Error> {
        self.emit
            .cmp_reg_imm32(Register::RAX, value)
            .map_err(Error::IOError)?;
        self.emit
            .mov_reg_imm32(Register::RAX, 0)
            .map_err(Error::IOError)?;
        self.emit
            .setcc_imm8(Condition::Equal, RegisterPiece::Al)
            .map_err(Error::IOError)?;
        self.emit
            .shl_reg_imm8(Register::RAX, object::BOOL_SHIFT as i8)
            .map_err(Error::IOError)?;
        self.emit
            .or_reg_imm8(Register::RAX, object::BOOL_TAG as u8)
            .map_err(Error::IOError)
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

    #[test]
    fn compile_unary_add1() -> Result {
        let node = ASTNode::new_unary_call("add1".to_string(), ASTNode::Integer(123));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let expected = &[
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x05, 0x04, 0x00, 0x00, 0x00, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(124)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_sub1() -> Result {
        let node = ASTNode::new_unary_call("sub1".to_string(), ASTNode::Integer(123));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        // mov rax, imm(123); sub rax, imm(1); ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x2d, 0x04, 0x00, 0x00, 0x00, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(122)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_integer_to_char() -> Result {
        let node = ASTNode::new_unary_call("integer->char".to_string(), ASTNode::Integer(97));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        // mov rax, imm(97); shl rax, 6; or rax, 0xf, ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0x84, 0x01, 0x00, 0x00, 0x48, 0xc1, 0xe0, 0x06, 0x48, 0x83, 0xc8,
            0xf, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_char('a') as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_char_to_integer() -> Result {
        let node = ASTNode::new_unary_call("char->integer".to_string(), ASTNode::Char('a'));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        // mov rax, imm('a'); shr rax, 6; ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00, 0x48, 0xc1, 0xe8, 0x06, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(97)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_add1_nested() -> Result {
        let node = ASTNode::new_unary_call(
            "add1".to_string(),
            ASTNode::new_unary_call("add1".to_string(), ASTNode::Integer(123)),
        );
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        // mov rax, imm(123); add rax, imm(1); add rax, imm(1); ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x05, 0x04, 0x00, 0x00, 0x00, 0x48,
            0x05, 0x04, 0x00, 0x00, 0x00, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(125)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_nilp_with_nil_returns_true() -> Result {
        let node = ASTNode::new_unary_call("nil?".to_string(), ASTNode::Nil);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 2f 00 00 00    mov    rax,0x2f
        // 7:  48 3d 2f 00 00 00       cmp    rax,0x0000002f
        // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
        // 14: 0f 94 c0                sete   al
        // 17: 48 c1 e0 07             shl    rax,0x7
        // 1b: 48 83 c8 1f             or     rax,0x1f
        let expected = &[
            0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x2f, 0x00, 0x00, 0x00, 0x48,
            0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48, 0xc1, 0xe0, 0x07, 0x48,
            0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(true) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_nilp_with_non_nil_returns_false() -> Result {
        let node = ASTNode::new_unary_call("nil?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
        // 7:  48 3d 2f 00 00 00       cmp    rax,0x0000002f
        // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
        // 14: 0f 94 c0                sete   al
        // 17: 48 c1 e0 07             shl    rax,0x7
        // 1b: 48 83 c8 1f             or     rax,0x1f
        let expected = &[
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x2f, 0x00, 0x00, 0x00, 0x48,
            0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48, 0xc1, 0xe0, 0x07, 0x48,
            0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_zerop_with_zero_returns_true() -> Result {
        let node = ASTNode::new_unary_call("zero?".to_string(), ASTNode::Integer(0));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 00 00 00 00    mov    rax,0x0
        // 7:  48 3d 00 00 00 00       cmp    rax,0x00000000
        // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
        // 14: 0f 94 c0                sete   al
        // 17: 48 c1 e0 07             shl    rax,0x7
        // 1b: 48 83 c8 1f             or     rax,0x1f
        let expected = &[
            0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x00, 0x00, 0x00, 0x00, 0x48,
            0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48, 0xc1, 0xe0, 0x07, 0x48,
            0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(true) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_zerop_with_non_zero_returns_false() -> Result {
        let node = ASTNode::new_unary_call("zero?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
        // 7:  48 3d 00 00 00 00       cmp    rax,0x00000000
        // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
        // 14: 0f 94 c0                sete   al
        // 17: 48 c1 e0 07             shl    rax,0x7
        // 1b: 48 83 c8 1f             or     rax,0x1f
        let expected = &[
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x00, 0x00, 0x00, 0x00, 0x48,
            0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48, 0xc1, 0xe0, 0x07, 0x48,
            0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_not_with_false_returns_true() -> Result {
        let node = ASTNode::new_unary_call("not".to_string(), ASTNode::Bool(false));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 1f 00 00 00    mov    rax,0x1f
        // 7:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
        // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
        // 14: 0f 94 c0                sete   al
        // 17: 48 c1 e0 07             shl    rax,0x7
        // 1b: 48 83 c8 1f             or     rax,0x1f
        let expected = &[
            0x48, 0xc7, 0xc0, 0x1f, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00, 0x48,
            0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48, 0xc1, 0xe0, 0x07, 0x48,
            0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(true) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_not_with_non_false_returns_false() -> Result {
        let node = ASTNode::new_unary_call("not".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
        // 7:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
        // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
        // 14: 0f 94 c0                sete   al
        // 17: 48 c1 e0 07             shl    rax,0x7
        // 1b: 48 83 c8 1f             or     rax,0x1f
        let expected = &[
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00, 0x48,
            0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48, 0xc1, 0xe0, 0x07, 0x48,
            0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_integerp_with_integer_returns_true() -> Result {
        let node = ASTNode::new_unary_call("integer?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
        // 7:  48 83 e0 03             and    rax,0x3
        // b:  48 3d 00 00 00 00       cmp    rax,0x00000000
        // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
        // 18: 0f 94 c0                sete   al
        // 1b: 48 c1 e0 07             shl    rax,0x7
        // 1f: 48 83 c8 1f             or     rax,0x1f
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48, 0x83, 0xe0, 0x03, 0x48, 0x3d, 0x00,
            0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(true) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_integerp_with_non_integer_returns_false() -> Result {
        let node = ASTNode::new_unary_call("integer?".to_string(), ASTNode::Nil);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 2f 00 00 00    mov    rax,0x2f
        // 7:  48 83 e0 03             and    rax,0x3
        // b:  48 3d 00 00 00 00       cmp    rax,0x00000000
        // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
        // 18: 0f 94 c0                sete   al
        // 1b: 48 c1 e0 07             shl    rax,0x7
        // 1f: 48 83 c8 1f             or     rax,0x1f
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00, 0x48, 0x83, 0xe0, 0x03, 0x48, 0x3d, 0x00,
            0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_booleanp_with_boolean_returns_true() -> Result {
        let node = ASTNode::new_unary_call("boolean?".to_string(), ASTNode::Bool(true));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 9f 00 00 00    mov    rax,0x9f
        // 7:  48 83 e0 1f             and    rax,0x3f
        // b:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
        // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
        // 18: 0f 94 c0                sete   al
        // 1b: 48 c1 e0 07             shl    rax,0x7
        // 1f: 48 83 c8 1f             or     rax,0x1f
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x9f, 0x00, 0x00, 0x00, 0x48, 0x83, 0xe0, 0x3f, 0x48, 0x3d, 0x1f,
            0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(true) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_unary_booleanp_with_non_boolean_returns_false() -> Result {
        let node = ASTNode::new_unary_call("boolean?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
        // 7:  48 83 e0 3f             and    rax,0x3f
        // b:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
        // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
        // 18: 0f 94 c0                sete   al
        // 1b: 48 c1 e0 07             shl    rax,0x7
        // 1f: 48 83 c8 1f             or     rax,0x1f
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48, 0x83, 0xe0, 0x3f, 0x48, 0x3d, 0x1f,
            0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f, 0xc3,
        ];
        let buf = compiler.finish();
        assert_eq!(expected, buf.code());
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }
}
