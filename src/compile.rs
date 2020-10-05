use crate::ast::{ASTNode, Pair};
use crate::buffer::Buffer;
use crate::emit::{
    Condition, Emit, Indirect, Register, RegisterPiece, FUNCTION_EPILOGUE, FUNCTION_PROLOGUE,
};
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

macro_rules! impl_from_error {
    ($typ:ty, $variant:path) => {
        impl From<$typ> for Error {
            fn from(e: $typ) -> Error {
                $variant(e)
            }
        }
    };
}

impl_from_error!(std::io::Error, Error::IOError);
impl_from_error!(object::Error, Error::ObjectError);
impl_from_error!(TryFromIntError, Error::ConversionError);
impl_from_error!(String, Error::NotImplemented);

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

    pub(crate) fn compile_expr(&mut self, node: &ASTNode, stack_index: isize) -> Result<(), Error> {
        match node {
            ASTNode::Integer(w) => self
                .emit
                .mov_reg_imm32(Register::RAX, object::encode_integer(*w)?.try_into()?),
            ASTNode::Char(c) => self
                .emit
                .mov_reg_imm32(Register::RAX, object::encode_char(*c) as i32),
            ASTNode::Bool(b) => self
                .emit
                .mov_reg_imm32(Register::RAX, object::encode_bool(*b) as i32),
            ASTNode::Nil => self.emit.mov_reg_imm32(Register::RAX, object::nil() as i32),
            ASTNode::Pair(p) => Ok(self.compile_call(&*p, stack_index)?),
            _ => unimplemented!(),
        }?;
        Ok(())
    }

    pub(crate) fn compile_function(&mut self, node: &ASTNode) -> Result<(), Error> {
        self.emit.buf_mut().write_slice(FUNCTION_PROLOGUE)?;
        self.compile_expr(node, -(object::WORD_SIZE as isize))?;
        self.emit.buf_mut().write_slice(FUNCTION_EPILOGUE)?;
        Ok(())
    }

    pub(crate) fn compile_call(&mut self, pair: &Pair, stack_index: isize) -> Result<(), Error> {
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
                self.compile_expr(arg, stack_index)?;
                match sym.name() {
                    "add1" => self
                        .emit
                        .add_reg_imm32(Register::RAX, object::encode_integer(1)? as i32)?,
                    "sub1" => self
                        .emit
                        .sub_reg_imm32(Register::RAX, object::encode_integer(1)? as i32)?,
                    "integer->char" => {
                        self.emit.shl_reg_imm8(
                            Register::RAX,
                            (object::CHAR_SHIFT - object::INTEGER_SHIFT) as i8,
                        )?;
                        self.emit
                            .or_reg_imm8(Register::RAX, object::CHAR_TAG as u8)?;
                    }
                    "char->integer" => self.emit.shr_reg_imm8(
                        Register::RAX,
                        (object::CHAR_SHIFT - object::INTEGER_SHIFT) as i8,
                    )?,
                    "nil?" => self.compile_compare_imm32(object::nil() as i32)?,
                    "zero?" => self.compile_compare_imm32(object::encode_integer(0)? as i32)?,
                    "not" => self.compile_compare_imm32(object::encode_bool(false) as i32)?,
                    "integer?" => {
                        self.emit
                            .and_reg_imm8(Register::RAX, object::INTEGER_TAG_MASK as u8)?;
                        self.compile_compare_imm32(object::INTEGER_TAG as i32)?;
                    }
                    "boolean?" => {
                        self.emit
                            .and_reg_imm8(Register::RAX, object::IMMEDIATE_TAG_MASK as u8)?;
                        self.compile_compare_imm32(object::BOOL_TAG as i32)?;
                    }
                    name => return Err(Error::NotImplemented(format!("unary {}", name))),
                }

                Ok(())
            } else if let Pair {
                car: a,
                cdr: ASTNode::Pair(p),
            } = p
            {
                let p: &Pair = p;
                if let Pair {
                    car: b,
                    cdr: ASTNode::Nil,
                } = p
                {
                    self.compile_expr(b, stack_index)?;
                    self.emit
                        .store_reg_indirect(Indirect(Register::RBP, stack_index), Register::RAX)?;
                    self.compile_expr(a, stack_index - object::WORD_SIZE as isize)?;
                    match sym.name() {
                        "+" => self.emit.add_reg_indirect(
                            Register::RAX,
                            Indirect(Register::RBP, stack_index),
                        )?,
                        "-" => self.emit.sub_reg_indirect(
                            Register::RAX,
                            Indirect(Register::RBP, stack_index),
                        )?,
                        "*" => {
                            self.emit
                                .mul_reg_indirect(Indirect(Register::RBP, stack_index))?;
                            // Remove the extra tag (which is now 0b0000)
                            self.emit
                                .shr_reg_imm8(Register::RAX, object::INTEGER_SHIFT as i8)?;
                        }
                        "=" => {
                            self.emit.cmp_reg_indirect(
                                Register::RAX,
                                Indirect(Register::RBP, stack_index),
                            )?;
                            self.emit
                                .mov_reg_imm32(Register::RAX, object::encode_integer(0)? as i32)?;
                            self.emit.setcc_imm8(Condition::Equal, RegisterPiece::Al)?;
                            self.emit
                                .shl_reg_imm8(Register::RAX, object::BOOL_SHIFT as i8)?;
                            self.emit
                                .or_reg_imm8(Register::RAX, object::BOOL_TAG as u8)?;
                        }
                        "<" => {
                            self.emit.cmp_reg_indirect(
                                Register::RAX,
                                Indirect(Register::RBP, stack_index),
                            )?;
                            self.emit
                                .mov_reg_imm32(Register::RAX, object::encode_integer(0)? as i32)?;
                            self.emit.setcc_imm8(Condition::Less, RegisterPiece::Al)?;
                            self.emit
                                .shl_reg_imm8(Register::RAX, object::BOOL_SHIFT as i8)?;
                            self.emit
                                .or_reg_imm8(Register::RAX, object::BOOL_TAG as u8)?;
                        }
                        name => return Err(Error::NotImplemented(format!("binary {}", name))),
                    }

                    Ok(())
                } else {
                    unreachable!("Improper list in AST?");
                }
            } else {
                Err(Error::NotImplemented(
                    "non-unary/binary function calls".to_string(),
                ))
            }
        } else {
            Err(Error::NotImplemented("non-symbol functions".to_string()))
        }
    }

    fn compile_compare_imm32(&mut self, value: i32) -> Result<(), Error> {
        self.emit.cmp_reg_imm32(Register::RAX, value)?;
        self.emit.mov_reg_imm32(Register::RAX, 0)?;
        self.emit.setcc_imm8(Condition::Equal, RegisterPiece::Al)?;
        self.emit
            .shl_reg_imm8(Register::RAX, object::BOOL_SHIFT as i8)?;
        self.emit
            .or_reg_imm8(Register::RAX, object::BOOL_TAG as u8)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result = std::result::Result<(), Box<dyn std::error::Error>>;

    fn assert_function_contents(buf: &[u8], expected: &[u8]) {
        assert!(buf.starts_with(FUNCTION_PROLOGUE));
        assert_eq!(
            &buf[FUNCTION_PROLOGUE.len()..buf.len() - FUNCTION_EPILOGUE.len()],
            expected
        );
        assert!(buf.ends_with(FUNCTION_EPILOGUE));
    }

    #[test]
    fn compile_positive_integer() -> Result {
        let value: object::Word = 123;
        let node = ASTNode::Integer(value);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00];
        assert_function_contents(buf.code(), expected);
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
        let expected = &[0x48, 0xc7, 0xc0, 0x14, 0xfe, 0xff, 0xff];
        assert_function_contents(buf.code(), expected);
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
        let expected = &[0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00];
        assert_function_contents(buf.code(), expected);
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
            ];
            assert_function_contents(buf.code(), expected);
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
        let expected = &[0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00];
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), object::nil().try_into()?);
        Ok(())
    }

    #[test]
    fn compile_unary_add1() -> Result {
        let node = ASTNode::new_unary_call("add1".to_string(), ASTNode::Integer(123));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let expected = &[
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x05, 0x04, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x2d, 0x04, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x48, 0xc7, 0xc0, 0x84, 0x01, 0x00, 0x00, 0x48, 0xc1, 0xe0, 0x06, 0x48, 0x83, 0xc8, 0xf,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00, 0x48, 0xc1, 0xe8, 0x06,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x05, 0x04, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
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
            0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_plus() -> Result {
        let node =
            ASTNode::new_binary_call("+".to_string(), ASTNode::Integer(5), ASTNode::Integer(8));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        let expected: &[u8] = &[
            // 0:  48 c7 c0 20 00 00 00    mov    rax,0x20
            0x48, 0xc7, 0xc0, 0x20, 0x00, 0x00, 0x00,
            // 7:  48 89 45 f8             mov    QWORD PTR [rbp-0x8],rax
            0x48, 0x89, 0x45, 0xf8, // b:  48 c7 c0 14 00 00 00    mov    rax,0x14
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
            // 12: 48 03 45 f8             add    rax,QWORD PTR [rbp-0x8]
            0x48, 0x03, 0x45, 0xf8,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(13)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_plus_nested() -> Result {
        let node = ASTNode::new_binary_call(
            "+".to_string(),
            ASTNode::new_binary_call("+".to_string(), ASTNode::Integer(1), ASTNode::Integer(2)),
            ASTNode::new_binary_call("+".to_string(), ASTNode::Integer(3), ASTNode::Integer(4)),
        );
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        let expected: &[u8] = &[
            // 4:  48 c7 c0 10 00 00 00    mov    rax,0x10
            0x48, 0xc7, 0xc0, 0x10, 0x00, 0x00, 0x00,
            // b:  48 89 45 f8             mov    QWORD PTR [rbp-0x8],rax
            0x48, 0x89, 0x45, 0xf8, // f:  48 c7 c0 0c 00 00 00    mov    rax,0xc
            0x48, 0xc7, 0xc0, 0x0c, 0x00, 0x00, 0x00,
            // 16: 48 03 45 f8             add    rax,QWORD PTR [rbp-0x8]
            0x48, 0x03, 0x45, 0xf8,
            // 1a: 48 89 45 f8             mov    QWORD PTR [rbp-0x8],rax
            0x48, 0x89, 0x45, 0xf8, // 1e: 48 c7 c0 08 00 00 00    mov    rax,0x8
            0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,
            // 25: 48 89 45 f0             mov    QWORD PTR [rbp-0x10],rax
            0x48, 0x89, 0x45, 0xf0, // 29: 48 c7 c0 04 00 00 00    mov    rax,0x4
            0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
            // 30: 48 03 45 f0             add    rax,QWORD PTR [rbp-0x10]
            0x48, 0x03, 0x45, 0xf0,
            // 34: 48 03 45 f8             add    rax,QWORD PTR [rbp-0x8]
            0x48, 0x03, 0x45, 0xf8,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(10)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_minus() -> Result {
        let node =
            ASTNode::new_binary_call("-".to_string(), ASTNode::Integer(5), ASTNode::Integer(8));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        let expected: &[u8] = &[
            // 0:  48 c7 c0 20 00 00 00    mov    rax,0x20
            0x48, 0xc7, 0xc0, 0x20, 0x00, 0x00, 0x00,
            // 7:  48 89 45 f8             mov    QWORD PTR [rbp-0x8],rax
            0x48, 0x89, 0x45, 0xf8, // b:  48 c7 c0 14 00 00 00    mov    rax,0x14
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
            // 12: 48 2b 45 f8             add    rax,QWORD PTR [rbp-0x8]
            0x48, 0x2b, 0x45, 0xf8,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(-3)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_minus_nested() -> Result {
        let node = ASTNode::new_binary_call(
            "-".to_string(),
            ASTNode::new_binary_call("-".to_string(), ASTNode::Integer(5), ASTNode::Integer(1)),
            ASTNode::new_binary_call("-".to_string(), ASTNode::Integer(4), ASTNode::Integer(3)),
        );
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;

        let expected: &[u8] = &[
            // 4:  48 c7 c0 0c 00 00 00    mov    rax,0xc
            0x48, 0xc7, 0xc0, 0x0c, 0x00, 0x00, 0x00,
            // b:  48 89 45 f8             mov    QWORD PTR [rbp-0x8],rax
            0x48, 0x89, 0x45, 0xf8, // f:  48 c7 c0 10 00 00 00    mov    rax,0x10
            0x48, 0xc7, 0xc0, 0x10, 0x00, 0x00, 0x00,
            // 16: 48 2b 45 f8             add    rax,QWORD PTR [rbp-0x8]
            0x48, 0x2b, 0x45, 0xf8,
            // 1a: 48 89 45 f8             mov    QWORD PTR [rbp-0x8],rax
            0x48, 0x89, 0x45, 0xf8, // 1e: 48 c7 c0 04 00 00 00    mov    rax,0x4
            0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
            // 25: 48 89 45 f0             mov    QWORD PTR [rbp-0x10],rax
            0x48, 0x89, 0x45, 0xf0, // 29: 48 c7 c0 14 00 00 00    mov    rax,0x14
            0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
            // 30: 48 2b 45 f0             add    rax,QWORD PTR [rbp-0x10]
            0x48, 0x2b, 0x45, 0xf0,
            // 34: 48 2b 45 f8             add    rax,QWORD PTR [rbp-0x8]
            0x48, 0x2b, 0x45, 0xf8,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(3)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_mul() -> Result {
        let node =
            ASTNode::new_binary_call("*".to_string(), ASTNode::Integer(5), ASTNode::Integer(8));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(40)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_mul_nested() -> Result {
        let node = ASTNode::new_binary_call(
            "*".to_string(),
            ASTNode::new_binary_call("*".to_string(), ASTNode::Integer(1), ASTNode::Integer(2)),
            ASTNode::new_binary_call("*".to_string(), ASTNode::Integer(3), ASTNode::Integer(4)),
        );
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_integer(24)? as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_eq_with_same_address_returns_true() -> Result {
        let node =
            ASTNode::new_binary_call("=".to_string(), ASTNode::Integer(5), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(true) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_eq_with_different_address_returns_false() -> Result {
        let node =
            ASTNode::new_binary_call("=".to_string(), ASTNode::Integer(5), ASTNode::Integer(4));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_lt_with_left_less_than_right_returns_true() -> Result {
        let node =
            ASTNode::new_binary_call("<".to_string(), ASTNode::Integer(-5), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(true) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_lt_with_left_equal_to_right_returns_false() -> Result {
        let node =
            ASTNode::new_binary_call("<".to_string(), ASTNode::Integer(5), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }

    #[test]
    fn compile_binary_lt_with_left_greater_than_right_returns_false() -> Result {
        let node =
            ASTNode::new_binary_call("<".to_string(), ASTNode::Integer(6), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node)?;
        let buf = compiler.finish();
        assert_eq!(
            buf.make_executable()?.exec(),
            object::encode_bool(false) as i32
        );
        Ok(())
    }
}
