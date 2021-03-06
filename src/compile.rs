use crate::ast::{ASTNode, Pair, Symbol};
use crate::buffer::Buffer;
use crate::emit::{
    Condition, Emit, Indirect, Register, RegisterPiece, FUNCTION_EPILOGUE, FUNCTION_PROLOGUE,
};
use crate::env::Env;
use crate::object::{self, Object};
use std::convert::TryInto;
use std::num::TryFromIntError;

const LABEL_PLACEHOLDER: u32 = 0xdeadbeef;
const HEAP_POINTER: Register = Register::RSI;

#[derive(Debug)]
pub(crate) enum Error {
    ConversionError(TryFromIntError),
    IOError(std::io::Error),
    NotImplemented(String),
    UnboundSymbol(Symbol),
    SyntaxError(String),
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

    pub(crate) fn compile_expr(
        &mut self,
        node: &ASTNode,
        stack_index: isize,
        env: &mut Env,
    ) -> Result<(), Error> {
        match node {
            ASTNode::Integer(w) => self
                .emit
                .mov_reg_imm32(Register::RAX, Object::Integer(*w).encode() as _),
            ASTNode::Char(c) => self
                .emit
                .mov_reg_imm32(Register::RAX, Object::Char(*c).encode() as i32),
            ASTNode::Bool(b) => self
                .emit
                .mov_reg_imm32(Register::RAX, Object::Bool(*b).encode() as i32),
            ASTNode::Nil => self
                .emit
                .mov_reg_imm32(Register::RAX, Object::Nil.encode() as i32),
            ASTNode::Pair(p) => Ok(self.compile_call(&*p, stack_index, env)?),
            ASTNode::Symbol(sym) => Ok(self.compile_symbol(sym, env)?),
        }?;
        Ok(())
    }

    fn compile_symbol(&mut self, sym: &Symbol, env: &mut Env) -> Result<(), Error> {
        if let Some(value) = env.find(sym.name()) {
            self.emit
                .load_reg_indirect(Register::RAX, Indirect(Register::RBP, value as i8))?;
            Ok(())
        } else {
            Err(Error::UnboundSymbol(sym.clone()))
        }
    }

    pub(crate) fn compile_function(&mut self, node: &ASTNode, env: &Env) -> Result<(), Error> {
        self.emit.buf_mut().write_slice(FUNCTION_PROLOGUE)?;
        self.compile_expr(node, -(object::WORD_SIZE as isize), &mut env.extend())?;
        self.emit.buf_mut().write_slice(FUNCTION_EPILOGUE)?;
        Ok(())
    }

    pub(crate) fn compile_call(
        &mut self,
        pair: &Pair,
        stack_index: isize,
        env: &mut Env,
    ) -> Result<(), Error> {
        let items = pair.as_slice();
        let (callable, args) = (items[0], &items[1..]);

        let callable = if let ASTNode::Symbol(sym) = callable {
            sym.name()
        } else {
            return Err(Error::NotImplemented("non-symbol functions".to_string()));
        };

        macro_rules! _n_args {
            ($n:expr, $body:tt) => {
                if args.len() != $n {
                    return Err(Error::NotImplemented(format!(
                        "Can't call {} with {} arguments",
                        callable,
                        args.len()
                    )));
                } else {
                    $body;
                }
            };
        }

        macro_rules! n_args {
            (1, $body:tt) => {
                _n_args!(1, {
                    self.compile_expr(args[0], stack_index, env)?;
                    $body;
                })
            };
            (2, $body:tt) => {
                _n_args!(2, {
                    self.compile_expr(args[1], stack_index, env)?;
                    self.emit.store_reg_indirect(
                        Indirect(Register::RBP, stack_index.try_into().unwrap()),
                        Register::RAX,
                    )?;
                    self.compile_expr(args[0], stack_index - object::WORD_SIZE as isize, env)?;
                    $body;
                })
            };
            ($n:expr, $body:tt) => {
                _n_args!($n, $body)
            };
        }

        match callable {
            "add1" => n_args!(1, {
                self.emit
                    .add_reg_imm32(Register::RAX, Object::Integer(1).encode() as i32)?;
            }),
            "sub1" => n_args!(1, {
                self.emit
                    .sub_reg_imm32(Register::RAX, Object::Integer(1).encode() as i32)?;
            }),
            "integer->char" => n_args!(1, {
                self.emit.shl_reg_imm8(
                    Register::RAX,
                    (object::CHAR_SHIFT - object::INTEGER_SHIFT) as i8,
                )?;
                self.emit
                    .or_reg_imm8(Register::RAX, object::CHAR_TAG as u8)?;
            }),
            "char->integer" => n_args!(1, {
                self.emit.shr_reg_imm8(
                    Register::RAX,
                    (object::CHAR_SHIFT - object::INTEGER_SHIFT) as i8,
                )?;
            }),
            "nil?" => n_args!(1, {
                self.compile_compare_imm32(Object::Nil.encode() as i32)?
            }),
            "zero?" => n_args!(1, {
                self.compile_compare_imm32(Object::Integer(0).encode() as i32)?
            }),
            "not" => n_args!(1, {
                self.compile_compare_imm32(Object::Bool(false).encode() as i32)?
            }),
            "integer?" => n_args!(1, {
                self.emit
                    .and_reg_imm8(Register::RAX, object::INTEGER_TAG_MASK as u8)?;
                self.compile_compare_imm32(object::INTEGER_TAG as i32)?;
            }),
            "boolean?" => n_args!(1, {
                self.emit
                    .and_reg_imm8(Register::RAX, object::IMMEDIATE_TAG_MASK as u8)?;
                self.compile_compare_imm32(object::BOOL_TAG as i32)?;
            }),
            "car" => n_args!(1, {
                self.emit.load_reg_indirect(
                    Register::RAX,
                    Indirect(
                        Register::RAX,
                        object::CAR_OFFSET as i8 - object::PAIR_TAG as i8,
                    ),
                )?;
            }),
            "cdr" => n_args!(1, {
                self.emit.load_reg_indirect(
                    Register::RAX,
                    Indirect(Register::RAX, (object::CDR_OFFSET - object::PAIR_TAG) as i8),
                )?;
            }),

            "+" => n_args!(2, {
                self.emit.add_reg_indirect(
                    Register::RAX,
                    Indirect(Register::RBP, stack_index.try_into().unwrap()),
                )?;
            }),
            "-" => n_args!(2, {
                self.emit.sub_reg_indirect(
                    Register::RAX,
                    Indirect(Register::RBP, stack_index.try_into().unwrap()),
                )?;
            }),
            "*" => n_args!(2, {
                self.emit
                    .mul_reg_indirect(Indirect(Register::RBP, stack_index.try_into().unwrap()))?;
                // Remove the extra tag (which is now 0b0000)
                self.emit
                    .shr_reg_imm8(Register::RAX, object::INTEGER_SHIFT as i8)?;
            }),
            "=" => n_args!(2, {
                self.emit.cmp_reg_indirect(
                    Register::RAX,
                    Indirect(Register::RBP, stack_index.try_into().unwrap()),
                )?;
                self.emit
                    .mov_reg_imm32(Register::RAX, Object::Integer(0).encode() as i32)?;
                self.emit.setcc_imm8(Condition::Equal, RegisterPiece::Al)?;
                self.emit
                    .shl_reg_imm8(Register::RAX, object::BOOL_SHIFT as i8)?;
                self.emit
                    .or_reg_imm8(Register::RAX, object::BOOL_TAG as u8)?;
            }),
            "<" => n_args!(2, {
                self.emit.cmp_reg_indirect(
                    Register::RAX,
                    Indirect(Register::RBP, stack_index.try_into().unwrap()),
                )?;
                self.emit
                    .mov_reg_imm32(Register::RAX, Object::Integer(0).encode() as i32)?;
                self.emit.setcc_imm8(Condition::Less, RegisterPiece::Al)?;
                self.emit
                    .shl_reg_imm8(Register::RAX, object::BOOL_SHIFT as i8)?;
                self.emit
                    .or_reg_imm8(Register::RAX, object::BOOL_TAG as u8)?;
            }),
            "let" => _n_args!(2, {
                self.compile_let(
                    args[0],
                    args[1],
                    stack_index,
                    &mut env.extend(),
                    &mut env.extend(),
                )?;
            }),
            "cons" => _n_args!(2, {
                self.compile_cons(args[0], args[1], stack_index, env)?;
            }),

            "if" => _n_args!(3, {
                self.compile_if(args[0], args[1], args[2], stack_index, env)?;
            }),

            _ => return Err(Error::NotImplemented(format!("Callable {}", callable))),
        }

        Ok(())
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

    fn compile_let(
        &mut self,
        bindings: &ASTNode,
        body: &ASTNode,
        mut stack_index: isize,
        binding_env: &mut Env,
        body_env: &mut Env,
    ) -> Result<(), Error> {
        let syntax_error =
            || Error::SyntaxError("let binding must be (name value) pair".to_string());

        match bindings {
            ASTNode::Nil => self.compile_expr(body, stack_index, body_env),
            mut p @ ASTNode::Pair(..) => {
                loop {
                    let Pair {
                        car: binding,
                        cdr: bindings,
                    }: &Pair = match p {
                        ASTNode::Nil => break,
                        ASTNode::Pair(p) => p,
                        _ => return Err(syntax_error()),
                    };
                    p = bindings;

                    let binding: &Pair = if let ASTNode::Pair(p) = binding {
                        p
                    } else {
                        return Err(syntax_error());
                    };
                    if let Pair {
                        car: ASTNode::Symbol(sym),
                        cdr: ASTNode::Pair(binding_expr_list),
                    } = binding
                    {
                        let binding_expr_list: &Pair = binding_expr_list;
                        if let Pair {
                            car: binding_expr,
                            cdr: ASTNode::Nil,
                        } = binding_expr_list
                        {
                            self.compile_expr(binding_expr, stack_index, binding_env)?;
                            self.emit.store_reg_indirect(
                                Indirect(Register::RBP, stack_index.try_into().unwrap()),
                                Register::RAX,
                            )?;
                            body_env.bind(sym.name().to_string(), stack_index as object::Word);
                            stack_index -= object::WORD_SIZE as isize;
                        } else {
                            return Err(syntax_error());
                        }
                    } else {
                        return Err(syntax_error());
                    }
                }

                self.compile_expr(body, stack_index, body_env)
            }
            _ => Err(syntax_error()),
        }
    }

    fn compile_if(
        &mut self,
        cond: &ASTNode,
        consequent: &ASTNode,
        alternate: &ASTNode,
        stack_index: isize,
        env: &mut Env,
    ) -> Result<(), Error> {
        self.compile_expr(cond, stack_index, env)?;
        self.emit
            .cmp_reg_imm32(Register::RAX, Object::Bool(false).encode() as i32)?;

        let alternate_pos = self.emit.jcc(Condition::Equal, LABEL_PLACEHOLDER as i32)?;
        self.compile_expr(consequent, stack_index, env)?;

        let end_pos = self.emit.jmp(LABEL_PLACEHOLDER as i32)?;
        self.emit.backpatch_imm32(alternate_pos);
        self.compile_expr(alternate, stack_index, env)?;

        self.emit.backpatch_imm32(end_pos);
        Ok(())
    }

    fn compile_cons(
        &mut self,
        car: &ASTNode,
        cdr: &ASTNode,
        stack_index: isize,
        env: &mut Env,
    ) -> Result<(), Error> {
        self.compile_expr(car, stack_index, env)?;
        // the CAR expression is stored on the stack before moving it to the
        // heap in case the CDR expression makes use of the heap.
        self.emit.store_reg_indirect(
            Indirect(Register::RBP, stack_index.try_into().unwrap()),
            Register::RAX,
        )?;
        self.compile_expr(cdr, stack_index - object::WORD_SIZE as isize, env)?;
        self.emit.store_reg_indirect(
            Indirect(HEAP_POINTER, object::CDR_OFFSET as i8),
            Register::RAX,
        )?;
        self.emit.load_reg_indirect(
            Register::RAX,
            Indirect(Register::RBP, stack_index.try_into().unwrap()),
        )?;
        self.emit.store_reg_indirect(
            Indirect(HEAP_POINTER, object::CAR_OFFSET as i8),
            Register::RAX,
        )?;
        self.emit.mov_reg_reg(Register::RAX, HEAP_POINTER)?;
        self.emit
            .or_reg_imm8(Register::RAX, object::PAIR_TAG as u8)?;
        self.emit
            .add_reg_imm32(HEAP_POINTER, object::PAIR_SIZE as i32)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader::read;

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
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00];
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            Object::Integer(value).encode().try_into()?
        );
        Ok(())
    }

    #[test]
    fn compile_negative_integer() -> Result {
        let value: object::Word = -123;
        let node = ASTNode::Integer(value);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0x14, 0xfe, 0xff, 0xff];
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            Object::Integer(value).encode()
        );
        Ok(())
    }

    #[test]
    fn compile_char() -> Result {
        let value = 'a';
        let node = ASTNode::Char(value);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00];
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            Object::Char(value).encode().try_into()?
        );
        Ok(())
    }

    #[test]
    fn compile_bool() -> Result {
        for value in &[true, false] {
            let node = ASTNode::Bool(*value);
            let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
            compiler.compile_function(&node, &mut Env::new())?;
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
                Object::Bool(*value).encode().try_into()?
            );
        }
        Ok(())
    }

    #[test]
    fn compile_nil() -> Result {
        let node = ASTNode::Nil;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        let expected = &[0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00];
        assert_function_contents(buf.code(), expected);
        assert_eq!(
            buf.make_executable()?.exec(),
            Object::Nil.encode().try_into()?
        );
        Ok(())
    }

    #[test]
    fn compile_unary_add1() -> Result {
        let node = ASTNode::new_unary_call("add1".to_string(), ASTNode::Integer(123));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let expected = &[
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x05, 0x04, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(124).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_sub1() -> Result {
        let node = ASTNode::new_unary_call("sub1".to_string(), ASTNode::Integer(123));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        // mov rax, imm(123); sub rax, imm(1); ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x2d, 0x04, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(122).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_integer_to_char() -> Result {
        let node = ASTNode::new_unary_call("integer->char".to_string(), ASTNode::Integer(97));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        // mov rax, imm(97); shl rax, 6; or rax, 0xf, ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0x84, 0x01, 0x00, 0x00, 0x48, 0xc1, 0xe0, 0x06, 0x48, 0x83, 0xc8, 0xf,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), Object::Char('a').encode());
        Ok(())
    }

    #[test]
    fn compile_unary_char_to_integer() -> Result {
        let node = ASTNode::new_unary_call("char->integer".to_string(), ASTNode::Char('a'));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        // mov rax, imm('a'); shr rax, 6; ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00, 0x48, 0xc1, 0xe8, 0x06,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(97).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_add1_nested() -> Result {
        let node = ASTNode::new_unary_call(
            "add1".to_string(),
            ASTNode::new_unary_call("add1".to_string(), ASTNode::Integer(123)),
        );
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        // mov rax, imm(123); add rax, imm(1); add rax, imm(1); ret
        let expected = &[
            0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x05, 0x04, 0x00, 0x00, 0x00, 0x48,
            0x05, 0x04, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(125).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_nilp_with_nil_returns_true() -> Result {
        let node = ASTNode::new_unary_call("nil?".to_string(), ASTNode::Nil);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(true).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_nilp_with_non_nil_returns_false() -> Result {
        let node = ASTNode::new_unary_call("nil?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_zerop_with_zero_returns_true() -> Result {
        let node = ASTNode::new_unary_call("zero?".to_string(), ASTNode::Integer(0));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(true).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_zerop_with_non_zero_returns_false() -> Result {
        let node = ASTNode::new_unary_call("zero?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_not_with_false_returns_true() -> Result {
        let node = ASTNode::new_unary_call("not".to_string(), ASTNode::Bool(false));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(true).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_not_with_non_false_returns_false() -> Result {
        let node = ASTNode::new_unary_call("not".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_integerp_with_integer_returns_true() -> Result {
        let node = ASTNode::new_unary_call("integer?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(true).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_integerp_with_non_integer_returns_false() -> Result {
        let node = ASTNode::new_unary_call("integer?".to_string(), ASTNode::Nil);
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_booleanp_with_boolean_returns_true() -> Result {
        let node = ASTNode::new_unary_call("boolean?".to_string(), ASTNode::Bool(true));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(true).encode());
        Ok(())
    }

    #[test]
    fn compile_unary_booleanp_with_non_boolean_returns_false() -> Result {
        let node = ASTNode::new_unary_call("boolean?".to_string(), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_plus() -> Result {
        let node =
            ASTNode::new_binary_call("+".to_string(), ASTNode::Integer(5), ASTNode::Integer(8));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(13).encode());
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
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(10).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_minus() -> Result {
        let node =
            ASTNode::new_binary_call("-".to_string(), ASTNode::Integer(5), ASTNode::Integer(8));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(-3).encode());
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
        compiler.compile_function(&node, &mut Env::new())?;

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
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(3).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_mul() -> Result {
        let node =
            ASTNode::new_binary_call("*".to_string(), ASTNode::Integer(5), ASTNode::Integer(8));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(40).encode());
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
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(24).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_eq_with_same_address_returns_true() -> Result {
        let node =
            ASTNode::new_binary_call("=".to_string(), ASTNode::Integer(5), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(true).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_eq_with_different_address_returns_false() -> Result {
        let node =
            ASTNode::new_binary_call("=".to_string(), ASTNode::Integer(5), ASTNode::Integer(4));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_lt_with_left_less_than_right_returns_true() -> Result {
        let node =
            ASTNode::new_binary_call("<".to_string(), ASTNode::Integer(-5), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(true).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_lt_with_left_equal_to_right_returns_false() -> Result {
        let node =
            ASTNode::new_binary_call("<".to_string(), ASTNode::Integer(5), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_binary_lt_with_left_greater_than_right_returns_false() -> Result {
        let node =
            ASTNode::new_binary_call("<".to_string(), ASTNode::Integer(6), ASTNode::Integer(5));
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        assert_eq!(buf.make_executable()?.exec(), Object::Bool(false).encode());
        Ok(())
    }

    #[test]
    fn compile_let_with_no_bindings() -> Result {
        let node = read("(let () (+ 1 2))")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let mut exec = compiler.finish().make_executable()?;
        let result = exec.exec();
        assert_eq!(Object::decode(exec.heap(), result.into()), Object::Integer(3));
        Ok(())
    }

    #[test]
    fn compile_let_with_one_binding() -> Result {
        let node = read("(let ((a 1)) (+ a 2))")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let mut exec = compiler.finish().make_executable()?;
        let result = exec.exec();
        assert_eq!(Object::decode(exec.heap(), result.into()), Object::Integer(3));
        Ok(())
    }

    #[test]
    fn compile_let_with_multiple_bindings() -> Result {
        let node = read("(let ((a 1) (b 2)) (+ a b))")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let mut exec = compiler.finish().make_executable()?;
        let result = exec.exec();
        assert_eq!(Object::decode(exec.heap(), result.into()), Object::Integer(3));
        Ok(())
    }

    #[test]
    fn compile_nested_let() -> Result {
        let node = read("(let ((a 1)) (let ((b 2)) (+ a b)))")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let mut exec = compiler.finish().make_executable()?;
        let result = exec.exec();
        assert_eq!(Object::decode(exec.heap(), result.into()), Object::Integer(3));
        Ok(())
    }

    #[test]
    fn compile_let_is_not_let_star() -> Result {
        let node = read("(let ((a 1) (b a)) a)")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        let res = compiler.compile_function(&node, &mut Env::new());
        assert!(res.is_err());
        if let Error::UnboundSymbol(sym) = res.as_ref().unwrap_err() {
            assert_eq!(*sym, Symbol::new("a".to_string()));
        } else {
            res?;
        }
        Ok(())
    }

    #[test]
    fn compile_if_with_true_cond() -> Result {
        let node = read("(if #t 1 2)")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

        // mov rax, 0x9f
        // cmp rax, 0x1f
        // je alternate
        // mov rax, compile(1)
        // jmp end
        // alternate:
        // mov rax, compile(2)
        // end:
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x9f, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00, 0x0f,
            0x84, 0x0c, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00, 0xe9, 0x07,
            0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(1).encode());
        Ok(())
    }

    #[test]
    fn compile_if_with_false_cond() -> Result {
        let node = read("(if #f 1 2)")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;

        // mov rax, 0x1f
        // cmp rax, 0x1f
        // je alternate
        // mov rax, compile(1)
        // jmp end
        // alternate:
        // mov rax, compile(2)
        // end:
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x1f, 0x00, 0x00, 0x00, 0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00, 0x0f,
            0x84, 0x0c, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00, 0xe9, 0x07,
            0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        assert_eq!(buf.make_executable()?.exec(), Object::Integer(2).encode());
        Ok(())
    }

    #[test]
    fn compile_nested_if() -> Result {
        let node = read("(if (< 1 2) (if #f 3 4) 5)")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        assert_eq!(
            compiler.finish().make_executable()?.exec(),
            Object::Integer(4).encode()
        );
        Ok(())
    }

    #[test]
    fn compile_cons() -> Result {
        let node = read("(cons 1 2)")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        // mov rax, 0x2
        // mov [rbp-8], rax
        // mov rax, 0x4
        // mov [rsi+Cdr], rax
        // mov rax, [rbp-8]
        // mov [rsi+Car], rax
        // mov rax, rsi
        // or rax, kPairTag
        // add rsi, 2*kWordSize
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45, 0xf8, 0x48, 0xc7, 0xc0,
            0x08, 0x00, 0x00, 0x00, 0x48, 0x89, 0x46, 0x08, 0x48, 0x8b, 0x45, 0xf8, 0x48, 0x89,
            0x46, 0x00, 0x48, 0x89, 0xf0, 0x48, 0x83, 0xc8, 0x01, 0x48, 0x81, 0xc6, 0x10, 0x00,
            0x00, 0x00,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        let mut exec = buf.make_executable()?;
        let result = exec.exec();
        assert_eq!(
            Object::Pair(Box::new(Object::Integer(1)), Box::new(Object::Integer(2))),
            Object::decode(exec.heap(), result)
        );
        Ok(())
    }

    #[test]
    fn compile_nested_cons() -> Result {
        let node = read("(cons (cons 1 2) (cons 3 4))")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        let buf = compiler.finish();
        let mut exec = buf.make_executable()?;
        let result = exec.exec();

        assert_eq!(
            Object::Pair(
                Box::new(Object::Pair(
                    Box::new(Object::Integer(1)),
                    Box::new(Object::Integer(2)),
                )),
                Box::new(Object::Pair(
                    Box::new(Object::Integer(3)),
                    Box::new(Object::Integer(4)),
                )),
            ),
            Object::decode(exec.heap(), result),
        );

        Ok(())
    }

    #[test]
    fn compile_car() -> Result {
        let node = read("(car (cons 1 2))")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        // mov rax, 0x2
        // mov [rbp-8], rax
        // mov rax, 0x4
        // mov [rsi+Cdr], rax
        // mov rax, [rbp-8]
        // mov [rsi+Car], rax
        // mov rax, rsi
        // or rax, kPairTag
        // add rsi, 2*kWordSize
        // mov rax, [rax-1]
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45, 0xf8, 0x48, 0xc7, 0xc0,
            0x08, 0x00, 0x00, 0x00, 0x48, 0x89, 0x46, 0x08, 0x48, 0x8b, 0x45, 0xf8, 0x48, 0x89,
            0x46, 0x00, 0x48, 0x89, 0xf0, 0x48, 0x83, 0xc8, 0x01, 0x48, 0x81, 0xc6, 0x10, 0x00,
            0x00, 0x00, 0x48, 0x8b, 0x40, 0xff,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        let mut exec = buf.make_executable()?;
        let result = exec.exec();
        assert_eq!(Object::decode(exec.heap(), result), Object::Integer(1));
        Ok(())
    }

    #[test]
    fn compile_cdr() -> Result {
        let node = read("(cdr (cons 1 2))")?;
        let mut compiler = Compiler::new(Emit::new(Buffer::new(10)?));
        compiler.compile_function(&node, &mut Env::new())?;
        // mov rax, 0x2
        // mov [rbp-8], rax
        // mov rax, 0x4
        // mov [rsi+Cdr], rax
        // mov rax, [rbp-8]
        // mov [rsi+Car], rax
        // mov rax, rsi
        // or rax, kPairTag
        // add rsi, 2*kWordSize
        // mov rax, [rax+7]
        let expected: &[u8] = &[
            0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45, 0xf8, 0x48, 0xc7, 0xc0,
            0x08, 0x00, 0x00, 0x00, 0x48, 0x89, 0x46, 0x08, 0x48, 0x8b, 0x45, 0xf8, 0x48, 0x89,
            0x46, 0x00, 0x48, 0x89, 0xf0, 0x48, 0x83, 0xc8, 0x01, 0x48, 0x81, 0xc6, 0x10, 0x00,
            0x00, 0x00, 0x48, 0x8b, 0x40, 0x07,
        ];
        let buf = compiler.finish();
        assert_function_contents(buf.code(), expected);
        let mut exec = buf.make_executable()?;
        let result = exec.exec();
        assert_eq!(Object::decode(exec.heap(), result), Object::Integer(2));
        Ok(())
    }
}
