use crate::buffer::Buffer;

type Result = std::io::Result<()>;

const REX_PREFIX: u8 = 0x48;

pub(crate) const FUNCTION_PROLOGUE: &[u8] = &[
    // Save the heap (first argument) in rsi, our global heap pointer
    REX_PREFIX, 0x89, 0xfe, // mov rsi, rdi
    0x55, // push rbp
    REX_PREFIX, 0x89, 0xe5, // mov rbp, rsp
];

pub(crate) const FUNCTION_EPILOGUE: &[u8] = &[
    0x5d, // pop rbp
    0xc3, // ret
];

#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum Register {
    RAX = 0,
    RCX,
    RDX,
    RBX,
    RSP,
    RBP,
    RSI,
    RDI,
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub(crate) enum RegisterPiece {
    Al = 0,
    Cl,
    Dl,
    Bl,
    Ah,
    Ch,
    Dh,
    Bh,
}

#[derive(Clone, Copy)]
pub(crate) enum Condition {
    Overflow,
    NotOverflow,
    Below,
    Carry,
    NotAboveOrEqual,
    AboveOrEqual,
    NotBelow,
    NotCarry,
    Equal,
    Zero,
    Less,
}

impl Condition {
    fn value(self) -> u8 {
        use Condition::*;

        match self {
            Overflow => 0,
            NotOverflow => 1,
            Below | Carry | NotAboveOrEqual => 2,
            AboveOrEqual | NotBelow | NotCarry => 3,
            Equal | Zero => 4,
            Less => 0xc,
        }
    }
}

fn disp32(disp: i32) -> u32 {
    if disp >= 0 {
        disp as u32
    } else {
        (0x100000000 + disp as i64) as u32
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Indirect(pub(crate) Register, pub(crate) i8);

impl Indirect {
    fn offset(&self) -> u8 {
        if self.1 >= 0 {
            self.1 as u8
        } else {
            (0x100 + self.1 as i16) as u8
        }
    }
}

pub(crate) struct Emit {
    buf: Buffer,
}

impl Emit {
    pub(crate) fn new(buf: Buffer) -> Self {
        Self { buf }
    }

    pub(crate) fn finish(self) -> Buffer {
        self.buf
    }

    pub(crate) fn buf_mut(&mut self) -> &mut Buffer {
        &mut self.buf
    }

    pub(crate) fn mov_reg_imm32(&mut self, dst: Register, src: i32) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0xc7)?;
        self.buf.write_8(0xc0 + dst as u8)?;
        self.buf.write_32(src)?;
        Ok(())
    }

    pub(crate) fn add_reg_imm32(&mut self, dst: Register, src: i32) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        // add eax, {imm32} can be encoded as 0x05
        if let Register::RAX = dst {
            self.buf.write_8(0x05)?;
        } else {
            self.buf.write_8(0x81)?;
            self.buf.write_8(0xc0 + dst as u8)?;
        }
        self.buf.write_32(src)
    }

    pub(crate) fn sub_reg_imm32(&mut self, dst: Register, src: i32) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        // sub eax, {imm32} can be encoded as 0x2d
        if let Register::RAX = dst {
            self.buf.write_8(0x2d)?;
        } else {
            self.buf.write_8(0x81)?;
            self.buf.write_8(0xe8 + dst as u8)?;
        }
        self.buf.write_32(src)
    }

    pub(crate) fn shl_reg_imm8(&mut self, dst: Register, bits: i8) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0xc1)?;
        self.buf.write_8(0xe0 + dst as u8)?;
        self.buf.write_8(bits as u8)
    }

    pub(crate) fn shr_reg_imm8(&mut self, dst: Register, bits: i8) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0xc1)?;
        self.buf.write_8(0xe8 + dst as u8)?;
        self.buf.write_8(bits as u8)
    }

    pub(crate) fn or_reg_imm8(&mut self, dst: Register, tag: u8) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x83)?;
        self.buf.write_8(0xc8 + dst as u8)?;
        self.buf.write_8(tag)
    }

    pub(crate) fn and_reg_imm8(&mut self, dst: Register, tag: u8) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x83)?;
        self.buf.write_8(0xe0 + dst as u8)?;
        self.buf.write_8(tag)
    }

    pub(crate) fn cmp_reg_imm32(&mut self, left: Register, right: i32) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        // cmp rax, {imm32} can be encoded as 3d
        if let Register::RAX = left {
            self.buf.write_8(0x3d)?;
        } else {
            self.buf.write_8(0x81)?;
            self.buf.write_8(0xf8 + left as u8)?;
        }
        self.buf.write_32(right)
    }

    pub(crate) fn setcc_imm8(&mut self, cond: Condition, dst: RegisterPiece) -> Result {
        self.buf.write_8(0x0f)?;
        self.buf.write_8(0x90 + cond.value())?;
        self.buf.write_8(0xc0 + dst as u8)
    }

    pub(crate) fn ret(&mut self) -> std::io::Result<()> {
        self.buf.write_8(0xc3)
    }

    pub(crate) fn store_reg_indirect(&mut self, dst: Indirect, src: Register) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x89)?;
        self.buf.write_8(0x40 + src as u8 * 8 + dst.0 as u8)?;
        self.buf.write_8(dst.offset())
    }

    pub(crate) fn add_reg_indirect(&mut self, dst: Register, src: Indirect) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x03)?;
        self.buf.write_8(0x40 + dst as u8 * 8 + src.0 as u8)?;
        self.buf.write_8(src.offset())
    }

    pub(crate) fn sub_reg_indirect(&mut self, dst: Register, src: Indirect) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x2b)?;
        self.buf.write_8(0x40 + dst as u8 * 8 + src.0 as u8)?;
        self.buf.write_8(src.offset())
    }

    pub(crate) fn mul_reg_indirect(&mut self, src: Indirect) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0xf7)?;
        self.buf.write_8(0x60 + src.0 as u8)?;
        self.buf.write_8(src.offset())
    }

    pub(crate) fn cmp_reg_indirect(&mut self, left: Register, right: Indirect) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x3b)?;
        self.buf.write_8(0x40 + left as u8 * 8 + right.0 as u8)?;
        self.buf.write_8(right.offset())
    }

    pub(crate) fn load_reg_indirect(&mut self, dst: Register, src: Indirect) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x8b)?;
        self.buf.write_8(0x40 + dst as u8 * 8 + src.0 as u8)?;
        self.buf.write_8(src.offset())
    }

    pub(crate) fn jcc(&mut self, cond: Condition, offset: i32) -> std::io::Result<i32> {
        self.buf.write_8(0x0f)?;
        self.buf.write_8(0x80 + cond.value())?;
        let pos = self.buf.code().len();
        self.buf.write_32(disp32(offset) as i32)?;
        Ok(pos as i32)
    }

    pub(crate) fn jmp(&mut self, offset: i32) -> std::io::Result<i32> {
        self.buf.write_8(0xe9)?;
        let pos = self.buf.code().len();
        self.buf.write_32(disp32(offset) as i32)?;
        Ok(pos as i32)
    }

    pub(crate) fn backpatch_imm32(&mut self, target_pos: i32) {
        let current_pos = self.buf.code().len() as i32;
        let relative_pos = current_pos - target_pos - std::mem::size_of::<i32>() as i32;
        self.buf.put_32(target_pos as usize, disp32(relative_pos));
    }

    pub(crate) fn mov_reg_reg(&mut self, dst: Register, src: Register) -> Result {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0x89)?;
        self.buf.write_8(0xc0 + src as u8 * 8 + dst as u8)
    }
}
