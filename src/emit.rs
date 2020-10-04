use crate::buffer::Buffer;

type Result = std::io::Result<()>;

const REX_PREFIX: u8 = 0x48;

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
}

impl Condition {
    fn value(&self) -> u8 {
        use Condition::*;

        match self {
            Overflow => 0,
            NotOverflow => 1,
            Below | Carry | NotAboveOrEqual => 2,
            AboveOrEqual | NotBelow | NotCarry => 3,
            Equal | Zero => 4,
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
}
