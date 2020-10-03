use crate::buffer::Buffer;

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

    pub(crate) fn mov_reg_imm32(&mut self, dst: Register, src: i32) -> std::io::Result<()> {
        self.buf.write_8(REX_PREFIX)?;
        self.buf.write_8(0xc7)?;
        self.buf.write_8(0xc0 + dst as u8)?;
        self.buf.write_32(src)?;
        Ok(())
    }

    pub(crate) fn ret(&mut self) -> std::io::Result<()> {
        self.buf.write_8(0xc3)
    }
}
