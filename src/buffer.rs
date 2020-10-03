use crate::exec::Exec;
use memmap::{Mmap, MmapMut};

pub(crate) struct Buffer {
    pos: usize,
    mem: MmapMut,
}

impl Buffer {
    pub(crate) fn new(capacity: usize) -> std::io::Result<Self> {
        Ok(Self {
            pos: 0,
            mem: MmapMut::map_anon(capacity)?,
        })
    }

    pub(crate) fn code(&self) -> &[u8] {
        &self.mem[..self.pos]
    }

    pub(crate) fn make_executable(self) -> std::io::Result<Exec> {
        Ok(Exec::new(self.mem.make_exec()?))
    }

    fn ensure_capacity(&mut self, additional_capacity: usize) -> std::io::Result<()> {
        if self.pos + additional_capacity <= self.mem.len() {
            return Ok(());
        }
        let new_cap = usize::max(self.mem.len() + additional_capacity, self.mem.len() * 2);
        let mut new_map = MmapMut::map_anon(new_cap)?;
        new_map[..self.mem.len()].copy_from_slice(&*self.mem);
        self.mem = new_map;

        Ok(())
    }

    pub(crate) fn get_8(&self, i: usize) -> u8 {
        self.mem[i]
    }

    pub(crate) fn write_8(&mut self, b: u8) -> std::io::Result<()> {
        self.ensure_capacity(1)?;
        self.mem[self.pos] = b;
        self.pos += 1;
        Ok(())
    }

    pub(crate) fn write_32(&mut self, value: i32) -> std::io::Result<()> {
        self.ensure_capacity(4)?;
        for b in value.to_le_bytes().iter() {
            self.write_8(*b)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result = std::result::Result<(), Box<dyn std::error::Error>>;

    #[test]
    fn write_8_increases_length() -> Result {
        let mut buf = Buffer::new(5)?;
        assert_eq!(buf.pos, 0);
        buf.write_8(0xdb)?;
        assert_eq!(buf.get_8(0), 0xdb);
        assert_eq!(buf.pos, 1);
        Ok(())
    }

    #[test]
    fn write_8_expands_buffer() -> Result {
        let mut buf = Buffer::new(1)?;
        assert_eq!(buf.mem.len(), 1);
        assert_eq!(buf.pos, 0);
        buf.write_8(0xdb)?;
        buf.write_8(0xef)?;
        assert!(buf.mem.len() > 1);
        assert_eq!(buf.pos, 2);
        Ok(())
    }

    #[test]
    fn write_32_expands_buffer() -> Result {
        let mut buf = Buffer::new(1)?;
        assert_eq!(buf.mem.len(), 1);
        assert_eq!(buf.pos, 0);
        buf.write_32(0xdeadbeefu32 as i32)?;
        assert!(buf.mem.len() > 1);
        assert_eq!(buf.pos, 4);
        Ok(())
    }

    #[test]
    fn write_32_writes_little_endian() -> Result {
        let mut buf = Buffer::new(4)?;
        buf.write_32(0xdeadbeefu32 as i32)?;
        assert_eq!(buf.get_8(0), 0xef);
        assert_eq!(buf.get_8(1), 0xbe);
        assert_eq!(buf.get_8(2), 0xad);
        assert_eq!(buf.get_8(3), 0xde);
        Ok(())
    }
}
