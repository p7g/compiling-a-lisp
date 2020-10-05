pub(crate) type Word = i64;
pub(crate) type Uword = u64;
pub(crate) const WORD_SIZE: usize = std::mem::size_of::<Word>();
pub(crate) const BITS_PER_WORD: usize = 8 * WORD_SIZE;

pub(crate) const INTEGER_TAG: usize = 0;
pub(crate) const INTEGER_TAG_MASK: usize = 3;
pub(crate) const INTEGER_SHIFT: usize = 2;
pub(crate) const INTEGER_BITS: usize = BITS_PER_WORD - INTEGER_SHIFT;
pub(crate) const INTEGER_MAX: Word = (1 << (INTEGER_BITS - 1)) - 1;
pub(crate) const INTEGER_MIN: Word = -(1 << (INTEGER_BITS - 1));

pub(crate) const IMMEDIATE_TAG_MASK: usize = 0x3f;

pub(crate) const CHAR_TAG: usize = 0xf;
pub(crate) const CHAR_MASK: usize = 0xff;
pub(crate) const CHAR_SHIFT: usize = 8;

pub(crate) const BOOL_TAG: usize = 0x1f;
pub(crate) const BOOL_MASK: usize = 0x80;
pub(crate) const BOOL_SHIFT: usize = 7;

pub(crate) const PAIR_TAG: usize = 0x1;
pub(crate) const HEAP_TAG_MASK: Uword = 0x7;
pub(crate) const HEAP_PTR_MASK: Uword = !HEAP_TAG_MASK;

pub(crate) const SYMBOL_TAG: usize = 0x5;

#[derive(Debug)]
pub(crate) enum Error {
    IntegerOutOfRange,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

pub(crate) type Result<T> = std::result::Result<T, Error>;

pub(crate) fn encode_integer(value: Word) -> Result<Word> {
    if INTEGER_MIN > value || value > INTEGER_MAX {
        Err(Error::IntegerOutOfRange)
    } else {
        Ok(value << INTEGER_SHIFT)
    }
}

pub(crate) fn decode_integer(value: Word) -> Word {
    (value >> INTEGER_SHIFT) | INTEGER_TAG as Word
}

pub(crate) fn encode_char(value: char) -> Word {
    ((value as Word) << CHAR_SHIFT) | CHAR_TAG as Word
}

pub(crate) fn decode_char(value: Word) -> char {
    ((value >> CHAR_SHIFT) & CHAR_MASK as Word) as u8 as char
}

pub(crate) fn encode_bool(value: bool) -> Word {
    ((if value { 1 } else { 0 } << BOOL_SHIFT) | BOOL_TAG) as Word
}

pub(crate) fn decode_bool(value: Word) -> bool {
    value & BOOL_MASK as Word != 0
}

pub(crate) fn nil() -> Word {
    0x2f
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result = std::result::Result<(), Box<dyn std::error::Error>>;

    #[test]
    fn encode_positive_integer() -> Result {
        assert_eq!(0x0, encode_integer(0)?);
        assert_eq!(0x4, encode_integer(1)?);
        assert_eq!(0x28, encode_integer(10)?);
        Ok(())
    }

    #[test]
    fn encode_negative_integer() -> Result {
        assert_eq!(0x0, encode_integer(0)?);
        assert_eq!(0xfffffffffffffffcu64, encode_integer(-1)? as u64);
        assert_eq!(0xffffffffffffffd8u64, encode_integer(-10)? as u64);
        Ok(())
    }

    #[test]
    fn encode_char() {
        assert_eq!(super::encode_char('\0'), 0xf);
        assert_eq!(super::encode_char('a'), 0x610f);
    }

    #[test]
    fn decode_char() {
        assert_eq!(super::decode_char(0xf), '\0');
        assert_eq!(super::decode_char(0x610f), 'a');
    }

    #[test]
    fn encode_bool() {
        assert_eq!(super::encode_bool(true), 0x9f);
        assert_eq!(super::encode_bool(false), 0x1f);
    }

    #[test]
    fn decode_bool() {
        assert_eq!(super::decode_bool(0x9f), true);
        assert_eq!(super::decode_bool(0x1f), false);
    }
}
