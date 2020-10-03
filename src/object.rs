pub(crate) type Word = i64;
pub(crate) type Uword = u64;
const BITS_PER_WORD: usize = 8 * std::mem::size_of::<Word>();

const INTEGER_TAG: usize = 0;
const INTEGER_TAG_MASK: usize = 3;
const INTEGER_SHIFT: usize = 2;
const INTEGER_BITS: usize = BITS_PER_WORD - INTEGER_SHIFT;
pub(crate) const INTEGER_MAX: Word = (1 << (INTEGER_BITS - 1)) - 1;
pub(crate) const INTEGER_MIN: Word = -(1 << (INTEGER_BITS - 1));

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
}
