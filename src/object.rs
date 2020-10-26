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

pub(crate) const NIL: usize = 0x2f;

pub(crate) const PAIR_TAG: usize = 0x1;
pub(crate) const HEAP_TAG_MASK: Uword = 0x7;
pub(crate) const HEAP_PTR_MASK: Uword = !HEAP_TAG_MASK;

pub(crate) const SYMBOL_TAG: usize = 0x5;

pub(crate) const CAR_INDEX: usize = 0;
pub(crate) const CAR_OFFSET: usize = CAR_INDEX * WORD_SIZE;
pub(crate) const CDR_INDEX: usize = CAR_INDEX + 1;
pub(crate) const CDR_OFFSET: usize = CDR_INDEX * WORD_SIZE;
pub(crate) const PAIR_SIZE: usize = CDR_OFFSET + WORD_SIZE;

#[derive(Debug, PartialEq)]
pub(crate) enum Object {
    Integer(Word),
    Char(char),
    Bool(bool),
    Nil,
    Pair(Box<Object>, Box<Object>),
}

impl Object {
    pub(crate) fn decode(heap: &Vec<Uword>, value: Uword) -> Object {
        if value == NIL as Uword {
            Object::Nil
        } else if value & INTEGER_TAG_MASK as Uword == 0 {
            Object::Integer(((value >> INTEGER_SHIFT) | INTEGER_TAG as Uword) as i64)
        } else if value & 7 == 7 {
            match value & IMMEDIATE_TAG_MASK as Uword {
                t if t == CHAR_TAG as Uword => {
                    Object::Char(((value >> CHAR_SHIFT) & CHAR_MASK as Uword) as u8 as char)
                }
                t if t == BOOL_TAG as Uword => Object::Bool((value & BOOL_MASK as Uword) != 0),
                _ => panic!("Invalid immediate tag"),
            }
        } else if (value & HEAP_TAG_MASK) & PAIR_TAG as Uword != 0 {
            let offset =
                unsafe { ((value & HEAP_PTR_MASK) as *const Uword).offset_from(heap.as_ptr()) };
            assert!(offset >= 0 && (offset as usize) < heap.len());
            let offset = offset as usize;
            Object::Pair(
                Box::new(Self::decode(heap, heap[offset])),
                Box::new(Self::decode(heap, heap[offset + 1])),
            )
        } else {
            Object::Nil
        }
    }

    pub(crate) fn encode(&self) -> Uword {
        match self {
            Object::Nil => NIL as Uword,
            Object::Bool(b) => ((if *b { 1 } else { 0 } << BOOL_SHIFT) | BOOL_TAG) as Uword,
            Object::Char(c) => ((*c as Uword) << CHAR_SHIFT) | CHAR_TAG as Uword,
            Object::Integer(n) => {
                assert!(INTEGER_MIN <= *n && *n <= INTEGER_MAX);
                (*n << INTEGER_SHIFT) as Uword
            }
            _ => unimplemented!(),
        }
    }
}

impl std::fmt::Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Object::Nil => write!(f, "()"),
            Object::Bool(b) => {
                if *b {
                    write!(f, "#t")
                } else {
                    write!(f, "#f")
                }
            }
            Object::Char(c) => write!(f, "'{}'", c),
            Object::Integer(n) => write!(f, "{}", n),
            Object::Pair(car, cdr) => {
                write!(f, "({}", car)?;
                let mut current: &Object = cdr;
                loop {
                    if let Object::Nil = current {
                        break;
                    } else if let Object::Pair(car, cdr) = current {
                        write!(f, " {}", car)?;
                        current = cdr;
                    } else {
                        write!(f, " . {}", cdr)?;
                        break;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result = std::result::Result<(), Box<dyn std::error::Error>>;

    #[test]
    fn encode_positive_integer() -> Result {
        assert_eq!(0x0, Object::Integer(0).encode());
        assert_eq!(0x4, Object::Integer(1).encode());
        assert_eq!(0x28, Object::Integer(10).encode());
        Ok(())
    }

    #[test]
    fn encode_negative_integer() -> Result {
        assert_eq!(0x0, Object::Integer(0).encode());
        assert_eq!(0xfffffffffffffffcu64, Object::Integer(-1).encode());
        assert_eq!(0xffffffffffffffd8u64, Object::Integer(-10).encode());
        Ok(())
    }

    #[test]
    fn encode_char() {
        assert_eq!(Object::Char('\0').encode(), 0xf);
        assert_eq!(Object::Char('a').encode(), 0x610f);
    }

    #[test]
    fn decode_char() {
        let heap = vec![];
        assert_eq!(Object::decode(&heap, 0xf), Object::Char('\0'));
        assert_eq!(Object::decode(&heap, 0x610f), Object::Char('a'));
    }

    #[test]
    fn encode_bool() {
        assert_eq!(Object::Bool(true).encode(), 0x9f);
        assert_eq!(Object::Bool(false).encode(), 0x1f);
    }

    #[test]
    fn decode_bool() {
        let heap = vec![];
        assert_eq!(Object::decode(&heap, 0x9f), Object::Bool(true));
        assert_eq!(Object::decode(&heap, 0x1f), Object::Bool(false));
    }
}
