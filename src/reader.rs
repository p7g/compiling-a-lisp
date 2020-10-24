use crate::ast::{ASTNode, Pair, Symbol};
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, PartialEq)]
pub(crate) enum ReaderError {
    UnexpectedEndOfInput,
    UnexpectedInput(char),
}

impl std::fmt::Display for ReaderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ReaderError {}

pub(crate) type Result = std::result::Result<ASTNode, ReaderError>;

#[derive(Clone, Copy)]
enum Sign {
    Positive,
    Negative,
}

pub(crate) fn read(input: &str) -> Result {
    let mut reader = Reader::new(input);
    reader.read()
}

fn starts_symbol(c: char) -> bool {
    "+-*<>=?".contains(c) || c.is_ascii_alphabetic()
}

fn is_symbol_char(c: char) -> bool {
    starts_symbol(c) || c.is_ascii_digit()
}

struct Reader<'a> {
    input: Peekable<Chars<'a>>,
    unpeeked: Option<char>,
}

impl<'a> Reader<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input: input.chars().peekable(),
            unpeeked: None,
        }
    }

    fn peek(&mut self) -> Option<&char> {
        #[allow(clippy::or_fun_call)]
        self.unpeeked.as_ref().or(self.input.peek())
    }

    fn next(&mut self) -> Option<char> {
        self.unpeeked.take().or_else(|| self.input.next())
    }

    fn read(&mut self) -> Result {
        self.skip_whitespace();
        match self.next().ok_or(ReaderError::UnexpectedEndOfInput)? {
            c @ '0'..='9' => {
                self.unpeeked.replace(c);
                self.read_integer(Sign::Positive)
            }
            c @ '+' | c @ '-'
                if self
                    .peek()
                    .map(char::is_ascii_digit)
                    .ok_or(ReaderError::UnexpectedEndOfInput)? =>
            {
                self.read_integer(if c == '+' {
                    Sign::Positive
                } else {
                    Sign::Negative
                })
            }
            '#' if self
                .peek()
                .map(|c| "tf".contains(*c))
                .ok_or(ReaderError::UnexpectedEndOfInput)? =>
            {
                let c = self.next().unwrap_or_else(|| unreachable!());
                Ok(ASTNode::Bool(c == 't'))
            }
            '\'' => self.read_char(),
            '(' => self.read_list(),
            c if starts_symbol(c) => {
                self.unpeeked.replace(c);
                self.read_symbol()
            }
            c => Err(ReaderError::UnexpectedInput(c)),
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.next();
            } else {
                break;
            }
        }
    }

    fn read_integer(&mut self, sign: Sign) -> Result {
        let mut result = 0;
        while let Some(c) = self.peek() {
            if !c.is_ascii_digit() {
                break;
            }
            let c = self.next().unwrap();
            result *= 10;
            result += c
                .to_digit(10)
                .map(i64::from)
                .ok_or_else(|| ReaderError::UnexpectedInput(c))?;
        }
        Ok(ASTNode::Integer(match sign {
            Sign::Positive => result,
            Sign::Negative => -result,
        }))
    }

    fn read_char(&mut self) -> Result {
        let c = self.next().ok_or(ReaderError::UnexpectedEndOfInput)?;
        let c = match c {
            '\'' => return Err(ReaderError::UnexpectedInput(c)),
            '\\' => self.next().ok_or(ReaderError::UnexpectedEndOfInput)?,
            c => c,
        };
        match self.next() {
            Some('\'') => Ok(ASTNode::Char(c)),
            Some(c) => Err(ReaderError::UnexpectedInput(c)),
            None => Err(ReaderError::UnexpectedEndOfInput),
        }
    }

    fn read_list(&mut self) -> Result {
        self.skip_whitespace();
        match self.peek() {
            Some(')') => {
                self.next();
                Ok(ASTNode::Nil)
            }
            Some(_) => {
                let car = self.read()?;
                let cdr = self.read_list()?;
                Ok(ASTNode::Pair(Box::new(Pair::new(car, cdr))))
            }
            None => Err(ReaderError::UnexpectedEndOfInput),
        }
    }

    fn read_symbol(&mut self) -> Result {
        let mut buf = String::new();
        while let Some(c) = self.peek() {
            if !is_symbol_char(*c) {
                break;
            }
            buf.push(self.next().unwrap());
        }
        Ok(ASTNode::Symbol(Symbol::new(buf)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_with_integer_returns_integer() {
        assert_eq!(read("1234"), Ok(ASTNode::Integer(1234)));
    }

    #[test]
    fn read_with_negative_integer_returns_integer() {
        assert_eq!(read("-1234"), Ok(ASTNode::Integer(-1234)));
    }

    #[test]
    fn read_with_positive_integer_returns_integer() {
        assert_eq!(read("+1234"), Ok(ASTNode::Integer(1234)));
    }

    #[test]
    fn read_with_leading_whitespace_ignores_whitespace() {
        assert_eq!(read("   \t   \n  1234"), Ok(ASTNode::Integer(1234)));
    }

    #[test]
    fn read_with_symbol_returns_symbol() {
        assert_eq!(
            read("hello?+-*=>"),
            Ok(ASTNode::Symbol(Symbol::new("hello?+-*=>".to_string())))
        );
    }

    #[test]
    fn read_with_symbol_with_trailing_digits() {
        assert_eq!(
            read("add1 1"),
            Ok(ASTNode::Symbol(Symbol::new("add1".to_string())))
        );
    }

    #[test]
    fn read_with_char_returns_char() {
        assert_eq!(read("'a'"), Ok(ASTNode::Char('a')));
    }

    #[test]
    fn read_with_escaped_char_returns_char() {
        assert_eq!(read("'\\\\'"), Ok(ASTNode::Char('\\')));
    }

    #[test]
    fn read_with_bool_returns_bool() {
        assert_eq!(read("#t"), Ok(ASTNode::Bool(true)));
        assert_eq!(read("#f"), Ok(ASTNode::Bool(false)));
        assert_eq!(read("#"), Err(ReaderError::UnexpectedEndOfInput));
        assert_eq!(read("#x"), Err(ReaderError::UnexpectedInput('#')));
        assert_eq!(read("##"), Err(ReaderError::UnexpectedInput('#')));
    }

    #[test]
    fn read_with_nil_returns_nil() {
        assert_eq!(read("()"), Ok(ASTNode::Nil));
    }

    #[test]
    fn read_with_list_ignores_whitespace() {
        assert_eq!(read("(1 2 0)"), read("( 1 2 0 )"));
    }

    #[test]
    fn read_with_list_returns_list() {
        assert_eq!(read("(1 2 0)"), read("( 1 2 0 )"));
        assert_eq!(
            read("(1 2 0)"),
            Ok(ASTNode::Pair(Box::new(Pair::new(
                ASTNode::Integer(1),
                ASTNode::Pair(Box::new(Pair::new(
                    ASTNode::Integer(2),
                    ASTNode::Pair(Box::new(Pair::new(ASTNode::Integer(0), ASTNode::Nil)))
                )))
            ))))
        );
    }

    #[test]
    fn read_with_nested_list_returns_list() {
        assert_eq!(
            read("((hello world) (foo bar))"),
            Ok(ASTNode::Pair(Box::new(Pair::new(
                ASTNode::Pair(Box::new(Pair::new(
                    ASTNode::Symbol(Symbol::new("hello".to_string())),
                    ASTNode::Pair(Box::new(Pair::new(
                        ASTNode::Symbol(Symbol::new("world".to_string())),
                        ASTNode::Nil
                    )))
                ))),
                ASTNode::Pair(Box::new(Pair::new(
                    ASTNode::Pair(Box::new(Pair::new(
                        ASTNode::Symbol(Symbol::new("foo".to_string())),
                        ASTNode::Pair(Box::new(Pair::new(
                            ASTNode::Symbol(Symbol::new("bar".to_string())),
                            ASTNode::Nil
                        )))
                    ))),
                    ASTNode::Nil
                )))
            ))))
        );
    }
}
