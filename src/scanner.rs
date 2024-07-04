use std::iter::Peekable;
use std::str::{from_utf8, Chars};

use thiserror::Error;

use crate::token::{Token, TokenType};

/// public interface for tokenizing
pub fn tokenize(source: String, error_reporter: fn(ScanningError) -> ()) -> Vec<Token> {
    let mut scanner = Scanner::new(&source, error_reporter);
    scanner.scan_tokens();
    scanner.tokens
}

struct Scanner<'a> {
    source: &'a str,
    char_iter: Peekable<Chars<'a>>,
    tokens: Vec<Token>,
    error_reporter: fn(ScanningError) -> (),

    // position of the start of lexeme
    current_lexeme_start: usize,
    current: usize,
    line: usize,
}

#[derive(Debug, Error)]
pub enum ScanningError {
    #[error("Unexpected character.")]
    UnexpectedCharacter { line: usize, character: char },
    #[error("Unterminated string.")]
    UnterminatedString { line: usize, string_start: String },
    #[error("Unterminated block comment.")]
    UnterminatedBlockComment { line: usize, comment_start: String },
}
impl ScanningError {
    // not sure how I feel about this. But also wrapping the error in yet another struct feels bad.
    pub fn get_line(&self) -> usize {
        match self {
            ScanningError::UnexpectedCharacter { line, .. }
            | ScanningError::UnterminatedString { line, .. }
            | ScanningError::UnterminatedBlockComment { line, .. } => *line,
        }
    }
}

impl Scanner<'_> {
    fn new(source: &str, error_reporter: fn(ScanningError) -> ()) -> Scanner {
        Scanner {
            source,
            char_iter: source.chars().peekable(),
            tokens: vec![],
            error_reporter,
            current_lexeme_start: 0,
            current: 0,
            line: 1,
        }
    }
    fn scan_tokens(&mut self) {
        while !self.is_at_end() {
            let maybe_error = self.scan_token();
            if let Err(scanning_error) = maybe_error {
                (self.error_reporter)(scanning_error)
            }
        }
        self.tokens.push(Token {
            r#type: TokenType::EOF,
            lexeme: "".to_string(),
            line: self.line,
        });
    }

    fn scan_token(&mut self) -> Result<(), ScanningError> {
        // set start of lexeme
        self.current_lexeme_start = self.current;
        let c: char = self.advance();
        let maybe_token_type = match c {
            '(' => Some(TokenType::LeftParen),
            ')' => Some(TokenType::RightParen),
            '{' => Some(TokenType::LeftBrace),
            '}' => Some(TokenType::RightBrace),
            ',' => Some(TokenType::Comma),
            '.' => Some(TokenType::Dot),
            '-' => Some(TokenType::Minus),
            '+' => Some(TokenType::Plus),
            ';' => Some(TokenType::Semicolon),
            '*' => Some(TokenType::Star),
            '!' => match self.match_one('=') {
                true => Some(TokenType::BangEqual),
                false => Some(TokenType::Bang),
            },
            '=' => match self.match_one('=') {
                true => Some(TokenType::EqualEqual),
                false => Some(TokenType::Equal),
            },
            '<' => match self.match_one('=') {
                true => Some(TokenType::LessEqual),
                false => Some(TokenType::Less),
            },
            '>' => match self.match_one('=') {
                true => Some(TokenType::GreaterEqual),
                false => Some(TokenType::Greater),
            },
            '/' => {
                if self.match_one('*') {
                    self.consume_if_match_block_comment()?;
                    None
                } else if self.match_one('/') {
                    while self.peek_one() != Some(&'\n') && self.peek_one() != None {
                        self.advance();
                    }
                    None
                } else {
                    Some(TokenType::Slash)
                }
            }
            ' ' | '\r' | '\t' => None,
            '\n' => {
                self.line += 1;
                None
            }
            '"' => Some(self.consume_if_match_string()?),
            c if is_digit(&c) => Some(self.consume_if_match_number()),
            c if is_alpha(&c) => Some(self.consume_if_match_identifier()),
            _ => {
                return Err(ScanningError::UnexpectedCharacter {
                    line: self.line,
                    character: c,
                });
            }
        };
        // println!("{:#?}", token_type);

        if let Some(token_type) = maybe_token_type {
            self.add_token(token_type);
            return Ok(());
        }
        Ok(())
    }

    fn is_at_end(&self) -> bool {
        return self.current >= self.source.len();
    }

    fn match_one(&mut self, expected: char) -> bool {
        if self.is_at_end() {
            return false;
        }
        if self.peek_one() != Some(&expected) {
            return false;
        }
        self.advance();
        return true;
    }
    fn advance(&mut self) -> char {
        // unwrapping \o/
        // I guess we could use the None case to detect the end of the file
        match self.char_iter.next() {
            Some(current_char) => {
                self.current += current_char.len_utf8();
                Some(current_char)
            }
            None => None,
        }
        .unwrap()
    }
    fn add_token(&mut self, token_type: TokenType) {
        // /!\ using a string slice is a dangerous thing!
        // We might be slicing at something that isn't a character boundary (we slice bytes).
        // https://doc.rust-lang.org/book/ch08-02-strings.html#indexing-into-strings
        let text: String = self.source[self.current_lexeme_start..self.current].to_string();
        self.tokens.push(Token {
            r#type: token_type,
            lexeme: text,
            line: self.line,
        });
    }

    /// like advance but does not consume the character. 1 lookahead.
    fn peek_one(&mut self) -> Option<&char> {
        self.char_iter.peek()
    }

    /// 2 lookahead
    /// Sad that it doesn't return a reference to be consistent with its friend peek_one.
    /// The implementation can't help it though. It's hacky.
    /// Ideally we'd use an iterator that allows peek(2) but it's probably a bit involved (though
    /// I think simple on principle?) to implement the Iterator trait for a PeekableTwo type.
    fn peek_two(&self) -> Option<char> {
        // HOW WOULD I KNOW HOW MANY BYTES ARE NEEDED FOR ONE CHARACTER? I CANT. I NEED THE CHARS THING.
        from_utf8(&self.source.as_bytes()[self.current..])
            .expect("play with strings, utf-8, and get burned")
            .chars()
            .nth(1)
    }

    fn consume_if_match_string(&mut self) -> Result<TokenType, ScanningError> {
        while self.peek_one() != None && self.peek_one() != Some(&'"') {
            if self.peek_one() == Some(&'\n') {
                self.line += 1;
            }
            self.advance();
        }

        if self.peek_one() == None {
            return Err(ScanningError::UnterminatedString {
                line: self.line,
                string_start: self.source[self.current_lexeme_start..self.current].to_string(),
            });
        }

        // consume closing quote
        self.advance();

        return Ok(TokenType::String);
    }
    fn consume_if_match_number(&mut self) -> TokenType {
        while self.peek_one().is_some_and(is_digit) {
            self.advance();
        }

        if self.peek_one() == Some(&'.') && self.peek_two().is_some_and(|c| is_digit(&c)) {
            // consume the '.'
            self.advance();
        }

        while self.peek_one().is_some_and(is_digit) {
            self.advance();
        }

        TokenType::Number
    }
    fn consume_if_match_identifier(&mut self) -> TokenType {
        while self.peek_one().is_some_and(is_alphanumeric) {
            self.advance();
        }

        let lexeme = self.source[self.current_lexeme_start..self.current].to_string();

        match match_keyword(&lexeme) {
            Some(keyword_token) => keyword_token,
            _ => TokenType::Identifier,
        }
    }
    fn consume_if_match_block_comment(&mut self) -> Result<(), ScanningError> {
        while self.peek_one() != Some(&'*') || self.peek_two() != Some('/') {
            if self.peek_one() == Some(&'\n') {
                self.line += 1;
            }
            self.advance();
        }

        if self.peek_one().is_none() {
            return Err(ScanningError::UnterminatedBlockComment {
                line: self.line,
                comment_start: self.source[self.current_lexeme_start..self.current].to_string(),
            });
        }

        // consume '*' and '/'
        self.advance();
        self.advance();

        Ok(())
    }
}

fn match_keyword(input: &str) -> Option<TokenType> {
    // Here nothing tells us we need to update this when we add a keyword.
    // it's not really a frequent operation but still would be nice.
    match input {
        "and" => Some(TokenType::And),
        "class" => Some(TokenType::Class),
        "else" => Some(TokenType::Else),
        "false" => Some(TokenType::False),
        "fun" => Some(TokenType::Fun),
        "for" => Some(TokenType::For),
        "if" => Some(TokenType::If),
        "nil" => Some(TokenType::Nil),
        "or" => Some(TokenType::Or),
        "print" => Some(TokenType::Print),
        "return" => Some(TokenType::Return),
        "super" => Some(TokenType::Super),
        "this" => Some(TokenType::This),
        "true" => Some(TokenType::True),
        "var" => Some(TokenType::Var),
        "while" => Some(TokenType::While),
        _ => None,
    }
}

fn is_digit(c: &char) -> bool {
    match c {
        '0'..='9' => true,
        _ => false,
    }
}
fn is_alpha(c: &char) -> bool {
    match c {
        'a'..='z' | 'A'..='Z' | '_' => true,
        _ => false,
    }
}
fn is_alphanumeric(c: &char) -> bool {
    is_digit(c) || is_alpha(c)
}

#[cfg(test)]
mod tests {
    use crate::scanner::{tokenize, Scanner};
    use crate::token::{Token, TokenType};

    #[test]
    fn test_scanning_regular_tokens() {
        let mut scanner = Scanner::new("{,.}", |_err| ());
        scanner.scan_tokens();
        // array comparison is not super helpful when this fails.
        assert_eq!(
            scanner.tokens,
            vec![
                Token {
                    r#type: TokenType::LeftBrace,
                    line: 1,
                    lexeme: "{".to_string()
                },
                Token {
                    r#type: TokenType::Comma,
                    line: 1,
                    lexeme: ",".to_string()
                },
                Token {
                    r#type: TokenType::Dot,
                    line: 1,
                    lexeme: ".".to_string()
                },
                Token {
                    r#type: TokenType::RightBrace,
                    line: 1,
                    lexeme: "}".to_string()
                },
                Token {
                    r#type: TokenType::EOF,
                    line: 1,
                    lexeme: "".to_string()
                },
            ]
        )
    }

    #[test]
    fn test_scanning_multiple_character_operator() {
        let mut scanner = Scanner::new(">=", |_err| ());
        scanner.scan_tokens();
        // array comparison is not super helpful when this fails.
        assert_eq!(
            scanner.tokens,
            vec![
                Token {
                    r#type: TokenType::GreaterEqual,
                    line: 1,
                    lexeme: ">=".to_string()
                },
                Token {
                    r#type: TokenType::EOF,
                    line: 1,
                    lexeme: "".to_string()
                },
            ]
        )
    }
    #[test]
    fn test_scanner_handles_strings() {
        let mut scanner = Scanner::new("\"hello\"", |err| panic!("{err:?}"));
        scanner.scan_tokens();
        // println!("{:#?}", scanner.tokens);
        assert_eq!(scanner.tokens.len(), 2);
        assert_eq!(
            scanner.tokens[0],
            Token {
                r#type: TokenType::String,
                line: 1,
                lexeme: "\"hello\"".to_string()
            }
        );
    }
    #[test]
    fn test_string_multiple_lines() {
        let s = "var a = \"a string \n with newlines in it\"".to_string();
        println!("{}", s);
        let tokens = tokenize(s, |err| panic!("{err:?}"));
        println!("{:#?}", tokens);
        assert_eq!(tokens.len(), 5);
        assert_eq!(
            tokens[3],
            Token {
                r#type: TokenType::String,
                lexeme: "\"a string \n with newlines in it\"".to_string(),
                line: 2,
            }
        );
    }

    #[test]
    fn test_scanner_handles_numbers() {
        let mut scanner = Scanner::new("1.2", |err| panic!("{err:?}"));
        scanner.scan_tokens();
        // println!("{:#?}", scanner.tokens);
        assert_eq!(scanner.tokens.len(), 2);
        assert_eq!(
            scanner.tokens[0],
            Token {
                r#type: TokenType::Number,
                line: 1,
                lexeme: "1.2".to_string()
            }
        );
    }

    #[test]
    fn test_scanner_handles_numbers_2() {
        let mut scanner = Scanner::new("1.some", |err| panic!("{err:?}"));
        scanner.scan_tokens();
        // println!("{:#?}", scanner.tokens);
        assert_eq!(scanner.tokens.len(), 4);
        assert_eq!(
            scanner.tokens[0],
            Token {
                r#type: TokenType::Number,
                line: 1,
                lexeme: "1".to_string()
            }
        );
        assert_eq!(
            scanner.tokens[1],
            Token {
                r#type: TokenType::Dot,
                line: 1,
                lexeme: ".".to_string()
            }
        );
        assert_eq!(
            scanner.tokens[2],
            Token {
                r#type: TokenType::Identifier,
                lexeme: "some".to_string(),
                line: 1
            }
        )
    }
    #[test]
    fn test_pretending_to_handle_non_ascii() {
        let tokens = tokenize("// 🤩 this is all a _façade_".to_string(), |err| {
            panic!("{err:?}")
        });
        // println!("{tokens:#?}");
        // since we don't parse comments and only alphanumeric characters are allowed in Lox code,
        // we're really just checking we don't crash :)
        assert_eq!(tokens.len(), 1);
    }

    #[test]
    fn test_block_comments() {
        let s = "/* here's a block comment \n with newlines in it */".to_string();
        // println!("{}", s);
        let tokens = tokenize(s, |err| panic!("{err:?}"));
        println!("{:#?}", tokens);
        assert_eq!(tokens.len(), 1);
        assert_eq!(
            tokens[0],
            Token {
                r#type: TokenType::EOF,
                lexeme: "".to_string(),
                line: 2,
            }
        );
    }

    #[test]
    fn test_identifier_with_digit() {
        let tokens = tokenize("a_0".to_string(), |err| panic!("{err:?}"));
        assert_eq!(
            tokens[0],
            Token {
                r#type: TokenType::Identifier,
                lexeme: "a_0".to_string(),
                line: 1,
            }
        );
        assert_eq!(
            tokens[1],
            Token {
                r#type: TokenType::EOF,
                lexeme: "".to_string(),
                line: 1,
            }
        );
    }
}
