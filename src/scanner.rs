use crate::token::{Token, TokenType};
use std::error::Error;
use std::iter::Scan;
use thiserror::Error;

pub struct Scanner {
    source: String,
    pub(crate) tokens: Vec<Token>,
    error_reporter: fn(ScanningError) -> (),

    // position of the start of lexeme
    start: usize,
    current: usize,
    line: usize,
}

#[derive(Debug, Error)]
pub enum ScanningError {
    #[error("Unexpected character {character:?}")]
    UnexpectedCharacter { line: usize, character: char },
}

impl Scanner {
    pub(crate) fn new(source: String, error_reporter: fn(ScanningError) -> ()) -> Scanner {
        Scanner {
            source,
            tokens: vec![],
            error_reporter,
            start: 0,
            current: 0,
            line: 1,
        }
    }
    pub(crate) fn scan_tokens(&mut self) {
        while !self.is_at_end() {
            let maybe_error = self.scan_token();
            if let Some(scanning_error) = maybe_error {
                (self.error_reporter)(scanning_error)
            }
        }
        self.tokens.push(Token {
            r#type: TokenType::EOF,
            lexeme: "".to_string(),
            line: self.line,
        });
    }

    fn scan_token(&mut self) -> Option<ScanningError> {
        let c: char = self.advance();
        let token_type = match c {
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
            _ => None,
        };
        // println!("{:#?}", token_type);

        if let Some(regular_token_type) = token_type {
            self.add_token(regular_token_type);
            return None;
        }
        self.start = self.current;
        return Some(ScanningError::UnexpectedCharacter {
            line: self.line,
            character: c,
        });
    }

    fn is_at_end(&self) -> bool {
        return self.current >= self.source.len();
    }
    fn advance(&mut self) -> char {
        // this is NOT efficient at all, we are re-reading all characters in the source every time
        let current_char = self.source.chars().nth(self.current);
        self.current += 1;
        // println!("CURRENT CAR {current_char:?}");
        // unwrapping \o/
        // I guess we could use the None case to detect the end of the file
        current_char.unwrap()
    }
    fn add_token(&mut self, token_type: TokenType) {
        let text: String = self.source[self.start..self.current].to_string();
        self.tokens.push(Token {
            r#type: token_type,
            lexeme: text,
            line: self.line,
        });
        self.start = self.current;
    }
}

#[cfg(test)]
mod tests {
    use crate::scanner::Scanner;
    use crate::token::{Token, TokenType};

    #[test]
    fn test_scanning_regular_tokens() {
        let mut scanner = Scanner::new("{,.}".to_string(), |_err| ());
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
}
