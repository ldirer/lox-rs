use thiserror::Error;

use crate::token::{Token, TokenType};

/// public interface for tokenizing
pub fn tokenize(source: String, error_reporter: fn(ScanningError) -> ()) -> Vec<Token> {
    let mut scanner = Scanner::new(source, error_reporter);
    scanner.scan_tokens();
    scanner.tokens
}

struct Scanner {
    source: String,
    tokens: Vec<Token>,
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
    #[error("Unterminated string {string_start:?}")]
    UnterminatedString { line: usize, string_start: String },
}

impl Scanner {
    fn new(source: String, error_reporter: fn(ScanningError) -> ()) -> Scanner {
        Scanner {
            source,
            tokens: vec![],
            error_reporter,
            start: 0,
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
                if self.match_one('/') {
                    while self.peek_one() != Some('\n') && self.peek_one() != None {
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
            c if is_digit(c) => Some(self.consume_if_match_number()),
            c if is_alphanumeric(c) => Some(self.consume_if_match_identifier()),
            _ => {
                self.start = self.current;
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
        self.start = self.current;
        Ok(())
    }

    fn is_at_end(&self) -> bool {
        return self.current >= self.source.len();
    }

    fn match_one(&mut self, expected: char) -> bool {
        if self.is_at_end() {
            return false;
        }
        if self.source.chars().nth(self.current) != Some(expected) {
            return false;
        }
        self.current += 1;
        return true;
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

    /// like advance but does not consume the character. 1 lookahead.
    fn peek_one(&self) -> Option<char> {
        self.source.chars().nth(self.current)
    }

    // 2 lookahead
    fn peek_two(&self) -> Option<char> {
        self.source.chars().nth(self.current + 1)
    }

    // TODO question: I'd prefer that to return `Result<TokenType::String, ScanningError::UnterminatedString>`.
    // But these are not types, the compiler complains:
    // error[E0573]: expected type, found variant `ScanningError::UnterminatedString`
    // --> src/scanner.rs:168:36
    // |
    // 168 |     ) -> Result<TokenType::String, ScanningError::UnterminatedString> {
    // |                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    // |                                    |
    // |                                    not a type
    // |                                    help: try using the variant's enum: `crate::ScanningError`
    fn consume_if_match_string(&mut self) -> Result<TokenType, ScanningError> {
        while self.peek_one() != None && self.peek_one() != Some('"') {
            if self.peek_one() == Some('\n') {
                self.line += 1;
            }
            self.advance();
        }

        if self.peek_one() == None {
            self.start = self.current;
            return Err(ScanningError::UnterminatedString {
                line: self.line,
                string_start: self.source[self.start..self.current].to_string(),
            });
        }

        // consume closing quote
        self.advance();

        return Ok(TokenType::String(
            // string without the quotes
            self.source[self.start + 1..self.current - 1].to_string(),
        ));
    }
    fn consume_if_match_number(&mut self) -> TokenType {
        while self.peek_one().is_some_and(is_digit) {
            self.advance();
        }

        if self.peek_one() == Some('.') && self.peek_two().is_some_and(is_digit) {
            // consume the '.'
            self.advance();
        }

        while self.peek_one().is_some_and(is_digit) {
            self.advance();
        }

        TokenType::Number(self.source[self.start..self.current].parse().unwrap())
    }
    fn consume_if_match_identifier(&mut self) -> TokenType {
        while self.peek_one().is_some_and(is_alphanumeric) {
            self.advance();
        }

        let lexeme = self.source[self.start..self.current].to_string();

        match match_keyword(&lexeme) {
            Some(keyword_token) => keyword_token,
            _ => TokenType::Identifier(lexeme),
        }
    }
}

fn match_keyword(input: &str) -> Option<TokenType> {
    // TODO not great that nothing tells us we need to update this when we add a keyword
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

fn is_digit(c: char) -> bool {
    match c {
        '0'..='9' => true,
        _ => false,
    }
}
fn is_alphanumeric(c: char) -> bool {
    match c {
        'a'..='z' | 'A'..='Z' | '_' => true,
        _ => false,
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

    #[test]
    fn test_scanning_multiple_character_operator() {
        let mut scanner = Scanner::new(">=".to_string(), |_err| ());
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
        let mut scanner = Scanner::new("\"hello\"".to_string(), |err| panic!("{err:?}"));
        scanner.scan_tokens();
        // println!("{:#?}", scanner.tokens);
        assert_eq!(scanner.tokens.len(), 2);
        assert_eq!(
            scanner.tokens[0],
            Token {
                r#type: TokenType::String("hello".to_string()),
                line: 1,
                lexeme: "\"hello\"".to_string()
            }
        );
    }

    #[test]
    fn test_scanner_handles_numbers() {
        let mut scanner = Scanner::new("1.2".to_string(), |err| panic!("{err:?}"));
        scanner.scan_tokens();
        // println!("{:#?}", scanner.tokens);
        assert_eq!(scanner.tokens.len(), 2);
        assert_eq!(
            scanner.tokens[0],
            Token {
                r#type: TokenType::Number(1.2),
                line: 1,
                lexeme: "1.2".to_string()
            }
        );
    }

    #[test]
    fn test_scanner_handles_numbers_2() {
        let mut scanner = Scanner::new("1.some".to_string(), |err| panic!("{err:?}"));
        scanner.scan_tokens();
        // println!("{:#?}", scanner.tokens);
        assert_eq!(scanner.tokens.len(), 4);
        assert_eq!(
            scanner.tokens[0],
            Token {
                r#type: TokenType::Number(1.0),
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
                r#type: TokenType::Identifier("some".to_string()),
                lexeme: "some".to_string(),
                line: 1
            }
        )
    }
}
