#[derive(Debug, PartialEq)]
pub enum TokenTypeLiteral {
    Identifier,
    String,
    Number,
}

#[derive(Debug, PartialEq)]
pub struct TokenRegular {
    pub(crate) r#type: TokenTypeRegular,
    pub(crate) lexeme: String,
    pub(crate) line: usize,
}
type Object = String;

#[derive(Debug, PartialEq)]
pub struct TokenLiteral {
    r#type: TokenTypeLiteral,
    lexeme: String,
    line: usize,
    literal: Object,
}

#[derive(Debug, PartialEq)]
pub enum Token {
    Regular(TokenRegular),
    Literal(TokenLiteral),
}

#[derive(Debug, PartialEq)]
pub enum TokenTypeRegular {
    // Single-character tokens
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // keywords
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    EOF,
}
