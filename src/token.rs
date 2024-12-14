// ### Token constants and lexing library. ###

use std::fmt;

use logos::{Logos, SpannedIter};

pub const INFIX_RELATION_SYMBOLS: [&str; 5] = ["<", "<=", "=", ">=", ">"];

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\n\f\r]+")] // Ignore Whitespace
pub enum Token {
    #[regex("nil|[0-9]+", |lex| lex.slice().to_string(), priority = 1)]
    Constant(String),

    #[regex("[a-zA-Z0-9\'_]+", |lex| lex.slice().to_string(), priority = 0)]
    Alphanumeric(String),

    #[regex("<|<=|=|>=|>", |lex| lex.slice().to_string())]
    InfixRelation(String),

    #[regex("[`!@#$%&|;?]+", |lex| lex.slice().to_string())]
    Symbolic(String),

    #[token("forall")]
    Forall,

    #[token("exists")]
    Exists,

    #[token("true")]
    True,

    #[token("false")]
    False,

    #[token("~")]
    Negation,

    #[token("\\/")]
    Or,

    #[token("/\\")]
    And,

    #[token("==>")]
    Imp,

    #[token("<=>")]
    Iff,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("+")]
    Plus,

    #[token("-")]
    Minus,

    #[token("*")]
    Times,

    #[token("/")]
    Divide,

    #[token("^")]
    Exp,

    #[token("::")]
    Cons,

    #[token(",")]
    Comma,

    #[token(".")]
    Period,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub fn lex(input: &str) -> Vec<String> {
    // let token_stream: SpannedIter<'input, Token> = Token::lexer(input).spanned();
    let mut lexer = Token::lexer(input);
    let mut result = vec![];
    while lexer.next().is_some() {
        result.push(String::from(lexer.slice()));
    }
    result
}

// #######  For LALRPOP Parser #########
//
// lalrpop parser needs an iterator of the following type as input
pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

pub struct Lexer<'input> {
    token_stream: SpannedIter<'input, Token>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        // the Token::lexer() method is provided by the Logos trait
        Self {
            token_stream: Token::lexer(input).spanned(),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Default)]
pub enum LexicalError {
    #[default]
    Other,
}

impl Iterator for Lexer<'_> {
    type Item = Spanned<Token, usize, LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.token_stream.next() {
            None => None,
            Some((Err(_), _)) => Some(Err(LexicalError::Other)),
            Some((Ok(token), span)) => Some(Ok((span.start, token, span.end))),
        }
    }
}

#[cfg(test)]
mod lex_tests {
    use super::*;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn simple_lex_0() {
        let input = "aba = bada";
        let result = lex(input);
        let desired = vec!["aba", "=", "bada"];
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex_1() {
        let input = "a - b";
        let result = lex(input);
        let desired = vec!["a", "-", "b"];
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex_2() {
        let input = "a / b";
        let result = lex(input);
        let desired = vec!["a", "/", "b"];
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex_3() {
        let input = "a ^ b";
        let result = lex(input);
        let desired = vec!["a", "^", "b"];
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex_4() {
        let input = "A \\/ B";
        let result = lex(input);
        let desired = vec!["A", "\\/", "B"];
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex_5() {
        let input = "A /\\ B";
        let result = lex(input);
        let desired = vec!["A", "/\\", "B"];
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex_6() {
        let input = "F(x, z)";
        let result = lex(input);
        let desired = vec!["F", "(", "x", ",", "z", ")"];
        assert_eq!(result, desired);
    }

    #[test]
    fn simple_lex_7() {
        let input = "forall z'. ~F(x', z)";
        let result = lex(input);
        let desired = vec!["forall", "z'", ".", "~", "F", "(", "x'", ",", "z", ")"];
        assert_eq!(result, desired);
    }

    #[test]
    fn double_neg() {
        let input = "~~A";
        let result = lex(input);
        let desired = vec!["~", "~", "A"];
        assert_eq!(result, desired);
    }

    #[test]
    fn less_simple_lex() {
        let input = "((a + b * 17) + cab)";
        let result = lex(input);
        let desired = vec!["(", "(", "a", "+", "b", "*", "17", ")", "+", "cab", ")"];
        assert_eq!(result, desired);
    }

    #[test]
    fn test_lexer() {
        let input = "a + (bc * 17)";
        let lexer = Lexer::new(input);
        let result = Vec::from_iter(lexer);
        let desired: Vec<Spanned<Token, usize, LexicalError>> = vec![
            Ok((0, Token::Alphanumeric("a".to_string()), 1)),
            Ok((2, Token::Plus, 3)),
            Ok((4, Token::LParen, 5)),
            Ok((5, Token::Alphanumeric("bc".to_string()), 7)),
            Ok((8, Token::Times, 9)),
            Ok((10, Token::Constant("17".to_string()), 12)),
            Ok((12, Token::RParen, 13)),
        ];
        assert_eq!(result, desired);
    }

    #[test]
    fn test_lexer_err() {
        // Encounter an unknown symbol "{"
        let input = "a {";
        let lexer = Lexer::new(input);
        let result = Vec::from_iter(lexer);
        let desired: Vec<Spanned<Token, usize, LexicalError>> = vec![
            Ok((0, Token::Alphanumeric("a".to_string()), 1)),
            Err(LexicalError::Other),
        ];
        assert_eq!(result, desired);
    }

    #[test]
    fn test_lexer_constant() {
        let input = "42";
        let lexer = Lexer::new(input);
        let result = Vec::from_iter(lexer);
        let desired: Vec<Spanned<Token, usize, LexicalError>> =
            vec![Ok((0, Token::Constant("42".to_string()), 2))];
        assert_eq!(result, desired);
    }

    #[test]
    fn test_lexer_variable() {
        let input = "x";
        let lexer = Lexer::new(input);
        let result = Vec::from_iter(lexer);
        let desired: Vec<Spanned<Token, usize, LexicalError>> =
            vec![Ok((0, Token::Alphanumeric("x".to_string()), 1))];
        assert_eq!(result, desired);
    }
}
