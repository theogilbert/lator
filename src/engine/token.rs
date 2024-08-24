use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;

use crate::engine::operator::OperatorType;

/// A TokenType indicates the semantic nature of a token.
#[derive(Eq, PartialEq, Debug, Copy, Clone, Hash)]
pub enum TokenType {
    /// Represents an invalid sequence of characters.
    Invalid,
    /// Represents a sequence of whitespace characters.
    Whitespace,
    /// Classifies a token as either an integer or a decimal numeral.
    Number,
    /// Classifies a token as an operator sign.
    Operator(OperatorType),
    /// Indicates the start of a prioritized sub-expression.
    OpenParenthesis,
    /// Indicates the end of a prioritized sub-expression.
    CloseParenthesis,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct Token<'a> {
    token_type: TokenType,
    // The content of the token
    content: &'a str,
}

impl<'a> Token<'a> {
    pub fn new(token_type: TokenType, content: &'a str) -> Self {
        Self {
            token_type,
            content,
        }
    }

    pub fn token_type(&self) -> TokenType {
        self.token_type
    }

    pub fn length(&self) -> usize {
        self.content.len()
    }

    pub fn content(&self) -> &str {
        self.content
    }
}

impl<'a> Token<'a> {
    pub fn is_whitespace(&self) -> bool {
        self.token_type == TokenType::Whitespace
    }

    pub fn is_operator(&self) -> bool {
        matches!(self.token_type, TokenType::Operator(_))
    }
}

/// Split the expression in an ordered sequence of tokens.\
/// Each character of the expression belongs to exactly one of the returned tokens.
pub fn tokenize(expression: &str) -> Vec<Token> {
    let mut tokens = vec![];
    let mut cursor = 0;

    while cursor < expression.len() {
        let next_token = produce_next_token(&expression[cursor..]);
        cursor += next_token.length();
        tokens.push(next_token);
    }

    tokens
}

lazy_static! {
    /// TOKEN_PATTERNS represent the list of tokens parseable from the parser.
    static ref TOKEN_PATTERNS: HashMap<TokenType, Regex> = HashMap::from([
        (TokenType::Whitespace, r"^\s+"),
        (TokenType::Number, r"(\d+(\.\d*)?)|^(\.\d+)"),
        (TokenType::Operator(OperatorType::Addition), r"\+"),
        (TokenType::Operator(OperatorType::Subtraction), "-"),
        (TokenType::Operator(OperatorType::Multiplication), "×"),
        (TokenType::Operator(OperatorType::Division), "÷"),
        (TokenType::OpenParenthesis, r"\("),
        (TokenType::CloseParenthesis, r"\)"),
    ])
    .into_iter()
    .map(|(token_type, re_expr)| (token_type, Regex::new(re_expr).unwrap()))
    .collect();
}

/// Produce a token starting from the start of the given expression.\
/// If the start of the expression matches no token pattern, an [invalid token](TokenType::Invalid)
/// is produced. This token ends before the position of the next valid token.
fn produce_next_token(expr: &str) -> Token {
    let mut tokens_and_pos: Vec<(Token, usize)> = TOKEN_PATTERNS
        .iter()
        .filter_map(|(token_type, pattern)| {
            build_token_matching_pattern(expr, *token_type, pattern)
        })
        .collect();

    tokens_and_pos.sort_by_key(|(_, pos)| *pos);
    let first_token = tokens_and_pos.into_iter().next();

    if let Some((token, start)) = first_token {
        if start == 0 {
            token
        } else {
            Token::new(TokenType::Invalid, &expr[..start])
        }
    } else {
        Token::new(TokenType::Invalid, expr)
    }
}

/// Produces a tuple containing:
/// 1. The first [`Token`] in the expression matching the given regex pattern.
/// 2. The starting position of this token in the expression.
///
/// Returns [`None`] if the expression contains no such token.
fn build_token_matching_pattern<'a>(
    expr: &'a str,
    token_type: TokenType,
    pattern: &Regex,
) -> Option<(Token<'a>, usize)> {
    pattern
        .find(expr)
        .map(|re_match| (Token::new(token_type, re_match.as_str()), re_match.start()))
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::engine::token::test_helpers::{
        add_token, invalid_token, num_token, whitespace_token,
    };

    use super::*;

    #[test]
    fn should_evaluate_empty_expr_as_no_token() {
        let expr = "";
        assert_eq!(Vec::<Token>::new(), tokenize(expr));
    }

    #[test]
    fn should_evaluate_word_as_invalid_token() {
        let expr = "hello";
        assert_eq!(vec![str_to_token(expr, TokenType::Invalid)], tokenize(expr));
    }

    #[rstest]
    #[case("00")]
    #[case("123")]
    #[case("123.45")]
    #[case(".3")]
    #[case("18.")]
    fn should_evaluate_number_as_valid_token(#[case] expr: &str) {
        assert_eq!(vec![str_to_token(expr, TokenType::Number)], tokenize(expr));
    }

    #[test]
    fn should_evaluate_number_with_two_decimal_separators_as_two_tokens() {
        let expr = "123.45.67";
        assert_eq!(vec![num_token("123.45"), num_token(".67")], tokenize(expr));
    }

    #[rstest]
    #[case("+", OperatorType::Addition)]
    #[case("-", OperatorType::Subtraction)]
    #[case("×", OperatorType::Multiplication)]
    #[case("÷", OperatorType::Division)]
    fn should_evaluate_operator_as_valid_token(#[case] expr: &str, #[case] op_type: OperatorType) {
        assert_eq!(
            vec![str_to_token(expr, TokenType::Operator(op_type))],
            tokenize(expr)
        );
    }

    #[rstest]
    #[case("(", TokenType::OpenParenthesis)]
    #[case(")", TokenType::CloseParenthesis)]
    fn should_evaluate_parenthesis_token(#[case] expr: &str, #[case] token_type: TokenType) {
        assert_eq!(vec![str_to_token(expr, token_type)], tokenize(expr));
    }

    #[rstest]
    #[case("123abc", vec![num_token("123"), invalid_token("abc")])]
    #[case("abc123", vec![invalid_token("abc"), num_token("123")])]
    #[case("123+.456", vec![num_token("123"), add_token(), num_token(".456")])]
    fn should_evaluate_expression_as_sequence(#[case] expr: &str, #[case] tokens: Vec<Token>) {
        assert_eq!(tokens, tokenize(expr));
    }

    #[test]
    fn should_extract_whitespace_tokens() {
        let expr = " 1   + \t\t\t   \x0a2 ";

        let expected_sequence = vec![
            whitespace_token(" "),
            num_token("1"),
            whitespace_token("   "),
            add_token(),
            whitespace_token(" \t\t\t   \x0a"),
            num_token("2"),
            whitespace_token(" "),
        ];

        assert_eq!(expected_sequence, tokenize(expr));
    }

    fn str_to_token(expr: &str, token_type: TokenType) -> Token {
        Token::new(token_type, expr)
    }
}

#[cfg(test)]
pub mod test_helpers {
    use crate::engine::operator::OperatorType;
    use crate::engine::token::{Token, TokenType};

    pub fn invalid_token(content: &str) -> Token {
        Token::new(TokenType::Invalid, content)
    }

    pub fn whitespace_token(content: &str) -> Token {
        Token::new(TokenType::Whitespace, content)
    }

    pub fn num_token(content: &str) -> Token {
        Token::new(TokenType::Number, content)
    }

    pub fn add_token() -> Token<'static> {
        let operator_type = OperatorType::Addition;
        Token::new(TokenType::Operator(operator_type), operator_type.as_str())
    }

    pub fn sub_token() -> Token<'static> {
        let operator_type = OperatorType::Subtraction;
        Token::new(TokenType::Operator(operator_type), operator_type.as_str())
    }

    pub fn mul_token() -> Token<'static> {
        let operator_type = OperatorType::Multiplication;
        Token::new(TokenType::Operator(operator_type), operator_type.as_str())
    }
}
