use std::collections::HashMap;

use lazy_static::lazy_static;
use regex::Regex;

use crate::engine::operator::OperatorType;

/// A TokenType indicates the semantic nature of a token.
#[derive(Eq, PartialEq, Debug, Copy, Clone, Hash)]
pub enum TokenType {
    /// Represents an invalid sequence of characters.
    Invalid,
    /// Classifies a token as either an integer or a decimal numeral.
    Number,
    /// Classifies a token as a '+' sign operator.
    Operator(OperatorType),
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub struct Token<'a> {
    token_type: TokenType,
    // The position of the first character of the token in the original expression
    start: usize,
    // The content of the token
    content: &'a str,
}

impl<'a> Token<'a> {
    pub fn new(token_type: TokenType, content: &'a str, start: usize) -> Self {
        Self {
            token_type,
            start,
            content,
        }
    }

    pub fn token_type(&self) -> TokenType {
        self.token_type
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn length(&self) -> usize {
        self.content.len()
    }

    pub fn content(&self) -> &str {
        self.content
    }
}

/** Split the expression in an ordered sequence of tokens.\
Each character of the expression belongs to exactly one of the returned tokens.
*/
pub fn tokenize(expression: &str) -> Vec<Token> {
    let mut tokens = vec![];
    let mut cursor = 0;

    while cursor < expression.len() {
        cursor += measure_leading_whitespace(&expression[cursor..]);
        if cursor >= expression.len() {
            break;
        }
        let next_token = produce_next_token(&expression[cursor..], cursor);
        cursor += next_token.length();
        tokens.push(next_token);
    }

    tokens
}

lazy_static! {
    static ref WHITESPACE_PATTERN: Regex = Regex::new(r"^\s+").unwrap();
    /// TOKEN_PATTERNS represent the list of tokens parseable from the parser.
    static ref TOKEN_PATTERNS: HashMap<TokenType, Regex> = HashMap::from([
        (
            TokenType::Number,
            Regex::new(r"(\d+(\.\d*)?)|^(\.\d+)").unwrap()
        ),
        (
            TokenType::Operator(OperatorType::Addition),
            Regex::new(r"\+").unwrap()
        ),
        (
            TokenType::Operator(OperatorType::Subtraction),
            Regex::new(r"-").unwrap()
        ),
        (
            TokenType::Operator(OperatorType::Multiplication),
            Regex::new(r"×").unwrap()
        ),
    ]);
}

/// Returns the length of an eventual leading whitespace in the given expression.
fn measure_leading_whitespace(expr: &str) -> usize {
    let whitespace_prefix_match = WHITESPACE_PATTERN.find(expr);
    whitespace_prefix_match.map(|m| m.len()).unwrap_or(0)
}

/// Produce a token starting from the start of the given expression.\
/// If the start of the expression matches no token pattern, an [invalid token](TokenType::Invalid)
/// is produced. This token ends before the position of the next valid token.
fn produce_next_token(expr: &str, cursor: usize) -> Token {
    let mut tokens: Vec<Token> = TOKEN_PATTERNS
        .iter()
        .filter_map(|(token_type, pattern)| {
            build_token_matching_pattern(expr, *token_type, pattern)
        })
        .collect();

    tokens.sort_by_key(|token| token.start);

    let next_token_opt = tokens.first();

    if let Some(next_token) = next_token_opt {
        if next_token.start == 0 {
            // We re-create the token to change its start position to `cursor`
            Token::new(next_token.token_type, next_token.content, cursor)
        } else {
            Token::new(TokenType::Invalid, &expr[..next_token.start], cursor)
        }
    } else {
        Token::new(TokenType::Invalid, expr, cursor)
    }
}

/// Produces the first [`Token`] in the expression which matches the given Regex pattern.
///
/// Returns [`None`] if the expression contains no such token.
fn build_token_matching_pattern<'a>(
    expr: &'a str,
    token_type: TokenType,
    pattern: &Regex,
) -> Option<Token<'a>> {
    pattern
        .find(expr)
        .map(|re_match| Token::new(token_type, re_match.as_str(), re_match.start()))
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

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
        assert_eq!(
            vec![
                Token::new(TokenType::Number, "123.45", 0),
                Token::new(TokenType::Number, ".67", 6)
            ],
            tokenize(expr)
        );
    }

    #[rstest]
    #[case("+", OperatorType::Addition)]
    #[case("-", OperatorType::Subtraction)]
    #[case("×", OperatorType::Multiplication)]
    fn should_evaluate_operator_as_valid_token(#[case] expr: &str, #[case] op_type: OperatorType) {
        assert_eq!(
            vec![str_to_token(expr, TokenType::Operator(op_type))],
            tokenize(expr)
        );
    }

    #[rstest]
    #[case("123abc", vec![Token::new(TokenType::Number, "123", 0), Token::new(TokenType::Invalid, "abc", 3)])]
    #[case("abc123", vec![Token::new(TokenType::Invalid, "abc", 0), Token::new(TokenType::Number, "123", 3)])]
    #[case("123+.456", vec![Token::new(TokenType::Number, "123", 0),
                            Token::new(TokenType::Operator(OperatorType::Addition), "+" , 3),
                            Token::new(TokenType::Number, ".456", 4)
    ])]
    fn should_evaluate_expression_as_sequence(#[case] expr: &str, #[case] tokens: Vec<Token>) {
        assert_eq!(tokens, tokenize(expr));
    }

    #[test]
    fn should_ignore_white_spaces() {
        let expr = " 1   + \t\t\t   \x0a2 ";
        let expected_sequence = vec![
            Token::new(TokenType::Number, "1", 1),
            Token::new(TokenType::Operator(OperatorType::Addition), "+", 5),
            Token::new(TokenType::Number, "2", 14),
        ];
        assert_eq!(expected_sequence, tokenize(expr));
    }

    fn str_to_token(expr: &str, token_type: TokenType) -> Token {
        Token::new(token_type, expr, 0)
    }
}
