use crate::engine::token::TokenCandidate::{Invalid, Number};

/** A token represents an atomic element in an expression. */
#[derive(Eq, PartialEq, Debug)]
pub enum Token<'a> {
    /** Having such a token in an expression should result in an invalid expression.
    All tokens which are not classified as another valid token type are invalid. */
    Invalid(&'a str),
    /** A simple number, which may or may not contain decimals.\
    The decimal separator is the dot `.` character. */
    Number(&'a str),
}

/** Split the expression in an ordered sequence of tokens.\
All characters of the expression should belong to at least and at most one and only one
of the returned tokens.
*/
pub fn tokenize(expression: &str) -> Vec<Token> {
    let mut scanner = ExpressionScanner::new(expression);

    let mut token_list: Vec<Token> = expression
        .chars()
        .filter_map(|char| scanner.scan(char))
        .collect();

    if let Some(final_token) = scanner.current_token() {
        token_list.push(final_token);
    }

    token_list
}

/** This structure can be used to scan an expression character by character, in order to find
tokens in this expression.
*/
struct ExpressionScanner<'a> {
    expression: &'a str,
    cursor: usize,
    token_start: usize,
    token_type: Option<TokenCandidate>,
}

impl<'a> ExpressionScanner<'a> {
    fn new(expr: &'a str) -> Self {
        ExpressionScanner {
            expression: expr,
            cursor: 0,
            token_start: 0,
            token_type: None,
        }
    }

    /**
    Scans an additional character in search of the next token.

    If this `character` is detected to be part of a new token, the previous token will be returned.\
    Otherwise, this method will return `None`.
     */
    fn scan(&mut self, character: char) -> Option<Token<'a>> {
        let end_of_token = self
            .token_type
            .as_mut()
            .is_some_and(|token_type| !token_type.scan_next_char(character));

        let mut token = None;
        if end_of_token {
            token = self.current_token();
        }

        if self.token_type.is_none() {
            self.token_type = Some(TokenCandidate::from_char(character));
            self.token_start = self.cursor;
        }

        self.cursor += 1;
        token
    }

    /**
    Returns the current token, which starts at the character following the previous token, and ends
    at the position of this builder's cursor in the expression.

    This method consumes the current token. Calling it a second time without scanning additional
    characters will return `None`.
     */
    fn current_token(&mut self) -> Option<Token<'a>> {
        self.token_type.take().map(|token_type| {
            let content = &self.expression[self.token_start..self.cursor];
            token_type.build_token(content)
        })
    }
}

/** Represents a token currently being scanned */
#[derive(Eq, PartialEq, Debug)]
enum TokenCandidate {
    Invalid,
    // `has_decimals` indicates whether this token already contains a decimal separator.
    Number { has_decimals: bool },
}

impl TokenCandidate {
    fn from_char(character: char) -> TokenCandidate {
        match character {
            '0'..='9' => Number {
                has_decimals: false,
            },
            '.' => Number { has_decimals: true },
            _ => Invalid,
        }
    }

    /**
    Scans the next character and returns true if it is a continuation of the current token.
     */
    fn scan_next_char(&mut self, character: char) -> bool {
        match self {
            Number { has_decimals: true } => character.is_ascii_digit(),
            Number {
                has_decimals: false,
            } => {
                if character == '.' {
                    *self = Number { has_decimals: true };
                    return true;
                }

                character.is_ascii_digit()
            }
            Invalid => true,
        }
    }

    fn build_token(self, content: &str) -> Token {
        match self {
            Number { has_decimals: _ } => Token::Number(content),
            Invalid => Token::Invalid(content),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[test]
    fn should_evaluate_empty_expr_as_no_token() {
        let expr = "";
        assert_eq!(Vec::<Token>::new(), tokenize(expr));
    }

    #[test]
    fn should_evaluate_word_as_invalid_token() {
        let expr = "hello";
        assert_eq!(vec![Token::Invalid(expr)], tokenize(expr));
    }

    #[rstest]
    #[case("00")]
    #[case("123")]
    #[case("123.45")]
    #[case(".3")]
    #[case("18.")]
    fn should_evaluate_number_as_valid_token(#[case] expr: &str) {
        assert_eq!(vec![Token::Number(expr)], tokenize(expr));
    }

    #[test]
    fn should_evaluate_number_with_two_decimal_separators_as_two_tokens() {
        let expr = "123.45.67";
        assert_eq!(
            vec![Token::Number("123.45"), Token::Number(".67")],
            tokenize(expr)
        );
    }

    #[rstest]
    #[case("123abc", vec![Token::Number("123"), Token::Invalid("abc")])]
    fn should_evaluate_expression_as_sequence(#[case] expr: &str, #[case] tokens: Vec<Token>) {
        assert_eq!(tokens, tokenize(expr));
    }
}
