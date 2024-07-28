use thiserror::Error;

use crate::engine::parser::parse;
use crate::engine::token::{tokenize, Token};

mod ast;
mod number;
mod operator;
mod parser;
mod token;

#[derive(Error, Debug, PartialEq)]
pub enum Error {
    /// Indicates that an expression is empty.
    /// Empty expressions are considered as invalid as no result can be produced from
    /// such expressions.
    #[error("empty expression")]
    EmptyExpression(),
    #[error("number expression {0} has an invalid format: {1}")]
    InvalidNumberExpr(String, String),
    /// Indicates that an expression is invalid.
    /// This error variant contains a TextSpan to indicate the portion of the expression that is invalid.
    #[error("invalid expression")]
    InvalidExpression(TextSpan),
}

// Represents the position of a contiguous section of a String.
#[derive(Debug, PartialEq)]
pub struct TextSpan {
    pub start: usize,
    pub length: usize,
}

impl TextSpan {
    pub fn new(start: usize, length: usize) -> Self {
        TextSpan { start, length }
    }
}

impl Into<TextSpan> for &Token<'_> {
    fn into(self) -> TextSpan {
        TextSpan {
            start: self.start(),
            length: self.length(),
        }
    }
}

/** Evaluates textual expressions */
pub fn evaluate(expr: &str) -> Result<String, Error> {
    let tokens = tokenize(expr);
    let ast_root = parse(&tokens)?;

    Ok(ast_root.resolve().to_string())
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::{evaluate, Error};

    #[rstest]
    #[case("")]
    #[case("   \t ")]
    fn test_should_fail_when_expression_is_empty(#[case] expr: &str) {
        assert_eq!(evaluate(expr), Err(Error::EmptyExpression()));
    }

    #[rstest]
    #[case("invalid")]
    #[case("+1")]
    #[case("1+")]
    #[case("1++1")]
    fn test_should_fail_when_expression_is_invalid(#[case] expr: &str) {
        assert!(matches!(evaluate(expr), Err(Error::InvalidExpression(_))));
    }

    #[rstest]
    #[case("123", "123")]
    #[case("18+1.48", "19.48")]
    #[case(" 1+\t2+    3+4 ", "10")]
    fn test_should_evaluate_valid_expressions(#[case] num_repr: &str, #[case] result: &str) {
        assert_eq!(evaluate(num_repr), Ok(result.into()));
    }
}
