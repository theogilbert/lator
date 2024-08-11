use thiserror::Error;

use crate::engine::parser::parse;
use crate::engine::token::tokenize;

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
    /// Indicates that an expression is invalid.
    /// This error variant contains a field indicating from which position the expression
    /// becomes invalid.
    #[error("invalid expression")]
    InvalidExpression(usize),
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
    #[case("1+")]
    #[case("1++1")]
    fn test_should_fail_when_expression_is_invalid(#[case] expr: &str) {
        assert!(matches!(evaluate(expr), Err(Error::InvalidExpression(_))));
    }

    #[rstest]
    #[case("-1", "-1")]
    #[case("+1", "1")]
    fn test_should_evaluate_signed_number(#[case] expr: &str, #[case] result: &str) {
        assert_eq!(evaluate(expr), Ok(result.into()));
    }

    #[rstest]
    #[case("123", "123")]
    #[case("18+1.48", "19.48")]
    #[case(" 1+\t2+    3+4 ", "10")]
    #[case("1+2-4", "-1")]
    #[case("1+2×4", "9")]
    #[case("13×24-54-52-45×37×90+63", "-149581")]
    #[case("91×59×41×88×21+69+67×8", "406798997")]
    fn test_should_evaluate_valid_expressions(#[case] num_repr: &str, #[case] result: &str) {
        assert_eq!(evaluate(num_repr), Ok(result.into()));
    }
}
