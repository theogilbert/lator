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
    #[error("empty expression")]
    EmptyExpression(),
    #[error("number expression {0} has an invalid format: {1}")]
    InvalidNumberExpr(String, String),
    #[error("invalid expression")]
    InvalidExpression(),
}

/** Evaluates textual expressions */
pub fn evaluate(expr: &str) -> Result<String, Error> {
    let tokens = tokenize(expr);

    if tokens.is_empty() {
        return Err(Error::EmptyExpression());
    }

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
        assert_eq!(evaluate(expr), Err(Error::InvalidExpression()));
    }

    #[rstest]
    #[case("123", "123")]
    #[case("18+1.48", "19.48")]
    #[case(" 1+\t2+    3+4 ", "10")]
    fn test_should_evaluate_valid_expressions(#[case] num_repr: &str, #[case] result: &str) {
        assert_eq!(evaluate(num_repr), Ok(result.into()));
    }
}
