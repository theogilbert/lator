use thiserror::Error;

use crate::engine::ast::{Node, NumberNode};
use crate::engine::token::tokenize;

mod token;
mod ast;
mod number;


#[derive(Error, Debug, PartialEq)]
pub enum Error {
    #[error("this type of expression is not yet supported")]
    UnsupportedExpression(),
    #[error("number expression {0} has an invalid format: {1}")]
    InvalidNumberExpr(String, String),
}

/** Evaluates textual expressions */
pub fn evaluate(expr: &str) -> Result<String, Error> {
    let tokens = tokenize(expr);

    if tokens.len() != 1 {
        return Err(Error::UnsupportedExpression());
    }

    Ok(NumberNode::from_str(tokens[0].content())?.resolve().to_string())
}


#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::evaluate;

    #[test]
    fn test_invalid_expr() {
        assert!(evaluate("invalid").is_err());
    }


    #[rstest]
    #[case("123", "123")]
    fn test_should_evaluate_valid_expressions(#[case] num_repr: &str, #[case] result: &str) {
        assert_eq!(evaluate(num_repr), Ok(result.into()));
    }
}