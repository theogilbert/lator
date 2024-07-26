use thiserror::Error;

use crate::engine::token::{tokenize, TokenType};

mod token;
mod number;


#[derive(Error, Debug, PartialEq)]
pub enum Error {
    #[error("number expression {0} has an invalid format: {1}")]
    InvalidNumberExpr(String, String),
}

/** Evaluates textual expressions */
pub fn evaluate(expr: &str) -> Result<String, ()> {
    let tokens = tokenize(expr);

    if tokens.len() != 1 {
        return Err(());
    }

    let only_token = tokens.first().unwrap();
    match only_token.token_type() {
        TokenType::Number => Ok(only_token.content().to_string()),
        _ => Err(())
    }
}


#[cfg(test)]
mod tests {
    use super::evaluate;

    #[test]
    fn test_invalid_expr() {
        assert!(evaluate("invalid").is_err());
    }

    #[test]
    fn test_numerical_expr() {
        assert_eq!(evaluate("42"), Ok("42".into()));
    }
}