use crate::engine::token::{Token, tokenize};

mod token;

/** Evaluates textual expressions */
pub fn evaluate(expr: &str) -> Result<String, ()> {
    let tokens = tokenize(expr);

    if tokens.len() != 1 {
        return Err(());
    }

    match tokens.first().unwrap() {
        Token::Number(num) => Ok(num.to_string()),
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