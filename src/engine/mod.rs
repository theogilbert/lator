/** Evaluates textual expressions */
pub fn evaluate(expr: &str) -> Result<String, ()> {
    if expr.parse::<f32>().is_err() {
       return Err(())
    }

    Ok(expr.into())
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