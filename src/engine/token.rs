#[derive(Eq, PartialEq, Debug)]
enum Token<'a> {
    INVALID(&'a str),
}

fn tokenize(expr: &str) -> Vec<Token> {
    vec![Token::INVALID(expr)]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_evaluate_word_as_invalid_token() {
        let expr = "hello";
        assert_eq!(vec![Token::INVALID(expr)], tokenize(expr));
    }
}