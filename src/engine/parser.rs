use crate::engine::ast::Ast;
use crate::engine::Error;
use crate::engine::number::Number;
use crate::engine::token::{Token, TokenType};

pub fn parse(tokens: &[Token]) -> Result<Ast, Error> {
    return build_naive_tree(tokens);
}

// This function builds a naive AST in that it does not care about priority of operators.
fn build_naive_tree(tokens: &[Token]) -> Result<Ast, Error> {
    if tokens.is_empty() {
        return Err(Error::InvalidExpression());
    }

    let mut node: Option<Ast> = None;

    for token in tokens {
        match token.token_type() {
            TokenType::Invalid => {
                return Err(Error::InvalidExpression());
            }
            TokenType::Number => {
                let current_node = Ast::Number(Number::from_str(token.content())?);
                node = Some(current_node);
            }
            TokenType::Operator(_) => {
                return Err(Error::UnsupportedExpression())
            }
        }
    }

    node.ok_or(Error::InvalidExpression())
}

#[cfg(test)]
mod tests {
    use crate::engine::Error;
    use crate::engine::parser::parse;
    use crate::engine::token::{Token, TokenType};

    #[test]
    fn test_parsing_no_tokens_should_fail() {
        let result = parse(&[]);
        assert_eq!(result.err().unwrap(), Error::InvalidExpression());
    }
    #[test]
    fn test_parsing_one_number_token_should_produce_number_node() {
        let token = Token::new(TokenType::Number, "49", 0);
        let result = parse(&[token]).unwrap();
        assert_eq!("49", result.resolve().to_string());
    }
}
