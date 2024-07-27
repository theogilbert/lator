use crate::engine::ast::Ast;
use crate::engine::Error;
use crate::engine::number::Number;
use crate::engine::operator::OperatorType;
use crate::engine::token::{Token, TokenType};

pub fn parse(tokens: &[Token]) -> Result<Ast, Error> {
    return build_naive_tree(tokens);
}

// This function builds a naive AST in that it does not care about priority of operators.
fn build_naive_tree(tokens: &[Token]) -> Result<Ast, Error> {
    if tokens.is_empty() {
        return Err(Error::InvalidExpression());
    }

    let mut previous_node: Option<Ast> = None;
    let mut previous_operator: Option<OperatorType> = None;

    for token in tokens {
        match token.token_type() {
            TokenType::Invalid => {
                return Err(Error::InvalidExpression());
            }
            TokenType::Number => {
                let current_node = Ast::Number(Number::from_str(token.content())?);
                if let Some(ope_type) = previous_operator {
                    let ope = build_operator(ope_type, previous_node.unwrap(), current_node);
                    previous_node = Some(ope);
                    previous_operator = None;
                } else {
                    previous_node = Some(current_node);
                }
            }
            TokenType::Operator(ope_type) => {
                previous_operator = Some(ope_type);
            }
        }
    }

    previous_node.ok_or(Error::InvalidExpression())
}

fn build_operator(operator_type: OperatorType, lhs: Ast, rhs: Ast) -> Ast {
    match operator_type {
        OperatorType::Addition => {
            Ast::Operator(OperatorType::Addition, Box::new(lhs), Box::new(rhs))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::ast::Ast;
    use crate::engine::number::Number;
    use crate::engine::operator::OperatorType;
    use crate::engine::parser::parse;
    use crate::engine::token::{Token, TokenType};
    use crate::engine::Error;

    #[test]
    fn test_parsing_no_tokens_should_fail() {
        let result = parse(&[]);
        assert_eq!(result.err().unwrap(), Error::InvalidExpression());
    }

    #[test]
    fn test_parsing_one_number_token_should_produce_number_node() {
        let token = Token::new(TokenType::Number, "49", 0);
        let result = parse(&[token]).unwrap();
        assert_eq!(number_node("49"), result);
    }

    #[test]
    fn test_parsing_addition_token_sequence_should_produce_add_node() {
        let tokens = [
            Token::new(TokenType::Number, "49", 0),
            Token::new(TokenType::Operator(OperatorType::Addition), "+", 2),
            Token::new(TokenType::Number, "1.5", 3),
        ];

        let expected_tree = Ast::Operator(
            OperatorType::Addition,
            number_node("49").into(),
            number_node("1.5").into(),
        );
        assert_eq!(expected_tree, parse(&tokens).unwrap());
    }

    fn number_node(value: &str) -> Ast {
        Ast::Number(Number::from_str(value).unwrap())
    }
}
