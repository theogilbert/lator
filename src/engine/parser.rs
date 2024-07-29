use crate::engine::ast::Ast;
use crate::engine::number::Number;
use crate::engine::operator::OperatorType;
use crate::engine::token::{Token, TokenType};
use crate::engine::Error;

pub fn parse(tokens: &[Token]) -> Result<Ast, Error> {
    return build_naive_tree(tokens);
}

// This function builds a naive AST in that it does not care about priority of operators.
fn build_naive_tree(tokens: &[Token]) -> Result<Ast, Error> {
    if tokens.is_empty() {
        return Err(Error::EmptyExpression());
    }

    let mut current_ast_root: Option<Ast> = None;
    let mut previous_operator: Option<OperatorType> = None;

    for (idx, token) in tokens.iter().enumerate() {
        match token.token_type() {
            TokenType::Invalid => {
                return Err(invalid_token_err(token));
            }
            TokenType::Number => {
                if current_ast_root.is_some() && previous_operator.is_none() {
                    return Err(invalid_token_err(token));
                }

                let current_node = Ast::Number(Number::from_str(token.content())?);
                if let Some(ope_type) = previous_operator {
                    let lhs = current_ast_root
                        .ok_or_else(|| invalid_token_err(&tokens[idx - 1]))?;
                    let ope = build_operator(ope_type, lhs, current_node);
                    current_ast_root = Some(ope);
                    previous_operator = None;
                } else {
                    current_ast_root = Some(current_node);
                }
            }
            TokenType::Operator(ope_type) => {
                if previous_operator.is_some() {
                    return Err(invalid_token_err(token));
                }
                previous_operator = Some(ope_type);
            }
        }
    }

    // unwrap() is safe as we checked that tokens is not empty
    let last_token = tokens.last().unwrap();

    if previous_operator.is_some() {
        return Err(invalid_token_err(last_token));
    }

    current_ast_root.ok_or(invalid_token_err(last_token))
}

fn invalid_token_err(token: &Token) -> Error {
    Error::InvalidExpression(token.start())
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

    const ADD_TOKEN_TYPE: TokenType = TokenType::Operator(OperatorType::Addition);

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
            Token::new(ADD_TOKEN_TYPE, "+", 0),
            Token::new(TokenType::Number, "1.5", 3),
        ];

        let expected_tree = Ast::Operator(
            OperatorType::Addition,
            number_node("49").into(),
            number_node("1.5").into(),
        );
        assert_eq!(expected_tree, parse(&tokens).unwrap());
    }

    #[test]
    fn test_parsing_no_tokens_should_fail() {
        let result = parse(&[]);
        assert_eq!(result.err().unwrap(), Error::EmptyExpression());
    }

    #[test]
    fn test_parsing_sequence_with_only_operator_should_fail() {
        assert_eq!(
            Err(Error::InvalidExpression(0)),
            parse(&[Token::new(ADD_TOKEN_TYPE, "+", 0)])
        );
    }

    #[test]
    fn test_parsing_sequence_with_only_operator_and_no_lhs_should_fail() {
        let seq = [
            Token::new(ADD_TOKEN_TYPE, "+", 0),
            Token::new(TokenType::Number, "2", 1),
        ];
        assert_eq!(Err(Error::InvalidExpression(0)), parse(&seq));
    }

    #[test]
    fn test_parsing_sequence_with_adjacent_numbers_should_fail() {
        let seq = [
            Token::new(TokenType::Number, "1", 0),
            Token::new(TokenType::Number, "2", 1),
        ];
        assert_eq!(Err(Error::InvalidExpression(1)), parse(&seq));
    }

    #[test]
    fn test_parsing_sequence_with_adjacent_operators_should_fail() {
        let seq = [
            Token::new(TokenType::Number, "1", 0),
            Token::new(ADD_TOKEN_TYPE, "+", 1),
            Token::new(ADD_TOKEN_TYPE, "+", 2),
            Token::new(TokenType::Number, "2", 3),
        ];
        assert_eq!(Err(Error::InvalidExpression(2)), parse(&seq));
    }

    #[test]
    fn test_parsing_sequence_with_final_operator_should_fail() {
        let seq = [
            Token::new(TokenType::Number, "1", 0),
            Token::new(ADD_TOKEN_TYPE, "+", 1),
        ];
        assert_eq!(Err(Error::InvalidExpression(1)), parse(&seq));
    }

    fn number_node(value: &str) -> Ast {
        Ast::Number(Number::from_str(value).unwrap())
    }
}
