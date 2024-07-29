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

    let mut parsing_context = ParsingContext::Empty;

    for token in tokens.iter() {
        parsing_context = parsing_context.update_from_next_token(token)?;
    }

    // unwrap() is safe as we checked that tokens is not empty
    let last_token = tokens.last().unwrap();

    if let ParsingContext::Value(ast) = parsing_context {
        Ok(ast)
    } else {
        Err(Error::InvalidExpression(last_token.start()))
    }
}

/// This class represents the state of the parser while parsing an AST.
enum ParsingContext {
    /// No tokens have been parsed yet. This is the initial state of the context.
    Empty,
    /// The parsed tokens resolve to a computable value.
    Value(Ast),
    /// An operation is pending, meaning that the last token which has been parsed is
    /// an operation sign.
    /// 1. The first field of this variant is the left hand side value.
    /// 2. The second field indicates the operation to perform on this value.
    ///
    /// The operation will be complete when the right hand side value is parsed.
    PendingOperation(Ast, OperatorType),
}

impl ParsingContext {
    fn update_from_next_token(self, token: &Token) -> Result<Self, Error> {
        match token.token_type() {
            TokenType::Invalid => Err(Error::InvalidExpression(token.start())),
            TokenType::Number => {
                let current_node = Ast::Number(Number::from_str(token.content())?);

                match self {
                    Self::Empty => Ok(Self::Value(current_node)),
                    Self::Value(_) => Err(Error::InvalidExpression(token.start())),
                    Self::PendingOperation(lhs, op_type) => {
                        let ope = Ast::Operator(op_type, Box::new(lhs), Box::new(current_node));
                        Ok(Self::Value(ope))
                    }
                }
            }
            TokenType::Operator(ope_type) => match self {
                ParsingContext::Value(lhs) => Ok(Self::PendingOperation(lhs, ope_type)),
                _ => Err(Error::InvalidExpression(token.start())),
            },
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
