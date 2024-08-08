use crate::engine::ast::Ast;
use crate::engine::number::Number;
use crate::engine::operator::OperatorType;
use crate::engine::token::{Token, TokenType};
use crate::engine::Error;

/// Parses a sequence of tokens into an AST.\
/// Returns an error if the sequence is invalid (e.g. two Number tokens next to each others).\
/// An empty sequence is considered as invalid.
pub fn parse(tokens: &[Token]) -> Result<Ast, Error> {
    let ast = build_naive_tree(tokens)?;
    Ok(prioritize_operators(ast))
}

/// This function builds a naive AST that does not care about priority of operators.
/// The AST will always be left-aligned, meaning that the tree always develops through the left
/// branch of operator nodes.
///
/// For example, the expression 1+2+3+4 will be represented as:
/// ```text
///          +
///        /  \
///       +    4
///     /  \
///    +    3
///  /  \
/// 1    2
/// ```
///
/// This property is important as it allows us to later re-arrange the tree to respect the priority
/// of different operators.
fn build_naive_tree(tokens: &[Token]) -> Result<Ast, Error> {
    let mut cursor: usize = 0;
    let mut parsing_context = ParsingContext::Empty;

    for token in tokens.iter() {
        parsing_context = parsing_context.update_from_next_token(token, cursor)?;
        cursor += token.length();
    }

    match parsing_context {
        ParsingContext::Value(ast) => Ok(ast),
        ParsingContext::Empty => Err(Error::EmptyExpression()),
        ParsingContext::PendingOperation(_, _) => {
            // unwrap() is safe as we know that the tokens array is not empty
            let last_token = tokens.last().unwrap();
            Err(Error::InvalidExpression(cursor - last_token.length()))
        }
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
    fn update_from_next_token(self, token: &Token, token_pos: usize) -> Result<Self, Error> {
        match token.token_type() {
            TokenType::Invalid => Err(Error::InvalidExpression(token_pos)),
            TokenType::Whitespace => Ok(self),
            TokenType::Number => {
                let current_node = Ast::Number(Number::from_str(token.content())?);

                match self {
                    Self::Empty => Ok(Self::Value(current_node)),
                    Self::Value(_) => Err(Error::InvalidExpression(token_pos)),
                    Self::PendingOperation(lhs, op_type) => {
                        let ope = Ast::Operator(op_type, Box::new(lhs), Box::new(current_node));
                        Ok(Self::Value(ope))
                    }
                }
            }
            TokenType::Operator(ope_type) => match self {
                ParsingContext::Value(lhs) => Ok(Self::PendingOperation(lhs, ope_type)),
                _ => Err(Error::InvalidExpression(token_pos)),
            },
        }
    }
}

/// Re-arrange a naive AST to make sure that operators with higher priority are evaluated first.\
/// As an AST is evaluated from the bottom up, this means that unless parenthesis are involved,
/// higher priority operators should end up deeper in the tree than lower priority ancestor
/// operators.
fn prioritize_operators(naive_tree: Ast) -> Ast {
    match naive_tree {
        Ast::Number(_) => naive_tree,
        Ast::Operator(kind, lhs, rhs) => {
            // As documented in build_naive_tree, a naive tree should be left-aligned.
            // The right child should only be populated by number nodes.
            assert!(
                matches!(*rhs, Ast::Number(_)),
                "rhs of naive tree node is not a number: {:?}",
                *rhs
            );

            let left_ast = prioritize_operators(*lhs);
            match left_ast {
                Ast::Number(_) => Ast::Operator(kind, Box::new(left_ast), rhs),
                Ast::Operator(child_kind, child_lhs, child_rhs) => {
                    if kind.priority() > child_kind.priority() {
                        // Parent operator has higher priority than child operator.
                        // Parent operator should be applied first, and thus should be lower in
                        // the tree hierarchy.
                        let new_child = Ast::Operator(kind, child_rhs, rhs);
                        Ast::Operator(child_kind, child_lhs, Box::new(new_child))
                    } else {
                        let old_child = Ast::Operator(child_kind, child_lhs, child_rhs);
                        Ast::Operator(kind, Box::new(old_child), rhs)
                    }
                }
                Ast::Negative(_) => unimplemented!(),
            }
        }
        Ast::Negative(_) => unimplemented!(),
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::ast::test_helpers::*;
    use crate::engine::parser::{parse, prioritize_operators};
    use crate::engine::token::test_helpers::{add_token, num_token};
    use crate::engine::Error;

    #[test]
    fn test_parsing_one_number_token_should_produce_number_node() {
        let token = num_token("49");
        let result = parse(&[token]).unwrap();
        assert_eq!(num_node("49"), result);
    }

    #[test]
    fn test_parsing_addition_token_sequence_should_produce_add_node() {
        let tokens = [num_token("49"), add_token(), num_token("1.5")];

        let expected_tree = add_node(num_node("49"), num_node("1.5"));
        assert_eq!(expected_tree, parse(&tokens).unwrap());
    }

    #[test]
    fn test_parsing_no_tokens_should_fail() {
        let result = parse(&[]);
        assert_eq!(result.err().unwrap(), Error::EmptyExpression());
    }

    #[test]
    fn test_parsing_sequence_with_only_operator_should_fail() {
        assert_eq!(Err(Error::InvalidExpression(0)), parse(&[add_token()]));
    }

    #[test]
    fn test_parsing_sequence_with_only_operator_and_no_lhs_should_fail() {
        let seq = [add_token(), num_token("2")];
        assert_eq!(Err(Error::InvalidExpression(0)), parse(&seq));
    }

    #[test]
    fn test_parsing_sequence_with_adjacent_numbers_should_fail() {
        let seq = [num_token("1"), num_token("2")];
        assert_eq!(Err(Error::InvalidExpression(1)), parse(&seq));
    }

    #[test]
    fn test_parsing_sequence_with_adjacent_operators_should_fail() {
        let seq = [num_token("1"), add_token(), add_token(), num_token("2")];
        assert_eq!(Err(Error::InvalidExpression(2)), parse(&seq));
    }

    #[test]
    fn test_parsing_sequence_with_final_operator_should_fail() {
        let seq = [num_token("1"), add_token()];
        assert_eq!(Err(Error::InvalidExpression(1)), parse(&seq));
    }

    #[test]
    fn test_naive_tree_should_always_develop_through_left_branch() {
        let tokens = [
            num_token("1"),
            add_token(),
            num_token("2"),
            add_token(),
            num_token("3"),
            add_token(),
            num_token("4"),
        ];

        let expected_tree = add_node(
            add_node(add_node(num_node("1"), num_node("2")), num_node("3")),
            num_node("4"),
        );
        assert_eq!(expected_tree, parse(&tokens).unwrap());
    }

    #[test]
    fn should_prioritize_multi_level_naive_tree_using_operator_priority() {
        // At first the expression 1+2*3+4 will be naively parsed as ((1+2)*3)+4
        let naive_ast = add_node(
            mul_node(add_node(num_node("1"), num_node("2")), num_node("3")),
            num_node("4"),
        );
        // Once sorted, the AST should be transformed to (1+(2*3))+4 to run the multiplication first
        let sorted_ast = add_node(
            add_node(num_node("1"), mul_node(num_node("2"), num_node("3"))),
            num_node("4"),
        );

        assert_eq!(sorted_ast, prioritize_operators(naive_ast));
    }
}
