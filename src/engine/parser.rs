use crate::engine::ast::Ast;
use crate::engine::number::Number;
use crate::engine::operator::{OperatorType, Sign};
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
    let mut states = NestedStates::default();

    for token in tokens.iter() {
        let result = match token.token_type() {
            TokenType::OpenParenthesis => Ok(states.open_parenthesis(cursor)),
            TokenType::CloseParenthesis => states.close_parenthesis(),
            _ => states.update_from_token(token),
        };

        result.or(Err(Error::InvalidExpression(cursor)))?;
        cursor += token.length();
    }

    states.into_value(tokens)
}

/// NestedStates provides a way to parse a new [AST] while keeping the currently parsed AST
/// in memory.
/// This allows us to start with a fresh parsing [State] when opening a new parenthesis.
/// When closing a parenthesis, the AST built from within the parenthesis can then be added to the
/// parsing State from before the opening parenthesis.
struct NestedStates {
    states: Vec<MarkedState>,
}

/// A MarkedState associates a position to the beginning of a [State].
struct MarkedState {
    position: usize,
    value: State,
}

impl MarkedState {
    fn new(position: usize, value: State) -> Self {
        Self { position, value }
    }
}

impl Default for NestedStates {
    fn default() -> Self {
        Self {
            states: vec![MarkedState::new(0, State::Empty)],
        }
    }
}

impl NestedStates {
    fn update_from_token(&mut self, token: &Token) -> Result<(), ()> {
        self.transform_current_state(|state| state.update_from_next_token(token))
    }

    fn open_parenthesis(&mut self, cursor: usize) {
        self.states.push(MarkedState::new(cursor, State::Empty));
    }

    fn close_parenthesis(&mut self) -> Result<(), ()> {
        if self.states.len() <= 1 {
            return Err(());
        }

        let closed_sub_expr_state = self.states.pop().unwrap().value;
        let ast = closed_sub_expr_state.into_value()?;
        let parenthesized = Ast::Parenthesized(Box::new(ast));

        self.transform_current_state(|state| state.update_from_value(parenthesized))
    }

    fn transform_current_state(
        &mut self,
        transform: impl FnOnce(State) -> Result<State, ()>,
    ) -> Result<(), ()> {
        let current_state = self.states.pop().unwrap();
        let updated_state = transform(current_state.value)?;
        let new_marked_state = MarkedState::new(current_state.position, updated_state);
        self.states.push(new_marked_state);
        Ok(())
    }

    fn into_value(mut self, tokens: &[Token]) -> Result<Ast, Error> {
        let current_state = self.states.pop().unwrap();

        if !self.states.is_empty() {
            return Err(Error::InvalidExpression(current_state.position));
        }

        match current_state.value {
            State::Value(ast) => Ok(ast),
            State::Empty => Err(Error::EmptyExpression()),
            State::PendingOperation(_, _, _) => {
                let op_position = find_position_of_unfinished_operator(tokens);
                Err(Error::InvalidExpression(op_position))
            }
            State::PendingSign(_) => Err(Error::InvalidExpression(0)),
        }
    }
}

/// This class represents the state of the parser while transforming a sequence of tokens forming
/// an expression into an AST.
enum State {
    /// No tokens have been parsed yet. This is the initial state of the context.
    Empty,
    /// A sign has been parsed and will be added to the next value or expression.
    PendingSign(Sign),
    /// The parsed tokens resolve to a computable value.
    Value(Ast),
    /// An operation is pending, meaning that the last token which has been parsed is
    /// an operation sign.
    /// 1. The first field of this variant is the left hand side value.
    /// 2. The second field indicates the operation to perform on this value.
    /// 3. The third field contains the parser used to build the right hand side value.
    ///
    /// The operation will be complete when the right hand side value is parsed.
    PendingOperation(Ast, OperatorType, Box<State>),
}

impl State {
    fn update_from_next_token(self, token: &Token) -> Result<Self, ()> {
        match token.token_type() {
            TokenType::Invalid => Err(()),
            TokenType::Whitespace => Ok(self), // Whitespaces do not affect the parsing context.
            TokenType::Number => self.update_from_number(token.content()),
            TokenType::Operator(op_type) => self.update_from_operator(op_type),
            TokenType::OpenParenthesis | TokenType::CloseParenthesis => Err(()),
        }
    }

    fn update_from_value(self, ast: Ast) -> Result<Self, ()> {
        let new_value = match self {
            Self::Empty | Self::PendingSign(Sign::Positive) => Ok(ast),
            Self::PendingSign(Sign::Negative) => Ok(Ast::Negative(Box::new(ast))),
            Self::Value(_) => Err(()),
            Self::PendingOperation(lhs, op_type, rhs) => {
                let updated_rhs = (*rhs).update_from_value(ast)?;
                Self::build_operation_node(lhs, op_type, updated_rhs.into_value()?)
            }
        }?;

        Ok(Self::Value(new_value))
    }

    fn update_from_number(self, num_text: &str) -> Result<State, ()> {
        let num_node = Ast::Number(Number::from_str(num_text)?);

        let resolvable_node: Ast = match self {
            Self::Empty | Self::PendingSign(Sign::Positive) => Ok(num_node),
            Self::PendingSign(Sign::Negative) => Ok(Ast::Negative(Box::new(num_node))),
            Self::Value(_) => Err(()),
            Self::PendingOperation(lhs, op_type, rhs_parser) => {
                let new_rhs_parser = (*rhs_parser).update_from_number(num_text)?;
                Self::build_operation_node(lhs, op_type, new_rhs_parser.into_value()?)
            }
        }?;

        Ok(Self::Value(resolvable_node))
    }

    fn build_operation_node(lhs: Ast, op_type: OperatorType, num_node: Ast) -> Result<Ast, ()> {
        Ok(Ast::Operator(op_type, Box::new(lhs), Box::new(num_node)))
    }

    fn update_from_operator(self, new_operator: OperatorType) -> Result<State, ()> {
        Ok(match self {
            Self::Empty => Self::PendingSign(Sign::from_operator(new_operator)?),
            Self::PendingSign(sign) => {
                let new_sign = Sign::from_operator(new_operator)?;
                Self::PendingSign(sign.combine(new_sign))
            }
            Self::Value(lhs) => Self::PendingOperation(lhs, new_operator, Box::new(State::Empty)),
            Self::PendingOperation(lhs, op_type, mut rhs_parser) => {
                rhs_parser = Box::new((*rhs_parser).update_from_operator(new_operator)?);
                Self::PendingOperation(lhs, op_type, rhs_parser)
            }
        })
    }

    fn into_value(self) -> Result<Ast, ()> {
        match self {
            State::Value(val) => Ok(val),
            _ => Err(()),
        }
    }
}

/// Given a sequence of tokens, retrieve the position of the last unfinished operator, ignoring
/// following sign operators.
fn find_position_of_unfinished_operator(tokens: &[Token]) -> usize {
    let mut current_position = 0;
    let mut last_operator_position = 0;
    let mut previous_token_was_operator = false;

    for token in tokens {
        if !previous_token_was_operator && token.is_operator() {
            last_operator_position = current_position;
        }

        if !token.is_whitespace() {
            previous_token_was_operator = token.is_operator();
        }

        current_position += token.length();
    }

    last_operator_position
}

/// Re-arrange a naive AST to make sure that operators with higher priority are evaluated first.\
/// As an AST is evaluated from the bottom up, this means that unless parenthesis are involved,
/// higher priority operators should end up deeper in the tree than lower priority operators.
fn prioritize_operators(naive_tree: Ast) -> Ast {
    match naive_tree {
        Ast::Number(_) | Ast::Negative(_) => naive_tree, // no further prioritization on these nodes
        Ast::Operator(kind, lhs, rhs) => {
            let mut operator = Operator::new(kind, *lhs, *rhs);

            operator.lhs = prioritize_operators(operator.lhs);
            operator = operator.reorder_with_left_branch();

            operator.rhs = prioritize_operators(operator.rhs);
            operator = operator.reorder_with_right_branch();

            operator.into_ast()
        }
        Ast::Parenthesized(value) => {
            let prioritized_subtree = prioritize_operators(*value);
            Ast::Parenthesized(Box::new(prioritized_subtree))
        }
    }
}

struct Operator {
    op_type: OperatorType,
    lhs: Ast,
    rhs: Ast,
}

impl Operator {
    pub fn new(op_type: OperatorType, lhs: Ast, rhs: Ast) -> Self {
        Operator { op_type, lhs, rhs }
    }

    pub fn into_ast(self) -> Ast {
        Ast::Operator(self.op_type, Box::new(self.lhs), Box::new(self.rhs))
    }

    /// If the parent operation should be evaluated before its left child, swap them such as:
    ///
    /// ```text
    ///  (a+b)×c  becomes  a+(b×c)
    ///     ×                 +
    ///    / \               / \
    ///   +   c             a   ×
    ///  / \                   / \
    /// a   b                 b   c
    /// ```
    pub fn reorder_with_left_branch(self) -> Operator {
        match self.lhs {
            Ast::Operator(child_op_type, child_lhs, child_rhs)
                if self.op_type.priority() > child_op_type.priority() =>
            {
                let prioritized = Ast::Operator(self.op_type, child_rhs, Box::new(self.rhs));
                Operator::new(child_op_type, *child_lhs, prioritized)
            }
            _ => self,
        }
    }

    /// If the parent operation should be evaluated before its right child, swap them such as:
    ///
    /// ```text
    ///  a×(b+c)  becomes  (a×b)+c
    ///     ×                 +
    ///    / \               / \
    ///   a   +             ×   c
    ///      / \           / \
    ///     b   c         a   b
    /// ```
    pub fn reorder_with_right_branch(self) -> Operator {
        match self.rhs {
            Ast::Operator(child_op_type, child_lhs, child_rhs)
                if self.op_type.priority() > child_op_type.priority() =>
            {
                let prioritized = Ast::Operator(self.op_type, Box::new(self.lhs), child_lhs);
                Operator::new(child_op_type, prioritized, *child_rhs)
            }
            _ => self,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::ast::test_helpers::*;
    use crate::engine::parser::parse;
    use crate::engine::token::test_helpers::{
        add_token, close_par_token, div_token, mul_token, num_token, open_par_token, sub_token,
    };
    use crate::engine::token::Token;
    use crate::engine::Error;
    use rstest::rstest;

    #[test]
    fn test_parsing_no_tokens_should_fail() {
        assert_eq!(Err(Error::EmptyExpression()), parse(&[]));
    }

    #[test]
    fn test_parsing_one_number_token_should_produce_number_node() {
        assert_eq!(Ok(num_node("49")), parse(&[num_token("49")]));
    }

    #[test]
    fn test_parsing_negative_number_should_produce_value_node() {
        let tokens = [sub_token(), num_token("1")];
        let expected_tree = neg_node(num_node("1"));

        // -1 is parsed into the tree (0-1)
        assert_eq!(Ok(expected_tree), parse(&tokens));
    }

    #[test]
    fn test_parsing_positive_number_should_produce_value_node() {
        let tokens = [add_token(), num_token("1")];
        let expected_tree = num_node("1");

        assert_eq!(Ok(expected_tree), parse(&tokens));
    }

    #[test]
    fn test_positive_sign_following_operator_should_be_ignored() {
        let tokens = [num_token("1"), mul_token(), add_token(), num_token("2")];
        let expected_tree = mul_node(num_node("1"), num_node("2"));

        assert_eq!(Ok(expected_tree), parse(&tokens));
    }

    #[test]
    fn test_negative_sign_following_operator_should_turn_rhs_to_negative() {
        let tokens = [num_token("1"), mul_token(), sub_token(), num_token("2")];
        let expected_tree = mul_node(num_node("1"), neg_node(num_node("2")));

        assert_eq!(Ok(expected_tree), parse(&tokens));
    }

    #[test]
    fn test_pair_number_of_negative_sign_following_operator_should_turn_rhs_to_positive() {
        let tokens = [
            num_token("1"),
            mul_token(),
            sub_token(),
            add_token(),
            sub_token(),
            num_token("2"),
        ];
        let expected_tree = mul_node(num_node("1"), num_node("2"));

        assert_eq!(Ok(expected_tree), parse(&tokens));
    }

    #[test]
    fn test_parsing_addition_token_sequence_should_produce_add_node() {
        let tokens = [num_token("49"), add_token(), num_token("1.5")];

        let expected_tree = add_node(num_node("49"), num_node("1.5"));
        assert_eq!(Ok(expected_tree), parse(&tokens));
    }

    #[test]
    fn test_parsing_sequence_with_only_operator_should_fail() {
        assert_eq!(Err(Error::InvalidExpression(0)), parse(&[add_token()]));
    }

    #[rstest]
    #[case(&[add_token(), num_token("1")])]
    #[case(&[sub_token(), num_token("1")])]
    fn test_parsing_sequence_starting_with_sign_should_succeed(#[case] seq: &[Token]) {
        assert!(parse(seq).is_ok())
    }

    #[rstest]
    #[case(&[mul_token(), num_token("1")])]
    #[case(&[div_token(), num_token("1")])]
    fn test_parsing_sequence_starting_with_non_sign_op_should_fail(#[case] seq: &[Token]) {
        assert!(matches!(parse(seq), Err(Error::InvalidExpression(0))));
    }

    #[test]
    fn test_parsing_sequence_with_adjacent_numbers_should_fail() {
        let seq = [num_token("1"), num_token("2")];
        assert_eq!(Err(Error::InvalidExpression(1)), parse(&seq));
    }

    #[test]
    fn test_parsing_sequence_ending_with_operator_should_fail() {
        let seq = [num_token("1"), add_token()];
        assert_eq!(Err(Error::InvalidExpression(1)), parse(&seq));
    }

    #[test]
    fn test_parsing_parenthesized_expression_should_produce_prioritized_node() {
        let seq = [open_par_token(), num_token("1"), close_par_token()];

        let expected_tree = prioritized_node(num_node("1"));
        assert_eq!(Ok(expected_tree), parse(&seq));
    }

    #[rstest]
    #[case(&[
        num_token("1"), add_token(), open_par_token(), num_token("1")],
        Error::InvalidExpression(2))
    ]
    #[case(&[num_token("1"), close_par_token()], Error::InvalidExpression(1))]
    fn test_parsing_expression_should_fail_when_parentheses_do_not_match(
        #[case] seq: &[Token],
        #[case] err: Error,
    ) {
        assert_eq!(Err(err), parse(&seq), "{:?}", seq);
    }

    #[test]
    fn test_parsing_expression_should_fail_when_parenthesis_closes_on_pending_operation() {
        let seq = [
            open_par_token(),
            num_token("1"),
            add_token(),
            close_par_token(),
        ];
        assert_eq!(Err(Error::InvalidExpression(3)), parse(&seq), "{:?}", seq);
    }

    #[test]
    fn test_parsing_expression_should_fail_when_parentheses_englobe_nothing() {
        let seq = [open_par_token(), close_par_token()];
        assert_eq!(Err(Error::InvalidExpression(1)), parse(&seq), "{:?}", seq);
    }
}

#[cfg(test)]
mod test_prioritization {
    use rstest::rstest;

    use crate::engine::ast::test_helpers::*;
    use crate::engine::ast::Ast;
    use crate::engine::parser::{parse, prioritize_operators};
    use crate::engine::token::test_helpers::*;
    use crate::engine::token::Token;
    use crate::engine::Error;

    #[test]
    fn should_prioritize_tree_when_lhs_has_lower_priority() {
        let original_tree = mul_node(add_node(num_node("1"), num_node("2")), num_node("3"));

        prioritize_and_check_tree(original_tree);
    }

    #[test]
    fn should_prioritize_tree_when_rhs_has_lower_priority() {
        let original_tree = div_node(num_node("1"), add_node(num_node("2"), num_node("3")));

        prioritize_and_check_tree(original_tree);
    }

    #[test]
    fn should_prioritize_tree_when_lhs_and_rhs_have_lower_priority() {
        let original_tree = mul_node(
            add_node(num_node("1"), num_node("2")),
            add_node(num_node("3"), num_node("4")),
        );

        prioritize_and_check_tree(original_tree);
    }

    #[test]
    fn should_prioritize_multi_level_naive_tree_using_operator_priority() {
        // A tree naively parsed as ((1+2)*3)+4 should be updated to 1+(2*3)+4
        let original_tree = add_node(
            mul_node(add_node(num_node("1"), num_node("2")), num_node("3")),
            num_node("4"),
        );

        prioritize_and_check_tree(original_tree);
    }

    fn prioritize_and_check_tree(original_tree: Ast) {
        let original_repr = original_tree.to_string();

        let prioritized_tree = prioritize_operators(original_tree);
        let prioritized_repr = prioritized_tree.to_string();

        assert_subtree_is_prioritized(prioritized_tree);
        // the order of numbers and operators should be retained:
        assert_eq!(original_repr, prioritized_repr);
    }

    /// A tree is evaluated from the bottom-up.\
    /// Hence, in a prioritized tree, children nodes should never have lower priorities than
    /// their parents.
    fn assert_subtree_is_prioritized(ast: Ast) {
        match ast {
            Ast::Number(_) | Ast::Negative(_) => {}
            Ast::Operator(op_kind, lhs, rhs) => {
                assert!(
                    node_priority(&lhs) >= op_kind.priority(),
                    "Left child {:?} has a lower priority than parent operator {:?}",
                    lhs,
                    op_kind
                );
                assert!(
                    node_priority(&rhs) >= op_kind.priority(),
                    "Right child {:?} has a lower priority than parent operator {:?}",
                    rhs,
                    op_kind
                );
                assert_subtree_is_prioritized(*lhs);
                assert_subtree_is_prioritized(*rhs);
            }
            Ast::Parenthesized(value) => assert_subtree_is_prioritized(*value),
        }
    }

    fn node_priority(ast: &Ast) -> usize {
        match ast {
            Ast::Number(_) => usize::MAX,
            Ast::Operator(op_type, _, _) => op_type.priority(),
            Ast::Negative(value) => node_priority(value),
            Ast::Parenthesized(_) => usize::MAX,
        }
    }

    #[test]
    fn should_support_prioritizing_when_children_are_negative() {
        let naive_ast = add_node(neg_node(num_node("1")), neg_node(num_node("2")));

        assert_eq!(naive_ast, prioritize_operators(naive_ast.clone()));
    }

    #[test]
    fn should_not_prioritize_mul_over_explicitly_prioritized_add() {
        let naive_ast = mul_node(
            num_node("1"),
            prioritized_node(add_node(num_node("2"), num_node("3"))),
        );

        assert_eq!(naive_ast, prioritize_operators(naive_ast.clone()));
    }

    #[rstest]
    #[case(&[num_token("1"), mul_token(), whitespace_token(" "), ], 1)]
    #[case(&[num_token("1"), whitespace_token(" "), mul_token()], 2)]
    #[case(&[num_token("1"), whitespace_token(" "), add_token(),
                whitespace_token(""), sub_token(), whitespace_token("")], 2)]
    fn should_detect_last_invalid_operator_position(#[case] tokens: &[Token], #[case] pos: usize) {
        assert_eq!(Err(Error::InvalidExpression(pos)), parse(tokens));
    }
}
