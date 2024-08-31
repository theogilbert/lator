use std::fmt::{Display, Formatter};

use crate::engine::number::Number;
use crate::engine::operator::OperatorType;

/// An AST (Abstract Syntax Tree) represents a mathematical expression in the form of a tree.
///
/// For example, the expression 1+2*3 is represented as:
/// ```text
///    +
///  /   \
/// 1     ×
///     /   \
///    2     3
/// ```
#[derive(Debug, PartialEq, Clone)]
pub enum Ast {
    /// An actual, raw number.
    /// Leaf nodes in AST are always [Ast::Number] nodes.
    Number(Number),
    /// Applies the operator described by [OperatorType] using two sub-ASTs.
    Operator(OperatorType, Box<Ast>, Box<Ast>),
    /// Applies the opposite function to value computed from the child AST.
    Negative(Box<Ast>),
    /// Denotes a section of the AST which should always be evaluated first, regardless of operator
    /// priority rules.
    Parenthesized(Box<Ast>),
}

impl Ast {
    /// Resolve the value from an AST, starting from the bottom nodes up to the root of the tree.
    pub fn resolve(self) -> Number {
        match self {
            Ast::Number(num) => num,
            Ast::Operator(op, lhs, rhs) => op.calculate(lhs.resolve(), rhs.resolve()),
            Ast::Negative(value) => -value.resolve(),
            Ast::Parenthesized(value) => value.resolve(),
        }
    }
}

impl Display for Ast {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Ast::Number(value) => write!(f, "{}", value),
            Ast::Operator(op_type, lhs, rhs) => write!(f, "{}{}{}", lhs, op_type, rhs),
            Ast::Negative(value) => write!(f, "-{}", value),
            Ast::Parenthesized(value) => write!(f, "({})", value),
        }
    }
}

impl OperatorType {
    fn calculate(&self, lhs: Number, rhs: Number) -> Number {
        match self {
            OperatorType::Addition => lhs + rhs,
            OperatorType::Subtraction => lhs - rhs,
            OperatorType::Multiplication => lhs * rhs,
            OperatorType::Division => lhs / rhs,
        }
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::engine::ast::test_helpers::{add_node, neg_node, num_node, prioritized_node};

    #[rstest]
    #[case("0")]
    #[case("123")]
    #[case("123.456")]
    fn should_parse_str_into_number(#[case] num_repr: &str) {
        let num_node = num_node(num_repr);
        assert_eq!(num_node.resolve().to_string(), num_repr);
    }

    #[test]
    fn should_add_leading_zero_when_number_starts_with_dot() {
        let num_node = num_node(".456");
        assert_eq!(num_node.resolve().to_string(), "0.456");
    }

    #[test]
    fn should_add_numbers() {
        let add = add_node(num_node(".456"), num_node("18.1"));
        assert_eq!(add.resolve().to_string(), "18.556");
    }

    #[test]
    fn should_negate_number() {
        let ast = neg_node(num_node("10"));
        assert_eq!(ast.resolve().to_string(), "-10")
    }

    #[test]
    fn should_return_original_value_when_prioritized() {
        let ast = prioritized_node(num_node("10"));
        assert_eq!(ast.resolve().to_string(), "10")
    }
}

/// This module provides helper functions to create ASTs with as little noise as possible.
#[cfg(test)]
pub mod test_helpers {
    use crate::engine::ast::Ast;
    use crate::engine::number::test_helpers::num;
    use crate::engine::operator::OperatorType;

    pub fn num_node(value: &str) -> Ast {
        Ast::Number(num(value))
    }

    pub fn mul_node(lhs: Ast, rhs: Ast) -> Ast {
        Ast::Operator(OperatorType::Multiplication, Box::new(lhs), Box::new(rhs))
    }

    pub fn div_node(lhs: Ast, rhs: Ast) -> Ast {
        Ast::Operator(OperatorType::Division, Box::new(lhs), Box::new(rhs))
    }

    pub fn add_node(lhs: Ast, rhs: Ast) -> Ast {
        Ast::Operator(OperatorType::Addition, Box::new(lhs), Box::new(rhs))
    }

    pub fn neg_node(value: Ast) -> Ast {
        Ast::Negative(Box::new(value))
    }

    pub fn prioritized_node(value: Ast) -> Ast {
        Ast::Parenthesized(Box::new(value))
    }
}
