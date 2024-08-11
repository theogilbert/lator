use crate::engine::number::Number;
use crate::engine::operator::OperatorType;

/// An AST (Abstract Syntax Tree) represents a mathematical expression in the form of a tree.
///
/// For example, the expression 1+2*3 is represented as:
/// ```text
///    +
///  /   \
/// 1     *
///     /   \
///    2     3
/// ```
#[derive(Debug, PartialEq)]
pub enum Ast {
    /// An actual, raw number.
    /// Leaf nodes in AST are always [Ast::Number] nodes.
    Number(Number),
    /// Applies the operator described by [OperatorType] using two sub-ASTs.
    Operator(OperatorType, Box<Ast>, Box<Ast>),
    /// Applies the opposite function to value computed from the child AST.
    Negative(Box<Ast>),
}

impl Ast {
    pub fn resolve(&self) -> Number {
        match self {
            Ast::Number(num) => *num,
            Ast::Operator(op, lhs, rhs) => op.calculate(lhs.resolve(), rhs.resolve()),
            Ast::Negative(value) => -value.resolve(),
        }
    }
}

impl OperatorType {
    fn calculate(&self, lhs: Number, rhs: Number) -> Number {
        match self {
            OperatorType::Addition => lhs + rhs,
            OperatorType::Subtraction => lhs - rhs,
            OperatorType::Multiplication => lhs * rhs,
        }
    }

    /// Indicates the priority of an operator.\
    /// A higher value means a higher priority.
    pub fn priority(&self) -> usize {
        match self {
            OperatorType::Addition => 0,
            OperatorType::Subtraction => 0,
            OperatorType::Multiplication => 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::engine::ast::test_helpers::{add_node, neg_node, num_node};

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
}

/// This module provides helper functions to create ASTs with as little noise as possible.
#[cfg(test)]
pub mod test_helpers {
    use crate::engine::ast::Ast;
    use crate::engine::number::Number;
    use crate::engine::operator::OperatorType;

    pub fn num_node(value: &str) -> Ast {
        Ast::Number(Number::from_str(value).unwrap())
    }

    pub fn mul_node(lhs: Ast, rhs: Ast) -> Ast {
        Ast::Operator(OperatorType::Multiplication, Box::new(lhs), Box::new(rhs))
    }

    pub fn add_node(lhs: Ast, rhs: Ast) -> Ast {
        Ast::Operator(OperatorType::Addition, Box::new(lhs), Box::new(rhs))
    }

    pub fn sub_node(lhs: Ast, rhs: Ast) -> Ast {
        Ast::Operator(OperatorType::Subtraction, Box::new(lhs), Box::new(rhs))
    }

    pub fn neg_node(value: Ast) -> Ast {
        Ast::Negative(Box::new(value))
    }
}
