use crate::engine::number::Number;
use crate::engine::operator::OperatorType;

#[derive(Debug, PartialEq)]
pub enum Ast {
    Number(Number),
    Operator(OperatorType, Box<Ast>, Box<Ast>),
}

impl Ast {
    pub fn resolve(&self) -> Number {
        match self {
            Ast::Number(num) => *num,
            Ast::Operator(op, lhs, rhs) => op.calculate(lhs.resolve(), rhs.resolve()),
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
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::engine::ast::test_helpers::{add_node, num_node};

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
}

/// This module provides helper functions to create ASTs with at little noise as possible.
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
}
