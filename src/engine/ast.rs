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
        }
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

    #[rstest]
    #[case("0")]
    #[case("123")]
    #[case("123.456")]
    fn should_parse_str_into_number(#[case] num_repr: &str) {
        let num_node = number(num_repr);
        assert_eq!(num_node.resolve().to_string(), num_repr);
    }

    #[test]
    fn should_add_leading_zero_when_number_starts_with_dot() {
        let num_node = number(".456");
        assert_eq!(num_node.resolve().to_string(), "0.456");
    }

    #[test]
    fn should_add_numbers() {
        let add = Ast::Operator(
            OperatorType::Addition,
            number(".456").into(),
            number("18.1").into(),
        );
        assert_eq!(add.resolve().to_string(), "18.556");
    }

    fn number(repr: &str) -> Ast {
        Ast::Number(Number::from_str(repr).unwrap())
    }
}
