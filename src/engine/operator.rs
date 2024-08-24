use std::fmt::{Display, Formatter, Write};

/// Describes an operation to perform on values.
#[derive(Eq, PartialEq, Debug, Copy, Clone, Hash)]
pub enum OperatorType {
    Addition,
    Subtraction,
    Multiplication,
    Division,
}

impl OperatorType {
    /// Indicates the priority of an operator. A higher value means a higher priority.\
    /// Higher priority operators should be evaluated first.
    pub fn priority(&self) -> usize {
        match self {
            OperatorType::Addition => 0,
            OperatorType::Subtraction => 0,
            OperatorType::Multiplication => 1,
            OperatorType::Division => 1,
        }
    }
}

impl Display for OperatorType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let repr = match self {
            OperatorType::Addition => '+',
            OperatorType::Subtraction => '-',
            OperatorType::Multiplication => '×',
            OperatorType::Division => '÷',
        };

        f.write_char(repr)
    }
}

/// Describes either a positive `+` or negative `-` sign which can be present in front of
/// an expression.
pub enum Sign {
    Positive,
    Negative,
}

impl Sign {
    pub fn from_operator(op_type: OperatorType) -> Result<Self, ()> {
        match op_type {
            OperatorType::Addition => Ok(Self::Positive),
            OperatorType::Subtraction => Ok(Self::Negative),
            _ => Err(()),
        }
    }

    pub fn is_negative(&self) -> bool {
        match &self {
            Sign::Positive => false,
            Sign::Negative => true,
        }
    }
}
