/// Describes an operation to perform on values.
#[derive(Eq, PartialEq, Debug, Copy, Clone, Hash)]
pub enum OperatorType {
    Addition,
    Subtraction,
    Multiplication,
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
