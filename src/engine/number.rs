use std::num::ParseFloatError;
use std::fmt::Display;
use std::ops::Add;
use crate::engine::Error;

/// A wrapper around a decimal number.
#[derive(Copy, Clone, Debug, Default)]
pub struct Number {
    value: f64,
}

impl Number {

    pub fn from_str(decimal_repr: &str) -> Result<Self, Error> {
        let value = decimal_repr.parse().map_err(|pre:  ParseFloatError| {
            Error::InvalidNumberExpr(decimal_repr.to_string(), pre.to_string())
        })?;
        Ok(Number { value })
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Add for Number {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        return Number { value: self.value + rhs.value }
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::number::Number;

    #[test]
    fn test_display_number() {
        let num = Number::from_str("12.34").unwrap();
        assert_eq!("12.34", num.to_string())
    }

    #[test]
    fn test_add_number() {
        let lhs = Number::from_str(".123").unwrap();
        let rhs = Number::from_str("4").unwrap();
        assert_eq!("4.123", (lhs + rhs).to_string());
    }
}
