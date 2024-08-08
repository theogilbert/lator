use std::fmt::Display;
use std::num::ParseFloatError;
use std::ops::{Add, Mul, Neg, Sub};

use crate::engine::Error;

/// A wrapper around a decimal number.
#[derive(Copy, Clone, Debug, Default, PartialEq)]
pub struct Number {
    value: f64,
}

impl Number {
    pub fn from_str(decimal_repr: &str) -> Result<Self, Error> {
        let value = decimal_repr.parse().map_err(|pre: ParseFloatError| {
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
        Number {
            value: self.value + rhs.value,
        }
    }
}

impl Sub for Number {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Number {
            value: self.value - rhs.value,
        }
    }
}

impl Mul for Number {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Number {
            value: self.value * rhs.value,
        }
    }
}

impl Neg for Number {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Number { value: -self.value }
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

    #[test]
    fn test_sub_number() {
        let lhs = Number::from_str("3.5").unwrap();
        let rhs = Number::from_str("1").unwrap();
        assert_eq!("2.5", (lhs - rhs).to_string());
    }

    #[test]
    fn test_mul_number() {
        let lhs = Number::from_str("3.5").unwrap();
        let rhs = Number::from_str("3").unwrap();
        assert_eq!("10.5", (lhs * rhs).to_string());
    }

    #[test]
    fn test_negate_number() {
        let num = Number::from_str("3.5").unwrap();
        assert_eq!("-3.5", (-num).to_string());
    }
}
