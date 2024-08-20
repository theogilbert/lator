use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A wrapper around a decimal number.
#[derive(Copy, Clone, Default, PartialEq)]
pub struct Number {
    value: f64,
}

impl Number {
    pub fn zero() -> Self {
        Number { value: 0. }
    }

    pub fn from_str(decimal_repr: &str) -> Result<Self, ()> {
        let value = decimal_repr.parse().map_err(|_| ())?;
        Ok(Number { value })
    }
}

impl Debug for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

impl Div for Number {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Number {
            value: self.value / rhs.value,
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
    use crate::engine::number::test_helpers::num;

    #[test]
    fn test_display_number() {
        assert_eq!("12.34", num("12.34").to_string())
    }

    #[test]
    fn test_add_number() {
        assert_eq!("4.123", (num(".123") + num("4")).to_string());
    }

    #[test]
    fn test_sub_number() {
        assert_eq!("2.5", (num("3.5") - num("1")).to_string());
    }

    #[test]
    fn test_mul_number() {
        assert_eq!("10.5", (num("3.5") * num("3")).to_string());
    }

    #[test]
    fn test_div_number() {
        assert_eq!("1.5", (num("3") / num("2")).to_string());
    }

    #[test]
    fn test_negate_number() {
        assert_eq!("-3.5", (-num("3.5")).to_string());
    }

    #[test]
    fn test_decimal_number_with_no_decimal_part() {
        assert_eq!("12", num("12").to_string())
    }
}

#[cfg(test)]
pub mod test_helpers {
    use crate::engine::number::Number;

    pub fn num(repr: &str) -> Number {
        Number::from_str(repr).unwrap()
    }
}
