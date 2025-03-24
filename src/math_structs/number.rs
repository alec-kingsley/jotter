use rust_decimal::prelude::*;

use std::cmp::Ordering;
use std::convert::From;
use std::fmt;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::*;

static SIGNIFICANT_DIGITS: u32 = 10;

#[derive(Debug, Clone, Copy)]
pub enum Number {
    /// Rational number known exactly, stored in reduced form.
    Rational(i64, i64),
    /// Decimal number with possible lost precision.
    Approximate(Decimal),
}

impl Hash for Number {
    /// Hash for a `Number`.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        // they're equal if they look equal
        self.to_string().hash(state);
    }
}

impl PartialEq for Number {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        match self {
            &Number::Rational(self_numerator, self_denominator) => match other {
                &Number::Rational(other_numerator, other_denominator) => {
                    self_numerator == other_numerator && self_denominator == other_denominator
                }
                &Number::Approximate(other_decimal) => {
                    (Decimal::from(self_numerator) / Decimal::from(self_denominator))
                        .round_dp(SIGNIFICANT_DIGITS)
                        == other_decimal.round_dp(SIGNIFICANT_DIGITS)
                }
            },
            &Number::Approximate(self_decimal) => match other {
                &Number::Rational(other_numerator, other_denominator) => {
                    self_decimal.round_dp(SIGNIFICANT_DIGITS)
                        == (Decimal::from(other_numerator) / Decimal::from(other_denominator))
                            .round_dp(SIGNIFICANT_DIGITS)
                }
                &Number::Approximate(other_decimal) => {
                    self_decimal.round_dp(SIGNIFICANT_DIGITS)
                        == other_decimal.round_dp(SIGNIFICANT_DIGITS)
                }
            },
        }
    }
}

impl Eq for Number {}

/// Gets the greatest common denominator of `x` and `y`.
///
/// # Arguments
/// * `x` - the first argument
/// * `y` - the second argument
///
const fn gcd(x: i64, y: i64) -> i64 {
    if y == 0 {
        x
    } else {
        gcd(y, x % y)
    }
}

/// Gets the least common multiple of `x` and `y`.
///
/// # Arguments
/// * `x` - the first argument
/// * `y` - the second argument
///
const fn lcm(x: i64, y: i64) -> i64 {
    x / gcd(x, y) * y
}

impl Number {
    pub const ZERO: Number = Number::Rational(0, 1);
    pub const ONE: Number = Number::Rational(1, 1);

    /// Reduces a Rational number to its simplest form.
    ///
    /// # Requires
    /// `self` is a Number::Rational
    ///
    fn reduce_rational(&self) -> Self {
        if let &Number::Rational(numerator, denominator) = self {
            let gcd = gcd(numerator, denominator);
            Number::Rational(numerator / gcd, denominator / gcd)
        } else {
            panic!("reduce_rational called with Approximate value");
        }
    }

    /// Returns true iff `self` is exact.
    ///
    pub fn is_exact(&self) -> bool {
        if let Number::Approximate(_) = self {
            false
        } else {
            true
        }
    }

    /// Takes `self` to the `pow`'th power and returns it.
    ///
    /// # Arguments:
    /// * `pow` - the power to be raised to
    ///
    pub fn powi(&self, pow: i32) -> Self {
        match self {
            &Number::Rational(numerator, denominator) => {
                if pow >= 0 {
                    Number::Rational(numerator.pow(pow as u32), denominator.pow(pow as u32))
                } else {
                    Number::from(Decimal::from(self.clone()).powi(pow as i64))
                }
            }
            &Number::Approximate(decimal) => Number::Approximate(decimal.powi(pow as i64)),
        }
    }

    /// Returns the absolute value of the number.
    ///
    pub fn abs(&self) -> Self {
        if self.is_negative() {
            -self.clone()
        } else {
            self.clone()
        }
    }

    /// Returns true iff the number has a value of 1.
    ///
    pub fn is_one(&self) -> bool {
        self == &Number::from(1)
    }

    /// Returns true iff the number has an exact value of 1.
    ///
    pub fn is_exact_one(&self) -> bool {
        self.is_exact() && self == &Number::from(1)
    }

    /// Returns true iff the number has a value of 0.
    ///
    pub fn is_zero(&self) -> bool {
        self == &Number::from(0)
    }

    /// Returns true iff the number is negative.
    ///
    pub fn is_negative(&self) -> bool {
        match self {
            &Number::Rational(numerator, denominator) => (numerator < 0) != (denominator < 0),
            &Number::Approximate(decimal) => decimal.is_sign_negative(),
        }
    }
}

impl From<i64> for Number {
    fn from(num: i64) -> Self {
        Number::Rational(num, 1)
    }
}

impl From<f64> for Number {
    fn from(num: f64) -> Self {
        Number::Approximate(Decimal::from_f64_retain(num).unwrap())
    }
}

impl From<Decimal> for Number {
    fn from(num: Decimal) -> Self {
        Number::Approximate(num)
    }
}

impl From<Number> for Decimal {
    fn from(num: Number) -> Decimal {
        match num {
            Number::Rational(numerator, denominator) => {
                Decimal::from(numerator) / Decimal::from(denominator)
            }
            Number::Approximate(decimal) => decimal,
        }
    }
}

impl TryFrom<String> for Number {
    type Error = &'static str;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        if let Ok(i64_val) = value.parse::<i64>() {
            let value: Number = i64_val.into();
            Ok(value)
        } else if let Ok(f64_val) = value.parse::<f64>() {
            let value: Number = f64_val.into();
            Ok(value)
        } else {
            Err("Only i64s and f64s can be parsed as numbers at this time")
        }
    }
}

impl Display for Number {
    /// Format `Number` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let neg_sign = if self.is_negative() { "-" } else { "" };
        let number = self.abs();
        match number {
            Number::Rational(numerator, denominator) => {
                if denominator.is_one() {
                    write!(f, "{neg_sign}{numerator}")
                } else if numerator.is_zero() {
                    write!(f, "0")
                } else {
                    write!(f, "{neg_sign}{numerator}/{denominator}")
                }
            }
            Number::Approximate(decimal) => {
                let decimal = decimal.round_dp(SIGNIFICANT_DIGITS).normalize();
                if decimal.is_integer() {
                    write!(f, "{neg_sign}{decimal}.")
                } else {
                    write!(f, "{neg_sign}{decimal}")
                }
            }
        }
    }
}

impl Add for Number {
    type Output = Self;

    /// Operator overload for +.
    ///
    fn add(self, other: Self) -> Self {
        match self {
            Number::Rational(self_numerator, self_denominator) => match other {
                Number::Rational(other_numerator, other_denominator) => {
                    if self_numerator.is_zero() {
                        Number::Rational(other_numerator, other_denominator)
                    } else if other_numerator.is_zero() {
                        Number::Rational(self_numerator, self_denominator)
                    } else {
                        let lcm = lcm(self_denominator, other_denominator);
                        Number::Rational(
                            self_numerator * (lcm / self_denominator)
                                + other_numerator * (lcm / other_denominator),
                            lcm,
                        )
                        .reduce_rational()
                    }
                }
                Number::Approximate(other_decimal) => Number::Approximate(
                    Decimal::from(self_numerator) / Decimal::from(self_denominator) + other_decimal,
                ),
            },
            Number::Approximate(self_decimal) => match other {
                Number::Rational(other_numerator, other_denominator) => Number::Approximate(
                    self_decimal
                        + Decimal::from(other_numerator) / Decimal::from(other_denominator),
                ),
                Number::Approximate(other_decimal) => {
                    Number::Approximate(self_decimal + other_decimal)
                }
            },
        }
    }
}

impl AddAssign for Number {
    /// Operator overload for +=.
    ///
    fn add_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() + other))
    }
}

impl Neg for Number {
    type Output = Self;

    /// Operator overload for unary -.
    ///
    fn neg(self) -> Self {
        match self {
            Number::Rational(numerator, denominator) => Number::Rational(-numerator, denominator),
            Number::Approximate(decimal) => Number::Approximate(-decimal),
        }
    }
}

impl Sub for Number {
    type Output = Self;

    /// Operator overload for -.
    ///
    fn sub(self, other: Self) -> Self {
        match self {
            Number::Rational(self_numerator, self_denominator) => match other {
                Number::Rational(other_numerator, other_denominator) => {
                    if self_numerator.is_zero() {
                        Number::Rational(-other_numerator, other_denominator)
                    } else if other_numerator.is_zero() {
                        Number::Rational(self_numerator, self_denominator)
                    } else {
                        let lcm = lcm(self_denominator, other_denominator);
                        Number::Rational(
                            self_numerator * (lcm / self_denominator)
                                - other_numerator * (lcm / other_denominator),
                            lcm,
                        )
                        .reduce_rational()
                    }
                }
                Number::Approximate(other_decimal) => Number::Approximate(
                    Decimal::from(self_numerator) / Decimal::from(self_denominator) - other_decimal,
                ),
            },
            Number::Approximate(self_decimal) => match other {
                Number::Rational(other_numerator, other_denominator) => Number::Approximate(
                    self_decimal
                        - Decimal::from(other_numerator) / Decimal::from(other_denominator),
                ),
                Number::Approximate(other_decimal) => {
                    Number::Approximate(self_decimal - other_decimal)
                }
            },
        }
    }
}

impl SubAssign for Number {
    /// Operator overload for -=.
    ///
    fn sub_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() - other))
    }
}

impl Mul for Number {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        match self {
            Number::Rational(self_numerator, self_denominator) => match other {
                Number::Rational(other_numerator, other_denominator) => {
                    let down_gcd = gcd(self_numerator, other_denominator);
                    let up_gcd = gcd(self_denominator, other_numerator);
                    Number::Rational(
                        (self_numerator / down_gcd) * (other_numerator / up_gcd),
                        (self_denominator / up_gcd) * (other_denominator / down_gcd),
                    )
                }
                Number::Approximate(other_decimal) => Number::Approximate(
                    Decimal::from(self_numerator) / Decimal::from(self_denominator) * other_decimal,
                ),
            },
            Number::Approximate(self_decimal) => match other {
                Number::Rational(other_numerator, other_denominator) => Number::Approximate(
                    Decimal::from(other_numerator) / Decimal::from(other_denominator)
                        * self_decimal,
                ),
                Number::Approximate(other_decimal) => {
                    Number::Approximate(self_decimal * other_decimal)
                }
            },
        }
    }
}

impl MulAssign for Number {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other))
    }
}

impl Mul<i64> for Number {
    type Output = Self;

    fn mul(self, rhs: i64) -> Self {
        match self {
            Number::Rational(numerator, denominator) => {
                let gcd = gcd(denominator, rhs);
                Number::Rational(numerator * (rhs / gcd), denominator / gcd)
            }
            Number::Approximate(decimal) => Number::Approximate(decimal * Decimal::from(rhs)),
        }
    }
}

impl MulAssign<i64> for Number {
    fn mul_assign(&mut self, rhs: i64) {
        self.clone_from(&(self.clone() * rhs))
    }
}

impl Div for Number {
    type Output = Self;

    /// Operator overload for /.
    ///
    fn div(self, other: Self) -> Self {
        match self {
            Number::Rational(self_numerator, self_denominator) => match other {
                Number::Rational(other_numerator, other_denominator) => {
                    let down_gcd = gcd(self_numerator, other_numerator);
                    let up_gcd = gcd(self_denominator, other_denominator);
                    let numerator = (self_numerator / down_gcd) * (other_denominator / up_gcd);
                    let denominator = (self_denominator / up_gcd) * (other_numerator / down_gcd);
                    if denominator.is_zero() {
                        panic!("Attempt to divide by 0: [{self} / {other}]");
                    }
                    Number::Rational(numerator, denominator)
                }
                Number::Approximate(other_decimal) => Number::Approximate(
                    Decimal::from(self_numerator) / Decimal::from(self_denominator) / other_decimal,
                ),
            },
            Number::Approximate(self_decimal) => match other {
                Number::Rational(other_numerator, other_denominator) => Number::Approximate(
                    self_decimal
                        / (Decimal::from(other_numerator) / Decimal::from(other_denominator)),
                ),
                Number::Approximate(other_decimal) => {
                    Number::Approximate(self_decimal / other_decimal)
                }
            },
        }
    }
}

impl DivAssign for Number {
    /// Operator overload for /=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other))
    }
}

impl Div<i64> for Number {
    type Output = Self;

    fn div(self, rhs: i64) -> Self {
        match self {
            Number::Rational(numerator, denominator) => {
                let gcd = gcd(numerator, rhs);
                Number::Rational(numerator / gcd, denominator * (rhs / gcd))
            }
            Number::Approximate(decimal) => Number::Approximate(decimal / Decimal::from(rhs)),
        }
    }
}

impl DivAssign<i64> for Number {
    fn div_assign(&mut self, rhs: i64) {
        self.clone_from(&(self.clone() / rhs))
    }
}

impl PartialOrd for Number {
    /// Operator overload for <, >, <=, >=
    ///
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            &Number::Rational(self_numerator, self_denominator) => match other {
                &Number::Rational(other_numerator, other_denominator) => {
                    (Decimal::from(self_numerator) / Decimal::from(self_denominator))
                        .round_dp(SIGNIFICANT_DIGITS)
                        .partial_cmp(
                            &(Decimal::from(other_numerator) / Decimal::from(other_denominator))
                                .round_dp(SIGNIFICANT_DIGITS),
                        )
                }
                &Number::Approximate(other_decimal) => (Decimal::from(self_numerator)
                    / Decimal::from(self_denominator))
                .round_dp(SIGNIFICANT_DIGITS)
                .partial_cmp(&other_decimal.round_dp(SIGNIFICANT_DIGITS)),
            },
            &Number::Approximate(self_decimal) => match other {
                &Number::Rational(other_numerator, other_denominator) => {
                    self_decimal.round_dp(SIGNIFICANT_DIGITS).partial_cmp(
                        &(Decimal::from(other_numerator) / Decimal::from(other_denominator))
                            .round_dp(SIGNIFICANT_DIGITS),
                    )
                }
                &Number::Approximate(other_decimal) => self_decimal
                    .round_dp(SIGNIFICANT_DIGITS)
                    .partial_cmp(&other_decimal.round_dp(SIGNIFICANT_DIGITS)),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eq_1() {
        assert_eq!(Number::from(3), Number::from(3));
    }

    #[test]
    fn test_eq_2() {
        assert_eq!(Number::from(3), Number::from(3.));
    }

    #[test]
    fn test_eq_3() {
        assert_eq!(Number::from(3.), Number::from(3.));
    }

    #[test]
    fn test_powi_1() {
        let result = Number::from(2).powi(3);
        assert!(result.is_exact());
        assert_eq!(Number::from(8), result);
    }

    #[test]
    fn test_powi_2() {
        let result = Number::from(2.).powi(3);
        assert!(!result.is_exact());
        assert_eq!(Number::from(8.), result);
    }

    #[test]
    fn test_powi_3() {
        let result = Number::from(5.).powi(0);
        assert!(!result.is_exact());
        assert_eq!(Number::from(1), result);
    }

    #[test]
    fn test_powi_4() {
        let result = Number::from(5).powi(0);
        assert!(result.is_exact());
        assert_eq!(Number::from(1), result);
    }

    #[test]
    fn test_abs_1() {
        let result = Number::from(3).abs();
        assert!(result.is_exact());
        assert_eq!(Number::from(3), result);
    }

    #[test]
    fn test_abs_2() {
        let result = Number::from(-3).abs();
        assert!(result.is_exact());
        assert_eq!(Number::from(3), result);
    }

    #[test]
    fn test_abs_3() {
        let result = Number::from(3.0).abs();
        assert!(!result.is_exact());
        assert_eq!(Number::from(3.0), result);
    }

    #[test]
    fn test_abs_4() {
        let result = Number::from(-3.0).abs();
        assert!(!result.is_exact());
        assert_eq!(Number::from(3.0), result);
    }

    #[test]
    fn test_is_zero_1() {
        assert!(Number::from(0).is_zero());
    }

    #[test]
    fn test_is_zero_2() {
        assert!(Number::from(0.).is_zero());
    }

    #[test]
    fn test_is_zero_3() {
        assert!(!Number::from(0.1).is_zero());
    }

    #[test]
    fn test_is_zero_4() {
        assert!(!Number::from(3).is_zero());
    }

    #[test]
    fn test_is_one_1() {
        assert!(Number::from(1).is_one());
    }

    #[test]
    fn test_is_one_2() {
        assert!(Number::from(1.).is_one());
    }

    #[test]
    fn test_is_one_3() {
        assert!(!Number::from(0.1).is_one());
    }

    #[test]
    fn test_is_one_4() {
        assert!(!Number::from(3).is_one());
    }

    #[test]
    fn test_is_negative_1() {
        assert!(!Number::from(0).is_negative());
    }

    #[test]
    fn test_is_negative_2() {
        assert!(!Number::from(0.).is_negative());
    }

    #[test]
    fn test_is_negative_3() {
        assert!(!Number::from(0.1).is_negative());
    }

    #[test]
    fn test_is_negative_4() {
        assert!(Number::from(-3).is_negative());
    }

    #[test]
    fn test_is_negative_5() {
        assert!(Number::from(-0.3).is_negative());
    }

    #[test]
    fn test_from_i64_1() {
        assert!(Number::from(3).is_exact());
    }

    #[test]
    fn test_from_f64_1() {
        assert!(!Number::from(3.).is_exact());
    }

    #[test]
    fn test_from_f64_2() {
        assert!(!Number::from(3.1).is_exact());
    }

    #[test]
    fn test_try_from_string_1() {
        assert_eq!(
            Number::from(2),
            Number::try_from(String::from("2")).unwrap()
        );
    }

    #[test]
    fn test_try_from_string_2() {
        assert_eq!(
            Number::from(2.3),
            Number::try_from(String::from("2.3")).unwrap()
        );
    }

    #[test]
    fn test_display_1() {
        assert_eq!("3", Number::from(3).to_string());
    }

    #[test]
    fn test_display_2() {
        assert_eq!("3.", Number::from(3.).to_string());
    }

    #[test]
    fn test_display_3() {
        assert_eq!("3.2", Number::from(3.2).to_string());
    }

    #[test]
    fn test_display_4() {
        assert_eq!("1/2", (Number::from(1) / Number::from(2)).to_string());
    }

    #[test]
    fn test_display_5() {
        assert_eq!("3.", Number::from(3.000).to_string());
    }

    #[test]
    fn test_add_1() {
        let two = Number::from(2);
        let three = Number::from(3);
        let five = Number::from(5);
        assert_eq!(five, two + three);
        if let Number::Approximate(_) = two + three {
            panic!("Approximate number from rational constituents");
        }
    }

    #[test]
    fn test_add_2() {
        let two = Number::from(2.);
        let three = Number::from(3.);
        let five = Number::from(5.);
        assert_eq!(five, two + three);
    }

    #[test]
    fn test_add_3() {
        let two_thirds = Number::from(2) / Number::from(3);
        let three_fifths = Number::from(3) / Number::from(5);
        let nineteen_fifteenths = Number::from(19) / Number::from(15);
        assert_eq!(nineteen_fifteenths, two_thirds + three_fifths);
    }

    #[test]
    fn test_add_assign_1() {
        let mut val = Number::from(2);
        let three = Number::from(3);
        val += three;
        let five = Number::from(5);
        assert_eq!(five, val);
    }

    #[test]
    fn test_add_assign_2() {
        let mut val = Number::from(2.);
        let three = Number::from(3.);
        val += three;
        let five = Number::from(5.);
        assert_eq!(five, val);
    }

    #[test]
    fn test_add_assign_3() {
        let mut val = Number::from(2) / Number::from(3);
        let three_fifths = Number::from(3) / Number::from(5);
        val += three_fifths;
        let nineteen_fifteenths = Number::from(19) / Number::from(15);
        assert_eq!(nineteen_fifteenths, val);
    }

    #[test]
    fn test_neg_1() {
        assert_eq!(Number::from(-1), -Number::from(1));
    }

    #[test]
    fn test_neg_2() {
        assert_eq!(Number::from(1), -Number::from(-1));
    }

    #[test]
    fn test_neg_3() {
        assert_eq!(Number::from(-1.), -Number::from(1.));
    }

    #[test]
    fn test_neg_4() {
        assert_eq!(Number::from(1.), -Number::from(-1.));
    }

    #[test]
    fn test_sub_1() {
        let two = Number::from(2);
        let three = Number::from(3);
        let five = Number::from(5);
        assert_eq!(two, five - three);
    }

    #[test]
    fn test_sub_2() {
        let two = Number::from(2.);
        let three = Number::from(3.);
        let five = Number::from(5.);
        assert_eq!(two, five - three);
    }

    #[test]
    fn test_sub_3() {
        let two_thirds = Number::from(2) / Number::from(3);
        let three_fifths = Number::from(3) / Number::from(5);
        let nineteen_fifteenths = Number::from(19) / Number::from(15);
        assert_eq!(two_thirds, nineteen_fifteenths - three_fifths);
    }

    #[test]
    fn test_sub_assign_1() {
        let mut val = Number::from(5);
        let three = Number::from(3);
        val -= three;
        let two = Number::from(2);
        assert_eq!(two, val);
    }

    #[test]
    fn test_sub_assign_2() {
        let mut val = Number::from(5.);
        let three = Number::from(3.);
        val -= three;
        let two = Number::from(2.);
        assert_eq!(two, val);
    }

    #[test]
    fn test_sub_assign_3() {
        let mut val = Number::from(19) / Number::from(15);
        let three_fifths = Number::from(3) / Number::from(5);
        val -= three_fifths;
        let two_thirds = Number::from(2) / Number::from(3);
        assert_eq!(two_thirds, val);
    }

    #[test]
    fn test_mul_1() {
        let two = Number::from(2);
        let three = Number::from(3);
        let six = Number::from(6);
        assert_eq!(six, two * three);
    }

    #[test]
    fn test_mul_2() {
        let two = Number::from(2.);
        let three = Number::from(3.);
        let six = Number::from(6.);
        assert_eq!(six, two * three);
    }

    #[test]
    fn test_mul_3() {
        let two_thirds = Number::from(2) / Number::from(3);
        let three_fifths = Number::from(3) / Number::from(5);
        let two_fifths = Number::from(2) / Number::from(5);
        assert_eq!(two_fifths, two_thirds * three_fifths);
    }

    #[test]
    fn test_mul_assign_1() {
        let mut val = Number::from(2);
        let three = Number::from(3);
        val *= three;
        let six = Number::from(6);
        assert_eq!(six, val);
    }

    #[test]
    fn test_mul_assign_2() {
        let mut val = Number::from(2.);
        let three = Number::from(3.);
        val *= three;
        let six = Number::from(6.);
        assert_eq!(six, val);
    }

    #[test]
    fn test_mul_assign_3() {
        let mut val = Number::from(2) / Number::from(3);
        let three_fifths = Number::from(3) / Number::from(5);
        val *= three_fifths;
        let two_fifths = Number::from(2) / Number::from(5);
        assert_eq!(two_fifths, val);
    }

    #[test]
    fn test_mul_i64_1() {
        let two = Number::from(2);
        let three = 3;
        let six = Number::from(6);
        assert_eq!(six, two * three);
    }

    #[test]
    fn test_mul_i64_2() {
        let two = Number::from(2.);
        let three = 3;
        let six = Number::from(6.);
        assert_eq!(six, two * three);
    }

    #[test]
    fn test_mul_assign_i64_1() {
        let mut val = Number::from(2);
        let three = 3;
        val *= three;
        let six = Number::from(6);
        assert_eq!(six, val);
    }

    #[test]
    fn test_mul_assign_i64_2() {
        let mut val = Number::from(2.);
        let three = 3;
        val *= three;
        let six = Number::from(6.);
        assert_eq!(six, val);
    }

    #[test]
    fn test_div_1() {
        let two = Number::from(2);
        let three = Number::from(3);
        let six = Number::from(6);
        assert_eq!(two, six / three);
    }

    #[test]
    fn test_div_2() {
        let two = Number::from(2.);
        let three = Number::from(3.);
        let six = Number::from(6.);
        assert_eq!(two, six / three);
    }

    #[test]
    fn test_div_3() {
        let two_thirds = Number::from(2) / Number::from(3);
        let three_fifths = Number::from(3) / Number::from(5);
        let two_fifths = Number::from(2) / Number::from(5);
        assert_eq!(two_thirds, two_fifths / three_fifths);
    }

    #[test]
    fn test_div_assign_1() {
        let mut val = Number::from(6);
        let three = Number::from(3);
        val /= three;
        let two = Number::from(2);
        assert_eq!(two, val);
    }

    #[test]
    fn test_div_assign_2() {
        let mut val = Number::from(6.);
        let three = Number::from(3.);
        val /= three;
        let two = Number::from(2.);
        assert_eq!(two, val);
    }

    #[test]
    fn test_div_assign_3() {
        let mut val = Number::from(2) / Number::from(5);
        let three_fifths = Number::from(3) / Number::from(5);
        val /= three_fifths;
        let two_thirds = Number::from(2) / Number::from(3);
        assert_eq!(two_thirds, val);
    }

    #[test]
    fn test_div_i64_1() {
        let six = Number::from(6);
        let three = 3;
        let two = Number::from(2);
        assert_eq!(two, six / three);
    }

    #[test]
    fn test_div_i64_2() {
        let six = Number::from(6.);
        let three = 3;
        let two = Number::from(2.);
        assert_eq!(two, six / three);
    }

    #[test]
    fn test_div_assign_i64_1() {
        let mut val = Number::from(6);
        let three = 3;
        val /= three;
        let two = Number::from(2);
        assert_eq!(two, val);
    }

    #[test]
    fn test_div_assign_i64_2() {
        let mut val = Number::from(6.);
        let three = 3;
        val /= three;
        let two = Number::from(2.);
        assert_eq!(two, val);
    }

    #[test]
    fn test_partial_cmp_1() {
        let four = Number::from(4);
        let negone = Number::from(-1);
        let eight = Number::from(8);
        let six_thirds = Number::from(6) / Number::from(3);

        assert!(negone == negone);
        assert!(negone < four);
        assert!(negone < eight);
        assert!(negone < six_thirds);
        assert!(four == four);
        assert!(four < eight);
        assert!(four > six_thirds);
        assert!(eight == eight);
        assert!(eight > six_thirds);
        assert!(six_thirds == six_thirds);
    }

    #[test]
    fn test_partial_cmp_2() {
        let four = Number::from(4.);
        let negone = Number::from(-1.);
        let eight = Number::from(8.);
        let six_thirds = Number::from(6.) / Number::from(3.);

        assert!(negone == negone);
        assert!(negone < four);
        assert!(negone < eight);
        assert!(negone < six_thirds);
        assert!(four == four);
        assert!(four < eight);
        assert!(four > six_thirds);
        assert!(eight == eight);
        assert!(eight > six_thirds);
        assert!(six_thirds == six_thirds);
    }
}
