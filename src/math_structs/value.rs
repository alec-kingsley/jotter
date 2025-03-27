use rust_decimal::prelude::*;

use std::cmp::Ordering;
use std::collections::HashMap;
use std::convert::From;
use std::fmt;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::*;

use crate::math_structs::number::*;
use crate::math_structs::unit::*;

#[derive(Debug, Clone)]
pub struct Value {
    /// Real component of numeric literal.
    real: Number,
    /// Imaginary component of numeric literal.
    imaginary: Number,
    /// Unit of the numeric literal.
    unit: Unit,
}

impl Hash for Value {
    /// Hash for a `Value`.
    /// Necesarry since f64.hash() does not exist.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        // they're equal if they look equal
        self.to_string().hash(state);
        self.unit.hash(state);
    }
}

impl PartialEq for Value {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        self.unit == other.unit && self.real == other.real && self.imaginary == other.imaginary
    }
}

impl Eq for Value {}

impl Value {
    /// Constructor for unitless one.
    ///
    pub fn one() -> Self {
        Self {
            real: Number::ONE,
            imaginary: Number::ZERO,
            unit: Unit::unitless(),
        }
    }

    /// Constructor for unitless zero.
    ///
    pub fn zero() -> Self {
        Self {
            real: Number::ZERO,
            imaginary: Number::ZERO,
            unit: Unit::unitless(),
        }
    }

    /// Get an immutable reference to `self.unit`.
    ///
    pub fn get_unit(&self) -> &Unit {
        &self.unit
    }

    /// Returns `self` with unit `unit`.
    ///
    /// # Arguments:
    /// * `unit` - the unit to assign
    ///
    /// # Requires
    /// Current unit is unitless
    ///
    pub fn with_unit(&self, unit: Unit) -> Self {
        assert!(self.unit == Unit::unitless());
        Self {
            real: self.real,
            imaginary: self.imaginary,
            unit,
        }
    }

    /// Takes `self` to the `pow`'th power and returns it.
    ///
    /// # Arguments:
    /// * `pow` - the power to be raised to
    ///
    pub fn powi(&self, pow: i32) -> Self {
        if self.is_real() {
            Self {
                real: self.real.powi(pow),
                imaginary: Number::ZERO,
                unit: Unit {
                    exponent: self.unit.exponent * pow as i8,
                    constituents: self
                        .unit
                        .constituents
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone() * pow as i8))
                        .collect(),
                },
            }
        } else {
            // TODO - this could be more efficient
            let mut result = Value::one();
            for _ in 0..pow {
                result *= self.clone();
            }
            result
        }
    }

    /// Attempts to rationalize components of `self`.
    ///
    pub fn rationalize(&self) -> Self {
        let new_real = if let Number::Approximate(_) = self.real {
            if let Some(rationalized) = self.real.rationalize() {
                rationalized
            } else {
                self.real.clone()
            }
        } else {
            self.real.clone()
        };
        let new_imaginary = if let Number::Approximate(_) = self.imaginary {
            if let Some(rationalized) = self.imaginary.rationalize() {
                rationalized
            } else {
                self.imaginary.clone()
            }
        } else {
            self.imaginary.clone()
        };
        Value {
            real: new_real,
            imaginary: new_imaginary,
            unit: self.unit.clone(),
        }
    }

    /// Returns the absolute value of the number.
    /// Does not consider unit.
    ///
    pub fn abs(&self) -> Decimal {
        let real_abs = self.real.abs();
        let imaginary_abs = self.imaginary.abs();
        Decimal::from(real_abs * real_abs + imaginary_abs * imaginary_abs)
            .sqrt()
            .unwrap()
    }

    /// Returns true iff `self` is composed purely of rational components.
    ///
    pub fn is_exact(&self) -> bool {
        if let Number::Rational(_, _) = self.real {
            if let Number::Rational(_, _) = self.imaginary {
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Returns true iff the number has a value of 1.
    ///
    pub fn is_unitless_one(&self) -> bool {
        self.real.is_exact_one() && self.imaginary.is_zero() && self.unit == Unit::unitless()
    }

    /// Returns true iff the number has a value of 0.
    ///
    pub fn is_zero(&self) -> bool {
        self.real.is_zero() && self.imaginary.is_zero()
    }

    /// Returns true iff the number is in the real set.
    ///
    pub fn is_real(&self) -> bool {
        self.imaginary.is_zero()
    }

    /// Returns the imaginary constant i multiplied by Self.
    ///
    pub fn i(&self) -> Self {
        Self {
            real: -self.imaginary,
            imaginary: self.real,
            unit: self.unit.clone(),
        }
    }

    /// Refactor the unit such that its `unit.exponent` is divisible by `subunit_exponent`.
    /// It must also either be divisible by 3 or have a magnitude less than 3.
    ///
    /// # Arguments
    /// * `subunit_exponent` - thing to be divisible by.
    ///
    fn refactor_exponent(&mut self, subunit_exponent: i8) {
        // try to force self to be within 3 digits from 0
        if self.abs() >= Decimal::ONE {
            while self.abs() >= Decimal::TEN {
                self.real /= 10;
                self.imaginary /= 10;
                self.unit.exponent += 1;
            }
        } else {
            while !self.is_zero() && self.abs() < Decimal::ONE {
                self.real *= 10;
                self.imaginary *= 10;
                self.unit.exponent -= 1;
            }
        }

        // ensure exponent exists
        if self.unit.exponent > 0 {
            while self.unit.exponent > 30
                || (subunit_exponent != 0 && self.unit.exponent % (3 * subunit_exponent) != 0)
            {
                self.real *= 10;
                self.imaginary *= 10;
                self.unit.exponent -= 1;
            }
        } else {
            self.real *= 100;
            self.imaginary *= 100;
            self.unit.exponent -= 2;

            while self.unit.exponent < -30
                || (subunit_exponent != 0 && self.unit.exponent % (3 * subunit_exponent) != 0)
            {
                self.real /= 10;
                self.imaginary /= 10;
                self.unit.exponent += 1;
            }
        }
    }
}

impl From<f64> for Value {
    fn from(num: f64) -> Self {
        Self {
            real: Number::from(num),
            imaginary: Number::ZERO,
            unit: Unit::unitless(),
        }
    }
}

impl From<i64> for Value {
    fn from(num: i64) -> Self {
        Self {
            real: Number::from(num),
            imaginary: Number::ZERO,
            unit: Unit::unitless(),
        }
    }
}

impl From<Number> for Value {
    fn from(num: Number) -> Self {
        Self {
            real: num,
            imaginary: Number::ZERO,
            unit: Unit::unitless(),
        }
    }
}

impl From<Decimal> for Value {
    fn from(num: Decimal) -> Self {
        Self {
            real: Number::from(num),
            imaginary: Number::ZERO,
            unit: Unit::unitless(),
        }
    }
}

impl TryFrom<String> for Value {
    type Error = &'static str;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        let value = Self {
            real: Number::try_from(value)?,
            imaginary: Number::ZERO,
            unit: Unit::unitless(),
        };
        Ok(value)
    }
}

/// get appropriate SI prefix for a given power of 10
/// and power on the unit.
///
fn get_si_prefix(exponent: i8, unit_power: i8) -> String {
    HashMap::from([
        (30, "Q"), // quetta
        (27, "R"), // ronna
        (24, "Y"), // yotta
        (21, "Z"), // zotta
        (18, "E"), // exa
        (15, "P"), // peta
        (12, "T"), // tera
        (9, "G"),  // giga
        (6, "M"),  // mega
        (3, "k"),  // kilo
        (2, "h"),  // hecto
        (1, "da"), // deka
        (0, ""),
        (-1, "d"),  // deci
        (-2, "c"),  // centi
        (-3, "m"),  // milli
        (-6, "μ"),  // micro
        (-9, "n"),  // nano
        (-12, "p"), // pico
        (-15, "f"), // femto
        (-18, "a"), // atto
        (-21, "z"), // zepto
        (-24, "y"), // yocto
        (-27, "r"), // ronto
        (-30, "q"), // quecto
    ])
    .get(&(exponent / unit_power))
    .expect("No SI prefix for power")
    .to_string()
}

impl Display for Value {
    /// Format `Value` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut self_clone = self.clone();
        let unit_abbreviations = HashMap::from([
            (BaseUnit::Meter, "m"),     // m
            (BaseUnit::Kilogram, "kg"), // kg
            (BaseUnit::Second, "s"),    // s
            (BaseUnit::Ampere, "A"),    // A
            (BaseUnit::Kelvin, "K"),    // K
            (BaseUnit::Mole, "mol"),    // mol
            (BaseUnit::Candela, "cd"),  // cd
        ]);

        let mut numerator = String::new();
        let mut denominator = String::new();
        let mut processed_prefix = false;
        for (base_unit, unit_power) in self_clone.unit.constituents.clone() {
            if unit_power == 0 {
                continue;
            }

            let mut unit_name = unit_abbreviations.get(&base_unit).unwrap().to_string();
            // assign power on first iteration
            if !processed_prefix {
                self_clone.refactor_exponent(unit_power);
                unit_name = if unit_name == "kg" {
                    if unit_power > 0i8 {
                        format!(
                            "{}g",
                            get_si_prefix(self_clone.unit.exponent + 3, unit_power)
                        )
                    } else {
                        format!(
                            "{}g",
                            get_si_prefix(self_clone.unit.exponent - 3, unit_power)
                        )
                    }
                } else {
                    format!(
                        "{}{unit_name}",
                        get_si_prefix(self_clone.unit.exponent, unit_power)
                    )
                };
                processed_prefix = true;
            }

            // build units
            if unit_power > 0i8 {
                numerator = if numerator.is_empty() {
                    unit_name
                } else {
                    format!("{numerator} {}", unit_name)
                };
                if unit_power > 1i8 {
                    numerator = format!("{numerator}^{}", unit_power);
                }
            } else if unit_power < 0i8 {
                denominator = if denominator.is_empty() {
                    unit_name
                } else {
                    format!("{denominator} / {}", unit_name)
                };
                if unit_power < -1i8 {
                    denominator = format!("{denominator}^{}", -unit_power);
                }
            }
        }

        // if unitless or whatever, put the prefix in the number
        if !processed_prefix {
            self_clone.real *= Number::from(10).powi(self_clone.unit.exponent as i32);
            self_clone.imaginary *= Number::from(10).powi(self_clone.unit.exponent as i32);
        }

        // write final result depending on numerator/denominator contents
        let numeric_str = if self.imaginary.is_zero() {
            format!("{}", self_clone.real).to_owned()
        } else if self.real.is_zero() {
            if self_clone.imaginary.is_exact_one() {
                String::from("i")
            } else if (-self_clone.imaginary).is_exact_one() {
                String::from("-i")
            } else {
                format!("{}", self_clone.imaginary).to_owned() + "i"
            }
        } else {
            if self_clone.imaginary > Number::from(0) {
                format!("{}", self_clone.real)
                    .trim_end_matches('0')
                    .to_owned()
                    + if self_clone.imaginary.is_exact_one() {
                        String::from(" + i")
                    } else {
                        format!(" + {}", self_clone.imaginary)
                            .trim_end_matches('0')
                            .to_owned()
                            + "i"
                    }
                    .as_str()
            } else {
                format!("{}", self_clone.real)
                    .trim_end_matches('0')
                    .to_owned()
                    + if (-self_clone.imaginary).is_exact_one() {
                        String::from(" - i")
                    } else {
                        format!(" - {}", -self_clone.imaginary)
                            .trim_end_matches('0')
                            .to_owned()
                            + "i"
                    }
                    .as_str()
            }
        };
        let numeric_str = if !(numerator.is_empty() && denominator.is_empty())
            && (!self_clone.real.is_zero() && !self_clone.imaginary.is_zero())
        {
            format!("({})", numeric_str)
        } else {
            numeric_str
        };
        if numerator.is_empty() {
            if denominator.is_empty() {
                write!(f, "{}", numeric_str)
            } else {
                write!(f, "{} [1 / {}]", numeric_str, denominator)
            }
        } else {
            if denominator.is_empty() {
                write!(f, "{} [{}]", numeric_str, numerator)
            } else {
                write!(f, "{} [{} / {}]", numeric_str, numerator, denominator)
            }
        }
    }
}

impl Add for Value {
    type Output = Self;

    /// Operator overload for +.
    ///
    fn add(self, other: Self) -> Self {
        assert!(self.unit == other.unit, "Mismatched types");
        let mut other_clone = other.clone();
        let exp_diff = other_clone.unit.exponent - self.unit.exponent;
        other_clone.unit.exponent -= exp_diff;
        other_clone.real = other_clone.real * Number::from(10).powi(exp_diff as i32);
        other_clone.imaginary = other_clone.imaginary * Number::from(10).powi(exp_diff as i32);
        other_clone.real *=
            Number::from(10).powi((other.unit.exponent - self.unit.exponent) as i32);
        other_clone.imaginary *=
            Number::from(10).powi((other.unit.exponent - self.unit.exponent) as i32);
        Self {
            real: self.real + other_clone.real,
            imaginary: self.imaginary + other_clone.imaginary,
            unit: self.unit,
        }
    }
}

impl AddAssign for Value {
    /// Operator overload for +=.
    ///
    fn add_assign(&mut self, other: Self) {
        // only add if the other is not equal to 0
        // reason for this is that 0m/s + 3m would sensibly be 3m, even though
        // (m/s + m) is not a valid unit.
        //
        // this does not apply to plus by itself since it's not obvious which should
        // be prioritized.
        //
        // also the initial unit is prioritized for +=
        if !other.is_zero() {
            self.clone_from(&(self.clone() + other));
        }
    }
}

impl Neg for Value {
    type Output = Self;

    /// Operator overload for unary -.
    ///
    fn neg(self) -> Self {
        Self {
            real: -self.real,
            imaginary: -self.imaginary,
            unit: self.unit,
        }
    }
}

impl Sub for Value {
    type Output = Self;

    /// Operator overload for -.
    ///
    fn sub(self, other: Self) -> Self {
        assert!(self.unit == other.unit, "Mismatched types");
        let mut other_clone = other.clone();
        let exp_diff = other_clone.unit.exponent - self.unit.exponent;
        other_clone.unit.exponent -= exp_diff;
        other_clone.real = other_clone.real * Number::from(10).powi(exp_diff as i32);
        other_clone.imaginary = other_clone.imaginary * Number::from(10).powi(exp_diff as i32);
        other_clone.real *=
            Number::from(10).powi((other.unit.exponent - self.unit.exponent) as i32);
        other_clone.imaginary *=
            Number::from(10).powi((other.unit.exponent - self.unit.exponent) as i32);
        Self {
            real: self.real - other_clone.real,
            imaginary: self.imaginary - other_clone.imaginary,
            unit: self.unit,
        }
    }
}

impl SubAssign for Value {
    /// Operator overload for -=.
    ///
    fn sub_assign(&mut self, other: Self) {
        // only subtract if the other is not equal to 0
        // reason for this is that 3m/s - 0m would sensibly be 3m/s, even though
        // (m/s - m) is not a valid unit.
        //
        // this does not apply to minus by itself since it's not obvious which should
        // be prioritized.
        //
        // also the initial unit is prioritized for -=
        if !other.clone().is_zero() {
            self.clone_from(&(self.clone() - other));
        }
    }
}

impl Mul for Value {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut constituents = self.unit.constituents;
        for (base_unit, power) in other.unit.constituents {
            *constituents.entry(base_unit).or_insert(0) += power;
        }
        let value = Self {
            real: self.real * other.real - self.imaginary * other.imaginary,
            imaginary: self.real * other.imaginary + self.imaginary * other.real,
            unit: Unit {
                exponent: self.unit.exponent + other.unit.exponent,
                constituents,
            },
        };
        value
    }
}

impl MulAssign for Value {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Mul<i64> for Value {
    type Output = Self;

    fn mul(self, rhs: i64) -> Self {
        Self {
            real: self.real * rhs,
            imaginary: self.imaginary * rhs,
            unit: self.unit,
        }
    }
}

impl MulAssign<i64> for Value {
    fn mul_assign(&mut self, rhs: i64) {
        self.clone_from(&(self.clone() * rhs));
    }
}

impl Div for Value {
    type Output = Self;

    /// Operator overload for /.
    ///
    fn div(self, other: Self) -> Self {
        let mut constituents = self.unit.constituents;
        for (base_unit, power) in other.unit.constituents {
            *constituents.entry(base_unit).or_insert(0) -= power;
        }
        // ain't no way I finally used the complex conjugate thing from linear alg
        let divisor = other.real * other.real + other.imaginary * other.imaginary;

        Self {
            real: (self.real * other.real + self.imaginary * other.imaginary) / divisor,
            imaginary: (-self.real * other.imaginary + self.imaginary * other.real) / divisor,
            unit: Unit {
                exponent: self.unit.exponent - other.unit.exponent,
                constituents,
            },
        }
    }
}

impl DivAssign for Value {
    /// Operator overload for /=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}

impl Div<i64> for Value {
    type Output = Self;

    fn div(self, rhs: i64) -> Self {
        Self {
            real: self.real / rhs,
            imaginary: self.imaginary / rhs,
            unit: self.unit,
        }
    }
}

impl DivAssign<i64> for Value {
    fn div_assign(&mut self, rhs: i64) {
        self.clone_from(&(self.clone() / rhs));
    }
}

impl PartialOrd for Value {
    /// Operator overload for <, >, <=, >=
    /// Returns None for complex numbers.
    ///
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        assert!(
            self.unit == other.unit || (self.is_zero() || other.is_zero()),
            "Mismatched types"
        );

        if self == other {
            Some(Ordering::Equal)
        } else if self.is_real() && other.is_real() {
            let mut other_clone = other.clone();
            let exp_diff = other_clone.unit.exponent - self.unit.exponent;
            other_clone.unit.exponent -= exp_diff;
            other_clone.real = other_clone.real * Number::from(Decimal::TEN.powi(exp_diff as i64));
            other_clone.real *=
                Number::from(Decimal::TEN.powi((other.unit.exponent - self.unit.exponent) as i64));
            Some(if self.real < other_clone.real {
                Ordering::Less
            } else {
                Ordering::Greater
            })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_unit_1() {
        let unit = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };

        let value = Value::from(1).with_unit(unit.clone());
        assert_eq!(unit, value.get_unit().clone());
    }

    #[test]
    fn test_powi_1() {
        let unit = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };

        let number = Value::from(2).with_unit(unit.clone()).powi(4);

        let unit_expected = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 4)]),
        };

        let number_expected = Value::from(16).with_unit(unit_expected.clone());
        assert_eq!(number_expected, number);
    }

    #[test]
    fn test_powi_2() {
        let unit = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };

        let number = Value::from(5).with_unit(unit.clone()).powi(0);

        let number_expected = Value::one();
        assert_eq!(number_expected, number);
    }

    #[test]
    fn test_abs_1() {
        let expected = Decimal::from_u32(4).unwrap();
        let real = Value::from(4).abs();
        assert_eq!(expected, real);
    }

    #[test]
    fn test_abs_2() {
        let expected = Decimal::from_u32(4).unwrap();
        let real = Value::from(-4).abs();
        assert_eq!(expected, real);
    }

    #[test]
    fn test_abs_3() {
        let expected = Decimal::from_u32(5).unwrap();
        let real = (Value::from(3) + Value::from(4).i()).abs();
        assert_eq!(expected, real);
    }

    #[test]
    fn test_abs_4() {
        let expected = Decimal::from_u32(5).unwrap();
        let real = (Value::from(-3) + Value::from(-4).i()).abs();
        assert_eq!(expected, real);
    }

    #[test]
    fn test_abs_5() {
        let expected = Decimal::from_u32(5).unwrap();
        let real = (Value::from(-3) + Value::from(4).i()).abs();
        assert_eq!(expected, real);
    }

    #[test]
    fn test_abs_6() {
        let expected = Decimal::from_u32(5).unwrap();
        let real = (Value::from(3) + Value::from(-4).i()).abs();
        assert_eq!(expected, real);
    }

    #[test]
    fn test_is_unitless_one_1() {
        assert!(Value::one().is_unitless_one());
    }

    #[test]
    fn test_is_unitless_one_2() {
        assert!(!Value::from(1.0).is_unitless_one());
    }

    #[test]
    fn test_is_unitless_one_3() {
        assert!(!Value::zero().is_unitless_one());
    }

    #[test]
    fn test_is_zero_1() {
        assert!(Value::zero().is_zero());
    }

    #[test]
    fn test_is_zero_2() {
        assert!(!Value::one().is_zero());
    }

    #[test]
    fn test_is_zero_3() {
        assert!(Value::from(0).is_zero());
    }

    #[test]
    fn test_is_real_1() {
        assert!(Value::one().is_real());
    }

    #[test]
    fn test_is_real_2() {
        assert!(Value::zero().is_real());
    }

    #[test]
    fn test_is_real_3() {
        assert!(Value::from(5).is_real());
    }

    #[test]
    fn test_is_real_4() {
        assert!(!(Value::from(8) + Value::from(2).i()).is_real())
    }

    #[test]
    fn test_refactor_exponent_1() {
        let mut ten_thousand_meters = Value::from(10000).with_unit(Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        });
        ten_thousand_meters.refactor_exponent(1);
        assert_eq!(Number::from(10), ten_thousand_meters.real);
        assert_eq!(3, ten_thousand_meters.unit.exponent);
    }

    #[test]
    fn test_refactor_exponent_2() {
        let mut thousand_meters = Value::from(1000).with_unit(Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        });
        thousand_meters.refactor_exponent(1);
        assert_eq!(Number::from(1), thousand_meters.real);
        assert_eq!(3, thousand_meters.unit.exponent);
    }

    #[test]
    fn test_refactor_exponent_3() {
        let mut thousandth_meter = (Value::from(1) / Value::from(1000)).with_unit(Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        });
        thousandth_meter.refactor_exponent(1);
        assert_eq!(Number::from(1), thousandth_meter.real);
        assert_eq!(-3, thousandth_meter.unit.exponent);
    }

    #[test]
    fn test_refactor_exponent_4() {
        let mut hundredth_meter = (Value::from(1) / Value::from(100)).with_unit(Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        });
        hundredth_meter.refactor_exponent(1);
        assert_eq!(Number::from(10), hundredth_meter.real);
        assert_eq!(-3, hundredth_meter.unit.exponent);
    }

    #[test]
    fn test_display_1() {
        assert_eq!("1", Value::one().to_string());
    }

    #[test]
    fn test_display_2() {
        assert_eq!("5", Value::from(5).to_string());
    }

    #[test]
    fn test_display_3() {
        assert_eq!("i", Value::one().i().to_string());
    }

    #[test]
    fn test_display_4() {
        assert_eq!("3i", Value::from(3).i().to_string());
    }

    #[test]
    fn test_neg_1() {
        assert_eq!(Value::from(-1), -Value::one());
    }

    #[test]
    fn test_add_1() {
        let two = Value::from(2);
        let three = Value::from(3);
        let five = Value::from(5);
        let result = two + three;
        assert_eq!(five, result.clone());
        assert!(result.is_exact());
    }

    #[test]
    fn test_add_2() {
        let two_onei = Value::from(2) + Value::from(1).i();
        let three_twoi = Value::from(3) + Value::from(2).i();
        let five_threei = Value::from(5) + Value::from(3).i();
        let result = two_onei + three_twoi;
        assert_eq!(five_threei, result.clone());
        assert!(result.is_exact());
    }

    #[test]
    fn test_add_3() {
        let two_onei = Value::from(2) + Value::from(1).i();
        let zero_meters = Value::zero().with_unit(Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        });
        assert_eq!(two_onei, two_onei.clone() + zero_meters);
    }

    #[test]
    fn test_partialord_1() {
        let four = Value::from(4);
        let negone = Value::from(-1);
        let eight = Value::from(8);
        let six_threei = Value::from(6) + Value::from(3).i();

        assert!(negone == negone);
        assert!(negone < four);
        assert!(negone < eight);
        assert!(negone != six_threei);
        assert!(four == four);
        assert!(four < eight);
        assert!(four != six_threei);
        assert!(eight == eight);
        assert!(eight != six_threei);
        assert!(six_threei == six_threei);
    }
}
