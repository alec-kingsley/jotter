use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::*;

use crate::math_structs::unit::*;

static EPSILON: f64 = 1e-10;

#[derive(Debug, Clone)]
pub struct Number {
    /// Real component of numeric literal.
    real: f64,
    /// Imaginary component of numeric literal.
    imaginary: f64,
    /// Unit of the numeric literal.
    unit: Unit,
}

impl Hash for Number {
    /// Hash for a `Number`.
    /// Necesarry since f64.hash() does not exist.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        // they're equal if they look equal
        self.to_string().hash(state);
        self.unit.hash(state);
    }
}

impl PartialEq for Number {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        self.unit == other.unit && {
            let mut other_clone = other.clone();
            let exp_diff = other_clone.unit.exponent - self.unit.exponent;
            other_clone.unit.exponent -= exp_diff;
            other_clone.real = other_clone.real * (10 as f64).powi(exp_diff as i32);
            other_clone.imaginary = other_clone.imaginary * (10 as f64).powi(exp_diff as i32);
            other_clone.real *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
            other_clone.imaginary *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
            other_clone.real < self.real + EPSILON
                && other_clone.real > self.real - EPSILON
                && other_clone.imaginary < self.imaginary + EPSILON
                && other_clone.imaginary > self.imaginary - EPSILON
        }
    }
}

impl Eq for Number {}

impl Number {
    /// Constructor for a real number.
    ///
    /// # Arguments
    /// * `value` - value of the number
    /// * `unit` - unit of the number
    ///
    pub fn real(value: f64, unit: Unit) -> Self {
        Self {
            real: value,
            imaginary: 0f64,
            unit,
        }
    }

    /// Constructor for a complex number.
    ///
    /// # Arguments
    /// * `real` - real component of the number
    /// * `imaginary` - imaginary component of the number
    /// * `unit` - unit of the number
    ///
    pub fn complex(real: f64, imaginary: f64, unit: Unit) -> Self {
        Self {
            real,
            imaginary,
            unit,
        }
    }

    /// Constructor for unitless one.
    ///
    pub fn unitless_one() -> Self {
        Self {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit::unitless(),
        }
    }

    /// Constructor for unitless zero.
    ///
    pub fn unitless_zero() -> Self {
        Self {
            real: 0f64,
            imaginary: 0f64,
            unit: Unit::unitless(),
        }
    }

    /// Get an immutable reference to `self.unit`.
    ///
    pub fn get_unit(&self) -> &Unit {
        &self.unit
    }

    /// Takes `self` to the `pow`'th power and returns it.
    ///
    /// # Arguments:
    /// * `pow` - the power to be raised to
    ///
    pub fn powi(&self, pow: u32) -> Number {
        let mut builder = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit::unitless(),
        };
        for _ in 0..pow {
            builder *= self.clone();
        }

        builder
    }

    /// Returns the absolute value of the number.
    /// Does not consider unit.
    ///
    pub fn abs(&self) -> f64 {
        (self.real * self.real + self.imaginary * self.imaginary).sqrt()
    }

    /// Returns true iff the number has a value of 1
    ///
    pub fn is_unitless_one(&self) -> bool {
        let tester = self.real * 10f64.powi(self.unit.exponent as i32) as f64;
        tester + EPSILON > 1f64
            && 1f64 > tester - EPSILON
            && self.imaginary - EPSILON < 0f64
            && 0f64 < self.imaginary + EPSILON
            && self.unit.is_unitless()
    }

    /// Returns true iff the number has a value of 0
    ///
    pub fn is_zero(&self) -> bool {
        self.real - EPSILON < 0f64
            && 0f64 < self.real + EPSILON
            && self.imaginary - EPSILON < 0f64
            && 0f64 < self.imaginary + EPSILON
    }

    /// Returns true iff the number is in the real set.
    ///
    pub fn is_real(&self) -> bool {
        self.imaginary - EPSILON < 0f64 && 0f64 < self.imaginary + EPSILON
    }

    /// Refactor the unit such that its `unit.exponent` is divisible by `subunit_exponent`.
    /// It must also either be divisible by 3 or have a magnitude less than 3.
    ///
    /// # Arguments
    /// * `subunit_exponent` - thing to be divisible by.
    pub fn refactor_exponent(&mut self, subunit_exponent: i8) {
        // try to force self to be within 3 digits from 0
        while self.abs() >= 1.0 {
            self.real /= 10.0;
            self.imaginary /= 10.0;
            self.unit.exponent += 1;
        }
        while !self.is_zero() && self.abs() < 1.0 {
            self.real *= 10.0;
            self.imaginary *= 10.0;
            self.unit.exponent -= 1;
        }

        // ensure exponent exists
        if self.unit.exponent > 0 {
            while self.unit.exponent > 30
                || (subunit_exponent != 0 && self.unit.exponent % (3 * subunit_exponent) != 0)
            {
                self.real *= 10.0;
                self.imaginary *= 10.0;
                self.unit.exponent -= 1;
            }
        } else {
            while self.unit.exponent < -30
                || (subunit_exponent != 0 && self.unit.exponent % (3 * subunit_exponent) != 0)
            {
                self.real /= 10.0;
                self.imaginary /= 10.0;
                self.unit.exponent += 1;
            }
        }
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

impl Display for Number {
    /// Format `Number` appropriately.
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

        // write final result depending on numerator/denominator contents
        let numeric_str = if self.imaginary + EPSILON > 0f64 && 0f64 > self.imaginary - EPSILON {
            format!("{:.10}", self_clone.real)
                .trim_end_matches('0')
                .trim_end_matches('.')
                .to_owned()
        } else if self.real + EPSILON > 0f64 && 0f64 > self.real - EPSILON {
            if self_clone.imaginary + EPSILON > 1f64 && 1f64 > self_clone.imaginary - EPSILON {
                String::from("i")
            } else if self_clone.imaginary + EPSILON > -1f64
                && -1f64 > self_clone.imaginary - EPSILON
            {
                String::from("-i")
            } else {
                format!("{:.10}", self_clone.imaginary)
                    .trim_end_matches('0')
                    .trim_end_matches('.')
                    .to_owned()
                    + "i"
            }
        } else {
            if self_clone.imaginary > 0f64 {
                format!("{:.10}", self_clone.real)
                    .trim_end_matches('0')
                    .trim_end_matches('.')
                    .to_owned()
                    + if self_clone.imaginary + EPSILON > 1f64
                        && 1f64 > self_clone.imaginary - EPSILON
                    {
                        String::from(" + i")
                    } else {
                        format!(" + {:.10}", self_clone.imaginary)
                            .trim_end_matches('0')
                            .trim_end_matches('.')
                            .to_owned()
                            + "i"
                    }
                    .as_str()
            } else {
                format!("{:.10}", self_clone.real)
                    .trim_end_matches('0')
                    .trim_end_matches('.')
                    .to_owned()
                    + if self_clone.imaginary + EPSILON > -1f64
                        && 1f64 > self_clone.imaginary - EPSILON
                    {
                        String::from(" - i")
                    } else {
                        format!(" - {:.10}", -self_clone.imaginary)
                            .trim_end_matches('0')
                            .trim_end_matches('.')
                            .to_owned()
                            + "i"
                    }
                    .as_str()
            }
        };
        let numeric_str = if !(numerator.is_empty() && denominator.is_empty())
            && (self_clone.real != 0f64 && self_clone.imaginary != 0f64)
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

impl Add for Number {
    type Output = Self;

    /// Operator overload for +.
    ///
    fn add(self, other: Self) -> Self {
        assert!(self.unit == other.unit, "Mismatched types");
        let mut other_clone = other.clone();
        let exp_diff = other_clone.unit.exponent - self.unit.exponent;
        other_clone.unit.exponent -= exp_diff;
        other_clone.real = other_clone.real * (10 as f64).powi(exp_diff as i32) as f64;
        other_clone.imaginary = other_clone.imaginary * (10 as f64).powi(exp_diff as i32) as f64;
        other_clone.real *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
        other_clone.imaginary *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
        Self {
            real: self.real + other_clone.real,
            imaginary: self.imaginary + other_clone.imaginary,
            unit: self.unit,
        }
    }
}

impl AddAssign for Number {
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
        if !other.clone().is_zero() {
            self.clone_from(&(self.clone() + other));
        }
    }
}

impl Neg for Number {
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

impl Sub for Number {
    type Output = Self;

    /// Operator overload for -.
    ///
    fn sub(self, other: Self) -> Self {
        assert!(self.unit == other.unit, "Mismatched types");
        let mut other_clone = other.clone();
        let exp_diff = other_clone.unit.exponent - self.unit.exponent;
        other_clone.unit.exponent -= exp_diff;
        other_clone.real = other_clone.real * (10 as f64).powi(exp_diff as i32);
        other_clone.imaginary = other_clone.imaginary * (10 as f64).powi(exp_diff as i32);
        other_clone.real *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
        other_clone.imaginary *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
        Self {
            real: self.real - other_clone.real,
            imaginary: self.imaginary - other_clone.imaginary,
            unit: self.unit,
        }
    }
}

impl SubAssign for Number {
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

impl Mul for Number {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut constituents = self.unit.constituents;
        for (base_unit, power) in other.unit.constituents {
            *constituents.entry(base_unit).or_insert(0) += power;
        }
        Self {
            real: self.real * other.real - self.imaginary * other.imaginary,
            imaginary: self.real * other.imaginary + self.imaginary * other.real,
            unit: Unit {
                exponent: self.unit.exponent + other.unit.exponent,
                constituents,
            },
        }
    }
}

impl MulAssign for Number {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Mul<f64> for Number {
    type Output = Self;

    fn mul(self, rhs: f64) -> Self {
        Self {
            real: self.real * rhs,
            imaginary: self.imaginary * rhs,
            unit: self.unit,
        }
    }
}

impl MulAssign<f64> for Number {
    fn mul_assign(&mut self, rhs: f64) {
        self.clone_from(&(self.clone() * rhs));
    }
}

impl Div for Number {
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

impl DivAssign for Number {
    /// Operator overload for /=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}

impl Div<f64> for Number {
    type Output = Self;

    fn div(self, rhs: f64) -> Self {
        Self {
            real: self.real / rhs,
            imaginary: self.imaginary / rhs,
            unit: self.unit,
        }
    }
}

impl DivAssign<f64> for Number {
    fn div_assign(&mut self, rhs: f64) {
        self.clone_from(&(self.clone() / rhs));
    }
}

impl PartialOrd for Number {
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
            other_clone.real = other_clone.real * (10 as f64).powi(exp_diff as i32);
            other_clone.real *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
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
    fn test_constructors_1() {
        assert_eq!(Number::unitless_one(), Number::real(1f64, Unit::unitless()));
        assert_eq!(
            Number::unitless_one(),
            Number::complex(1f64, 0f64, Unit::unitless())
        );

        assert_eq!(
            Number::unitless_zero(),
            Number::real(0f64, Unit::unitless())
        );
        assert_eq!(
            Number::unitless_zero(),
            Number::complex(0f64, 0f64, Unit::unitless())
        );
    }

    #[test]
    fn test_get_unit_1() {
        let unit = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };

        let number = Number::real(1f64, unit.clone());
        assert_eq!(unit, number.get_unit().clone());
    }

    #[test]
    fn test_powi_1() {
        let unit = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };

        let number = Number::real(2f64, unit.clone()).powi(4);

        let unit_expected = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 4)]),
        };

        let number_expected = Number::real(16f64, unit_expected.clone());
        assert_eq!(number_expected, number);
    }

    #[test]
    fn test_powi_2() {
        let unit = Unit {
            exponent: 0i8,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };

        let number = Number::real(5f64, unit.clone()).powi(0);

        let number_expected = Number::unitless_one();
        assert_eq!(number_expected, number);
    }

    #[test]
    fn test_abs_1() {
        let expected = 4f64;
        let real = Number::real(4f64, Unit::unitless()).abs();
        assert!(expected - EPSILON < real && real < expected + EPSILON);
    }

    #[test]
    fn test_abs_2() {
        let expected = 4f64;
        let real = Number::real(-4f64, Unit::unitless()).abs();
        assert!(expected - EPSILON < real && real < expected + EPSILON);
    }

    #[test]
    fn test_abs_3() {
        let expected = 5f64;
        let real = Number::complex(3f64, 4f64, Unit::unitless()).abs();
        assert!(expected - EPSILON < real && real < expected + EPSILON);
    }

    #[test]
    fn test_abs_4() {
        let expected = 5f64;
        let real = Number::complex(-3f64, -4f64, Unit::unitless()).abs();
        assert!(expected - EPSILON < real && real < expected + EPSILON);
    }

    #[test]
    fn test_abs_5() {
        let expected = 5f64;
        let real = Number::complex(3f64, -4f64, Unit::unitless()).abs();
        assert!(expected - EPSILON < real && real < expected + EPSILON);
    }

    #[test]
    fn test_abs_6() {
        let expected = 5f64;
        let real = Number::complex(-3f64, 4f64, Unit::unitless()).abs();
        assert!(expected - EPSILON < real && real < expected + EPSILON);
    }

    #[test]
    fn test_is_unitless_one_1() {
        assert!(Number::unitless_one().is_unitless_one());
    }

    #[test]
    fn test_is_unitless_one_2() {
        assert!(!Number::unitless_zero().is_unitless_one());
    }

    #[test]
    fn test_is_zero_1() {
        assert!(Number::unitless_zero().is_zero());
    }

    #[test]
    fn test_is_zero_2() {
        assert!(!Number::unitless_one().is_zero());
    }

    #[test]
    fn test_is_zero_3() {
        assert!(Number::real(
            0f64,
            Unit {
                exponent: 0i8,
                constituents: HashMap::from([(BaseUnit::Meter, 1)]),
            }
        )
        .is_zero());
    }

    #[test]
    fn test_is_real_1() {
        assert!(Number::unitless_one().is_real());
    }

    #[test]
    fn test_is_real_2() {
        assert!(Number::unitless_zero().is_real());
    }

    #[test]
    fn test_is_real_3() {
        assert!(Number::real(5f64, Unit::unitless()).is_real());
    }

    #[test]
    fn test_is_real_4() {
        assert!(Number::complex(8f64, 0f64, Unit::unitless()).is_real());
    }

    #[test]
    fn test_is_real_5() {
        assert!(!Number::complex(8f64, 2f64, Unit::unitless()).is_real());
    }

    #[test]
    fn test_display_1() {
        assert_eq!("1", Number::unitless_one().to_string());
    }

    #[test]
    fn test_display_2() {
        assert_eq!("5", Number::real(5f64, Unit::unitless()).to_string());
    }

    #[test]
    fn test_display_3() {
        assert_eq!(
            "i",
            Number::complex(0f64, 1f64, Unit::unitless()).to_string()
        );
    }

    #[test]
    fn test_display_4() {
        assert_eq!(
            "3i",
            Number::complex(0f64, 3f64, Unit::unitless()).to_string()
        );
    }

    #[test]
    fn test_add_1() {
        let two = Number::real(2f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let five = Number::real(5f64, Unit::unitless());
        assert_eq!(five, two + three);
    }

    #[test]
    fn test_add_2() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let five_threei = Number::complex(5f64, 3f64, Unit::unitless());
        assert_eq!(five_threei, two_onei + three_twoi);
    }

    #[test]
    fn test_add_3() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let zero_meters = Number::real(
            0f64,
            Unit {
                exponent: 0i8,
                constituents: HashMap::from([(BaseUnit::Meter, 1)]),
            },
        );
        assert_eq!(two_onei, two_onei.clone() + zero_meters);
    }

    #[test]
    fn test_addassign_1() {
        let mut val = Number::real(2f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let five = Number::real(5f64, Unit::unitless());
        val += three;
        assert_eq!(five, val);
    }

    #[test]
    fn test_addassign_2() {
        let mut val = Number::complex(2f64, 1f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let five_threei = Number::complex(5f64, 3f64, Unit::unitless());
        val += three_twoi;
        assert_eq!(five_threei, val);
    }

    #[test]
    fn test_addassign_3() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let mut val = two_onei.clone();
        let zero_meters = Number::real(
            0f64,
            Unit {
                exponent: 0i8,
                constituents: HashMap::from([(BaseUnit::Meter, 1)]),
            },
        );
        val += zero_meters;
        assert_eq!(two_onei, val);
    }

    #[test]
    fn test_neg_1() {
        let negative_one = -Number::unitless_one();
        let expected = Number::real(-1f64, Unit::unitless());

        assert_eq!(expected, negative_one);
    }

    #[test]
    fn test_neg_2() {
        let two_threei = -Number::complex(-1f64, -3f64, Unit::unitless());
        let expected = Number::complex(1f64, 3f64, Unit::unitless());

        assert_eq!(expected, two_threei);
    }

    #[test]
    fn test_sub_1() {
        let two = Number::real(2f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let five = Number::real(5f64, Unit::unitless());
        assert_eq!(two, five - three);
    }

    #[test]
    fn test_sub_2() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let five_threei = Number::complex(5f64, 3f64, Unit::unitless());
        assert_eq!(two_onei, five_threei - three_twoi);
    }

    #[test]
    fn test_sub_3() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let zero_meters = Number::real(
            0f64,
            Unit {
                exponent: 0i8,
                constituents: HashMap::from([(BaseUnit::Meter, 1)]),
            },
        );
        assert_eq!(two_onei, two_onei.clone() - zero_meters);
    }

    #[test]
    fn test_subassign_1() {
        let mut val = Number::real(5f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let two = Number::real(2f64, Unit::unitless());
        val -= three;
        assert_eq!(two, val);
    }

    #[test]
    fn test_subassign_2() {
        let mut val = Number::complex(5f64, 3f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        val -= three_twoi;
        assert_eq!(two_onei, val);
    }

    #[test]
    fn test_subassign_3() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let mut val = two_onei.clone();
        let zero_meters = Number::real(
            0f64,
            Unit {
                exponent: 0i8,
                constituents: HashMap::from([(BaseUnit::Meter, 1)]),
            },
        );
        val -= zero_meters;
        assert_eq!(two_onei, val);
    }

    #[test]
    fn test_mul_1() {
        let two = Number::real(2f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let six = Number::real(6f64, Unit::unitless());
        assert_eq!(six, two * three);
    }

    #[test]
    fn test_mul_2() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let four_seveni = Number::complex(4f64, 7f64, Unit::unitless());
        assert_eq!(four_seveni, two_onei * three_twoi);
    }

    #[test]
    fn test_mulassign_1() {
        let mut val = Number::real(2f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let six = Number::real(6f64, Unit::unitless());
        val *= three;
        assert_eq!(six, val);
    }

    #[test]
    fn test_mulassign_2() {
        let mut val = Number::complex(2f64, 1f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let four_seveni = Number::complex(4f64, 7f64, Unit::unitless());
        val *= three_twoi;
        assert_eq!(four_seveni, val);
    }

    #[test]
    fn test_mul_f64_1() {
        let two = Number::real(2f64, Unit::unitless());
        let six = Number::real(6f64, Unit::unitless());
        assert_eq!(six, two * 3f64);
    }

    #[test]
    fn test_mul_f64_2() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let six_threei = Number::complex(6f64, 3f64, Unit::unitless());
        assert_eq!(six_threei, two_onei * 3f64);
    }

    #[test]
    fn test_mulassign_f64_1() {
        let mut val = Number::real(2f64, Unit::unitless());
        let six = Number::real(6f64, Unit::unitless());
        val *= 3f64;
        assert_eq!(six, val);
    }

    #[test]
    fn test_mulassign_f64_2() {
        let mut val = Number::complex(2f64, 1f64, Unit::unitless());
        let six_threei = Number::complex(6f64, 3f64, Unit::unitless());
        val *= 3f64;
        assert_eq!(six_threei, val);
    }

    #[test]
    fn test_div_1() {
        let two = Number::real(2f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let six = Number::real(6f64, Unit::unitless());
        assert_eq!(two, six / three);
    }

    #[test]
    fn test_div_2() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let four_seveni = Number::complex(4f64, 7f64, Unit::unitless());
        assert_eq!(two_onei, four_seveni / three_twoi);
    }

    #[test]
    fn test_divassign_1() {
        let mut val = Number::real(6f64, Unit::unitless());
        let three = Number::real(3f64, Unit::unitless());
        let two = Number::real(2f64, Unit::unitless());
        val /= three;
        assert_eq!(two, val);
    }

    #[test]
    fn test_divassign_2() {
        let mut val = Number::complex(4f64, 7f64, Unit::unitless());
        let three_twoi = Number::complex(3f64, 2f64, Unit::unitless());
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        val /= three_twoi;
        assert_eq!(two_onei, val);
    }

    #[test]
    fn test_div_f64_1() {
        let two = Number::real(2f64, Unit::unitless());
        let six = Number::real(6f64, Unit::unitless());
        assert_eq!(two, six / 3f64);
    }

    #[test]
    fn test_div_f64_2() {
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        let six_threei = Number::complex(6f64, 3f64, Unit::unitless());
        assert_eq!(two_onei, six_threei / 3f64);
    }

    #[test]
    fn test_divassign_f64_1() {
        let mut val = Number::real(6f64, Unit::unitless());
        let two = Number::real(2f64, Unit::unitless());
        val /= 3f64;
        assert_eq!(two, val);
    }

    #[test]
    fn test_divassign_f64_2() {
        let mut val = Number::complex(6f64, 3f64, Unit::unitless());
        let two_onei = Number::complex(2f64, 1f64, Unit::unitless());
        val /= 3f64;
        assert_eq!(two_onei, val);
    }

    #[test]
    fn test_partialord_1() {
        let four = Number::real(4f64, Unit::unitless());
        let negone = Number::real(-1f64, Unit::unitless());
        let eight = Number::real(8f64, Unit::unitless());
        let six_threei = Number::complex(6f64, 3f64, Unit::unitless());

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
