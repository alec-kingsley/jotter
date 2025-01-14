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
    pub real: f64,
    /// Imaginary component of numeric literal.
    pub imaginary: f64,
    /// Unit of the numeric literal.
    pub unit: Unit,
}

impl Hash for Number {
    /// Hash for a `Number`.
    /// Necesarry since f64.hash() does not exist.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.real.to_bits().hash(state);
        self.imaginary.to_bits().hash(state);
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
    /// Takes `self` to the `pow`'th power and returns it.
    ///
    /// # Arguments:
    /// * pow - the power to be raised to
    ///
    pub fn powi(&self, pow: u32) -> Number {
        let mut builder = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
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
        self.real * 10f64.powi(self.unit.exponent as i32) as f64 == 1f64
            && self.imaginary - EPSILON < 0f64
            && 0f64 < self.imaginary + EPSILON
            && self.unit
                == Unit {
                    exponent: 0,
                    constituents: HashMap::new(),
                }
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
            if self_clone.imaginary == 1f64 {
                String::from("i")
            } else if self_clone.imaginary == -1f64 {
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
                    + if self_clone.imaginary == 1f64 {
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
                    + if self_clone.imaginary == -1f64 {
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
