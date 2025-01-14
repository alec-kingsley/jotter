use std::collections::{HashMap, HashSet};

use crate::math_structs::number::*;
use crate::math_structs::unit::*;

#[derive(Debug, Clone)]
pub struct Polynomial {
    /// coefficients of the polynomial.
    /// |coefficients| - 1 = polynomial degree
    /// |coefficients| > 0
    ///
    /// the first coefficient corresponds to the lowest degree
    ///
    ///
    pub coefficients: Vec<Number>,
}

impl Polynomial {
    /// Scale polynomial such that highest degree coefficient is 1.
    ///
    fn scale(&mut self) {
        let factor = self.coefficients[self.coefficients.len() - 1].clone();
        for coefficient in &mut self.coefficients {
            *coefficient /= factor.clone();
        }
    }

    /// Extract the unit from the polynomial.
    ///
    pub fn extract_unit(&self) -> Result<Unit, String> {
        let mut unit_option: Option<Unit> = None;
        let degree = self.coefficients.len() - 1;
        // extract unit ;)
        for deg in 0..degree {
            let coefficient = &self.coefficients[deg];
            if !coefficient.is_zero() {
                let found_unit = Unit {
                    exponent: 0i8,
                    constituents: coefficient
                        .unit
                        .constituents
                        .clone()
                        .into_iter()
                        .map(|(k, v)| (k, v + deg as i8))
                        .collect(),
                };
                if let Some(unit) = &unit_option {
                    if unit != &found_unit {
                        return Err(String::from("Mismatched units"));
                    }
                } else {
                    unit_option = Some(found_unit);
                }
            }
        }
        if unit_option.is_none() {
            Err(String::from("Unit not found"))
        } else {
            Ok(unit_option.unwrap())
        }
    }

    /// Evaluate the `Polynomial` at a point `x`.
    ///
    /// # Arguments
    /// * `x` - The point at which the `Polynomial` should be evaluated.
    ///
    pub fn evaluate(&self, x: &Number) -> Number {
        let mut result = self.coefficients[0].clone();
        for degree in 1..self.coefficients.len() {
            result += self.coefficients[degree].clone() * x.powi(degree as u32);
        }
        result
    }

    /// Evaluate the derivative of the `Polynomial` at a point `x`.
    ///
    /// # Arguments
    /// * `x` - The point at which the derivative of the `Polynomial` should be evaluated.
    ///
    pub fn evaluate_derivative(&self, x: &Number) -> Number {
        let mut result = Number {
            real: 0f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        for degree in 1..self.coefficients.len() {
            let mut term = self.coefficients[degree].clone() * x.powi(degree as u32 - 1);
            term.real *= degree as f64;
            term.imaginary *= degree as f64;
            result += term;
        }
        result
    }

    /// Find roots of the polynomial. That is, solutions for its
    /// variable where the polynomial is set equal to 1.
    ///
    /// NOTE - this uses the Aberth method. It does this regardless of how complicated the
    /// polynomial is. It may be worthwhile to first see if there is a quicker way, or use
    /// different algorithms for different degrees in general. ALSO - Initial root guesses are
    /// arbitrarily chosen to be those that Wikipedia arbitrarily chose on its Durand-Kerner page.
    /// Maybe there's a better way of doing that.
    ///
    pub fn find_roots(&self) -> HashSet<Number> {
        let mut scaled_self = self.clone();
        scaled_self.scale();
        let degree = self.coefficients.len() - 1;
        let unit = self.extract_unit().expect("Failed to extract unit");
        let super_special_number = Number {
            // wikipedia on Durand-Kerner says this number isn't special :(
            // but I think it is 🥹
            real: 0.4,
            imaginary: 0.9,
            unit: unit.clone(),
        };
        let mut roots: Vec<Number> = Vec::with_capacity(degree);
        for deg in 0..degree {
            roots.push(super_special_number.clone().powi(deg as u32));
        }

        let mut sufficient = false;
        while !sufficient {
            let old_roots = roots.clone();

            sufficient = true;
            for deg in 0..degree {
                let derivative_ratio = scaled_self.evaluate(&roots[deg])
                    / scaled_self.evaluate_derivative(&roots[deg]);
                let mut subtrahend = derivative_ratio.clone();

                let mut subtrahend_sum = Number {
                    real: 0f64,
                    imaginary: 0f64,
                    unit: unit.clone(),
                };
                for foreigner in 0..degree {
                    if foreigner == deg {
                        continue;
                    }
                    subtrahend_sum += Number {
                        real: 1f64,
                        imaginary: 0f64,
                        unit: unit.clone(),
                    } / (roots[deg].clone() - roots[foreigner].clone());
                }

                subtrahend /= Number {
                    real: 1f64,
                    imaginary: 0f64,
                    unit: unit.clone(),
                } - (derivative_ratio * subtrahend_sum);

                roots[deg] -= subtrahend;
                sufficient &= roots[deg] == old_roots[deg];
            }
        }

        roots.into_iter().collect()
    }
}
