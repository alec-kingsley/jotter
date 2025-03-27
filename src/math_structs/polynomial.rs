use std::collections::HashSet;

use crate::math_structs::unit::*;
use crate::math_structs::value::*;

use rust_decimal::Decimal;

#[derive(Debug, Clone)]
pub struct Polynomial {
    /// coefficients of the polynomial.
    /// |coefficients| - 1 = polynomial degree
    /// |coefficients| > 0
    ///
    /// the first coefficient corresponds to the lowest degree
    ///
    ///
    pub coefficients: Vec<Value>,
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
                        .get_unit()
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
    fn evaluate(&self, x: &Value) -> Value {
        let mut result = self.coefficients[0].clone();
        for degree in 1..self.coefficients.len() {
            result += self.coefficients[degree].clone() * x.powi(degree as i32);
        }
        result
    }

    /// Evaluate the derivative of the `Polynomial` at a point `x`.
    ///
    /// # Arguments
    /// * `x` - The point at which the derivative of the `Polynomial` should be evaluated.
    ///
    fn evaluate_derivative(&self, x: &Value) -> Value {
        let mut result = Value::zero();
        for degree in 1..self.coefficients.len() {
            result += self.coefficients[degree].clone() * x.powi(degree as i32 - 1) * Value::from(Decimal::from(degree));
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
    pub fn find_roots(&self) -> HashSet<Value> {
        let mut scaled_self = self.clone();
        scaled_self.scale();
        let degree = self.coefficients.len() - 1;
        let unit = self.extract_unit().expect("Failed to extract unit");
        // wikipedia on Durand-Kerner says this number isn't special :(
        // but I think it is 🥹
        //
        // TODO - on a serious note this is problematic bc if the max coefficient
        // is smaller than this then it will probably not find it. Oopsies!
        let super_special_number =
            (Value::from(0.4) + Value::from(0.9).i()).with_unit(unit.clone());
        let mut roots: Vec<Value> = Vec::with_capacity(degree);
        for deg in 0..degree {
            // multiply by 1.0 to ensure inexact if 1 is solution
            roots.push(super_special_number.clone().powi(deg as i32) * Value::from(1.0));
        }

        let mut sufficient = false;
        while !sufficient {
            let old_roots = roots.clone();

            sufficient = true;
            for deg in 0..degree {
                let derivative_ratio = scaled_self.evaluate(&roots[deg])
                    / scaled_self.evaluate_derivative(&roots[deg]);
                let mut subtrahend = derivative_ratio.clone();

                let mut subtrahend_sum = Value::zero();
                for foreigner in 0..degree {
                    if foreigner == deg {
                        continue;
                    }
                    subtrahend_sum +=
                        Value::one() / (roots[deg].clone() - roots[foreigner].clone());
                }

                subtrahend /= Value::one() - (derivative_ratio * subtrahend_sum);

                roots[deg] -= subtrahend;
                sufficient &= roots[deg] == old_roots[deg];
            }
        }

        // rationalize anything that is sufficiently rational
        for i in 0..roots.len() {
            let rationalized = roots[i].rationalize();
            let evaluated = self.evaluate(&rationalized);
            if evaluated.is_exact() {
                roots[i] = rationalized;
            }
        }

        roots.into_iter().collect()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn polynomial_builder(coefficients: Vec<f64>) -> Polynomial {
        Polynomial {
            coefficients: coefficients
                .iter()
                .map(|&coefficient| Value::from(coefficient))
                .collect::<Vec<Value>>(),
        }
    }

    #[test]
    fn test_find_roots_1() {
        // x - 1 = 0
        let roots = polynomial_builder(vec![-1.0, 1.0]).find_roots();
        println!(
            "Roots found: {{{}}}",
            roots
                .iter()
                .map(|root| root.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        );
        assert_eq!(1, roots.len());
        assert!(roots.contains(&Value::from(1.0)));
        for root in roots {
            assert!(!root.is_exact());
        }
    }

    #[test]
    fn test_find_roots_2() {
        // x^2 - 1 = 0
        let roots = polynomial_builder(vec![-1.0, 0.0, 1.0]).find_roots();
        println!(
            "Roots found: {{{}}}",
            roots
                .iter()
                .map(|root| root.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        );
        assert_eq!(2, roots.len());
        assert!(roots.contains(&Value::from(1.0)));
        assert!(roots.contains(&Value::from(-1.0)));
        for root in roots {
            assert!(!root.is_exact());
        }
    }

    #[test]
    fn test_find_roots_3() {
        // x^4 - 1 = 0
        let roots = polynomial_builder(vec![-1.0, 0.0, 0.0, 0.0, 1.0]).find_roots();
        println!(
            "Roots found: {{{}}}",
            roots
                .iter()
                .map(|root| root.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        );
        assert_eq!(4, roots.len());
        assert!(roots.contains(&Value::from(1.0)));
        assert!(roots.contains(&Value::from(1.0).i()));
        assert!(roots.contains(&Value::from(1.0)));
        assert!(roots.contains(&Value::from(1.0).i()));
        for root in roots {
            assert!(!root.is_exact());
        }
    }

    #[test]
    fn test_find_roots_4() {
        // x^5 + 6x^4 - 26x^3 - 84x^2 + 313x - 210 = 0
        let roots = polynomial_builder(vec![-210.0, 313.0, -84.0, -26.0, 6.0, 1.0]).find_roots();
        println!(
            "Roots found: {{{}}}",
            roots
                .iter()
                .map(|root| root.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        );
        assert_eq!(5, roots.len());
        assert!(roots.contains(&Value::from(1.0)));
        assert!(roots.contains(&Value::from(2.0)));
        assert!(roots.contains(&Value::from(3.0)));
        assert!(roots.contains(&Value::from(-5.0)));
        assert!(roots.contains(&Value::from(-7.0)));
        for root in roots {
            assert!(!root.is_exact());
        }
    }
}
