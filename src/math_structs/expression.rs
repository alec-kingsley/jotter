use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::ops::*;

use crate::math_structs::factor::*;
use crate::math_structs::identifier::*;
use crate::math_structs::number::*;
use crate::math_structs::polynomial::*;
use crate::math_structs::term::*;
use crate::math_structs::unit::*;

#[derive(Debug, Clone, Hash)]
pub struct Expression {
    /// operands to be added.
    /// if empty, value is 0.
    ///
    pub minuend: Vec<Term>,

    /// operands to be subtracted.
    /// if empty, value is 0.
    ///
    pub subtrahend: Vec<Term>,
}

impl PartialEq for Expression {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        let mut removable = other.clone();
        let mut all_removed = true;
        for operand in &self.minuend {
            let mut removed = false;
            for i in (0..removable.minuend.len()).rev() {
                if operand == &removable.minuend[i] {
                    removable.minuend.remove(i);
                    removed = true;
                    break;
                }
            }
            all_removed &= removed;
        }
        for operand in &self.subtrahend {
            let mut removed = false;
            for i in (0..removable.subtrahend.len()).rev() {
                if operand == &removable.subtrahend[i] {
                    removable.subtrahend.remove(i);
                    removed = true;
                    break;
                }
            }
            all_removed &= removed;
        }
        all_removed && removable.minuend.is_empty() && removable.subtrahend.is_empty()
    }
}

impl Eq for Expression {}

impl Display for Expression {
    /// Format `Expression` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // format minuend elements, joined by `+`
        let minuend_str = self
            .minuend
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(" + ");

        // format subtrahend elements, each preceded by `-`
        let subtrahend_str = self
            .subtrahend
            .iter()
            .map(|x| format!("- {}", x))
            .collect::<Vec<_>>()
            .join(" ");

        // combine the two parts
        if subtrahend_str.is_empty() {
            if minuend_str.is_empty() {
                write!(f, "0")
            } else {
                write!(f, "{}", minuend_str)
            }
        } else if minuend_str.is_empty() {
            write!(f, "{}", subtrahend_str)
        } else {
            write!(f, "{} {}", minuend_str, subtrahend_str)
        }
    }
}

impl Expression {
    /// "flatten" the `Expression`.
    ///
    /// remove a many parentheticals as possible, such that it's just a sum of terms.
    /// combine like terms.
    ///
    pub fn flatten(&mut self) {
        let mut father_expression = Expression {
            minuend: Vec::new(),
            subtrahend: Vec::new(),
        };

        for mut self_term in self.minuend.clone() {
            self_term.flatten();
            if let Factor::Parenthetical(mut child_expression) = self_term
                .numerator
                .get(0)
                .cloned()
                .unwrap_or(Factor::Number(Number {
                    real: 1f64,
                    imaginary: 0f64,
                    unit: Unit {
                        exponent: 0i8,
                        constituents: HashMap::new(),
                    },
                }))
            {
                child_expression.flatten();
                for child_term in child_expression.minuend {
                    father_expression.minuend.push(child_term.clone());
                }
                for child_term in child_expression.subtrahend {
                    father_expression.subtrahend.push(child_term.clone());
                }
            } else {
                father_expression.minuend.push(self_term);
            }
        }

        for mut self_term in self.subtrahend.clone() {
            self_term.flatten();
            if let Factor::Parenthetical(mut child_expression) = self_term
                .numerator
                .get(0)
                .cloned()
                .unwrap_or(Factor::Number(Number {
                    real: 1f64,
                    imaginary: 0f64,
                    unit: Unit {
                        exponent: 0i8,
                        constituents: HashMap::new(),
                    },
                }))
            {
                child_expression.flatten();
                for child_term in child_expression.minuend {
                    father_expression.subtrahend.push(child_term.clone());
                }
                for child_term in child_expression.subtrahend {
                    father_expression.minuend.push(child_term.clone());
                }
            } else {
                father_expression.subtrahend.push(self_term);
            }
        }
        self.clone_from(&father_expression);
        self.combine_like_terms();
    }

    /// Combine like terms in `Expression`.
    ///
    fn combine_like_terms(&mut self) {
        let mut numbers: Vec<Number> = Vec::new();
        let mut terms: Vec<Term> = Vec::new();

        // extract all terms with their numeric factor
        for mut self_term in self.minuend.clone() {
            let number = self_term.extract_number();
            numbers.push(number);
            terms.push(self_term);
        }

        for mut self_term in self.subtrahend.clone() {
            let number = self_term.extract_number();
            numbers.push(-number);
            terms.push(self_term);
        }

        // combine like terms
        for term_i in (0..numbers.len()).rev() {
            for term_j in ((term_i + 1)..terms.len()).rev() {
                if terms[term_i] == terms[term_j] {
                    numbers[term_i] = numbers[term_i].clone() + numbers[term_j].clone();
                    terms.remove(term_j);
                    numbers.remove(term_j);
                }
            }
        }

        // restore self
        let one = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };

        let zero = one.clone() - one.clone();

        self.minuend.clear();
        self.subtrahend.clear();
        for i in 0..numbers.len() {
            let number = numbers[i].clone();
            let mut operand = terms[i].clone();
            if number != one && number != -one.clone() {
                operand.numerator.insert(
                    0,
                    Factor::Number(if number < zero.clone() {
                        -number.clone()
                    } else {
                        number.clone()
                    }),
                );
            }
            if number > zero.clone() {
                self.minuend.push(operand);
            } else if number < zero.clone() {
                self.subtrahend.push(operand);
            } else if !number.is_zero() {
                // it's complex
                self.minuend.push(operand);
            }
        }
    }

    /// Extract `Polynomial` from `self`.
    /// Assumes that `self` is already fully simplified.
    ///
    pub fn extract_polynomial(&self) -> Option<(Polynomial, Identifier)> {
        let mut variable_name_option: Option<Identifier> = None;
        let mut polynomial = Polynomial {
            coefficients: Vec::new(),
        };
        let zero = Number {
            real: 0f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        for term in &self.minuend {
            if term.denominator.len() > 0 {
                return None;
            }
            let mut degree = 0;
            let mut coefficient = Number {
                real: 1f64,
                imaginary: 0f64,
                unit: Unit {
                    exponent: 0i8,
                    constituents: HashMap::new(),
                },
            };
            for factor in &term.numerator {
                match factor {
                    Factor::Identifier(name) => {
                        if variable_name_option == None {
                            variable_name_option = Some(name.clone());
                        } else if &variable_name_option.clone().unwrap() != name {
                            // a polynomial can only have one variable
                            return None;
                        }
                        degree += 1;
                    }
                    Factor::Number(number) => {
                        coefficient *= number.clone();
                    }
                    _ => return None,
                }
            }
            if polynomial.coefficients.len() <= degree {
                polynomial
                    .coefficients
                    .resize_with(degree + 1, || zero.clone());
            }
            polynomial.coefficients[degree] = coefficient;
        }
        for term in &self.subtrahend {
            if term.denominator.len() > 0 {
                return None;
            }
            let mut degree = 0;
            let mut coefficient = Number {
                real: -1f64,
                imaginary: 0f64,
                unit: Unit {
                    exponent: 0i8,
                    constituents: HashMap::new(),
                },
            };
            for factor in &term.numerator {
                match factor {
                    Factor::Identifier(name) => {
                        if variable_name_option == None {
                            variable_name_option = Some(name.clone());
                        } else if &variable_name_option.clone().unwrap() != name {
                            // a polynomial can only have one variable
                            return None;
                        }
                        degree += 1;
                    }
                    Factor::Number(number) => {
                        coefficient *= number.clone();
                    }
                    _ => return None,
                }
            }
            if polynomial.coefficients.len() < degree {
                polynomial.coefficients.resize_with(degree, || zero.clone());
            }
            polynomial.coefficients[degree] = coefficient;
        }
        if variable_name_option.is_some() {
            Some((polynomial, variable_name_option.unwrap()))
        } else {
            None
        }
    }
}

impl Add for Expression {
    type Output = Self;

    /// Operator overload for +.
    ///
    fn add(self, other: Self) -> Self {
        let mut result = self.clone();
        for operand in &other.minuend {
            result.minuend.push(operand.clone());
        }
        for operand in &other.subtrahend {
            result.subtrahend.push(operand.clone());
        }
        result
    }
}

impl AddAssign for Expression {
    /// Operator overload for +=.
    ///
    fn add_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() + other));
    }
}

impl Sub for Expression {
    type Output = Self;

    /// Operator overload for -.
    ///
    fn sub(self, other: Self) -> Self {
        let mut result = self.clone();
        for operand in &other.minuend {
            result.subtrahend.push(operand.clone());
        }
        for operand in &other.subtrahend {
            result.minuend.push(operand.clone());
        }
        result
    }
}

impl SubAssign for Expression {
    /// Operator overload for -=.
    ///
    fn sub_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() - other));
    }
}

impl Mul for Expression {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut result = Expression {
            minuend: Vec::new(),
            subtrahend: Vec::new(),
        };
        for self_term in &self.minuend {
            for other_term in other.minuend.clone() {
                result.minuend.push(self_term.clone() * other_term);
            }
            for other_term in other.subtrahend.clone() {
                result.subtrahend.push(self_term.clone() * other_term);
            }
        }
        for self_term in &self.subtrahend {
            for other_term in other.minuend.clone() {
                result.subtrahend.push(self_term.clone() * other_term);
            }
            for other_term in other.subtrahend.clone() {
                result.minuend.push(self_term.clone() * other_term);
            }
        }
        result
    }
}

impl MulAssign for Expression {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Div for Expression {
    type Output = Self;

    /// Operator overload for /.
    ///
    /// Just take every term and divide it by `other` thrown in a parenthetical.
    /// Don't wanna think about math. Dividing by an expression is hard.
    ///
    fn div(self, other: Self) -> Self {
        let mut result = self.clone();

        // Process `minuend`
        result.minuend = result
            .minuend
            .into_iter()
            .map(|mut result_term| {
                result_term
                    .denominator
                    .push(Factor::Parenthetical(other.clone()));
                result_term
            })
            .collect();

        // Process `subtrahend`
        result.subtrahend = result
            .subtrahend
            .into_iter()
            .map(|mut result_term| {
                result_term
                    .denominator
                    .push(Factor::Parenthetical(other.clone()));
                result_term
            })
            .collect();

        result
    }
}

impl DivAssign for Expression {
    /// Operator overload for /=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}
