use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::ops::*;

use crate::math_structs::factor::*;
use crate::math_structs::identifier::*;
use crate::math_structs::number::*;
use crate::math_structs::unit::*;

#[derive(Debug, Clone, Hash)]
pub struct Term {
    /// operands being multiplied.
    /// if empty, value is 1.
    ///
    pub numerator: Vec<Factor>,

    /// operands being divided.
    /// if empty, value is 1.
    ///
    pub denominator: Vec<Factor>,
}

impl PartialEq for Term {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        let mut removable = other.clone();
        let mut all_removed = true;
        for operand in &self.numerator {
            let mut removed = false;
            for i in (0..removable.numerator.len()).rev() {
                if operand == &removable.numerator[i] {
                    removable.numerator.remove(i);
                    removed = true;
                    break;
                }
            }
            all_removed &= removed;
        }
        for operand in &self.denominator {
            let mut removed = false;
            for i in (0..removable.denominator.len()).rev() {
                if operand == &removable.denominator[i] {
                    removable.denominator.remove(i);
                    removed = true;
                    break;
                }
            }
            all_removed &= removed;
        }
        all_removed && removable.numerator.is_empty() && removable.denominator.is_empty()
    }
}

impl Eq for Term {}

impl Display for Term {
    /// Format `Term` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Format numerator elements, joined by `*` for numbers else ``
        let numerator_str = self
            .numerator
            .iter()
            .map(|x| match x {
                Factor::Number(_) => String::from("*") + x.to_string().as_str(),
                _ => x.to_string(),
            })
            .collect::<Vec<_>>()
            .join("");

        let numerator_str = if numerator_str.starts_with('*') {
            numerator_str.trim_start_matches('*').to_string()
        } else {
            numerator_str
        };

        // Format denominator elements, joined by `*` (to be wrapped in parenthetical)
        let denominator_str = self
            .denominator
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join("/");

        // Combine the two parts
        if denominator_str.is_empty() {
            if numerator_str.is_empty() {
                write!(f, "1")
            } else {
                write!(f, "{}", numerator_str)
            }
        } else if numerator_str.is_empty() {
            write!(f, "1/{}", denominator_str)
        } else {
            write!(f, "{}/{}", numerator_str, denominator_str)
        }
    }
}

impl Term {
    /// "flatten" the `Term`.
    ///
    /// remove a many parentheticals as possible, such that it's just a sum of terms.
    /// combine like terms.
    ///
    pub fn flatten(&mut self) {
        // initialize numerator and denominator to 1
        let mut new_term = Term {
            numerator: Vec::new(),
            denominator: Vec::new(),
        };

        let mut numerator_has_parenthetical = false;
        for self_factor in self.numerator.clone() {
            if let Factor::Parenthetical(mut self_expression) = self_factor.clone() {
                self_expression.flatten();
                // if it's just one term
                if self_expression.minuend.len() + self_expression.subtrahend.len() == 1 {
                    if self_expression.subtrahend.is_empty() {
                        new_term *= self_expression.minuend[0].clone();
                    } else {
                        new_term *= -self_expression.subtrahend[0].clone();
                    }
                } else {
                    new_term
                        .numerator
                        .push(Factor::Parenthetical(self_expression));
                    numerator_has_parenthetical = true;
                }
            } else {
                new_term.numerator.push(self_factor);
            }
        }
        if numerator_has_parenthetical {
            new_term.numerator = vec![new_term.numerator.drain(..).product()]
        }

        let mut denominator_has_parenthetical = false;
        for self_factor in self.denominator.clone() {
            if let Factor::Parenthetical(mut self_expression) = self_factor.clone() {
                self_expression.flatten();
                // if it's just one term
                if self_expression.minuend.len() + self_expression.subtrahend.len() == 1 {
                    if self_expression.subtrahend.is_empty() {
                        new_term /= self_expression.minuend[0].clone();
                    } else {
                        new_term /= -self_expression.subtrahend[0].clone();
                    }
                } else {
                    new_term
                        .denominator
                        .push(Factor::Parenthetical(self_expression));
                    denominator_has_parenthetical = true;
                }
            } else {
                new_term.denominator.push(self_factor);
            }
        }
        if denominator_has_parenthetical {
            new_term.denominator = vec![new_term.denominator.drain(..).product()]
        }

        self.clone_from(&new_term);
    }

    /// Extract the numeric factor of the `Term`.
    ///
    /// This can be called before comparing terms when combining like terms.
    ///
    pub fn extract_number(&mut self) -> Number {
        // initialize base variables
        let mut value = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };

        let mut new_term = Term {
            numerator: Vec::new(),
            denominator: Vec::new(),
        };

        // copy over operands
        for operand in self.numerator.clone() {
            if let Factor::Number(number) = operand {
                value *= number;
            } else {
                new_term.numerator.push(operand);
            }
        }

        for operand in self.denominator.clone() {
            if let Factor::Number(number) = operand {
                value /= number;
            } else {
                new_term.denominator.push(operand);
            }
        }

        self.clone_from(&new_term);
        value
    }

    /// Get an identifier out of the numerator.
    /// If none exists, return None.
    /// Whatever it returns is removed.
    ///
    pub fn extract_identifier(&mut self) -> Option<Identifier> {
        let mut result: Option<Identifier> = None;

        let mut new_term = Term {
            numerator: Vec::new(),
            denominator: self.denominator.clone(),
        };

        for factor in self.numerator.clone() {
            let mut kill = false;
            if result == None {
                if let Factor::Identifier(identifier) = factor.clone() {
                    result = Some(identifier);
                    kill = true;
                }
            }
            if !kill {
                new_term.numerator.push(factor);
            }
        }
        self.clone_from(&new_term);
        result
    }
}

impl Neg for Term {
    type Output = Self;

    fn neg(self) -> Self {
        let mut result = self.clone();
        result.numerator.push(Factor::Number(Number {
            real: -1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0,
                constituents: HashMap::new(),
            },
        }));
        result
    }
}

impl Mul for Term {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        for operand in &other.numerator {
            result.numerator.push(operand.clone());
        }
        for operand in &other.denominator {
            result.denominator.push(operand.clone());
        }
        result
    }
}

impl MulAssign for Term {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Div for Term {
    type Output = Self;

    /// Operator overload for /.
    ///
    fn div(self, other: Self) -> Self {
        let mut result = self.clone();
        for operand in &other.numerator {
            result.denominator.push(operand.clone());
        }
        for operand in &other.denominator {
            result.numerator.push(operand.clone());
        }
        result
    }
}

impl DivAssign for Term {
    /// Operator overload for /=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}
