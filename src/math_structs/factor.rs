use std::fmt;
use std::fmt::Display;
use std::iter::Product;
use std::ops::*;

use crate::math_structs::call::*;
use crate::math_structs::expression::*;
use crate::math_structs::identifier::*;
use crate::math_structs::number::*;

#[derive(Hash, Debug, Clone)]
pub enum Factor {
    /// Expression within a parenthetical.
    Parenthetical(Expression),
    /// Numeric literal.
    Number(Number),
    /// Identifier (variable / constant name).
    Identifier(Identifier),
    /// Call to a function.
    Call(Call),
}

impl PartialEq for Factor {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        match self {
            Factor::Parenthetical(self_expression) => match other {
                Factor::Parenthetical(other_expression) => self_expression == other_expression,
                _ => false,
            },
            Factor::Number(self_number) => match other {
                Factor::Number(other_number) => self_number == other_number,
                _ => false,
            },
            Factor::Identifier(self_identifier) => match other {
                Factor::Identifier(other_identifier) => self_identifier == other_identifier,
                _ => false,
            },
            Factor::Call(self_call) => match other {
                Factor::Call(other_call) => self_call == other_call,
                _ => false,
            },
        }
    }
}

impl Eq for Factor {}

impl Display for Factor {
    /// Format `Factor` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Factor::Parenthetical(expression) => write!(f, "({})", expression),
            Factor::Number(number) => write!(f, "{}", number),
            Factor::Identifier(identifier) => write!(f, "{}", identifier),
            Factor::Call(call) => write!(f, "{}", call),
        }
    }
}

impl Factor {
    /// Returns true iff the factor is a number with value 1
    ///
    pub fn is_unitless_one(self) -> bool {
        if let Factor::Number(number) = self {
            number.is_unitless_one()
        } else {
            false
        }
    }
}

impl Mul for Factor {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut result: Option<Factor> = None;
        if self.clone().is_unitless_one() {
            result = Some(other.clone());
        } else if other.clone().is_unitless_one() {
            result = Some(self.clone());
        } else if let Factor::Number(self_number) = self.clone() {
            if let Factor::Number(other_number) = other.clone() {
                result = Some(Factor::Number(self_number * other_number));
            }
        }
        if result == None {
            result = Some(
                if let Factor::Parenthetical(self_expression) = self.clone() {
                    if let Factor::Parenthetical(other_expression) = other.clone() {
                        Factor::Parenthetical(self_expression * other_expression)
                    } else {
                        Factor::Parenthetical(self_expression * Expression::from_factor(other))
                    }
                } else if let Factor::Parenthetical(other_expression) = other.clone() {
                    Factor::Parenthetical(other_expression * Expression::from_factor(self))
                } else {
                    Factor::Parenthetical(
                        Expression::from_factor(self) * Expression::from_factor(other),
                    )
                },
            );
        }
        result.unwrap()
    }
}

impl MulAssign for Factor {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Product for Factor {
    /// Overload for product
    ///
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|a, b| a * b).expect("Iterator is empty")
    }
}

impl Div for Factor {
    type Output = Self;

    /// Operator overload for /.
    ///
    fn div(self, other: Self) -> Self {
        let mut result: Option<Factor> = None;
        if let Factor::Number(self_number) = self.clone() {
            if let Factor::Number(other_number) = other.clone() {
                result = Some(Factor::Number(self_number / other_number));
            }
        }
        if result == None {
            result = Some(
                if let Factor::Parenthetical(self_expression) = self.clone() {
                    if let Factor::Parenthetical(other_expression) = other.clone() {
                        Factor::Parenthetical(self_expression / other_expression)
                    } else {
                        Factor::Parenthetical(self_expression / Expression::from_factor(other))
                    }
                } else if let Factor::Parenthetical(other_expression) = other.clone() {
                    Factor::Parenthetical(Expression::from_factor(other) / other_expression)
                } else {
                    Factor::Parenthetical(
                        Expression::from_factor(self) / Expression::from_factor(other),
                    )
                },
            );
        }
        result.unwrap()
    }
}

impl DivAssign for Factor {
    /// Operator overload for *=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}
