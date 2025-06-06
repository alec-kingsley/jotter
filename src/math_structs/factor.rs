use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::iter::Product;
use std::ops::*;

use crate::math_structs::call::*;
use crate::math_structs::expression::*;
use crate::math_structs::identifier::*;
use crate::math_structs::model::*;
use crate::math_structs::value::*;

#[derive(Hash, Debug, Clone)]
pub enum Factor {
    /// Expression within a parenthetical.
    Parenthetical(Expression),
    /// Numeric literal.
    Number(Value),
    /// Identifier (variable / constant name).
    Identifier(Identifier),
    /// Call to a function.
    Call(Call),
}

impl Factor {
    /// Simplify `self`.
    ///
    /// # Arguments
    /// * `knowns` - Known variables
    /// * `model` - Program model
    /// * `force_retrieve` - `true` iff it should force a retrieval
    ///
    pub fn simplify(
        &self,
        knowns: &HashMap<Identifier, Value>,
        model: &Model,
        force_retrieve: bool,
    ) -> Result<Factor, String> {
        #[cfg(debug_assertions)]
        {
            println!(
                "[DEBUG] performing simplification on factor: `{}`. force_retrieve: `{}`",
                self, force_retrieve
            );
        }

        let result = Ok(match self {
            Factor::Parenthetical(expression) => {
                if expression.len() > 1 {
                    Factor::Parenthetical(expression.simplify(knowns, model, force_retrieve)?)
                } else if expression.len() == 1 {
                    let sub_term = expression.into_iter().next().unwrap();
                    if sub_term.len() == 1 && !sub_term.has_denominator() {
                        // if the parenthetical is just a factor, return it
                        sub_term.numerator_ref()[0].clone()
                    } else {
                        Factor::Parenthetical(Expression::from(sub_term.simplify(
                            knowns,
                            model,
                            force_retrieve,
                        )?))
                    }
                } else {
                    Factor::Number(Value::zero())
                }
            }
            Factor::Number(number) => Factor::Number(*number),
            Factor::Identifier(identifier) => {
                if knowns.contains_key(&identifier) {
                    Factor::Number(*knowns.get(&identifier).unwrap())
                } else if force_retrieve {
                    Factor::Parenthetical(model.force_build_expression(identifier.clone())?)
                } else {
                    Factor::Identifier(identifier.clone())
                }
            }
            Factor::Call(call) => Factor::Parenthetical(call.execute(knowns, model)?.simplify(
                knowns,
                model,
                force_retrieve,
            )?),
        });

        #[cfg(debug_assertions)]
        {
            if result.is_ok() {
                println!(
                    "[DEBUG] simplified factor to: `{}`",
                    result.clone().unwrap()
                );
            }
        }
        result
    }
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
        } else if let Factor::Number(self_number) = self {
            if let Factor::Number(other_number) = other {
                result = Some(Factor::Number(self_number * other_number));
            }
        }
        if result == None {
            result = Some(if let Factor::Parenthetical(self_expression) = self {
                if let Factor::Parenthetical(other_expression) = other {
                    Factor::Parenthetical(self_expression * other_expression)
                } else {
                    Factor::Parenthetical(self_expression * Expression::from(other))
                }
            } else if let Factor::Parenthetical(other_expression) = other {
                Factor::Parenthetical(other_expression * Expression::from(self))
            } else {
                Factor::Parenthetical(Expression::from(self) * Expression::from(other))
            });
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
            result = Some(if let Factor::Parenthetical(self_expression) = self {
                if let Factor::Parenthetical(other_expression) = other {
                    Factor::Parenthetical(self_expression / other_expression)
                } else {
                    Factor::Parenthetical(self_expression / Expression::from(other))
                }
            } else if let Factor::Parenthetical(other_expression) = other.clone() {
                Factor::Parenthetical(Expression::from(other) / other_expression)
            } else {
                Factor::Parenthetical(Expression::from(self) / Expression::from(other))
            });
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_display_1() {
        assert_eq!("(0)", Factor::Parenthetical(Expression::new()).to_string());
    }

    #[test]
    fn test_display_2() {
        assert_eq!("0", Factor::Number(Value::zero()).to_string());
    }

    #[test]
    fn test_display_3() {
        assert_eq!(
            "x",
            Factor::Identifier(Identifier::new("x").unwrap()).to_string()
        );
    }

    #[test]
    fn test_display_4() {
        assert_eq!(
            "f(0)",
            Factor::Call(Call {
                name: Identifier::new("f").unwrap(),
                arguments: vec![Expression::new()],
            })
            .to_string()
        );
    }

    #[test]
    fn test_mul_1() {
        let two = Factor::Parenthetical(Expression::from(Value::from(2)));
        let a = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        let resulting_expression =
            Expression::from(Value::from(2)) * Expression::from(Identifier::new("a").unwrap());
        let expected = Factor::Parenthetical(resulting_expression);
        assert_eq!(expected, two * a);
    }

    #[test]
    fn test_mul_2() {
        let two = Factor::Number(Value::from(2));
        let three = Factor::Number(Value::from(3));
        let six = Factor::Number(Value::from(6));
        assert_eq!(six, two * three);
    }

    #[test]
    fn test_mul_3() {
        let a = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        let b = Factor::Parenthetical(Expression::from(Identifier::new("b").unwrap()));
        let expected = Factor::Parenthetical(
            Expression::from(Identifier::new("a").unwrap())
                * Expression::from(Identifier::new("b").unwrap()),
        );
        assert_eq!(expected, a * b);
    }

    #[test]
    fn test_mulassign_1() {
        let mut val = Factor::Parenthetical(Expression::from(Value::from(2)));
        let a = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        val *= a;
        let resulting_expression =
            Expression::from(Value::from(2)) * Expression::from(Identifier::new("a").unwrap());
        let expected = Factor::Parenthetical(resulting_expression);
        assert_eq!(expected, val);
    }

    #[test]
    fn test_mulassign_2() {
        let mut val = Factor::Number(Value::from(2));
        let three = Factor::Number(Value::from(3));
        let six = Factor::Number(Value::from(6));
        val *= three;
        assert_eq!(six, val);
    }

    #[test]
    fn test_mulassign_3() {
        let mut val = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        let b = Factor::Parenthetical(Expression::from(Identifier::new("b").unwrap()));
        val *= b;
        let expected = Factor::Parenthetical(
            Expression::from(Identifier::new("a").unwrap())
                * Expression::from(Identifier::new("b").unwrap()),
        );
        assert_eq!(expected, val);
    }

    #[test]
    fn test_product_1() {
        if let Factor::Parenthetical(expr) = vec![
            Factor::Identifier(Identifier::new("a").unwrap()),
            Factor::Number(Value::from(2)),
        ]
        .drain(..)
        .product()
        {
            assert_eq!(1, expr.len());
            assert_eq!(2, expr.into_iter().next().unwrap().len());
        } else {
            panic!("Expected parenthetical as product of factors `a` and `2`");
        }
    }

    #[test]
    fn test_div_1() {
        let two = Factor::Parenthetical(Expression::from(Value::from(2)));
        let a = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        let resulting_expression =
            Expression::from(Value::from(2)) / Expression::from(Identifier::new("a").unwrap());
        let expected = Factor::Parenthetical(resulting_expression);
        assert_eq!(expected, two / a);
    }

    #[test]
    fn test_div_2() {
        let two = Factor::Number(Value::from(2));
        let three = Factor::Number(Value::from(3));
        let six = Factor::Number(Value::from(6));
        assert_eq!(two, six / three);
    }

    #[test]
    fn test_div_3() {
        let a = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        let b = Factor::Parenthetical(Expression::from(Identifier::new("b").unwrap()));
        let expected = Factor::Parenthetical(
            Expression::from(Identifier::new("a").unwrap())
                / Expression::from(Identifier::new("b").unwrap()),
        );
        assert_eq!(expected, a / b);
    }

    #[test]
    fn test_divassign_1() {
        let mut val = Factor::Parenthetical(Expression::from(Value::from(2)));
        let a = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        val /= a;
        let resulting_expression =
            Expression::from(Value::from(2)) / Expression::from(Identifier::new("a").unwrap());
        let expected = Factor::Parenthetical(resulting_expression);
        assert_eq!(expected, val);
    }

    #[test]
    fn test_divassign_2() {
        let mut val = Factor::Number(Value::from(6));
        let three = Factor::Number(Value::from(3));
        let two = Factor::Number(Value::from(2));
        val /= three;
        assert_eq!(two, val);
    }

    #[test]
    fn test_divassign_3() {
        let mut val = Factor::Parenthetical(Expression::from(Identifier::new("a").unwrap()));
        let b = Factor::Parenthetical(Expression::from(Identifier::new("b").unwrap()));
        val /= b;
        let expected = Factor::Parenthetical(
            Expression::from(Identifier::new("a").unwrap())
                / Expression::from(Identifier::new("b").unwrap()),
        );
        assert_eq!(expected, val);
    }
}
