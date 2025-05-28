use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Display;
use std::ops::*;

use crate::math_structs::factor::*;
use crate::math_structs::identifier::*;
use crate::math_structs::model::*;
use crate::math_structs::polynomial::*;
use crate::math_structs::term::*;
use crate::math_structs::value::*;

#[derive(Debug, Clone, Hash)]
pub struct Expression {
    /// operands to be added.
    /// if empty, value is 0.
    ///
    minuend: Vec<Term>,

    /// operands to be subtracted.
    /// if empty, value is 0.
    ///
    subtrahend: Vec<Term>,
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
        let subtrahend_str = if self.minuend.is_empty() && !self.subtrahend.is_empty() {
            format!(
                "-{}",
                self.subtrahend
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(" - ")
            )
        } else {
            self.subtrahend
                .iter()
                .map(|x| format!("- {}", x))
                .collect::<Vec<_>>()
                .join(" ")
        };

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
    /// Default constructor. Returns an `Expression` of value 0.
    ///
    pub fn new() -> Self {
        Self {
            minuend: Vec::new(),
            subtrahend: Vec::new(),
        }
    }

    /// Get the # of terms in `self`.
    ///
    pub fn len(&self) -> usize {
        self.minuend.len() + self.subtrahend.len()
    }

    /// Get an immutable reference to `self`'s minuend.
    ///
    pub fn minuend_ref(&self) -> &Vec<Term> {
        &self.minuend
    }

    /// Get an immutable reference to `self`'s subtrahend.
    ///
    pub fn subtrahend_ref(&self) -> &Vec<Term> {
        &self.subtrahend
    }

    /// "flatten" the `Expression`.
    ///
    /// remove a many parentheticals as possible, such that it's just a sum of terms.
    /// combine like terms.
    ///
    pub fn flatten(&mut self) -> Result<(), String> {
        #[cfg(debug_assertions)]
        {
            println!("[DEBUG] flattening expression: `{}`", self);
        }

        let mut father_expression = Expression {
            minuend: Vec::new(),
            subtrahend: Vec::new(),
        };

        for mut self_term in self.minuend.clone() {
            self_term.flatten()?;
            if let Some(mut child_expression) = self_term.collapse_parenthetical() {
                child_expression.flatten()?;
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
            self_term.flatten()?;
            if let Some(mut child_expression) = self_term.collapse_parenthetical() {
                child_expression.flatten()?;
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
        self.combine_like_terms()
    }

    /// Combine like terms in `Expression`.
    ///
    fn combine_like_terms(&mut self) -> Result<(), String> {
        #[cfg(debug_assertions)]
        {
            println!("[DEBUG] combining like terms in expression: `{}`", self);
        }

        if self.len() <= 1 {
            // nothing to combine
            return Ok(());
        }

        let mut numbers: Vec<Value> = Vec::new();
        let mut terms: Vec<Term> = Vec::new();

        // extract all terms with their numeric factor
        for mut self_term in self.minuend.clone() {
            let number = self_term.extract_value()?;
            numbers.push(number);
            terms.push(self_term);
        }

        for mut self_term in self.subtrahend.clone() {
            let number = self_term.extract_value()?;
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
        let one = Value::one();

        let zero = Value::zero();

        self.minuend.clear();
        self.subtrahend.clear();
        for i in 0..numbers.len() {
            let number = numbers[i].clone();
            let mut operand = terms[i].clone();
            if !number.is_exact() || (number != one && number != -one.clone()) {
                operand *= Factor::Number(if number < zero.clone() {
                    -number.clone()
                } else {
                    number.clone()
                });
            }
            if number > zero.clone() {
                self.minuend.push(operand);
            } else if number < zero.clone() {
                self.subtrahend.push(operand);
            } else if !number.is_exact_zero() {
                // it's complex
                self.minuend.push(operand);
            }
        }
        Ok(())
    }

    /// Extract `Polynomial` from `self`.
    /// Assumes that `self` is already fully simplified.
    ///
    pub fn extract_polynomial(&self) -> Option<(Polynomial, Identifier)> {
        let mut variable_name_option: Option<Identifier> = None;
        let mut polynomial = Polynomial {
            coefficients: Vec::new(),
        };
        let zero = Value::zero();
        for term in &self.minuend {
            if term.has_denominator() {
                return None;
            }
            let mut degree = 0;
            let mut coefficient = Value::one();
            for factor in term.numerator_ref() {
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
            if term.has_denominator() {
                return None;
            }
            let mut degree = 0;
            let mut coefficient = -Value::one();
            for factor in term.numerator_ref() {
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
            if polynomial.coefficients.len() <= degree {
                polynomial
                    .coefficients
                    .resize_with(degree + 1, || zero.clone());
            }
            polynomial.coefficients[degree] = coefficient;
        }
        if variable_name_option.is_some() {
            Some((polynomial, variable_name_option.unwrap()))
        } else {
            None
        }
    }

    /// Tries to extract `self` as just a `Value`.
    ///
    pub fn as_value(&self) -> Option<Value> {
        if self.subtrahend.len() == 0 {
            if self.minuend.len() == 0 {
                Some(Value::zero())
            } else if self.minuend.len() == 1 {
                self.minuend[0].as_value()
            } else {
                None
            }
        } else if self.minuend.len() == 0 {
            if self.subtrahend.len() == 1 {
                if let Some(number) = self.subtrahend[0].as_value() {
                    Some(-number)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Simplify `self` to the result which only includes KNOWN knowns.
    ///
    /// # Arguments
    /// * `model` - Program model
    ///
    pub fn simplify_whole_loose(&self, model: &Model) -> Result<Expression, String> {
        #[cfg(debug_assertions)]
        {
            println!(
                "[DEBUG] performing loose whole simplification on expression: `{}`",
                self
            );
        }

        self.simplify(
            &model
                .solved_variables
                .clone()
                .into_iter()
                .filter_map(|(key, value_set)| {
                    if value_set.len() == 1 {
                        value_set.into_iter().next().map(|value| (key, value))
                    } else {
                        None
                    }
                })
                .collect::<HashMap<_, _>>(),
            model,
            false,
        )
    }

    /// Simplify `self` to every possible result.
    ///
    /// # Arguments
    /// * `model` - Program model
    /// * `force_retrieve` - `true` iff it should force a retrieval
    ///
    pub fn simplify_whole(
        &self,
        model: &Model,
        force_retrieve: bool,
    ) -> Result<HashSet<Expression>, String> {
        #[cfg(debug_assertions)]
        {
            println!(
                "[DEBUG] performing whole simplification on expression: `{}`",
                self
            );
        }

        model
            .generate_possible_knowns()
            .iter()
            .map(|knowns| self.simplify(knowns, model, force_retrieve))
            .collect::<Result<HashSet<Expression>, String>>()
    }

    /// Simplify `self` to every possible constant result. Returns Err() if any possible result is
    /// non-constant.
    ///
    /// # Arguments
    /// * `model` - Program model
    ///
    pub fn simplify_whole_as_constants(&self, model: &Model) -> Result<HashSet<Value>, String> {
        #[cfg(debug_assertions)]
        {
            println!("[DEBUG] performing whole simplification into constants on expression: `{}`, with model: `{}`", self, model);
        }

        model
            .generate_possible_knowns()
            .iter()
            .map(|knowns| {
                self.simplify(knowns, model, false)
                    .and_then(|expr| expr.as_value().ok_or(String::from("Expected a number")))
            })
            .collect::<Result<HashSet<_>, _>>()
    }

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
    ) -> Result<Expression, String> {
        #[cfg(debug_assertions)]
        {
            println!(
                "[DEBUG] performing simplification on expression: `{}`. force_retrieve: `{}`",
                self, force_retrieve
            );
        }

        let mut new_expression = Expression::new();

        // re-add the original terms after simplifying
        for operand in &self.minuend {
            new_expression += operand.simplify(knowns, model, force_retrieve)?;
        }

        for operand in &self.subtrahend {
            new_expression -= operand.simplify(knowns, model, force_retrieve)?;
        }

        // remove parentheticals and combine like terms
        new_expression.flatten()?;

        Ok(new_expression)
    }
}

impl From<Term> for Expression {
    fn from(term: Term) -> Self {
        Self {
            minuend: vec![term],
            subtrahend: Vec::new(),
        }
    }
}

impl From<Factor> for Expression {
    fn from(factor: Factor) -> Self {
        Self {
            minuend: vec![Term::from(factor)],
            subtrahend: Vec::new(),
        }
    }
}

impl From<Value> for Expression {
    fn from(value: Value) -> Self {
        Self {
            minuend: vec![Term::from(value)],
            subtrahend: Vec::new(),
        }
    }
}

impl From<Identifier> for Expression {
    fn from(identifier: Identifier) -> Self {
        Self {
            minuend: vec![Term::from(identifier)],
            subtrahend: Vec::new(),
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

impl Add<Term> for Expression {
    type Output = Expression;
    fn add(self, rhs: Term) -> Expression {
        let mut result = self.clone();
        result.minuend.push(rhs);
        result
    }
}

impl AddAssign<Term> for Expression {
    fn add_assign(&mut self, rhs: Term) {
        self.minuend.push(rhs);
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

impl Sub<Term> for Expression {
    type Output = Expression;
    fn sub(self, rhs: Term) -> Expression {
        let mut result = self.clone();
        result.subtrahend.push(rhs);
        result
    }
}

impl SubAssign<Term> for Expression {
    fn sub_assign(&mut self, rhs: Term) {
        self.subtrahend.push(rhs);
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
                result_term /= Factor::Parenthetical(other.clone());
                result_term
            })
            .collect();

        // Process `subtrahend`
        result.subtrahend = result
            .subtrahend
            .into_iter()
            .map(|mut result_term| {
                result_term /= Factor::Parenthetical(other.clone());
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

pub struct ExpressionIterator<'a> {
    collection: &'a Expression,
    index: usize,
}

impl<'a> Iterator for ExpressionIterator<'a> {
    // Not a reference to a `Term` since the subtrahend iterator modifies it
    type Item = Term;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.collection.minuend.len() {
            let result = self.collection.minuend[self.index].clone();
            self.index += 1;
            Some(result)
        } else if self.index - self.collection.minuend.len() < self.collection.subtrahend.len() {
            let subtrahend_index = self.index - self.collection.minuend.len();
            let result = -self.collection.subtrahend[subtrahend_index].clone();
            self.index += 1;
            Some(result)
        } else {
            None
        }
    }
}

impl<'a> IntoIterator for &'a Expression {
    type Item = Term;
    type IntoIter = ExpressionIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ExpressionIterator {
            collection: self,
            index: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn test_new_1() {
        assert_eq!(0, Expression::new().len());
    }

    #[test]
    fn test_from_term_1() {
        let expected = ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure");
        let actual = Expression::from(Term::from(Value::from(3)));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_factor_1() {
        let expected = ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure");
        let actual = Expression::from(Factor::Number(Value::from(3)));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_value_1() {
        let expected = ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure");
        let actual = Expression::from(Value::from(3));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_identifier_1() {
        let expected = ast::parse_expression("a", &mut 0).expect("ast::parse_expression - failure");
        let actual = Expression::from(Identifier::new("a").unwrap());
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_len_1() {
        assert_eq!(
            1,
            ast::parse_expression("a", &mut 0)
                .expect("ast::parse_expression - failure")
                .len()
        );
    }

    #[test]
    fn test_len_2() {
        assert_eq!(
            2,
            ast::parse_expression("a + b", &mut 0)
                .expect("ast::parse_expression - failure")
                .len()
        );
    }

    #[test]
    fn test_as_value_1() {
        let expression =
            ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(Some(Value::from(3)), expression.as_value());
    }

    #[test]
    fn test_as_value_2() {
        let expression =
            ast::parse_expression("a", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(None, expression.as_value());
    }

    #[test]
    fn test_add_1() {
        let op1 = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("2 + ab", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 + op2);
    }

    #[test]
    fn test_add_2() {
        let op1 = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("2 + 1", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 + op2);
    }

    #[test]
    fn test_addassign_1() {
        let mut val = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("2 + ab", &mut 0).expect("ast::parse_expression - failure");
        val += op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_addassign_2() {
        let mut val = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("2 + 1", &mut 0).expect("ast::parse_expression - failure");
        val += op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_add_term_1() {
        let op1 = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("2 + ab", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 + op2);
    }

    #[test]
    fn test_add_term_2() {
        let op1 = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("2 + 1", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 + op2);
    }

    #[test]
    fn test_addassign_term_1() {
        let mut val = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("2 + ab", &mut 0).expect("ast::parse_expression - failure");
        val += op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_addassign_term_2() {
        let mut val = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("2 + 1", &mut 0).expect("ast::parse_expression - failure");
        val += op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_sub_1() {
        let op1 = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("ab - 2", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 - op2);
    }

    #[test]
    fn test_sub_2() {
        let op1 = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("1 - 2", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 - op2);
    }

    #[test]
    fn test_subassign_1() {
        let mut val = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("ab - 2", &mut 0).expect("ast::parse_expression - failure");
        val -= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_subassign_2() {
        let mut val = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("2", &mut 0).expect("ast::parse_expression - failure");
        let expected =
            ast::parse_expression("1 - 2", &mut 0).expect("ast::parse_expression - failure");
        val -= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_sub_term_1() {
        let op1 = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("ab - 2", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 - op2);
    }

    #[test]
    fn test_sub_term_2() {
        let op1 = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("1 - 2", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 - op2);
    }

    #[test]
    fn test_subassign_term_1() {
        let mut val = ast::parse_expression("ab", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("ab - 2", &mut 0).expect("ast::parse_expression - failure");
        val -= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_subassign_term_2() {
        let mut val = ast::parse_expression("1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected =
            ast::parse_expression("1 - 2", &mut 0).expect("ast::parse_expression - failure");
        val -= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_mul_1() {
        let op1 = ast::parse_expression("a + b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c + d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("ac + ad + bc + bd", &mut 0)
            .expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 * op2);
    }

    #[test]
    fn test_mul_2() {
        let op1 = ast::parse_expression("a - b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c - d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("ac - ad - bc + bd", &mut 0)
            .expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 * op2);
    }

    #[test]
    fn test_mulassign_1() {
        let mut val =
            ast::parse_expression("a + b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c + d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("ac + ad + bc + bd", &mut 0)
            .expect("ast::parse_expression - failure");
        val *= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_mulassign_2() {
        let mut val =
            ast::parse_expression("a - b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c - d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("ac - ad - bc + bd", &mut 0)
            .expect("ast::parse_expression - failure");
        val *= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_div_1() {
        let op1 = ast::parse_expression("a + b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c + d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("a / (c + d) + b / (c + d)", &mut 0)
            .expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_div_2() {
        let op1 = ast::parse_expression("a - b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c - d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("a / (c - d) - b / (c - d)", &mut 0)
            .expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_div_3() {
        let op1 = ast::parse_expression("x + 1", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("x/(3) + 1/(3)", &mut 0)
            .expect("ast::parse_expression - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_divassign_1() {
        let mut val =
            ast::parse_expression("a + b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c + d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("a / (c + d) + b / (c + d)", &mut 0)
            .expect("ast::parse_expression - failure");
        val /= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_divassign_2() {
        let mut val =
            ast::parse_expression("a - b", &mut 0).expect("ast::parse_expression - failure");
        let op2 = ast::parse_expression("c - d", &mut 0).expect("ast::parse_expression - failure");
        let expected = ast::parse_expression("a / (c - d) - b / (c - d)", &mut 0)
            .expect("ast::parse_expression - failure");
        val /= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_simplify_1() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_expression("3 + 2", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_expression("5", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, result);
        if let Some(value) = result.as_value() {
            if !value.is_exact() {
                panic!("Approximate yielded from rational expression addition");
            }
        }
    }

    #[test]
    fn test_simplify_2() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_expression("3a + 2a", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected =
            ast::parse_expression("5a", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_3() {
        let knowns: HashMap<Identifier, Value> =
            HashMap::from([(Identifier::new("a").unwrap(), Value::from(3))]);
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_expression("3a + 2a", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected =
            ast::parse_expression("15", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_4() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_expression("0.0", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected =
            ast::parse_expression("0.0", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_5() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_expression("(x + 1)/3", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_expression("x/3 + 1/3", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        println!("Checking: `{result}` = `{expected}`");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_6() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_expression("3(x + 1)", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected =
            ast::parse_expression("3x + 3", &mut 0).expect("ast::parse_expression - failure");
        println!("Checking: `{result}` = `{expected}`");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_whole_1() {
        let mut model = Model::new(0);
        model
            .add_matrix_row(
                ast::parse_expression("5ax", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("10", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        let force_retrieve = true;
        let result = ast::parse_expression("2a", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify_whole(&model, force_retrieve)
            .unwrap();
        let expected = HashSet::from([
            ast::parse_expression("4/x", &mut 0).expect("ast::parse_expression - failure")
        ]);
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_whole_2() {
        let mut model = Model::new(0);
        model
            .add_matrix_row(
                ast::parse_expression("5ax", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("10", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        let force_retrieve = false;
        let result = ast::parse_expression("2a", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify_whole(&model, force_retrieve)
            .unwrap();
        let expected = HashSet::from([
            ast::parse_expression("2a", &mut 0).expect("ast::parse_expression - failure")
        ]);
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_whole_loose_1() {
        let mut model = Model::new(0);
        model
            .add_matrix_row(
                ast::parse_expression("5ax", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("10", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        let result = ast::parse_expression("2a", &mut 0)
            .expect("ast::parse_expression - failure")
            .simplify_whole_loose(&model)
            .unwrap();
        let expected =
            ast::parse_expression("2a", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(expected, result);
    }
}
