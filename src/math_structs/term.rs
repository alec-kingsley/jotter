use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::ops::*;

use crate::math_structs::expression::*;
use crate::math_structs::factor::*;
use crate::math_structs::identifier::*;
use crate::math_structs::model::*;
use crate::math_structs::value::*;

#[derive(Debug, Clone, Hash)]
pub struct Term {
    /// operands being multiplied.
    /// if empty, value is 1.
    ///
    numerator: Vec<Factor>,

    /// operands being divided.
    /// if empty, value is 1.
    ///
    denominator: Vec<Factor>,
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
    /// Default constructor. Returns a `Term` of value 1 (unitless).
    ///
    pub fn new() -> Self {
        Self {
            numerator: Vec::new(),
            denominator: Vec::new(),
        }
    }

    /// Get the # of terms in `self`.
    ///
    pub fn len(&self) -> usize {
        self.numerator.len() + self.denominator.len()
    }

    /// Return `true` iff `self` has a denominator.
    ///
    pub fn has_denominator(&self) -> bool {
        self.denominator.len() > 0
    }

    /// Get an immutable reference to `self`'s numerator.
    ///
    pub fn numerator_ref(&self) -> &Vec<Factor> {
        &self.numerator
    }

    /// Get an immutable reference to `self`'s denominator.
    ///
    pub fn denominator_ref(&self) -> &Vec<Factor> {
        &self.denominator
    }

    /// If `self`'s numerator is just a Parenthetical, return the inner `Expression` divided by the denominator. Otherwise `None`.
    ///
    pub fn collapse_parenthetical(&self) -> Option<Expression> {
        if self.numerator.len() == 1 {
            if let Factor::Parenthetical(expression) = self.numerator[0].clone() {
                if self.denominator.is_empty() {
                    Some(expression)
                } else {
                    let mut new_expression = expression;
                    for factor in self.denominator.clone() {
                        new_expression /= Expression::from(factor);
                    }
                    Some(new_expression)
                }
            } else {
                None
            }
        } else {
            None
        }
    }

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
                if self_expression.len() == 1 {
                    new_term *= self_expression.into_iter().next().unwrap();
                } else {
                    new_term
                        .numerator
                        .push(Factor::Parenthetical(self_expression));
                    numerator_has_parenthetical = true;
                }
            } else {
                new_term *= self_factor;
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
                if self_expression.len() == 1 {
                    new_term /= self_expression.into_iter().next().unwrap();
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
    pub fn extract_value(&mut self) -> Value {
        // initialize base variables
        let mut value = Value::one();

        let mut new_term = Term {
            numerator: Vec::new(),
            denominator: Vec::new(),
        };

        // copy over operands
        for operand in self.numerator.clone() {
            if let Factor::Number(number) = operand {
                value *= number;
            } else {
                new_term *= operand;
            }
        }

        for operand in self.denominator.clone() {
            if let Factor::Number(number) = operand {
                value /= number;
            } else {
                new_term /= operand;
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
                new_term *= factor;
            }
        }
        self.clone_from(&new_term);
        result
    }

    /// Tries to extract `self` as just a `Value`.
    ///
    pub fn as_value(&self) -> Option<Value> {
        if self.denominator.len() == 0 {
            if self.numerator.len() == 0 {
                Some(Value::one())
            } else if self.numerator.len() == 1 {
                if let Factor::Number(number) = self.numerator[0].clone() {
                    Some(number)
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

    /// Simplify `self` by cancelling terms which can't be 0 and replacing knowns.
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
    ) -> Result<Term, String> {
        let mut identifier_counts: HashMap<Identifier, (bool, isize)> = HashMap::new();

        // simplify original factors in term and throw them back in
        let mut new_term = Term::new();
        for operand in &self.numerator {
            let mut add_to_numerator = true;
            if let Factor::Identifier(name) = operand {
                if identifier_counts.contains_key(&name) {
                    let (could_be_0, _) = identifier_counts.get(&name).unwrap();
                    if !could_be_0 {
                        add_to_numerator = false;
                        identifier_counts
                            .entry(name.clone())
                            .and_modify(|(_, ct)| *ct += 1);
                    }
                } else if model.could_be_0(&name) || model.solved_variables.contains_key(&name) {
                    identifier_counts.insert(name.clone(), (true, 0));
                } else {
                    add_to_numerator = false;
                    identifier_counts.insert(name.clone(), (false, 1));
                }
            }
            if add_to_numerator {
                new_term *= operand.simplify(knowns, model, force_retrieve)?;
            }
        }
        for operand in &self.denominator {
            let mut add_to_denominator = true;
            if let Factor::Identifier(name) = operand {
                if identifier_counts.contains_key(&name) {
                    let (could_be_0, _) = identifier_counts.get(&name).unwrap();
                    if !could_be_0 {
                        add_to_denominator = false;
                        identifier_counts
                            .entry(name.clone())
                            .and_modify(|(_, ct)| *ct -= 1);
                    }
                }
            }
            if add_to_denominator {
                new_term /= operand.simplify(knowns, model, force_retrieve)?;
            }
        }
        // re-add reserved and cancelled terms
        for (name, (_, mut count)) in identifier_counts {
            while count > 0 {
                new_term *= Factor::Identifier(name.clone());
                count -= 1;
            }
            while count < 0 {
                new_term /= Factor::Identifier(name.clone());
                count += 1;
            }
        }

        Ok(new_term)
    }
}

impl From<Factor> for Term {
    fn from(factor: Factor) -> Self {
        Self {
            numerator: vec![factor],
            denominator: Vec::new(),
        }
    }
}

impl From<Value> for Term {
    fn from(value: Value) -> Self {
        Self {
            numerator: vec![Factor::Number(value)],
            denominator: Vec::new(),
        }
    }
}

impl From<Identifier> for Term {
    fn from(identifier: Identifier) -> Self {
        Self {
            numerator: vec![Factor::Identifier(identifier)],
            denominator: Vec::new(),
        }
    }
}

impl Neg for Term {
    type Output = Self;

    fn neg(self) -> Self {
        let mut result = self.clone();
        result.numerator.push(Factor::Number(-Value::one()));
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
            if let Factor::Number(_) = operand {
                result.numerator.insert(0, operand.clone());
            } else {
                result.numerator.push(operand.clone());
            }
        }
        for operand in &other.denominator {
            if let Factor::Number(_) = operand {
                result.denominator.insert(0, operand.clone());
            } else {
                result.denominator.push(operand.clone());
            }
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

impl Mul<Factor> for Term {
    type Output = Term;
    fn mul(self, rhs: Factor) -> Term {
        let mut result = self.clone();
        if let Factor::Number(_) = rhs {
            result.numerator.insert(0, rhs.clone());
        } else {
            result.numerator.push(rhs.clone());
        }
        result
    }
}

impl MulAssign<Factor> for Term {
    fn mul_assign(&mut self, rhs: Factor) {
        if let Factor::Number(_) = rhs {
            self.numerator.insert(0, rhs);
        } else {
            self.numerator.push(rhs);
        }
    }
}

impl Div for Term {
    type Output = Self;

    /// Operator overload for /.
    ///
    fn div(self, other: Self) -> Self {
        let mut result = self.clone();
        for operand in &other.numerator {
            if let Factor::Number(_) = operand {
                result.denominator.insert(0, operand.clone());
            } else {
                result.denominator.push(operand.clone());
            }
        }
        for operand in &other.denominator {
            if let Factor::Number(_) = operand {
                result.numerator.insert(0, operand.clone());
            } else {
                result.numerator.push(operand.clone());
            }
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

impl Div<Factor> for Term {
    type Output = Term;
    fn div(self, rhs: Factor) -> Term {
        let mut result = self.clone();
        if let Factor::Number(_) = rhs {
            result.denominator.insert(0, rhs);
        } else {
            result.denominator.push(rhs);
        }
        result
    }
}

impl DivAssign<Factor> for Term {
    fn div_assign(&mut self, rhs: Factor) {
        if let Factor::Number(_) = rhs {
            self.denominator.insert(0, rhs.clone());
        } else {
            self.denominator.push(rhs.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_structs::*;
    use crate::*;

    #[test]
    fn test_new_1() {
        assert_eq!(0, Term::new().len());
    }

    #[test]
    fn test_from_factor_1() {
        let expected = ast::parse_term("3", &mut 0).expect("ast::parse_term - failure");
        let actual = Term::from(Factor::Number(Value::from(3)));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_value_1() {
        let expected = ast::parse_term("3", &mut 0).expect("ast::parse_term - failure");
        let actual = Term::from(Value::from(3));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_identifier_1() {
        let expected = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        let actual = Term::from(Identifier::new("a").unwrap());
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_len_1() {
        assert_eq!(
            1,
            ast::parse_term("a", &mut 0)
                .expect("ast::parse_term - failure")
                .len()
        );
    }

    #[test]
    fn test_len_2() {
        assert_eq!(
            2,
            ast::parse_term("ab", &mut 0)
                .expect("ast::parse_term - failure")
                .len()
        );
    }

    #[test]
    fn test_len_3() {
        assert_eq!(
            3,
            ast::parse_term("3ab", &mut 0)
                .expect("ast::parse_term - failure")
                .len()
        );
    }

    #[test]
    fn test_has_denominator_1() {
        assert!(ast::parse_term("3ab/7", &mut 0)
            .expect("ast::parse_term - failure")
            .has_denominator());
    }

    #[test]
    fn test_has_denominator_2() {
        assert!(!ast::parse_term("3ab", &mut 0)
            .expect("ast::parse_term - failure")
            .has_denominator());
    }

    #[test]
    fn test_collapse_parenthetical_1() {
        assert_eq!(
            Some(ast::parse_expression("3a+b", &mut 0).expect("ast::parse_expression - failure")),
            ast::parse_term("(3a+b)", &mut 0)
                .expect("ast::parse_term - failure")
                .collapse_parenthetical()
        )
    }

    #[test]
    fn test_collapse_parenthetical_2() {
        assert_eq!(
            None,
            ast::parse_term("3a", &mut 0)
                .expect("ast::parse_term - failure")
                .collapse_parenthetical()
        )
    }

    #[test]
    fn test_extract_value_1() {
        let mut term = ast::parse_term("3ab", &mut 0).expect("ast::parse_term - failure");
        let number = term.extract_value();
        assert_eq!(Value::from(3), number);
        assert_eq!(
            ast::parse_term("ab", &mut 0).expect("ast::parse_term - failure"),
            term
        );
    }

    #[test]
    fn test_extract_identifier_1() {
        let mut term = ast::parse_term("3a", &mut 0).expect("ast::parse_term - failure");
        let identifier = term.extract_identifier();
        assert_eq!(Some(Identifier::new("a").unwrap()), identifier);
        assert_eq!(
            ast::parse_term("3", &mut 0).expect("ast::parse_term - failure"),
            term
        );
    }

    #[test]
    fn test_as_value_1() {
        let term = ast::parse_term("3", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(Some(Value::from(3)), term.as_value());
    }

    #[test]
    fn test_as_value_2() {
        let term = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(None, term.as_value());
    }

    #[test]
    fn test_mul_1() {
        let op1 = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("2a", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 * op2);
    }

    #[test]
    fn test_mul_2() {
        let op1 = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("c/d", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("ac/b/d", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 * op2);
    }

    #[test]
    fn test_mulassign_1() {
        let mut val = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("2a", &mut 0).expect("ast::parse_term - failure");
        val *= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_mulassign_2() {
        let mut val = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("c/d", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("ac/b/d", &mut 0).expect("ast::parse_term - failure");
        val *= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_mul_factor_1() {
        let op1 = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("2", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("2a", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 * op2);
    }

    #[test]
    fn test_mul_factor_2() {
        let op1 = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("c", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("ac/b", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 * op2);
    }

    #[test]
    fn test_mulassign_factor_1() {
        let mut val = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("2", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("2a", &mut 0).expect("ast::parse_term - failure");
        val *= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_mulassign_factor_2() {
        let mut val = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("c", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("ac/b", &mut 0).expect("ast::parse_term - failure");
        val *= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_div_1() {
        let op1 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("2/a", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_div_2() {
        let op1 = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("d/c", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("ac/b/d", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_divassign_1() {
        let mut val = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("a", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("2/a", &mut 0).expect("ast::parse_term - failure");
        val /= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_divassign_2() {
        let mut val = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_term("d/c", &mut 0).expect("ast::parse_term - failure");
        let expected = ast::parse_term("ac/b/d", &mut 0).expect("ast::parse_term - failure");
        val /= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_div_factor_1() {
        let op1 = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("a", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("2/a", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_div_factor_2() {
        let op1 = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("c", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("a/c/b", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_div_factor_3() {
        let op1 = ast::parse_term("(x+1)", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("3", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("(x+1)/3", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_div_factor_4() {
        let op1 = ast::parse_term("(x+1)", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("(3)", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("(x+1)/(3)", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, op1 / op2);
    }

    #[test]
    fn test_divassign_factor_1() {
        let mut val = ast::parse_term("2", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("a", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("2/a", &mut 0).expect("ast::parse_term - failure");
        val /= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_divassign_factor_2() {
        let mut val = ast::parse_term("a/b", &mut 0).expect("ast::parse_term - failure");
        let op2 = ast::parse_factor("c", &mut 0, false).expect("ast::parse_factor - failure");
        let expected = ast::parse_term("a/c/b", &mut 0).expect("ast::parse_term - failure");
        val /= op2;
        assert_eq!(expected, val);
    }

    #[test]
    fn test_simplify_1() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let mut model = Model::new(0);
        model.add_relation(
            Expression::from(Identifier::new("a").unwrap()),
            RelationOp::NotEqual,
            Expression::from(Value::zero()),
        );
        let force_retrieve = false;
        let result = ast::parse_term("3a/a", &mut 0)
            .expect("ast::parse_term - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_term("3", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_2() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_term("3a/a", &mut 0)
            .expect("ast::parse_term - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_term("3a/a", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_3() {
        let knowns: HashMap<Identifier, Value> =
            HashMap::from([(Identifier::new("a").unwrap(), Value::from(2))]);
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_term("3a", &mut 0)
            .expect("ast::parse_term - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_term("3*2", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_4() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_term("0.0", &mut 0)
            .expect("ast::parse_term - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_term("0.0", &mut 0).expect("ast::parse_term - failure");
        assert_eq!(expected, result);
    }
}
