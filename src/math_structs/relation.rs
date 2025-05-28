use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Display;

use crate::math_structs::expression::*;
use crate::math_structs::factor::*;
use crate::math_structs::identifier::*;
use crate::math_structs::model::*;
use crate::math_structs::term::*;
use crate::math_structs::value::*;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Relation {
    /// operands in relation.
    ///
    /// |operands| > 0
    operands: Vec<Expression>,

    /// operators which go between operands.
    ///
    /// |operators| = |operands| - 1
    operators: Vec<RelationOp>,
}

impl Relation {
    /// Get the # of operands in `self`.
    ///
    pub fn len(&self) -> usize {
        self.operands.len()
    }

    /// Gets the first operand in `self`.
    ///
    pub fn first_operand(&self) -> &Expression {
        &self.operands[0]
    }

    /// Append another operand/expression to `self`.
    ///
    pub fn extend(&mut self, operator: RelationOp, operand: Expression) {
        self.operands.push(operand);
        self.operators.push(operator);
    }

    /// If it is a representation of a boolean, extract as such.
    ///
    pub fn as_bool(&self) -> Option<bool> {
        if self == &Relation::from(Term::new()) {
            Some(true)
        } else if self == &Relation::from(Expression::new()) {
            Some(false)
        } else {
            None
        }
    }

    /// Tries to extract `self` as just a `Value`.
    ///
    pub fn as_value(&self) -> Option<Value> {
        if self.operands.len() == 1 {
            self.operands[0].as_value()
        } else {
            None
        }
    }

    /// Simplify `self` to the result which only includes KNOWN knowns.
    ///
    /// # Arguments
    /// * `model` - Program model
    ///
    pub fn simplify_whole_loose(&self, model: &Model) -> Result<Relation, String> {
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
    ) -> Result<HashSet<Relation>, String> {
        model
            .generate_possible_knowns()
            .iter()
            .map(|knowns| self.simplify(knowns, model, force_retrieve))
            .collect::<Result<HashSet<Relation>, String>>()
    }

    /// Simplify `self` to every possible constant result. Returns Err() if any possible result is
    /// non-constant.
    ///
    /// # Arguments
    /// * `model` - Program model
    ///
    pub fn simplify_whole_as_constants(&self, model: &Model) -> Result<HashSet<Value>, String> {
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
    /// If |relation.operands| > 1 then returned `Relation` may just be 1 for true and 0 for false.
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
    ) -> Result<Relation, String> {
        let mut all_true = self.len() > 1;
        let mut has_false = false;
        // attempt to evaluate to constant boolean value
        for (left, operator, right) in self.into_iter() {
            // evaluate left and right
            let left_result = left.simplify_whole_as_constants(model);
            let right_result = right.simplify_whole_as_constants(model);
            if left_result.is_ok() && right_result.is_ok() {
                let left_set = left_result.unwrap();
                let right_set = right_result.unwrap();
                if !left_set
                    .iter()
                    .all(|left| right_set.iter().all(|right| compare(left, operator, right)))
                {
                    // short circuit if any false ones found
                    has_false = true;
                    break;
                }
            } else {
                match operator {
                    RelationOp::Less | RelationOp::Greater => all_true = false,
                    RelationOp::Equal | RelationOp::LessEqual | RelationOp::GreaterEqual => {
                        if left != right {
                            let mut test_model = model.clone();
                            let logic_result =
                                test_model.add_matrix_row(left.clone(), right.clone());
                            if logic_result.is_err() || !test_model.assert_relations_hold() {
                                // stuff breaks if they were to be equal, so they are not equal
                                has_false = true;
                            } else {
                                all_true = false;
                            }
                        }
                    }
                    RelationOp::NotEqual => {
                        if left == right {
                            has_false = true;
                        } else {
                            let mut test_model = model.clone();
                            let logic_result =
                                test_model.add_matrix_row(left.clone(), right.clone());
                            if logic_result.is_ok() && test_model.assert_relations_hold() {
                                // nothing breaks if we add it, so we can't say anything
                                all_true = false;
                            }
                        }
                    }
                }
            }
        }

        Ok(if has_false {
            // return false
            Relation::from(Expression::new())
        } else if all_true {
            // return true
            Relation::from(Term::new())
        } else {
            // return relation as simplified as it can be
            let mut new_relation = Relation::from(self.first_operand().simplify(
                knowns,
                model,
                force_retrieve,
            )?);
            // re-add the original expressions after simplifying
            for (_, operator, right) in self.into_iter() {
                new_relation.extend(
                    operator.clone(),
                    right.simplify(knowns, model, force_retrieve)?,
                );
            }
            new_relation
        })
    }
}

impl From<Expression> for Relation {
    fn from(expression: Expression) -> Self {
        Self {
            operands: vec![expression],
            operators: Vec::new(),
        }
    }
}

impl From<Term> for Relation {
    fn from(term: Term) -> Self {
        Self {
            operands: vec![Expression::from(term)],
            operators: Vec::new(),
        }
    }
}

impl From<Factor> for Relation {
    fn from(factor: Factor) -> Self {
        Self {
            operands: vec![Expression::from(factor)],
            operators: Vec::new(),
        }
    }
}

impl From<Value> for Relation {
    fn from(value: Value) -> Self {
        Self {
            operands: vec![Expression::from(value)],
            operators: Vec::new(),
        }
    }
}

impl From<Identifier> for Relation {
    fn from(identifier: Identifier) -> Self {
        Self {
            operands: vec![Expression::from(identifier)],
            operators: Vec::new(),
        }
    }
}

#[derive(Hash, Debug, Clone, PartialEq, Eq)]
pub enum RelationOp {
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual,
}

pub fn compare<T: PartialOrd>(val1: T, operator: &RelationOp, val2: T) -> bool {
    match operator {
        RelationOp::Less => val1 < val2,
        RelationOp::Greater => val1 > val2,
        RelationOp::LessEqual => val1 <= val2,
        RelationOp::GreaterEqual => val1 >= val2,
        RelationOp::Equal => val1 == val2,
        RelationOp::NotEqual => val1 != val2,
    }
}

impl Display for Relation {
    /// Format `Relation` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let relational_ops_map = HashMap::from([
            (RelationOp::Less, String::from("<")),
            (RelationOp::Greater, String::from(">")),
            (RelationOp::LessEqual, String::from("≤")),
            (RelationOp::GreaterEqual, String::from("≥")),
            (RelationOp::Equal, String::from("=")),
            (RelationOp::NotEqual, String::from("≠")),
        ]);

        let mut result = String::new();
        for i in 0..self.operands.len() {
            if i > 0 {
                let operator = relational_ops_map.get(&self.operators[i - 1]).unwrap();
                result = format!("{} {} {}", result, operator, self.operands[i]);
            } else {
                result = format!("{}", self.operands[0]);
            }
        }
        write!(f, "{}", result)
    }
}

/// get a general true relation
///
pub fn get_true_relation() -> Relation {
    let zero = Expression::from(Value::zero());
    Relation {
        operands: vec![zero.clone(), zero.clone()],
        operators: vec![RelationOp::Equal],
    }
}

pub struct RelationIterator<'a> {
    collection: &'a Relation,
    index: usize,
}

impl<'a> Iterator for RelationIterator<'a> {
    type Item = (&'a Expression, &'a RelationOp, &'a Expression);
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.collection.operators.len() {
            let result = (
                &self.collection.operands[self.index],
                &self.collection.operators[self.index],
                &self.collection.operands[self.index + 1],
            );
            self.index += 1;
            Some(result)
        } else {
            None
        }
    }
}

impl<'a> IntoIterator for &'a Relation {
    type Item = (&'a Expression, &'a RelationOp, &'a Expression);
    type IntoIter = RelationIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        RelationIterator {
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
    fn test_from_1() {
        let expected =
            ast::parse_relation("3x + 2y", &mut 0).expect("ast::parse_relation - failure");
        let actual = Relation::from(
            ast::parse_expression("3x + 2y", &mut 0).expect("ast::parse_expression - failure"),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_term_1() {
        let expected = ast::parse_relation("3", &mut 0).expect("ast::parse_relation - failure");
        let actual = Relation::from(Term::from(Value::from(3)));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_factor_1() {
        let expected = ast::parse_relation("3", &mut 0).expect("ast::parse_relation - failure");
        let actual = Relation::from(Factor::Number(Value::from(3)));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_value_1() {
        let expected = ast::parse_relation("3", &mut 0).expect("ast::parse_relation - failure");
        let actual = Relation::from(Value::from(3));
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_from_identifier_1() {
        let expected = ast::parse_relation("a", &mut 0).expect("ast::parse_expression - failure");
        let actual = Relation::from(Identifier::new("a").unwrap());
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_len_1() {
        assert_eq!(
            1,
            ast::parse_relation("a", &mut 0)
                .expect("ast::parse_relation - failure")
                .len()
        );
    }

    #[test]
    fn test_len_2() {
        assert_eq!(
            2,
            ast::parse_relation("a < b", &mut 0)
                .expect("ast::parse_relation - failure")
                .len()
        );
    }

    #[test]
    fn test_first_operand_1() {
        let relation = ast::parse_relation("3x + 2 < 8 = 17 - 3 + y", &mut 0)
            .expect("ast::parse_relation - failure");
        let first_operand =
            ast::parse_expression("3x + 2", &mut 0).expect("ast::parse_expression - failure");
        assert_eq!(&first_operand, relation.first_operand());
    }

    #[test]
    fn test_extend_1() {
        let expected = ast::parse_relation("3x + 2 < 8 = 17 - 3 + y", &mut 0)
            .expect("ast::parse_relation - failure");
        let mut actual = Relation::from(
            ast::parse_expression("3x + 2", &mut 0).expect("ast::parse_expression - failure"),
        );
        actual.extend(
            RelationOp::Less,
            ast::parse_expression("8", &mut 0).expect("ast::parse_expression - failure"),
        );
        actual.extend(
            RelationOp::Equal,
            ast::parse_expression("17 - 3 + y", &mut 0).expect("ast::parse_expression - failure"),
        );
        assert_eq!(expected, actual)
    }

    #[test]
    fn test_as_bool_1() {
        assert_eq!(Some(false), Relation::from(Expression::new()).as_bool());
    }

    #[test]
    fn test_as_bool_2() {
        assert_eq!(
            Some(true),
            Relation::from(Expression::from(Term::new())).as_bool()
        );
    }

    #[test]
    fn test_as_bool_3() {
        assert_eq!(
            None,
            Relation::from(Expression::from(Value::one())).as_bool()
        );
    }

    #[test]
    fn test_as_value_1() {
        let relation = ast::parse_relation("3", &mut 0).expect("ast::parse_relation - failure");
        assert_eq!(Some(Value::from(3)), relation.as_value());
    }

    #[test]
    fn test_as_value_2() {
        let relation = ast::parse_relation("a", &mut 0).expect("ast::parse_relation - failure");
        assert_eq!(None, relation.as_value());
    }

    #[test]
    fn test_simplify_1() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_relation("3 + 2", &mut 0)
            .expect("ast::parse_relation - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_relation("5", &mut 0).expect("ast::parse_relation - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_2() {
        let knowns: HashMap<Identifier, Value> = HashMap::new();
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_relation("3a + 2a", &mut 0)
            .expect("ast::parse_relation - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_relation("5a", &mut 0).expect("ast::parse_relation - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_simplify_3() {
        let knowns: HashMap<Identifier, Value> =
            HashMap::from([(Identifier::new("a").unwrap(), Value::from(3))]);
        let model = Model::new(0);
        let force_retrieve = false;
        let result = ast::parse_relation("3a + 2a", &mut 0)
            .expect("ast::parse_relation - failure")
            .simplify(&knowns, &model, force_retrieve)
            .unwrap();
        let expected = ast::parse_relation("15", &mut 0).expect("ast::parse_relation - failure");
        assert_eq!(expected, result);
    }

    #[test]
    fn test_compare_1() {
        assert!(compare(1, &RelationOp::Equal, 1));
        assert!(compare(1, &RelationOp::NotEqual, 2));
        assert!(compare(1, &RelationOp::Less, 2));
        assert!(compare(1, &RelationOp::LessEqual, 1));
        assert!(compare(1, &RelationOp::Less, 2));
        assert!(compare(1, &RelationOp::GreaterEqual, 1));
        assert!(compare(2, &RelationOp::Greater, 1));
    }
}
