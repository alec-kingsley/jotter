use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;

use crate::math_structs::expression::*;
use crate::math_structs::factor::*;
use crate::math_structs::identifier::*;
use crate::math_structs::number::*;
use crate::math_structs::term::*;
use crate::math_structs::unit::*;

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
    /// Construct a `Relation` from an `Expression`.
    ///
    pub fn from_expression(expression: Expression) -> Self {
        Self {
            operands: vec![expression],
            operators: Vec::new(),
        }
    }

    /// Construct a `Relation` from a `Term`.
    ///
    pub fn from_term(term: Term) -> Self {
        Self {
            operands: vec![Expression::from_term(term)],
            operators: Vec::new(),
        }
    }

    /// Construct a `Relation` from a `Factor`.
    ///
    pub fn from_factor(factor: Factor) -> Self {
        Self {
            operands: vec![Expression::from_factor(factor)],
            operators: Vec::new(),
        }
    }

    /// Construct a `Relation` from a `Number`.
    ///
    pub fn from_number(number: Number) -> Self {
        Self {
            operands: vec![Expression::from_number(number)],
            operators: Vec::new(),
        }
    }

    /// Construct a `Relation` from an `Identifier`.
    ///
    pub fn from_identifier(identifier: Identifier) -> Self {
        Self {
            operands: vec![Expression::from_identifier(identifier)],
            operators: Vec::new(),
        }
    }

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
        if self == &Relation::from_term(Term::new()) {
            Some(true)
        } else if self == &Relation::from_expression(Expression::new()) {
            Some(false)
        } else {
            None
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
    let zero = Expression::from_number(Number {
        real: 0f64,
        imaginary: 0f64,
        unit: Unit {
            exponent: 0,
            constituents: HashMap::new(),
        },
    });
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
