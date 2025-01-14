use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;

use crate::math_structs::expression::*;
use crate::math_structs::factor::*;
use crate::math_structs::number::*;
use crate::math_structs::term::*;
use crate::math_structs::unit::*;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Relation {
    /// operands in relation.
    ///
    /// |operands| > 0
    pub operands: Vec<Expression>,

    /// operators which go between operands.
    ///
    /// |operators| = |operands| - 1
    pub operators: Vec<RelationOp>,
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

pub fn compare<T: PartialOrd>(val1: T, val2: T, operator: &RelationOp) -> bool {
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
    let zero = Expression {
        minuend: Vec::from([Term {
            numerator: Vec::from([Factor::Number(Number {
                real: 0f64,
                imaginary: 0f64,
                unit: Unit {
                    exponent: 0,
                    constituents: HashMap::new(),
                },
            })]),
            denominator: Vec::new(),
        }]),
        subtrahend: Vec::new(),
    };
    Relation {
        operands: vec![zero.clone(), zero.clone()],
        operators: vec![RelationOp::Equal],
    }
}
