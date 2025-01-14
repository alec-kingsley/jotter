use std::fmt;
use std::fmt::Display;
use std::hash::Hash;

use crate::math_structs::expression::*;
use crate::math_structs::identifier::*;

#[derive(Hash, Debug, Clone)]
pub struct Call {
    /// Name of the function.
    pub name: Identifier,
    /// Ordered arguments for the function call.
    pub arguments: Vec<Expression>,
}

impl PartialEq for Call {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        let mut equal = false;
        if self.name == other.name && self.arguments.len() == other.arguments.len() {
            equal = true;
            for i in 0..self.arguments.len() {
                equal &= self.arguments[i] == other.arguments[i];
            }
        }
        equal
    }
}

impl Display for Call {
    /// Format `Call` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.name,
            self.arguments
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}
