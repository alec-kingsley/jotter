use std::fmt;
use std::fmt::Display;

use crate::math_structs::expression::*;
use crate::math_structs::identifier::*;
use crate::math_structs::relation::*;

#[derive(Debug, Hash, Clone)]
pub enum Statement {
    /// prompt
    Prompt(Relation),
    /// equation
    Equation(Relation),
    /// name, arguments, actual function, and their relations.
    FunctionDefinition(Identifier, Vec<Identifier>, Vec<(Expression, Relation)>),
    /// false for <, true for >
    StateSwitch(bool),
}

impl PartialEq for Statement {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Statement::Prompt(self_relation) => {
                if let Statement::Prompt(other_relation) = other {
                    self_relation == other_relation
                } else {
                    false
                }
            }
            Statement::Equation(self_relation) => {
                if let Statement::Equation(other_relation) = other {
                    self_relation == other_relation
                } else {
                    false
                }
            }
            Statement::FunctionDefinition(self_identifier, _, _) => {
                if let Statement::FunctionDefinition(other_identifier, _, _) = other {
                    self_identifier == other_identifier
                } else {
                    false
                }
            }
            Statement::StateSwitch(self_state) => {
                if let Statement::StateSwitch(other_state) = other {
                    self_state == other_state
                } else {
                    false
                }
            }
        }
    }
}

impl Eq for Statement {}

impl Display for Statement {
    /// Format `Statement` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Statement::Prompt(relation) => write!(f, "{} ?", relation),
            Statement::Equation(relation) => write!(f, "{}", relation),
            Statement::FunctionDefinition(name, arguments, details) => write!(
                f,
                "{}\n}}",
                details.iter().fold(
                    format!(
                        "{}({}) = {{",
                        name,
                        arguments
                            .iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    |acc, (expression, relation)| format!(
                        "{}\n\t{},\t{}",
                        acc, expression, relation
                    )
                )
            ),
            Statement::StateSwitch(state) => if *state { write!(f,">") } else { write!(f, "<") },
        }
    }
}
