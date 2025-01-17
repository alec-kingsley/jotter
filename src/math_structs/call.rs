use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::hash::Hash;

use crate::math_structs::expression::*;
use crate::math_structs::identifier::*;
use crate::math_structs::model::*;
use crate::math_structs::number::*;
use crate::math_structs::statement::*;

#[derive(Hash, Debug, Clone)]
pub struct Call {
    /// Name of the function.
    pub name: Identifier,
    /// Ordered arguments for the function call.
    pub arguments: Vec<Expression>,
}

impl Call {
    /// Make the call in `call`.
    ///
    /// NOTE - does not check for matching variable names. So the code:
    /// f(x) = x
    /// f(x) ?
    /// would print
    /// f(x) : x
    /// as opposed to an error
    ///
    /// # Arguments
    /// * `knowns` - Known variables
    /// * `model` - Program model
    ///
    pub fn execute(
        &self,
        knowns: &HashMap<Identifier, Number>,
        model: &Model,
    ) -> Result<Expression, String> {
        if let Some(Statement::FunctionDefinition(_, arguments, definition)) = model
            .functions
            .iter()
            .find(|stmt| matches!(stmt, Statement::FunctionDefinition(n, _, _) if n == &self.name))
            .cloned()
        {
            if model.call_depth > 100 {
                Err(String::from("Maximum call depth of 100 reached"))
            } else if arguments.len() != self.arguments.len() {
                Err(format!(
                    "Function `{}` takes `{}` arguments, while `{}` were supplied.",
                    self.name,
                    arguments.len(),
                    self.arguments.len()
                ))
            } else {
                let mut test_model = model.clone();
                test_model.relations.clear();
                test_model.augmented_matrix.clear();
                test_model.call_depth += 1;
                for i in 0..arguments.len() {
                    // assign each variable name to its argument
                    let simplified_expression =
                        self.arguments[i].simplify(knowns, &test_model, false)?;

                    test_model
                        .add_matrix_row(
                            simplified_expression,
                            Expression::from_identifier(arguments[i].clone()),
                        )
                        .unwrap();
                }
                // find a true thing to return
                let mut result: Option<Expression> = None;
                for (expression, relation) in definition {
                    if result.is_none() {
                        let evaluated_result = relation.simplify_whole(&test_model, false);
                        if evaluated_result.is_ok() {
                            let evaluated = evaluated_result.unwrap();
                            if evaluated.iter().all(|relation| {
                                if let Some(true) = relation.as_bool() {
                                    true
                                } else {
                                    false
                                }
                            }) {
                                result = Some(expression.simplify_whole_loose(&test_model)?);
                            }
                        }
                    }
                }
                if result.is_none() {
                    Err(format!("Undefined"))
                } else {
                    Ok(result.unwrap())
                }
            }
        } else {
            Err(format!("Function `{}` not found.", self.name))
        }
    }
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
