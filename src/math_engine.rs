use crate::definitions::*;
use std::cmp;
use std::collections::HashMap;

/// Process the AST of a prompt.
///
/// # Arguments
/// * `prompt` - A Statement::Prompt representing the prompt to evaluate.
/// * `model` - The program model for the state of the program.
///
pub fn process_prompt(prompt: Relation, model: &ProgramModel) {
    let simplified_result = model.simplify_relation(&prompt);
    if simplified_result.is_ok() {
        println!("{prompt} : {}", simplified_result.unwrap());
    } else {
        println!("{prompt} : ERROR - {}", simplified_result.unwrap_err());
    }
}

/// Process the AST of a function.
///
/// # Arguments
/// * `function` - A Statement::FunctionDefinition representing the function to define.
/// * `model` - The program model for the state of the program.
///
pub fn process_function(
    _name: Identifier,
    _arguments: Vec<Identifier>,
    _definition: Vec<(Expression, Relation)>,
    _model: &mut ProgramModel,
) {
    // TODO - implement function

    panic!("Not implemented");
}

/// Process the AST of an equation / relation.
///
/// # Arguments
/// * `equation` - A `Relation` representing the relation to evaluate.
/// * `model` - The program model for the state of the program.
///
pub fn process_equation(_relation: Relation, _model: &mut ProgramModel) {
    // TODO - implement function

    // TODO - loop through operators

    {
        // TODO - extract each side of operator as clone

        // TODO - if equality, simply call add_matrix_row
    }

    panic!("Not implemented");
}

#[derive(Debug, Clone, PartialEq)]
struct Variable {
    pub name: Identifier,
    pub unit: Unit,
}

/// Model for program.
///
/// An individual model must be owned by each function call.
/// Includes matrix representing values of all variables.
/// Stores each function.
/// Also stores 'call depth' to keep recursion safe.
///
#[derive(Debug, Clone, PartialEq)]
pub struct ProgramModel {
    variables: Vec<Variable>,
    augmented_matrix: Vec<Vec<Expression>>,
    functions: Vec<Statement>,
    call_depth: u16,
}

impl ProgramModel {
    /// Make the call in `call`.
    ///
    /// # Arguments
    /// * `call` - The `Call` to make.
    ///
    fn make_call(&self, _call: &Call) -> Result<Expression, String> {
        // TODO - implement function

        Err(String::from("Not implemented"))
    }

    /// Evaluate the given `Factor` assuming all constant values.
    ///
    /// # Arguments
    /// * `factor` - The `Factor` to evaluate.
    ///
    fn evaluate_constant_factor(&self, factor: &Factor) -> Result<Number, String> {
        match factor {
            Factor::Parenthetical(expression) => self.evaluate_constant_expression(expression),
            Factor::Number(number) => Ok(number.clone()),
            Factor::Identifier(identifier) => Err(format!("Identifier found: {identifier}")),
            Factor::Call(call) => self.evaluate_constant_expression(&self.make_call(call)?),
        }
    }

    /// Evaluate the given `Term` assuming all constant values.
    ///
    /// # Arguments
    /// * `term` - The `Term` to evaluate.
    ///
    fn evaluate_constant_term(&self, term: &Term) -> Result<Number, String> {
        // value to return
        let mut value = Number {
            value: 1f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            }
        };

        for operand in term.numerator.clone() {
            value *= self.evaluate_constant_factor(&operand)?;
        }
        for operand in term.denominator.clone() {
            value /= self.evaluate_constant_factor(&operand)?;
        }
        Ok(value)
    }

    /// Evaluate the given `Expression` assuming all constant values.
    ///
    /// # Arguments
    /// * `expression` - The `Expression` to evaluate.
    ///
    fn evaluate_constant_expression(&self, expression: &Expression) -> Result<Number, String> {
        // value to return
        let mut value = Number {
            value: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            }
        };

        for operand in expression.minuend.clone() {
            value *= self.evaluate_constant_term(&operand)?;
        }
        for operand in expression.subtrahend.clone() {
            value /= self.evaluate_constant_term(&operand)?;
        }
        Ok(value)
    }

    /// Simplify the given `Factor`.
    ///
    /// # Arguments
    /// * `factor` - The `Factor` to simplify.
    /// * `make_substitutions` - True iff it should substitute known variables.
    ///
    fn simplify_factor(&self, factor: &Factor, make_substitutions: bool) -> Result<Factor, String> {
        Ok(match factor {
            Factor::Parenthetical(expression) => {
                Factor::Parenthetical(self.simplify_expression(expression, make_substitutions)?)
            }
            Factor::Number(number) => Factor::Number(number.clone()),
            Factor::Identifier(identifier) => {
                if make_substitutions {
                    match self.retrieve_value(identifier.clone()) {
                        Ok(value) => Factor::Parenthetical(value),
                        Err(_) => Factor::Identifier(identifier.clone()),
                    }
                } else {
                    Factor::Identifier(identifier.clone())
                }
            }
            Factor::Call(call) => Factor::Parenthetical(
                self.simplify_expression(&self.make_call(call)?, make_substitutions)?,
            ),
        })
    }

    /// Simplify the given `Term`.
    ///
    /// # Arguments
    /// * `term` - The `Term` to simplify.
    /// * `make_substitutions` - True iff it should substitute known variables.
    ///
    fn simplify_term(&self, term: &Term, make_substitutions: bool) -> Result<Term, String> {
        let mut new_term = Term {
            numerator: Vec::new(),
            denominator: Vec::new(),
        };

        // simplify original factors in term and throw them back in
        for operand in &term.numerator {
            new_term
                .numerator
                .push(self.simplify_factor(operand, make_substitutions)?)
        }
        for operand in &term.denominator {
            new_term
                .denominator
                .push(self.simplify_factor(operand, make_substitutions)?)
        }

        // TODO - call extract number then put it back in as a standalone if not one

        Ok(new_term)
    }

    /// Simplify the given `Expression`, using known variable values.
    ///
    /// # Arguments
    /// * `expression` - The `Expression` to simplify.
    /// * `make_substitutions` - True iff it should substitute known variables.
    ///
    fn simplify_expression(
        &self,
        expression: &Expression,
        make_substitutions: bool,
    ) -> Result<Expression, String> {
        let mut new_expression = Expression {
            minuend: Vec::new(),
            subtrahend: Vec::new(),
        };

        // re-add the original terms after simplifying
        for operand in &expression.minuend {
            new_expression
                .minuend
                .push(self.simplify_term(operand, make_substitutions)?)
        }

        for operand in &expression.subtrahend {
            new_expression
                .subtrahend
                .push(self.simplify_term(operand, make_substitutions)?)
        }

        // TODO - expand all parentheticals in each term (multiply out)

        // TODO - combine like terms

        Ok(new_expression)
    }

    /// Simplify the given `Relation`, using known variable values.
    /// Makes substitutions when possible. (This is since relation is not repeated in tree)
    ///
    /// # Arguments
    /// * `expression` - The `Expression` to simplify.
    /// * `make_substitutions` - True iff it should substitute known variables.
    ///
    pub fn simplify_relation(&self, _relation: &Relation) -> Result<Expression, String> {
        // TODO - implement function

        panic!("Not implemented");
    }

    /// Retrieve an expression for the value of the given identifier from `self.augmented_matrix`.
    /// Finds the expression in the most simplified form. That is, a non-zero multiplier with
    /// minimum other non-constant terms.
    ///
    /// # Arguments
    /// * `name` - The identifier to search for.
    ///
    fn retrieve_value(&self, name: Identifier) -> Result<Expression, String> {
        // find index of identifier
        let value_col = self.variables.iter().position(|v| v.name == name).unwrap();
        let row_ct = self.augmented_matrix.len();
        let col_ct = self.augmented_matrix[0].len();

        let mut best_row: Option<usize> = None;
        let mut min_expressions_plus_values = 0;

        // find the best row
        for row in 0..row_ct {
            if match self.evaluate_constant_expression(&self.augmented_matrix[row][value_col]) {
                Ok(number) => !number.is_zero(),
                Err(_) => true,
            } {
                // possible row. Evaluate for goodness
                let expressions_plus_values =
                    self.augmented_matrix[row].iter().fold(0, |acc, expr| {
                        acc + match self.evaluate_constant_expression(&expr) {
                            Ok(number) => {
                                if number.is_zero() {
                                    0
                                } else {
                                    1
                                }
                            }
                            Err(_) => 2,
                        }
                    });
                if best_row == None || expressions_plus_values < min_expressions_plus_values {
                    best_row = Some(row);
                    min_expressions_plus_values = expressions_plus_values;
                }
            }
        }

        if best_row == None {
            return Err(format!("No formula found for {name}"));
        }

        // build resulting formula
        let mut result = self.augmented_matrix[best_row.unwrap()][col_ct - 1].clone();
        for col in 0..(col_ct - 1) {
            if col != value_col {
                result -= self.augmented_matrix[best_row.unwrap()][col].clone();
            }
        }
        result /= self.augmented_matrix[best_row.unwrap()][value_col].clone();
        Ok(self.simplify_expression(&result, false).unwrap())
    }

    /// Get the row to switch out `row` for.
    /// Returns the first one at or below current one with non-zero constant.
    /// Prioritizes getting a row with all constants.
    ///
    /// # Arguments
    /// * `row` - The row to start at
    /// * `col` - The column of the pivot point
    ///
    fn get_switcher(&self, row: usize, col: usize) -> Option<usize> {
        let row_ct = self.augmented_matrix.len();

        let mut result: Option<usize> = None;
        for switcher in row..row_ct {
            if match self.evaluate_constant_expression(&self.augmented_matrix[switcher][col]) {
                Ok(number) => !number.is_zero(),
                Err(_) => false,
            } {
                // we want to prioritize getting a row with all constants
                let all_constants_in_row = self.augmented_matrix[switcher]
                    .iter()
                    .all(|expr| self.evaluate_constant_expression(expr).is_ok());

                // start at 0 not col+1 since there could be equations
                if all_constants_in_row || result.is_none() {
                    result = Some(switcher);
                }
                if all_constants_in_row {
                    // we've found prioritized type!
                    break;
                }
            }
        }
        result
    }

    /// In echelon form reduction, takes a pivot point as input, sets it to 1, then propogates it down
    /// until only 0s and equations are below it.
    ///
    /// # Arguments
    /// * `row` - The row of the pivot point
    /// * `col` - The column of the pivot point
    ///
    fn setup_pivot(&mut self, row: usize, col: usize) {
        let row_ct = self.augmented_matrix.len();
        let col_ct = self.augmented_matrix[0].len();

        // divide the row by the `col` element to get a 1
        {
            let factor = &self.augmented_matrix[row][col].clone();
            for col_update in col..col_ct {
                self.augmented_matrix[row][col_update] /= factor.clone();
            }
        }

        // subtract that row from rows above and below until they're all 0 or undetermined at that pos
        for row_update in 0..row_ct {
            // skip the current row
            if row_update != row {
                let factor = &self.augmented_matrix[row_update][col].clone();
                if match self.evaluate_constant_expression(factor) {
                    // don't subtract anything if it's already 0
                    Ok(number) => !number.is_zero(),
                    // don't subtract anything if there's an equation there
                    Err(_) => false,
                } {
                    // only update row if we have a known factor
                    // start at 0 not col since there could be equations
                    for col_update in 0..col_ct {
                        let pivot_row_element = &self.augmented_matrix[row][col_update].clone();
                        self.augmented_matrix[row_update][col_update] -=
                            factor.clone() * pivot_row_element.clone();
                    }
                }
            }
        }
    }

    /// Update `self.augmented_matrix` to reduced echelon form.
    ///
    fn reduce(&mut self) {
        assert!(
            self.augmented_matrix.len() > 0 && self.augmented_matrix[0].len() > 0,
            "Empty augmented matrix"
        );

        let row_ct = self.augmented_matrix.len();
        let col_ct = self.augmented_matrix[0].len();

        for col in 0..cmp::min(row_ct, col_ct) {
            // the goal is to get a 1 at each [row, col]
            let row = col;

            match self.get_switcher(row, col) {
                Some(switcher) => {
                    if row < switcher {
                        // swap the rows if they're different
                        self.augmented_matrix.swap(row, switcher);
                    }

                    self.setup_pivot(row, col);
                }
                None => {}
            }
        }

        // simplify all expressions
        for row in 0..row_ct {
            for col in 0..col_ct {
                self.augmented_matrix[row][col] = self
                    .simplify_expression(&self.augmented_matrix[row][col], true)
                    .unwrap();
            }
        }

        // remove expressions which are all 0s
        for row in 0..row_ct {
            let idx = row_ct - row - 1;
            if self.augmented_matrix[idx].iter().all(|expr| {
                match self.evaluate_constant_expression(&expr) {
                    Ok(number) => number.is_zero(),
                    Err(_) => false,
                }
            }) {
                self.augmented_matrix.remove(idx);
            }
        }
    }

    /// Add a row to `self.augmented_matrix` based on the provided equality.
    ///
    /// # Arguments
    /// * `left` - The left-hand side of the equality.
    /// * `right` - The right-hand side of the equality.
    ///
    fn add_matrix_row(&mut self, _left: Expression, _right: Expression) {
        // TODO - implement function

        panic!("Not implemented");
    }

    /// Add a variable with its unit to the model.
    ///
    /// # Arguments
    /// * `name` - The name of the variable
    /// * `unit` - The units of the variable
    ///
    fn add_variable(&mut self, name: Identifier, unit: Unit) {
        assert!(
            !self.variables.iter().any(|v| &v.name == &name),
            "Variable already exists"
        );
        self.variables.push(Variable { name, unit });
    }

    /// Initializes the ProgramModel.
    ///
    /// # Arguments
    /// * `call_depth` - The depth of calls. Safety for recursion.
    ///
    pub fn new(call_depth: u16) -> Self {
        ProgramModel {
            variables: Vec::new(),
            augmented_matrix: Vec::new(),
            functions: Vec::new(),
            call_depth,
        }
    }
}
