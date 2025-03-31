use crate::math_structs::*;
use std::cmp;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Display;
use std::process;

/// Model for program.
///
/// Includes matrix representing values of all variables.
/// Stores each function.
/// Also stores 'call depth' to keep recursion "safe".
///
#[derive(Debug, Clone)]
pub struct Model {
    /// variables that've been solved for, mapped to a finite solution list
    pub solved_variables: HashMap<Identifier, HashSet<Value>>,
    /// all variables, in the order they appear in the augmented matrix
    pub variables: Vec<Identifier>,
    /// description of all known equations in a mathematical augmented matrix
    pub augmented_matrix: Vec<Vec<Expression>>,
    /// all relations which are not equations
    pub relations: Vec<Relation>,
    /// function definitions
    pub functions: HashSet<Statement>,
    /// for functions ; depth of call (to protect against astray recursion)
    pub call_depth: u16,
}

impl Display for Model {
    /// Format `Model` appropriately.
    /// This is mainly for debug purposes.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        result.push_str("\nSolved Variables:\n");
        result.push_str(
            self.solved_variables
                .iter()
                .map(|(name, values)| {
                    if values.len() == 1 {
                        format!("{name} = {}", values.iter().next().unwrap().to_string())
                    } else {
                        format!(
                            "{name} ∈ {{{}}}",
                            values
                                .iter()
                                .map(|n| n.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
                .as_str(),
        );
        result.push_str("\nAugmented Matrix:\n");

        // print out the header
        let mut header = self
            .variables
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        header.push_str(
            format!(
                ", _\n{}\n",
                "-".repeat(header.chars().count() + ", _".len())
            )
            .as_str(),
        );

        result.push_str(header.as_str());

        // print out the matrix elements
        for row in 0..self.augmented_matrix.len() {
            for col in 0..self.augmented_matrix[0].len() {
                if col == 0 {
                    result.push_str(format!("{}", self.augmented_matrix[row][col]).as_str());
                } else {
                    result.push_str(format!(", {}", self.augmented_matrix[row][col]).as_str());
                }
            }
            result.push_str("\n");
        }

        // print out the known relations
        if self.relations.len() > 0 {
            result.push_str("Relations:\n");
            for relation in &self.relations {
                result.push_str(format!("{}\n", relation).as_str());
            }
        }

        // print out the defined functions
        if self.functions.len() > 0 {
            result.push_str("Functions:\n");
            for function in &self.functions {
                result.push_str(format!("{}\n", function).as_str());
            }
        }

        result.push_str(format!("Call Depth: {}\n", self.call_depth).as_str());

        write!(f, "{}", result)
    }
}

impl Model {
    /// Returns true iff the variable with `name` could possibly be 0.
    ///
    pub fn could_be_0(&self, name: &Identifier) -> bool {
        if self.solved_variables.contains_key(&name) {
            // return true iff any of the solutions are 0
            self.solved_variables
                .get(name)
                .unwrap()
                .iter()
                .find(|x| x.is_zero())
                .is_some()
        } else {
            let mut test_model = self.clone();
            test_model
                .solved_variables
                .insert(name.clone(), HashSet::from([Value::zero()]));
            // if this breaks, then it can't be 0
            test_model.assert_relations_hold()
        }
    }

    /// Attempts to build an expression for `name` from the augmented matrix.
    /// Finds the expression in the most simplified form. That is, a non-zero multiplier with
    /// minimum other non-constant terms.
    ///
    /// # Arguments
    /// * `name` - The identifier to search for.
    ///
    pub fn force_build_expression(&self, name: Identifier) -> Result<Expression, String> {
        // first, attempt to get out of already solved variables
        let value_col_result = self.variables.iter().position(|var| var == &name);
        if value_col_result.is_none() {
            // TODO - we don't need to give up here. Try to find some term in the augmented matrix
            // which uses this. There could be something.
            Ok(Expression::from_identifier(name))
        } else {
            let value_col = value_col_result.unwrap();
            let row_ct = self.augmented_matrix.len();
            let col_ct = if row_ct == 0 {
                1
            } else {
                self.augmented_matrix[0].len()
            };

            let mut best_row: Option<usize> = None;
            let mut min_expressions_plus_values = 0;

            // find the best row
            for row in 0..row_ct {
                if match self.augmented_matrix[row][value_col].simplify_whole_as_constants(&self) {
                    Ok(numbers) => !numbers.iter().all(|number| number.is_zero()),
                    Err(_) => true,
                } {
                    // possible row. Evaluate for goodness
                    let expressions_plus_values =
                        self.augmented_matrix[row].iter().fold(0, |acc, expr| {
                            acc + match expr.simplify_whole_as_constants(&self) {
                                Ok(numbers) => {
                                    if numbers.iter().all(|number| number.is_zero()) {
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
                Ok(Expression::from_identifier(name))
            } else {
                // build resulting formula
                let mut result = self.augmented_matrix[best_row.unwrap()][col_ct - 1].clone();
                for col in 0..(col_ct - 1) {
                    if col != value_col {
                        result -= self.augmented_matrix[best_row.unwrap()][col].clone()
                            * Expression::from_identifier(self.variables[col].clone());
                    }
                }
                result /= self.augmented_matrix[best_row.unwrap()][value_col].clone();
                result.simplify_whole_loose(&self)
            }
        }
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
            if match self.augmented_matrix[switcher][col].simplify_whole_as_constants(&self) {
                Ok(numbers) => !numbers.iter().any(|number| number.is_zero()),
                Err(_) => false,
            } {
                // we want to prioritize getting a row with all constants
                let all_constants_in_row = self.augmented_matrix[switcher]
                    .iter()
                    .all(|expr| expr.simplify_whole_as_constants(&self).is_ok());

                if all_constants_in_row {
                    // TODO - this is the preferable case -- that all elements of the row are
                    // constant -- but it'd be worth it as a backup to take something with all 0s
                    // preceding as a switcher. Update accordingly.
                    result = Some(switcher);
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
            let factor = self.augmented_matrix[row][col].clone();
            for col_update in col..col_ct {
                self.augmented_matrix[row][col_update] /= factor.clone();
            }
        }

        // subtract that row from rows above and below until they're all 0 or undetermined at that pos
        for row_update in 0..row_ct {
            // skip the current row
            if row_update != row {
                let factor = self.augmented_matrix[row_update][col].clone();
                if match factor.simplify_whole_loose(&self).unwrap().as_value() {
                    // don't subtract anything if it's already 0
                    Some(number) => !number.is_zero(),
                    // don't subtract anything if there's an equation there
                    None => false,
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

    /// Discover pairs of rows which are lonely, and pair them up.
    /// This is a weird one.
    /// Consider this example of an augmented matrix:
    ///
    /// a | _
    /// -----
    /// b | 6
    /// c | 3
    ///
    /// Let's also say that we know a ≠ 0
    /// In this case, we have that ab = 6 and ac = 3
    /// So we can multiply the second by 2 to get 2ac = 6
    /// Then set 2ac to ab
    /// Then since a ≠ 0, we can say 2c = b
    ///
    /// yielding this new augmented matrix:
    /// a |  b  | c | _
    /// ---------------
    /// b |  0  | 0 | 6
    /// c |  0  | 0 | 3
    /// 0 | -1  | 2 | 0
    ///
    /// This new information can then be used to further develop augmented matrix.
    ///
    fn make_less_lonely(&mut self) -> Result<(), String> {
        let mut row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        // find lonely groups, i.e., sets of rows which have exactly one column element, for each
        // column except the last.
        let mut lonely_groups: Vec<Vec<usize>> = Vec::with_capacity(col_ct - 1);
        for col in 0..(col_ct - 1) {
            let mut lonely_rows: Vec<usize> = Vec::new();
            for row in 0..row_ct {
                // only consider expressions which cannot evaluate to 0
                let is_zero = if let Ok(numbers) =
                    self.augmented_matrix[row][col].simplify_whole_as_constants(&self)
                {
                    numbers.iter().all(|number| number.is_zero())
                } else {
                    false
                };
                if !is_zero {
                    // determine if this row has a lonely column
                    let mut lonely_row = true;
                    for sub_col in 0..(col_ct - 1) {
                        if sub_col == col {
                            continue;
                        }
                        let is_zero = if let Ok(numbers) =
                            self.augmented_matrix[row][sub_col].simplify_whole_as_constants(&self)
                        {
                            numbers.iter().all(|number| number.is_zero())
                        } else {
                            false
                        };
                        lonely_row &= is_zero;
                    }
                    if lonely_row {
                        lonely_rows.push(row);
                    }
                }
            }
            lonely_groups.push(lonely_rows);
        }

        // for each lonely group with > 1 element, generate any possible equations
        let mut new_equations: Vec<(Expression, Expression)> = Vec::new();
        for col in 0..(col_ct - 1) {
            // it should only do this if it can guarantee the column variable is not 0
            if !self.could_be_0(&self.variables[col]) {
                if self.solved_variables.contains_key(&self.variables[col])
                    && self
                        .solved_variables
                        .get(&self.variables[col])
                        .unwrap()
                        .len()
                        == 1
                {
                    let value = self
                        .solved_variables
                        .get(&self.variables[col])
                        .unwrap()
                        .iter()
                        .next()
                        .unwrap();
                    for row in (0..row_ct).rev() {
                        if !self.augmented_matrix[row][col]
                            .simplify_whole_as_constants(&self)
                            .is_ok_and(|values| {
                                values.len() == 1 && values.iter().next().unwrap().is_zero()
                            })
                        {
                            let mut new_left = Expression::new();
                            for cell_col in 0..col_ct - 1 {
                                new_left += self.augmented_matrix[row][cell_col].clone()
                                    * if cell_col == col {
                                        Expression::from_value(value.clone())
                                    } else {
                                        Expression::from_identifier(
                                            self.variables[cell_col].clone(),
                                        )
                                    };
                            }
                            new_equations
                                .push((new_left, self.augmented_matrix[row][col_ct - 1].clone()));
                            self.augmented_matrix.remove(row);
                            row_ct -= 1;
                        }
                    }
                } else if lonely_groups[col].len() > 1 {
                    for right_idx in 1..lonely_groups[col].len() {
                        let left_row_idx = lonely_groups[col][right_idx - 1];
                        let right_row_idx = lonely_groups[col][right_idx];
                        // must multiply each side by the thing the other is equal to so that they're
                        // equal
                        new_equations.push((
                            self.augmented_matrix[left_row_idx][col].clone()
                                * self.augmented_matrix[right_row_idx][col_ct - 1].clone(),
                            self.augmented_matrix[right_row_idx][col].clone()
                                * self.augmented_matrix[left_row_idx][col_ct - 1].clone(),
                        ));
                    }
                }
            }
        }

        // add each equation to the augmented matrix
        // NOTE - this cannot be optimized by throwing this in the previous loop, since it edits
        // the augmented matrix and may delete necessary rows.
        for (left, right) in new_equations {
            self.add_matrix_row(left, right)?;
        }
        Ok(())
    }

    /// Simplify `self.augmented_matrix` by removing meaningless rows. (which are all 0s)
    ///
    fn remove_0s(&mut self) -> Result<(), String> {
        let row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        for row in (0..row_ct).rev() {
            if self.augmented_matrix[row][0..col_ct - 1]
                .iter()
                .all(|expr| match expr.simplify_whole_as_constants(&self) {
                    Ok(numbers) => numbers.iter().all(|number| number.is_zero()),
                    Err(_) => false,
                })
            {
                if self.augmented_matrix[row][col_ct - 1]
                    .simplify_whole_as_constants(&self)
                    .is_ok_and(|numbers| numbers.iter().all(|number| number.is_zero()))
                {
                    self.augmented_matrix.remove(row);
                } else {
                    eprintln!("ERROR: Logical error introduced.");
                    process::exit(1);
                }
            }
        }
        Ok(())
    }

    /// Solve for all solutions of lonely polynomials.
    ///
    fn resolve_lonely_polynomials(&mut self) -> Result<(), String> {
        let row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        for col in 0..(col_ct - 1) {
            let row_ct = self.augmented_matrix.len();
            for row in (0..row_ct).rev() {
                // determine if this row has a lonely column
                let mut lonely_row = true;
                for sub_col in 0..(col_ct - 1) {
                    if sub_col == col {
                        continue;
                    }
                    let is_zero = if let Ok(numbers) =
                        self.augmented_matrix[row][sub_col].simplify_whole_as_constants(&self)
                    {
                        numbers.iter().all(|number| number.is_zero())
                    } else {
                        false
                    };
                    lonely_row &= is_zero;
                }
                if lonely_row {
                    let zero_equivalent = (self.augmented_matrix[row][col].clone()
                        * Expression::from_identifier(self.variables[col].clone())
                        - self.augmented_matrix[row][col_ct - 1].clone())
                    .simplify_whole(&self, false);
                    if zero_equivalent.is_ok() {
                        if let Some((polynomial, name)) = zero_equivalent
                            .unwrap()
                            .iter()
                            .next()
                            .unwrap()
                            .extract_polynomial()
                        {
                            let equivalencies = polynomial.find_roots();
                            self.solved_variables.insert(name.clone(), HashSet::new());
                            self.augmented_matrix.remove(row);
                            let mut test_model = self.clone();
                            for equivalency in equivalencies {
                                // only add if solution does not break pre-order
                                test_model
                                    .solved_variables
                                    .insert(name.clone(), HashSet::from([equivalency.clone()]));
                                if test_model.assert_relations_hold() {
                                    self.solved_variables.entry(name.clone()).and_modify(
                                        |values| {
                                            values.insert(equivalency);
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Remove rows which are just a pivot and store them.
    ///
    fn store_lonely_pivots(&mut self) {
        let row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        for row in (0..row_ct).rev() {
            let equivalence_result =
                self.augmented_matrix[row][col_ct - 1].simplify_whole_as_constants(&self);
            if equivalence_result.is_ok() {
                let mut lonely_col_option: Option<(usize, Value)> = None;
                let mut too_many_non_zero_constants = false;
                // determine if row can be thrown into solved variables
                for col in 0..(col_ct - 1) {
                    let constant_result =
                        self.augmented_matrix[row][col].simplify_whole_as_constants(&self);
                    if constant_result.as_ref().is_ok_and(|values| {
                        values.len() == 1 && !values.iter().next().unwrap().is_zero()
                    }) {
                        if lonely_col_option.is_none() {
                            lonely_col_option = Some((
                                col,
                                constant_result.unwrap().iter().next().unwrap().clone(),
                            ));
                        } else {
                            too_many_non_zero_constants = true;
                        }
                    } else if constant_result.is_err() {
                        // if there's anything that's not a constant we can't remove it yet either
                        too_many_non_zero_constants = true;
                    }
                }
                if !too_many_non_zero_constants && lonely_col_option.is_some() {
                    let (lonely_col, constant) = lonely_col_option.unwrap();

                    // throw that sucker in the solved variables!
                    self.solved_variables.insert(
                        self.variables[lonely_col].clone(),
                        equivalence_result
                            .unwrap()
                            .iter()
                            .map(|equivalency| equivalency.clone() / constant.clone())
                            .collect::<HashSet<_>>(),
                    );

                    // that information is no longer needed!
                    self.augmented_matrix.remove(row);
                }
            }
        }
    }

    /// Update `self.augmented_matrix` to reduced echelon form.
    ///
    fn reduce(&mut self) -> Result<(), String> {
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
                self.augmented_matrix[row][col] = self.augmented_matrix[row][col]
                    .simplify_whole_loose(&self)
                    .unwrap()
                    .clone();
            }
        }

        // remove expressions which are just a pivot (these are now knowns!)
        self.store_lonely_pivots();

        // try to generate new equations with the gained info
        self.make_less_lonely()?;

        // try to solve any solvable polynomials
        self.resolve_lonely_polynomials()?;

        // remove expressions which are all 0s
        self.remove_0s()?;

        Ok(())
    }

    /// Assert all relations in `self` still hold.
    ///
    pub fn assert_relations_hold(&self) -> bool {
        let mut all_true = true;
        for relation in &self.relations {
            let simplified_result = relation.simplify_whole(&self, false);
            if simplified_result.is_err() {
                all_true = false;
            } else {
                let simplified = simplified_result.unwrap();
                for element in simplified {
                    if let Some(false) = element.as_bool() {
                        all_true = false;
                    }
                }
            }
        }
        all_true
    }

    /// Get the index of an identifier in `self.variables`, and create it if it does not exist.
    ///
    /// # Arguments
    /// * row_vector - the additional row vector to insert into
    /// * identifier - the `Identifier` to search for.
    ///
    fn get_index(&mut self, row_vector: &mut Vec<Expression>, identifier: Identifier) -> usize {
        let index_option = self.variables.iter().position(|var| var == &identifier);
        if index_option.is_some() {
            index_option.unwrap()
        } else {
            // if the variable is yet to be seen, create an entry for it
            self.variables.insert(0, identifier);
            // expression of value zero to cleanly insert
            let zero_expr = Expression::new();
            for row in &mut self.augmented_matrix {
                row.insert(0, zero_expr.clone());
            }
            row_vector.insert(0, zero_expr.clone());
            0
        }
    }

    /// Add a row to `self.augmented_matrix` based on the provided equality.
    ///
    /// # Arguments
    /// * `left` - The left-hand side of the equality.
    /// * `right` - The right-hand side of the equality.
    ///
    pub fn add_matrix_row(&mut self, left: Expression, right: Expression) -> Result<(), String> {
        // subtract one side from the other
        let mut zero_equivalent = left.clone() - right.clone();

        // combine like terms
        zero_equivalent.flatten();

        // extract the terms which have no identifiers in numerator
        let mut column_vector_element = Expression::new();

        let zero_expr = Expression::new();

        let mut row_vector = vec![zero_expr.clone(); self.variables.len()];

        // extract terms and place in augmented matrix
        for term in zero_equivalent.minuend_ref() {
            let mut term = term.clone();
            if let Some(identifier) = term.extract_identifier() {
                let index = self.get_index(&mut row_vector, identifier);
                row_vector[index] += term;
            } else {
                column_vector_element -= term;
            }
        }
        for term in zero_equivalent.subtrahend_ref() {
            let mut term = term.clone();
            if let Some(identifier) = term.extract_identifier() {
                let index = self.get_index(&mut row_vector, identifier);
                row_vector[index] -= term;
            } else {
                column_vector_element += term;
            }
        }

        // add to augmented matrix and update information
        row_vector.push(column_vector_element);
        self.augmented_matrix.push(row_vector);
        self.reduce()?;
        if !self.assert_relations_hold() {
            return Err(String::from("Logical error introduced"));
        }
        Ok(())
    }

    /// Add a relation to `self.relations`.
    ///
    /// # Arguments
    /// * `left` - The left-hand side of the relation.
    /// * `right` - The right-hand side of the relation.
    /// * `operator` - The operator between the relation elements.
    ///
    pub fn add_relation(&mut self, left: Expression, operator: RelationOp, right: Expression) {
        // TODO - for variables with multiple solutions, this should check if it can remove some
        let mut new_relation = Relation::from_expression(left);
        new_relation.extend(operator, right);
        self.relations.push(new_relation);
    }

    /// Add a function to the model.
    ///
    /// # Arguments
    /// * `function` - The function to add.
    /// * `name` - The name of the function.
    /// * `arguments` - The arguments for the function.
    /// * `definition` - The definition for the function.
    ///
    pub fn add_function(
        &mut self,
        name: Identifier,
        arguments: Vec<Identifier>,
        definition: Vec<(Expression, Relation)>,
    ) -> Result<(), String> {
        let function = Statement::FunctionDefinition(name.clone(), arguments, definition);

        // only insert if it doesn't already exist.
        // note that functions are compared for equality only by their name.
        if let Some(_) = self
            .functions
            .iter()
            .find(|stmt| matches!(stmt, Statement::FunctionDefinition(n, _, _) if n == &name))
            .cloned()
        {
            Err(format!("Function `{name}` already defined"))
        } else {
            self.functions.insert(function);
            Ok(())
        }
    }

    /// Initializes the Model.
    ///
    /// # Arguments
    /// * `call_depth` - The depth of calls. Safety for recursion.
    ///
    pub fn new(call_depth: u16) -> Self {
        Model {
            solved_variables: HashMap::new(),
            variables: Vec::new(),
            augmented_matrix: Vec::new(),
            relations: Vec::new(),
            functions: HashSet::new(),
            call_depth,
        }
    }

    /// Generate all possible known variables.
    ///
    pub fn generate_possible_knowns(&self) -> Vec<HashMap<Identifier, Value>> {
        let keys: Vec<&Identifier> = self.solved_variables.keys().collect();
        let value_sets: Vec<&HashSet<Value>> = self.solved_variables.values().collect();
        let mut combinations: Vec<HashMap<Identifier, Value>> = vec![HashMap::new()];
        for (key, value_set) in keys.iter().zip(value_sets.iter()) {
            let mut new_combinations = Vec::new();
            for combination in combinations.iter() {
                for value in value_set.iter().clone() {
                    let mut new_combination = combination.clone();
                    new_combination.insert((*key).clone(), value.clone());
                    new_combinations.push(new_combination);
                }
            }
            combinations = new_combinations;
        }
        combinations
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::*;

    #[test]
    fn test_linear_system_1() {
        let mut model = Model::new(0);
        model
            .add_matrix_row(
                ast::parse_expression("3x + 2y", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("19", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `3x + 2y = 19`. MODEL: {model}");
        model
            .add_matrix_row(
                ast::parse_expression("8x - 10y", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("20", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `8x - 10y = 20`. MODEL: {model}");
        assert_eq!(
            Value::from(5),
            Expression::from_identifier(Identifier::new("x").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
        assert_eq!(
            Value::from(2),
            Expression::from_identifier(Identifier::new("y").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
    }

    #[test]
    fn test_linear_system_2() {
        let mut model = Model::new(0);
        model
            .add_matrix_row(
                ast::parse_expression("3x + 2y + z", &mut 0)
                    .expect("ast::parse_expression - failure"),
                ast::parse_expression("26", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `3x + 2y + z = 26`. MODEL: {model}");
        model
            .add_matrix_row(
                ast::parse_expression("4x - 5y - z", &mut 0)
                    .expect("ast::parse_expression - failure"),
                ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `4x - 5y - z = 3`. MODEL: {model}");
        model
            .add_matrix_row(
                ast::parse_expression("x + 2y + 3z", &mut 0)
                    .expect("ast::parse_expression - failure"),
                ast::parse_expression("30", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `x + 2y + 3z = 30`. MODEL: {model}");
        assert_eq!(
            Value::from(5),
            Expression::from_identifier(Identifier::new("x").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
        assert_eq!(
            Value::from(2),
            Expression::from_identifier(Identifier::new("y").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
        assert_eq!(
            Value::from(7),
            Expression::from_identifier(Identifier::new("z").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
    }

    #[test]
    fn test_retrieval_1() {
        let mut model = Model::new(0);
        model
            .add_matrix_row(
                ast::parse_expression("a", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `a = 3`. MODEL: {model}");
        model
            .add_matrix_row(
                ast::parse_expression("ax + 2y", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("19", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `ax + 2y = 19`. MODEL: {model}");
        model
            .add_matrix_row(
                ast::parse_expression("8x - 10y", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("20", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `8x - 10y = 20`. MODEL: {model}");
        assert_eq!(
            Value::from(3),
            Expression::from_identifier(Identifier::new("a").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
        assert_eq!(
            Value::from(5),
            Expression::from_identifier(Identifier::new("x").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
        assert_eq!(
            Value::from(2),
            Expression::from_identifier(Identifier::new("y").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
    }

    #[test]
    fn test_retrieval_2() {
        let mut model = Model::new(0);
        model
            .add_matrix_row(
                ast::parse_expression("ax + 2y", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("19", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `ax + 2y = 19`. MODEL: {model}");
        model
            .add_matrix_row(
                ast::parse_expression("8x - 10y", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("20", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `8x - 10y = 20`. MODEL: {model}");
        model
            .add_matrix_row(
                ast::parse_expression("a", &mut 0).expect("ast::parse_expression - failure"),
                ast::parse_expression("3", &mut 0).expect("ast::parse_expression - failure"),
            )
            .unwrap();
        println!("ADDED: `a = 3`. MODEL: {model}");
        assert_eq!(
            Value::from(3),
            Expression::from_identifier(Identifier::new("a").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
        assert_eq!(
            Value::from(5),
            Expression::from_identifier(Identifier::new("x").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
        assert_eq!(
            Value::from(2),
            Expression::from_identifier(Identifier::new("y").unwrap())
                .simplify_whole_loose(&model)
                .unwrap()
                .as_value()
                .unwrap()
        );
    }
}
