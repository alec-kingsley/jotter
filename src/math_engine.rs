use crate::definitions::*;
use std::cmp;
use std::collections::{HashMap, HashSet};

/// Process the AST of a prompt.
///
/// # Arguments
/// * `model` - The program model for the state of the program.
/// * `prompt` - A Statement::Prompt representing the prompt to evaluate.
///
pub fn process_prompt(model: &ProgramModel, prompt: Relation) {
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
/// * `model` - The program model for the state of the program.
/// * `name` - The name of the function.
/// * `arguments` - The arguments for the function.
/// * `definition` - The definition for the function.
///
pub fn process_function(
    model: &mut ProgramModel,
    name: Identifier,
    arguments: Vec<Identifier>,
    definition: Vec<(Expression, Relation)>,
) {
    let add_function_result = model.add_function(name, arguments, definition);
    if add_function_result.is_err() {
        println!("WARNING - {}", add_function_result.unwrap_err());
    }
}

/// Process the AST of an equation / relation.
///
/// # Arguments
/// * `model` - The program model for the state of the program.
/// * `equation` - A `Relation` representing the relation to evaluate.
///
pub fn process_equation(model: &mut ProgramModel, relation: Relation) {
    assert!(
        relation.operands.len() == relation.operators.len() + 1,
        "Invalid Relation"
    );

    // loop through operators
    for i in 0..relation.operators.len() {
        // extract each side of operator as clone
        let left = relation.operands[i].clone();
        let right = relation.operands[i + 1].clone();
        // if equality, call add_matrix_row
        if relation.operators[i] == RelationOp::Equal {
            model.add_matrix_row(left, right);
        } else {
            // else, call add_relation
            model.add_relation(left, right, relation.operators[i].clone());
        }
    }
}

/// Model for program.
///
/// An individual model must be owned by each function call.
/// Includes matrix representing values of all variables.
/// Stores each function.
/// Also stores 'call depth' to keep recursion safe.
///
#[derive(Debug, Clone)]
pub struct ProgramModel {
    variables: Vec<Identifier>,
    augmented_matrix: Vec<Vec<Expression>>,
    relations: HashSet<Relation>,
    functions: HashSet<Statement>,
    call_depth: u16,
}

impl ProgramModel {
    /// Make the call in `call`.
    ///
    /// NOTE - does not check for matching variable names. So the code:
    /// f(x) = x
    /// f(x) ?
    /// would print
    /// f(x): x
    /// as opposed to an error
    ///
    /// # Arguments
    /// * `call` - The `Call` to make.
    ///
    fn make_call(&self, call: &Call) -> Result<Expression, String> {
        if let Some(Statement::FunctionDefinition(_, arguments, definition)) = self.functions.get(
            &Statement::FunctionDefinition(call.name.clone(), Vec::new(), Vec::new()),
        ) {
            assert!(self.call_depth < 500, "Maximum call depth of 500 reached");
            if arguments.len() != call.arguments.len() {
                Err(format!(
                    "Function `{}` takes `{}` arguments, while `{}` were supplied.",
                    call.name,
                    arguments.len(),
                    call.arguments.len()
                ))
            } else {
                let mut model = self.clone();
                model.augmented_matrix.clear();
                model.call_depth += 1;
                for i in 0..arguments.len() {
                    // assign each variable name to its argument
                    model.add_matrix_row(
                        call.arguments[i].clone(),
                        Expression {
                            minuend: HashSet::from([Term {
                                numerator: HashSet::from([Factor::Identifier(
                                    arguments[i].clone(),
                                )]),
                                denominator: HashSet::new(),
                            }]),
                            subtrahend: HashSet::new(),
                        },
                    );
                }
                // find a true thing to return
                let mut result: Option<Expression> = None;
                for (expression, relation) in definition {
                    if result.is_none() {
                        let evaluated_result = model.simplify_relation(relation);
                        if evaluated_result.is_ok() {
                            let evaluated = evaluated_result.unwrap();
                            let true_expr = Expression {
                                minuend: HashSet::from([Term {
                                    numerator: HashSet::new(),
                                    denominator: HashSet::new(),
                                }]),
                                subtrahend: HashSet::new(),
                            };
                            if evaluated.operands.len() == 1 && evaluated.operands[0] == true_expr {
                                result = Some(expression.clone());
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
            Err(format!("Function `{}` not found.", call.name))
        }
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
            },
        };

        for operand in &term.numerator {
            value *= self.evaluate_constant_factor(&operand)?;
        }
        for operand in &term.denominator {
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
            },
        };

        for operand in &expression.minuend {
            value *= self.evaluate_constant_term(&operand)?;
        }
        for operand in &expression.subtrahend {
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
            numerator: HashSet::new(),
            denominator: HashSet::new(),
        };

        // simplify original factors in term and throw them back in
        for operand in &term.numerator {
            new_term
                .numerator
                .insert(self.simplify_factor(operand, make_substitutions)?);
        }
        for operand in &term.denominator {
            new_term
                .denominator
                .insert(self.simplify_factor(operand, make_substitutions)?);
        }

        // combine all the numeric literals and return if not one
        let number = new_term.extract_number();
        if !number.is_one() {
            new_term.numerator.insert(Factor::Number(number));
        }

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
            minuend: HashSet::new(),
            subtrahend: HashSet::new(),
        };

        // re-add the original terms after simplifying
        for operand in &expression.minuend {
            new_expression
                .minuend
                .insert(self.simplify_term(operand, make_substitutions)?);
        }

        for operand in &expression.subtrahend {
            new_expression
                .subtrahend
                .insert(self.simplify_term(operand, make_substitutions)?);
        }

        // remove parentheticals and combine like terms
        new_expression.flatten();

        Ok(new_expression)
    }

    /// Simplify the given `Relation`, using known variable values.
    /// Makes substitutions when possible. (This is since relation is not repeated in tree)
    ///
    /// If |relation.operands| > 1 then returned `Relation` may just be 1 for true and 0 for false.
    ///
    /// # Arguments
    /// * `expression` - The `Expression` to simplify.
    /// * `make_substitutions` - True iff it should substitute known variables.
    ///
    pub fn simplify_relation(&self, relation: &Relation) -> Result<Relation, String> {
        let mut new_relation = Relation {
            operands: Vec::new(),
            operators: Vec::new(),
        };

        // re-add the original expressions after simplifying
        for operand in &relation.operands {
            new_relation
                .operands
                .push(self.simplify_expression(operand, true)?);
        }
        new_relation.operators.clone_from(&relation.operators);

        let mut all_true = true;
        let mut has_false = false;
        // attempt to evaluate to constant boolean value
        for op_i in 0..relation.operators.len() {
            // evaluate left and right
            let left_result = self.evaluate_constant_expression(&relation.operands[op_i]);
            let right_result = self.evaluate_constant_expression(&relation.operands[op_i + 1]);
            if left_result.is_ok() && right_result.is_ok() {
                if compare(
                    left_result.unwrap(),
                    right_result.unwrap(),
                    &relation.operators[op_i],
                ) {
                    // short circuit if any false ones found
                    has_false = true;
                    break;
                }
            } else {
                // if anything can't be evaluated, we can't say that it's all true
                all_true = false;
            }
        }

        Ok(if has_false {
            // return false
            Relation {
                operands: vec![Expression {
                    minuend: HashSet::new(),
                    subtrahend: HashSet::new(),
                }],
                operators: Vec::new(),
            }
        } else if all_true {
            // return true
            Relation {
                operands: vec![Expression {
                    minuend: HashSet::from([Term {
                        numerator: HashSet::new(),
                        denominator: HashSet::new(),
                    }]),
                    subtrahend: HashSet::new(),
                }],
                operators: Vec::new(),
            }
        } else {
            // return relation as simplified as it can be
            new_relation
        })
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
        let value_col = self.variables.iter().position(|var| var == &name).unwrap();
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

    /// Assert all relations in `self` still hold.
    ///
    fn assert_relations_hold(&self) -> bool {
        let mut all_true = true;
        for relation in &self.relations {
            let simplified_result = self.simplify_relation(relation);
            if simplified_result.is_err() {
                all_true = false;
            } else {
                let simplified = simplified_result.unwrap();
                if simplified.operands.len() == 1 {
                    if simplified.operands[0].minuend.is_empty() {
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
            let zero_expr = Expression {
                minuend: HashSet::new(),
                subtrahend: HashSet::new(),
            };
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
    fn add_matrix_row(&mut self, left: Expression, right: Expression) {
        // subtract one side from the other
        let mut zero_equivalent = left.clone() - right.clone();

        // combine like terms
        zero_equivalent.flatten();

        // extract the terms which have no identifiers in numerator
        let mut column_vector_element = Expression {
            minuend: HashSet::new(),
            subtrahend: HashSet::new(),
        };

        let zero_expr = Expression {
            minuend: HashSet::new(),
            subtrahend: HashSet::new(),
        };

        let mut row_vector = vec![zero_expr.clone(); self.variables.len()];

        // extract terms and place in augmented matrix
        for mut term in zero_equivalent.minuend {
            if let Some(identifier) = term.extract_identifier() {
                let index = self.get_index(&mut row_vector, identifier);
                row_vector[index].minuend.insert(term);
            } else {
                column_vector_element.subtrahend.insert(term);
            }
        }
        for mut term in zero_equivalent.subtrahend {
            if let Some(identifier) = term.extract_identifier() {
                let index = self.get_index(&mut row_vector, identifier);
                row_vector[index].subtrahend.insert(term);
            } else {
                column_vector_element.minuend.insert(term);
            }
        }
    }

    /// Add a relation to `self.relations`.
    ///
    /// # Arguments
    /// * `left` - The left-hand side of the relation.
    /// * `right` - The right-hand side of the relation.
    /// * `operator` - The operator between the relation elements.
    ///
    fn add_relation(&mut self, left: Expression, right: Expression, operator: RelationOp) {
        self.relations.insert(Relation {
            operands: vec![left, right],
            operators: vec![operator],
        });
    }

    /// Add a function to the model.
    ///
    /// # Arguments
    /// * `function` - The function to add.
    /// * `name` - The name of the function.
    /// * `arguments` - The arguments for the function.
    /// * `definition` - The definition for the function.
    ///
    fn add_function(
        &mut self,
        name: Identifier,
        arguments: Vec<Identifier>,
        definition: Vec<(Expression, Relation)>,
    ) -> Result<(), String> {
        let function = Statement::FunctionDefinition(name.clone(), arguments, definition);

        // only insert if it doesn't already exist.
        // note that functions are compared for equality only by their name.
        if let Some(_) = self.functions.get(&function) {
            Err(format!("Function `{name}` already defined"))
        } else {
            self.functions.insert(function);
            Ok(())
        }
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
            relations: HashSet::new(),
            functions: HashSet::new(),
            call_depth,
        }
    }
}
