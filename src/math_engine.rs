use crate::definitions::*;
use std::cmp;

/// Process the AST of a prompt.
///
/// # Arguments
/// * `prompt` - A Statement::Prompt representing the prompt to evaluate.
///
pub fn process_prompt(_prompt: Statement) {
    // TODO - implement function
        
}

/// Process the AST of a function.
///
/// # Arguments
/// * `function` - A Statement::FunctionDefinition representing the function to define.
///
pub fn process_function(_function: Statement) {
    // TODO - implement function
        
}

/// Process the AST of an equation.
///
/// # Arguments
/// * `equation` - A Statement::Equation representing the prompt to evaluate.
///
pub fn process_equation(_equation: Statement) {
    // TODO - implement function
        
}

#[derive(Debug, Clone, PartialEq)]
struct Variable {
    pub name: Identifier,
    pub unit: Unit,
}

/// Evaluate the given `Expression` assuming all constant values.
///
/// # Arguments
/// * `expression` - The `Expression` to evaluate.
///
fn evaluate_constant_expression(_expression: &Expression) -> Result<Number, String> {
    // TODO - implement function

    Err(String::from("Not implemented"))
}

/// Model for program.
///
/// An individual model must be owned by each function call.
/// Includes matrix representing values of all variables.
/// Stores each function.
/// Also stores 'call depth' to keep recursion safe.
///
#[derive(Debug, Clone, PartialEq)]
struct ProgramModel {
    variables: Vec<Variable>,
    augmented_matrix: Vec<Vec<Expression>>,
    functions: Vec<Statement>,
    call_depth: u16,

}

impl ProgramModel {
    /// Update `self.augmented_matrix` to reduced echelon form.
    ///
    fn reduce(&mut self) {
        assert!(self.augmented_matrix.len() > 0 
            && self.augmented_matrix[0].len() > 0, 
            "Empty augmented matrix");

        let row_ct = self.augmented_matrix.len();
        let col_ct = self.augmented_matrix[0].len();

        for col in 0..cmp::min(row_ct, col_ct) {
            // the goal is to get a 1 at each [row, col]
            let row = col;

            // the row to switch row out for
            let mut switcher = row;
            while switcher < row_ct && 
                match evaluate_constant_expression(&self.augmented_matrix[switcher][col]) {
                    Ok(number) => number.value == 0f64,
                    Err(_) => true, // skip non-constants
                } {
                switcher += 1;
            }

            // if a row can safely exist here
            if switcher < row_ct {
                if row < switcher {
                    // swap the rows
                    self.augmented_matrix.swap(row, switcher);
                }
                
                // divide the row by the `col` element to get a 1
                let factor = evaluate_constant_expression(&self.augmented_matrix[row][col]).unwrap();
                for col_update in col..col_ct {
                    let original = &self.augmented_matrix[row][col_update];

                    self.augmented_matrix[row][col_update] /= &self.augmented_matrix[row][col];
                }

                // TODO - subtract that row from rows below until they're all 0 at that pos
            }

            // TODO - go back up and subtract the 1s from rows above
            
        }

    }

    /// Retrieve an expression for the value of the given identifier from `self.augmented_matrix`.
    ///
    /// # Arguments
    /// * `name` - The identifier to search for.
    ///
    fn retrieve_value(&self, _name: Identifier) -> Result<Expression, String> {
        // TODO - implement function
        
        Err(String::from("Not implemented"))    
    }

    /// Add a row to `self.augmented_matrix` based on the provided equality.
    ///
    /// # Arguments
    /// * `left` - The left-hand side of the equality.
    /// * `right` - The right-hand side of the equality.
    ///
    fn add_matrix_row(&mut self, _left: Expression, _right: Expression) {
        // TODO - implement function

    }

    /// Add a variable with its unit to the model.
    ///
    /// # Arguments
    /// * `name` - The name of the variable
    /// * `unit` - The units of the variable
    ///
    fn add_variable(&mut self, name: Identifier, unit: Unit) {
        assert!(!self.variables.iter().any(|v| &v.name == &name), "Variable already exists");
        self.variables.push(Variable {
            name, unit
        });
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

