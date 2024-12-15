use crate::definitions::*;

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
    pub name: String,
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
struct ProgramModel {
    variables: Vec<Variable>,
    augmented_matrix: Vec<Vec<f64>>,
    functions: Vec<Statement>,
    call_depth: u16,

}

impl ProgramModel {
    /// Add a variable with its unit to the model.
    ///
    /// # Arguments
    /// * `name` - The name of the variable
    /// * `unit` - The units of the variable
    ///
    fn add_variable(&mut self, name: String, unit: Unit) {
        assert!(!self.variables.iter().any(|v| &v.name == &name), "Variable already exists");
        self.variables.push(Variable {
            name, unit
        });
    }

    /// Initializes the ProgramModel.
    ///
    pub fn new() -> Result<Self, String> {
        // TODO - implement function

        Err(String::from("Not implemented"))
    }
}




