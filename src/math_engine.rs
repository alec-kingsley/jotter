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

/// Model for program.
///
/// Includes matrix representing values of all variables.
/// An individual model must be owned by each function call.
/// Also stores 'call depth' to keep recursion safe.
///
#[derive(Debug, Clone, PartialEq)]
struct ProgramModel {
    // TODO - determine fields

}

impl ProgramModel {
    /// Initializes the MathModel.
    ///
    pub fn new() -> Result<Self, String> {
        // TODO - implement function

        Err(String::from("Not implemented"))
    }
}

