use crate::math_structs::*;
use std::process;

/// Process the AST of a prompt.
///
/// # Arguments
/// * `model` - The program model for the state of the program.
/// * `prompt` - A Statement::Prompt representing the prompt to evaluate.
///
pub fn process_prompt(model: &Model, prompt: Relation) {
    let simplified_result = prompt.simplify_whole(model, true);
    if simplified_result.is_ok() {
        let simplified = simplified_result.unwrap();
        if prompt.len() > 1 && simplified.len() == 1 && simplified.iter().next().unwrap().len() == 1
        {
            if let Some(true) = simplified.iter().next().unwrap().as_bool() {
                println!("{prompt} ≡ True");
            } else {
                println!("{prompt} ≡ False");
            }
        } else if simplified.len() == 1 {
            println!("{prompt} ≡ {}", simplified.iter().next().unwrap());
        } else {
            println!(
                "{prompt} ∈ {{{}}}",
                simplified
                    .iter()
                    .map(|option| option.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
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
    model: &mut Model,
    name: Identifier,
    arguments: Vec<Identifier>,
    definition: Vec<(Expression, Relation)>,
) {
    let add_function_result = model.add_function(name, arguments, definition);
    if add_function_result.is_err() {
        eprintln!("WARNING - {}", add_function_result.unwrap_err());
    }
}

/// Process the AST of an equation / relation.
///
/// # Arguments
/// * `model` - The program model for the state of the program.
/// * `equation` - A `Relation` representing the relation to evaluate.
///
pub fn process_equation(model: &mut Model, relation: Relation) {
    // loop through operators
    for (left, operator, right) in relation.into_iter() {
        // if equality, call add_matrix_row
        if operator == &RelationOp::Equal {
            let equal_result = model.add_matrix_row(left.clone(), right.clone());
            if equal_result.is_err() {
                eprintln!("ERROR - {}", equal_result.unwrap_err());
                process::exit(0);
            }
        } else {
            // else, call add_relation
            model.add_relation(left.clone(), operator.clone(), right.clone());
        }
    }
}
