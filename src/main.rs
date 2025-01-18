use std::env;
use std::fs;
use std::io;
use std::io::*;

mod ast;
mod math_structs;

mod driver;
mod tokenizer;
mod unit_parser;

use crate::ast::*;
use crate::driver::*;
use crate::math_structs::Model;
use crate::math_structs::Statement;

static TAB_WIDTH: usize = 2;

/// Interprets an entire Jotter program.
///
/// # Arguments:
/// * `code` - the code to interpret
///
fn interpret_as_whole(model: &mut Model, code: &str, i: &mut usize, tab_ct: usize) {
    // main loop
    let mut eof = false;
    while !eof {
        match parse_statement(code, i) {
            Ok(Statement::Prompt(relation)) => {
                print!(
                    "{}",
                    std::iter::repeat(' ')
                        .take(tab_ct * TAB_WIDTH)
                        .collect::<String>()
                );
                process_prompt(model, relation)
            }
            Ok(Statement::Equation(relation)) => process_equation(model, relation),
            Ok(Statement::FunctionDefinition(name, arguments, definition)) => {
                process_function(model, name, arguments, definition)
            }
            Ok(Statement::StateSwitch(new_state)) => {
                if new_state {
                    interpret_as_whole(&mut model.clone(), code, i, tab_ct + 1);
                } else {
                    break;
                }
            }
            Err(msg) => {
                if msg == "Not found" {
                    eof = true;
                }
            }
        }
    }
}

/// Spawn a jotter terminal, such that it can be interpreted as it's written.
///
fn spawn_jotter_terminal(model: &mut Model, tab_ct: usize) {
    let mut user_code = String::new();
    let mut overwrite = true;
    loop {
        print!(
            "{} ",
            std::iter::repeat('>')
                .take(tab_ct + 1)
                .collect::<String>()
        );
        io::stdout().flush().unwrap();
        if overwrite {
            user_code.clear();
        } else {
            user_code.push_str("\n");
            overwrite = true;
        }
        match io::stdin().read_line(&mut user_code) {
            Ok(0) => {
                println!();
                break;
            }
            Ok(_) => {
                user_code = user_code.trim().to_string();
                if user_code == "exit" {
                    break;
                }
                match parse_statement(user_code.as_str(), &mut 0) {
                    Ok(Statement::Prompt(relation)) => process_prompt(model, relation),
                    Ok(Statement::Equation(relation)) => process_equation(model, relation),
                    Ok(Statement::FunctionDefinition(name, arguments, definition)) => {
                        process_function(model, name, arguments, definition)
                    }
                    Ok(Statement::StateSwitch(new_state)) => {
                        if new_state {
                            spawn_jotter_terminal(&mut model.clone(), tab_ct + 1);
                        } else {
                            break;
                        }
                    }
                    Err(msg) => {
                        if msg == "Expected new line" {
                            overwrite = false;
                        }
                    }
                }
            }
            Err(err) => {
                eprintln!("Error: {err}");
                break;
            }
        }
    }
}

/// main function for Jotter interpreter.
///
fn main() {
    let args: Vec<String> = env::args().collect();
    assert!(
        args.len() <= 2,
        "Usage: \nFrom a file: cargo run -- source.jt\nFrom terminal: cargo run"
    );

    if args.len() == 2 {
        // read source file
        let src = &args[1];

        // setup state variables
        let code = fs::read_to_string(src).expect("Failed to read from file.");
        interpret_as_whole(&mut Model::new(0), code.as_str(), &mut 0, 0);
    } else {
        println!("Running Jotter");
        println!("Type \"exit\" to quit.");
        spawn_jotter_terminal(&mut Model::new(0), 0);
    }
}
