use std::env;
use std::fs;
use std::io;
use std::io::*;

mod ast;
mod math_structs;

mod math_engine;
mod tokenizer;
mod unit_parser;

use crate::math_structs::Statement;
use crate::ast::*;
use crate::math_engine::*;

/// Interprets an entire Jotter program.
///
/// # Arguments:
/// * `code` - the code to interpret
///
fn interpret_as_whole(code: &str) {
    let mut i = 0;
    let mut model = ProgramModel::new(0);

    // main loop
    let mut eof = false;
    while !eof {
        match parse_statement(code, &mut i) {
            Ok(Statement::Prompt(relation)) => process_prompt(&model, relation),
            Ok(Statement::Equation(relation)) => process_equation(&mut model, relation),
            Ok(Statement::FunctionDefinition(name, arguments, definition)) => {
                process_function(&mut model, name, arguments, definition)
            }
            Ok(Statement::Reset) => {
                println!("--------------------");
                model = ProgramModel::new(0);
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
fn spawn_jotter_terminal() {
    let mut model = ProgramModel::new(0);
    let mut user_code = String::new();
    let mut overwrite = true;
    println!("Running Jotter");
    println!("Type \"exit\" to quit.");
    loop {
        print!(">>> ");
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
                    Ok(Statement::Prompt(relation)) => process_prompt(&model, relation),
                    Ok(Statement::Equation(relation)) => process_equation(&mut model, relation),
                    Ok(Statement::FunctionDefinition(name, arguments, definition)) => {
                        process_function(&mut model, name, arguments, definition)
                    }
                    Ok(Statement::Reset) => {
                        println!("Program state reset.");
                        model = ProgramModel::new(0);
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
        interpret_as_whole(code.as_str());
    } else {
        spawn_jotter_terminal();
    }
}
