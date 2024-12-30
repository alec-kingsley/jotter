#![allow(dead_code)]

use std::env;
use std::fs;

mod ast;
mod unit_parser;
mod definitions;
mod math_engine;
mod tokenizer;

use crate::ast::*;
use crate::definitions::Statement;
use crate::math_engine::*;

fn main() {
    let args: Vec<String> = env::args().collect();
    assert!(args.len() >= 2, "Usage: cargo run -- source.jt");

    // read source file
    let src = &args[1];

    // setup state variables
    let code = fs::read_to_string(src).expect("Failed to read from file.");
    let mut i = 0;
    let mut model = ProgramModel::new(0);

    // main loop
    let mut eof = false;
    while !eof {
        let next_statement = parse_statement(code.as_str(), &mut i);
        match next_statement {
            Ok(Statement::Prompt(relation)) => process_prompt(&model, relation),
            Ok(Statement::Equation(relation)) => process_equation(&mut model, relation),
            Ok(Statement::FunctionDefinition(name, arguments, definition)) => {
                process_function(&mut model, name, arguments, definition)
            }
            Err(msg) => {
                if msg == "Not found" {
                    eof = true;
                }
            }
        }
    }
}
