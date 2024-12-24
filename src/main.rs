#![allow(dead_code)]

use std::env;
use std::fs;

mod ast;
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

    let code = fs::read_to_string(src).expect("Failed to read from file.");

    let mut model = ProgramModel::new(0);

    let mut i = 0;

    let mut eof = false;
    while !eof {
        let next_statement = parse_statement(code.as_str(), &mut i);
        match next_statement {
            Ok(Statement::Prompt(_)) => process_prompt(next_statement.unwrap(), &mut model),
            Ok(Statement::Equation(_)) => process_equation(next_statement.unwrap(), &mut model),
            Ok(Statement::FunctionDefinition(_, _, _)) => {
                process_function(next_statement.unwrap(), &mut model)
            }
            Err(msg) => {
                if msg == "Not found" {
                    eof = true;
                }
            }
        }
    }
}
