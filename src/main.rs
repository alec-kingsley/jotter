#![allow(dead_code)]

use std::env;
use std::fs;

mod ast;
mod definitions;
mod tokenizer;
mod math_engine;

fn main() {
    let args: Vec<String> = env::args().collect();
    assert!(args.len() >= 2, "Usage: cargo run -- source.jt");

    // read source file
    let src = &args[1];

    let _code = fs::read_to_string(src)
        .expect("Failed to read from file.");

    // TODO - for each line in program, get AST
    
    // TODO - interpret that line of the AST
    
}

