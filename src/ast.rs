use crate::definitions::*;
// use crate::tokenizer::*;

/// Parse statement into ast.
///
/// statement ::= prompt | function | relation
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index within `code` representing a point after the last token processed.
///
/// " Examples
///
/// ```
/// let code = "3x + 2 = 7";
/// let mut i: usize = 0;
/// let _ = parse_statement(code, &mut i).unwrap();
/// assert!(i = code.chars().count())
/// ```
///
pub fn parse_statement(_code: &str, _i: &mut usize) -> Result<Statement, String> {
    // TODO - implement function

    // NOTE - any calls to parse_<thing> should consider using ? operator for early return

    // TODO - check if it's a function definiton

    // TODO - if so, return Statement::Function(Identifier, Vec<Identifier>, Vec<(Expression, Relation)>)
    
    // TODO - else, assume relation

    // TODO - after parsing relation, check if ends in '?'
    
    // TODO - if so, return Statement::Prompt(Relation)

    // TODO - else, return Statement::Equation(Relation)
    
    Err(String::from("Not implemented"))
}



/// Parse function into ast.
///
/// function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' 'if' relation '\n' ) + '}' )
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index within `code` representing a point after the last token processed.
///
/// " Examples
///
/// ```
/// let code = "f(x) = 3x + 2";
/// let mut i: usize = 0;
/// let _ = parse_function(code, &mut i).unwrap();
/// ```
///
/// ```
/// let code = "f(x) = {\n\
///               3x,     x < 3\n\
///               2x + 3, x ≥ 3\n\
///             }";
/// let mut i: usize = 0;
/// let _ = parse_function(code, &mut i).unwrap();
/// ```
///
pub fn parse_function(_code: &str, _i: &mut usize) -> Result<Statement, String> {
    // TODO - implement function
    
    Err(String::from("Not implemented"))
}



