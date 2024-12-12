use crate::definitions::*;
// use crate::tokenizer::*;

/// Parse statement into ast.
///
/// statement ::= function | prompt | relation
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
    Err(String::from("Not implemented"))

}


