use crate::definitions::*;

use crate::tokenizer::*;

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
/// assert!(i == code.chars().count())
/// ```
///
pub fn parse_statement(code: &str, i: &mut usize) -> Result<Statement, String> {
    // check if it's a function definiton
    let mut j = i.clone();
    let function_result = parse_function(code, &mut j);
    if function_result.is_ok() {
        *i = j;
        function_result
    } else {
        // keep i how it is, not a function definition
        let relation = parse_relation(code, i)?;
        // since it could be end of input, an Err could happen. In that case,
        // a default string won't be "?" so it's fine.
        if next_token(code, i).unwrap_or_default() == "?" {
            Ok(Statement::Prompt(relation))
        } else {
            *i -= "?".chars().count();
            Ok(Statement::Equation(relation))
        }

    }
}

/// Parse function into ast.
///
/// function ::= identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' relation '\n' ) + '}' )
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
pub fn parse_function(code: &str, i: &mut usize) -> Result<Statement, String> {
    let mut token = next_token(code, i)?;

    let name = Identifier::new(token.as_str())?;

    if next_token(code, i)? != "(" {
        return Err(String::from("Expected '('"));
    }

    // parse arguments
    let mut arguments: Vec<Identifier> = Vec::new();
    token = next_token(code, i)?;
    while token != ")" {
        arguments.push(Identifier::new(token.as_str())?);
        // each identifier must have , or ) after it
        if ![",", ")"].contains(&next_token(code, i)?.as_str()) {
            return Err(String::from("Expected ',' or ')'"));
        }
        token = next_token(code, i)?;
    }
    if next_token(code, i)? != "=" {
        return Err(String::from("Expected '='"));
    }

    // parse definition
    let mut definition: Vec<(Expression, Relation)> = Vec::new();
    token = next_token(code, i)?;
    if token == "{" {
        // need to consume one token since while loop back-tracks once
        token = next_token(code, i)?;
        while token != "}" {
            // back-track since it's not a }
            *i -= token.chars().count();

            // parse expression with comma after
            let expression = parse_expression(code, i)?;
            if next_token(code, i)? != "," {
                return Err(String::from("Expected ','"));
            }

            // parse relation with new line after
            let relation = parse_relation(code, i)?;
            definition.push((expression, relation));
            if next_token(code, i)? != "\n" {
                return Err(String::from("Expected new line"));
            }
            token = next_token(code, i)?;
        }
    } else {
        definition.push((parse_expression(code, i)?, get_true_relation()));
    }

    Ok(Statement::FunctionDefinition(name, arguments, definition))
}

/// Parse relation into ast.
///
/// relation ::= expression | relation ( '<' | '>' | '<=' | '>=' | '=' | '<>' ) expression
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index within `code` representing a point after the last token processed.
///
/// " Examples
///
/// ```
/// let code = "2y + 7 = 3x + 2";
/// let mut i: usize = 0;
/// let _ = parse_relation(code, &mut i).unwrap();
/// ```
///
pub fn parse_relation(_code: &str, _i: &mut usize) -> Result<Relation, String> {
    // TODO - implement function

    Err(String::from("Not implemented"))
}

/// Parse expression into ast.
///
/// expression ::= term | expression ( '+' | '-' ) term
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index within `code` representing a point after the last token processed.
///
/// " Examples
///
/// ```
/// let code = "32x + 2ab";
/// let mut i: usize = 0;
/// let _ = parse_expression(code, &mut i).unwrap();
/// ```
///
pub fn parse_expression(_code: &str, _i: &mut usize) -> Result<Expression, String> {
    // TODO - implement function

    Err(String::from("Not implemented"))
}

/// Parse term into ast.
///
/// term ::= factor | term ( '*' | '/' ) ? factor
///
/// If no opertor separaters the term from the factor, a * should be inserted.
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index within `code` representing a point after the last token processed.
///
/// " Examples
///
/// ```
/// let code = "32x / 5 * 2";
/// let mut i: usize = 0;
/// let _ = parse_term(code, &mut i).unwrap();
/// ```
///
pub fn parse_term(_code: &str, _i: &mut usize) -> Result<Term, String> {
    // TODO - implement function

    Err(String::from("Not implemented"))
}

/// Parse factor into ast.
///
/// factor ::= '-' ? '(' expression ')' | number | identifier | call
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index within `code` representing a point after the last token processed.
/// * `preceding_identifier` - true iff last token was an identifier
///
/// # Errors
/// * "Unexpected ')'" - A ) was found while not parsing a parenthetical
/// * "Unclosed '('" - End of input reached and no closing ')' found
///
/// " Examples
///
/// ```
/// let code = "(3x + 2)";
/// let mut i: usize = 0;
/// assert!(if let Factor::Parenthetical(_) = parse_factor(code, &mut i, false).unwrap() { true } else { false });
/// ```
///
/// ```
/// let code = "3";
/// let mut i: usize = 0;
/// assert!(if let Factor::Number(_) = parse_factor(code, &mut i, false).unwrap() { true } else { false });
/// ```
///
/// ```
/// let code = "a";
/// let mut i: usize = 0;
/// assert!(if let Factor::Identifier(_) = parse_factor(code, &mut i, false).unwrap() { true } else { false });
/// ```
///
/// ```
/// let code = "f(x)";
/// let mut i: usize = 0;
/// assert!(if let Factor::Call(_) = parse_factor(code, &mut i, false).unwrap() { true } else { false });
/// ```
///
pub fn parse_factor(
    _code: &str,
    _i: &mut usize,
    _preceding_identifier: bool,
) -> Result<Factor, String> {
    // TODO - implement function

    // NOTE - if the first token is '-' as the grammar allows, but it is not a negative number,
    // ensure that the next token is NOT '-' as well (if it is, return an Err()), then return -1

    // NOTE - a call with one argument is hard to parse, since f(x) could be
    // parsed as f*x. To resolve this, only check for it if preceding_identifier
    // is false. (in that, only the current identifier would be the name of the
    // function)
    //
    // If this is an issue for the user, they can insert a * to be explicit.

    Err(String::from("Not implemented"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_statement_test1() {
        let code = "3x + 2 = 7";
        let mut i: usize = 0;
        let _ = parse_statement(code, &mut i).unwrap();
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_function_test1() {
        let code = "f(x) = 3x + 2";
        let mut i: usize = 0;
        let _ = parse_function(code, &mut i).unwrap();
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_function_test2() {
        let code = "f(x) = {\n\
            \t3x,     x < 3\n\
            \t2x + 3, x ≥ 3\n\
            }";
        let mut i: usize = 0;
        let _ = parse_function(code, &mut i).unwrap();
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_relation_test1() {
        let code = "2y + 7 = 3x + 2";
        let mut i: usize = 0;
        let _ = parse_relation(code, &mut i).unwrap();
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_expression_test1() {
        let code = "32x + 2ab";
        let mut i: usize = 0;
        let _ = parse_expression(code, &mut i).unwrap();
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_term_test1() {
        let code = "32x / 5 * 2";
        let mut i: usize = 0;
        let _ = parse_term(code, &mut i).unwrap();
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_factor_test1() {
        let code = "(3x + 2)";
        let mut i: usize = 0;
        assert!(
            if let Factor::Parenthetical(_) = parse_factor(code, &mut i, false).unwrap() {
                true
            } else {
                false
            }
        );
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_factor_test2() {
        let code = "3";
        let mut i: usize = 0;
        assert!(
            if let Factor::Number(_) = parse_factor(code, &mut i, false).unwrap() {
                true
            } else {
                false
            }
        );
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_factor_test3() {
        let code = "a";
        let mut i: usize = 0;
        assert!(
            if let Factor::Identifier(_) = parse_factor(code, &mut i, false).unwrap() {
                true
            } else {
                false
            }
        );
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_factor_test4() {
        let code = "f(x)";
        let mut i: usize = 0;
        assert!(
            if let Factor::Call(_) = parse_factor(code, &mut i, false).unwrap() {
                true
            } else {
                false
            }
        );
        assert!(i == code.chars().count())
    }

    #[test]
    fn parse_factor_test5() {
        let code = "af(x)";
        let mut i: usize = 1;
        assert!(
            if let Factor::Identifier(_) = parse_factor(code, &mut i, true).unwrap() {
                true
            } else {
                false
            }
        );
        assert!(i == 2)
    }
}
