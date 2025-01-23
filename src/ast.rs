use crate::math_structs::*;
use crate::tokenizer::*;
use crate::unit_parser::*;

use std::collections::HashMap;

/// Parse statement into ast.
///
/// statement ::= prompt | function | relation | reset
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
/// assert_eq!(i, code.chars().count())
/// ```
///
pub fn parse_statement(code: &str, i: &mut usize) -> Result<Statement, String> {
    // check if it's a function definiton
    let mut j = i.clone();
    let function_result = parse_function(code, &mut j);
    if function_result.is_ok() {
        *i = j;
        function_result
    } else if function_result.unwrap_err() == "Expected new line" {
        Err(String::from("Expected new line"))
    } else {
        let token = next_token(code, i)?;
        if token == ">" || token == "<" {
            if next_token(code, i).is_err() {
                Ok(Statement::StateSwitch(token == ">"))
            } else {
                Err(String::from(
                    "Line cannot begin with < or > without being < or >",
                ))
            }
        } else {
            *i -= token.chars().count();
            // keep i how it is, not a function definition
            let relation = parse_relation(code, i)?;
            // since it could be end of input, an Err could happen. In that case,
            // a default string won't be "?" so it's fine.
            if next_token(code, i).unwrap_or_default() == "?" {
                Ok(Statement::Prompt(relation))
            } else {
                Ok(Statement::Equation(relation))
            }
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
        return Err(String::from("Expected `(`"));
    }

    // parse arguments
    let mut arguments: Vec<Identifier> = Vec::new();
    while token != ")" {
        token = next_token(code, i)?;
        arguments.push(Identifier::new(token.as_str())?);
        // each identifier must have , or ) after it
        token = next_token(code, i)?;
        if ![",", ")"].contains(&token.as_str()) {
            return Err(String::from("Expected `,` or `)`"));
        }
    }
    if next_token(code, i)? != "=" {
        return Err(String::from("Expected `=`"));
    }

    // parse definition
    let mut definition: Vec<(Expression, Relation)> = Vec::new();
    token = next_token(code, i)?;
    if token == "{" {
        if next_token(code, i).unwrap_or_default() != "\n" {
            return Err(String::from("Expected new line"));
        }
        // need to consume one more token since back tracks
        token = next_token(code, i)?;
        while token != "}" {
            *i -= token.chars().count();
            // parse expression with comma after
            let expression = parse_expression(code, i)?;
            if next_token(code, i)? != "," {
                return Err(String::from("Expected `,`"));
            }

            // parse relation with new line after
            let relation = parse_relation(code, i)?;
            definition.push((expression, relation));
            if next_token(code, i).unwrap_or_default() != "\n" {
                return Err(String::from("Expected new line"));
            }
            token = next_token(code, i)?;
        }
    } else {
        *i -= token.chars().count();
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
pub fn parse_relation(code: &str, i: &mut usize) -> Result<Relation, String> {
    let mut result = Relation::from_expression(parse_expression(code, i)?);

    // setup map for `RelationOp`s
    let relation_op_map = HashMap::from([
        ("<", RelationOp::Less),
        (">", RelationOp::Greater),
        ("<=", RelationOp::LessEqual),
        (">=", RelationOp::GreaterEqual),
        ("=", RelationOp::Equal),
        ("<>", RelationOp::NotEqual),
    ]);

    // get each operand as long as `RelationOp`s are seen
    let mut relation_op_string = next_token(code, i).unwrap_or_default();
    while relation_op_map.contains_key(&relation_op_string.as_str()) {
        result.extend(
            relation_op_map
                .get(&relation_op_string.as_str())
                .unwrap()
                .clone(),
            parse_expression(code, i)?,
        );
        relation_op_string = next_token(code, i).unwrap_or_default();
    }
    *i -= relation_op_string.chars().count();

    Ok(result)
}

/// Parse expression into ast.
///
/// expression ::= term (( '+' | '-' ) term ) *
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
pub fn parse_expression(code: &str, i: &mut usize) -> Result<Expression, String> {
    let mut result = Expression::new();

    if next_token(code, &mut i.clone()).unwrap_or_default() == "-" {
        let _ = next_token(code, i);
        result -= parse_term(code, i)?;
    } else {
        result += parse_term(code, i)?;
    }

    // build minuend and subtrahend from - and + until none left seen
    let mut token = next_token(code, i).unwrap_or_default();
    while token == "+" || token == "-" {
        if token == "+" {
            result += parse_term(code, i)?;
        } else {
            result -= parse_term(code, i)?;
        }
        token = next_token(code, i).unwrap_or_default();
    }
    *i -= token.chars().count();

    Ok(result)
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
pub fn parse_term(code: &str, i: &mut usize) -> Result<Term, String> {
    let mut result = Term::new();

    let mut preceding_identifier = false;
    let factor = parse_factor(code, i, preceding_identifier)?;
    if let Factor::Identifier(_) = factor {
        preceding_identifier = true;
    }
    result *= factor;

    // build numerator and denominator from / and + and lack thereof until none left seen
    loop {
        let mut j = i.clone();
        let factor_result = parse_factor(code, &mut j, preceding_identifier);
        if factor_result.is_ok() {
            *i = j;
            let factor = factor_result.unwrap();
            preceding_identifier = if let Factor::Identifier(_) = factor {
                true
            } else {
                false
            };
            result *= factor;
        } else {
            preceding_identifier = false;
            let token = next_token(code, i).unwrap_or_default();
            if token == "*" || token == "/" {
                let factor = parse_factor(code, i, preceding_identifier)?;
                preceding_identifier = if let Factor::Identifier(_) = factor {
                    true
                } else {
                    false
                };
                if token == "*" {
                    result *= factor;
                } else {
                    result /= factor;
                }
            } else {
                *i -= token.chars().count();
                break;
            }
        }
    }

    Ok(result)
}

/// Parse factor into ast.
///
/// factor ::= '(' expression ')' | number | identifier | call
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
    code: &str,
    i: &mut usize,
    preceding_identifier: bool,
) -> Result<Factor, String> {
    let mut token = next_token(code, i)?;
    if token == "(" {
        let expression = parse_expression(code, i)?;
        if next_token(code, i)? != ")" {
            Err(String::from("Expected `)`"))
        } else {
            Ok(Factor::Parenthetical(expression))
        }
    } else if token.parse::<f64>().is_ok() || token == "i" || token == "[" {
        let value = if token == "i" {
            *i -= "i".chars().count();
            1f64
        } else if token == "[" {
            *i -= "[".chars().count();
            1f64
        } else {
            token.parse::<f64>().unwrap()
        };
        let mut j = i.clone();
        let is_imaginary = if next_token(code, &mut j).is_ok_and(|token| token == "i") {
            *i = j;
            true
        } else {
            false
        };
        let mut j = i.clone();
        let value = if next_token(code, &mut j).is_ok_and(|token| token == "%") {
            *i = j;
            value / 100.0
        } else {
            value
        };
        let mut j = i.clone();
        let unit_result = parse_unit(code, &mut j);
        if unit_result.is_ok() {
            *i = j;
            let (unit, factor) = unit_result.unwrap();
            Ok(Factor::Number(
                if is_imaginary {
                    Value::from(value * factor).i()
                } else {
                    Value::from(value * factor)
                }
                .with_unit(unit),
            ))
        } else {
            let mut j = i.clone();
            if next_token(code, &mut j).is_ok_and(|token| token == "[") {
                return Err(String::from("Expected unit"));
            }
            Ok(Factor::Number(if is_imaginary {
                Value::from(value).i()
            } else {
                Value::from(value)
            }))
        }
    } else {
        // must be an identifier, could be for a variable or a call.
        let name = Identifier::new(token.as_str())?;

        // a call with one argument is hard to parse, since f(x) could be
        // parsed as f*x. To resolve this, only check for it if preceding_identifier
        // is false. (in that, only the current identifier would be the name of the
        // function)
        //
        if preceding_identifier || next_token(code, &mut i.clone()).unwrap_or_default() != "(" {
            Ok(Factor::Identifier(name))
        } else {
            let _ = next_token(code, i);
            let mut arguments: Vec<Expression> = Vec::new();
            while token != ")" {
                arguments.push(parse_expression(code, i)?);
                token = next_token(code, i)?;
                if token != "," && token != ")" {
                    return Err(String::from("Expected `,` or `)`"));
                }
            }
            Ok(Factor::Call(Call { name, arguments }))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_statement_1() {
        let code = "3x + 2 = 7";
        let mut i: usize = 0;
        let statement = parse_statement(code, &mut i).unwrap();
        println!("{code} == {statement}");
        assert_eq!(i, code.chars().count());
    }

    #[test]
    fn test_parse_function_1() {
        let code = "f(x) = 3x + 2";
        let mut i: usize = 0;
        let function = parse_function(code, &mut i).unwrap();
        println!("{code} == {function}");
        assert_eq!(i, code.chars().count());
    }

    #[test]
    fn test_parse_function_2() {
        let code = "f(x) = {\n\
            \t3x,     x < 3\n\
            \t2x + 3, x ≥ 3\n\
            }";
        let mut i: usize = 0;
        let function = parse_function(code, &mut i).unwrap();
        println!("{code} == {function}");
        assert_eq!(i, code.chars().count());
    }

    #[test]
    fn test_parse_relation_1() {
        let code = "2y + 7 = 3x + 2";
        let mut i: usize = 0;
        let relation = parse_relation(code, &mut i).unwrap();
        println!("{code} == {relation}");
        assert_eq!(i, code.chars().count());
    }

    #[test]
    fn test_parse_expression_1() {
        let code = "32x + 2ab";
        let mut i: usize = 0;
        let expression = parse_expression(code, &mut i).unwrap();
        println!("{code} == {expression}");
        assert_eq!(i, code.chars().count());
    }

    #[test]
    fn test_parse_expression_2() {
        let code = "y - x";
        let mut i: usize = 0;
        let expression = parse_expression(code, &mut i).unwrap();
        println!("{code} == {expression}");
        assert_eq!(i, code.chars().count());
    }

    #[test]
    fn test_parse_term_1() {
        let code = "32x / 5 * 2";
        let mut i: usize = 0;
        let term = parse_term(code, &mut i).unwrap();
        println!("{code} == {term}");
        assert_eq!(i, code.chars().count());
    }

    #[test]
    fn test_parse_factor_1() {
        let code = "(3x + 2)";
        let mut i: usize = 0;
        let factor = parse_factor(code, &mut i, false).unwrap();
        println!("{code} == {factor}");
        assert!(if let Factor::Parenthetical(_) = factor {
            true
        } else {
            false
        });
        assert_eq!(i, code.chars().count())
    }

    #[test]
    fn test_parse_factor_2() {
        let code = "3";
        let mut i: usize = 0;
        let factor = parse_factor(code, &mut i, false).unwrap();
        println!("{code} == {factor}");
        assert!(if let Factor::Number(_) = factor {
            true
        } else {
            false
        });
        assert_eq!(i, code.chars().count())
    }

    #[test]
    fn test_parse_factor_3() {
        let code = "a";
        let mut i: usize = 0;
        let factor = parse_factor(code, &mut i, false).unwrap();
        println!("{code} == {factor}");
        assert!(if let Factor::Identifier(_) = factor {
            true
        } else {
            false
        });
        assert_eq!(i, code.chars().count())
    }

    #[test]
    fn test_parse_factor_4() {
        let code = "f(x)";
        let mut i: usize = 0;
        let factor = parse_factor(code, &mut i, false).unwrap();
        println!("{code} == {factor}");
        assert!(if let Factor::Call(_) = factor {
            true
        } else {
            false
        });
        assert_eq!(i, code.chars().count())
    }

    #[test]
    fn test_parse_factor_5() {
        let code = "af(x)";
        let mut i: usize = 1;
        let factor = parse_factor(code, &mut i, true).unwrap();
        println!("f(x) == {factor}");
        assert!(if let Factor::Identifier(_) = factor {
            true
        } else {
            false
        });
        assert_eq!(i, 2)
    }
}
