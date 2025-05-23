/// Returns true if the substring is at pos i
///
/// # Arguments
/// * `code` - String to look in
/// * `i` - Index to start at
/// * `substring` - Substring to compare against
///
/// # Returns
/// True if the substring is at position i in code
///
fn substring_at_pos(code: &str, i: usize, substring: &str) -> bool {
    let mut result = false;

    // only test if there's space for the substring in the first place
    if substring.chars().count() <= code.chars().count() - i {
        result = true;
        for c in 0..substring.chars().count() {
            if code.chars().nth(i + c) != substring.chars().nth(c) {
                result = false;
            }
        }
    }
    result
}

/// Returns true iff there is whitespace that is not in the language at pos
///
/// # Arguments
/// * `code` - Code to look in
/// * `i` - Index to observe
///
/// # Returns
/// True iff there is irrelevant whitespace at i
///
fn whitespace_at_pos(code: &str, i: usize) -> bool {
    // NOTE - since \n separates statements and is in the grammar, it is a token. No other
    // whitespace

    let char_test = code.chars().nth(i).unwrap();

    char_test == ' ' || char_test == '\t'
}

/// Moves forward the start index infront of any irrelevant whitespace or comments.
///
/// # Arguments
/// * `code` - Code to look in
/// * `i` - Index to move
///
/// # Updates
/// `i` - Set infront of any whitespace or comments in `code`
///
/// # Returns
/// Ok if there are no syntax errors while handling comments
/// Err if there are errors or if method is called where no tokens present
///
/// # Errors
/// "Unterminated comment" - A comment (starting with '(*' ) had no ending ( '*)' )
/// "Not found" - The next token does not exist
///
fn skip_whitespace_and_comments(code: &str, i: &mut usize) -> Result<String, String> {
    let code_length = code.chars().count();

    if *i >= code_length {
        return Err(String::from("Not found"));
    }
    // skip all comments and irrelevant whitespace
    while whitespace_at_pos(code, *i) || substring_at_pos(code, *i, "(*") {
        *i += 1;
        if !whitespace_at_pos(code, *i - 1) {
            // skip comment
            let mut bal = 1;
            while bal != 0 {
                *i += 1;
                if *i >= code_length {
                    return Err(String::from("Unterminated comment"));
                }
                if substring_at_pos(code, *i, "(*") {
                    bal += 1;
                    *i += 1;
                } else if substring_at_pos(code, *i, "*)") {
                    bal -= 1;
                    *i += 1;
                }
            }
            *i += 1;
        }
        if *i >= code_length {
            return Err(String::from("Not found"));
        }
    }

    Ok(String::from("Skipped whitespace and comments"))
}

/// Retrieves the next token in `code` starting at index `i`, and updates `i` accordingly.
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index in `code` representing where to start searching.
///
/// # Updates
/// * `i` - Set to 1 past end of returned token. Only updated if Ok() returned.
///
/// # Returns
/// Returns the token starting at index `i` in the string `code` (if found).
/// If not found, returns an error.
/// If token is a nickname (such as ≤ for <=), replaces with the more accessible one to type. (in
/// that case <= for example)
///
/// # Errors
/// * "Unterminated comment" - A comment (starting with '(*' ) had no ending ( '*)' )
/// * "Unterminated named identifier" - A named identifier (starting with '\'') had no matching
/// '\''
///
pub fn next_token(code: &str, i: &mut usize) -> Result<String, String> {
    // NOTE - since some of our characters are outside ascii range, functions like
    // code.len() are not allowed. Nor is indexing directly with things like code[i]

    let code_length = code.chars().count();

    if *i >= code_length {
        return Err(String::from("Not found"));
    }

    skip_whitespace_and_comments(code, i)?;

    let start_pos = *i;

    if code.chars().nth(*i).unwrap().is_digit(10) || code.chars().nth(*i).unwrap() == '.' {
        // numeric literal
        let mut seen_dot = code.chars().nth(*i).unwrap() == '.';
        *i += 1;
        while *i < code_length
            && (code.chars().nth(*i).unwrap().is_digit(10)
                || (!seen_dot && code.chars().nth(*i).unwrap() == '.'))
        {
            seen_dot |= code.chars().nth(*i).unwrap() == '.';
            *i += 1;
        }
        Ok(code.chars().skip(start_pos).take(*i - start_pos).collect())
    } else if code.chars().nth(*i).unwrap() == '\'' {
        // named identifier
        *i += 1;
        let mut terminated = false;
        while *i < code_length && !terminated {
            let c = code.chars().nth(*i).unwrap();
            terminated |= c == '\'';
            if c == '\n' {
                return Err(String::from("Unterminated named identifier"));
            }
            *i += 1;
        }
        if !terminated {
            return Err(String::from("Unterminated named identifier"));
        }
        Ok(code.chars().skip(start_pos).take(*i - start_pos).collect())
    } else if substring_at_pos(code, *i, "<=")
        || substring_at_pos(code, *i, ">=")
        || substring_at_pos(code, *i, "<>")
    {
        // multichar token
        *i += 2;
        Ok(code.chars().skip(start_pos).take(*i - start_pos).collect())
    } else if substring_at_pos(code, *i, "≤") {
        // nickname <=
        *i += 1;
        Ok(String::from("<="))
    } else if substring_at_pos(code, *i, "≥") {
        // nickname >=
        *i += 1;
        Ok(String::from(">="))
    } else if substring_at_pos(code, *i, "≠") {
        // nickname <>
        *i += 1;
        Ok(String::from("<>"))
    } else {
        // single char
        *i += 1;
        Ok(code.chars().skip(start_pos).take(*i - start_pos).collect())
    }
}

/// Retrieves the next "unit" token in `code` starting at index `i`, and updates `i` accordingly.
/// Since the grammar for units is so different, it requires its own tokenizer.
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index in `code` representing where to start searching.
///
/// # Updates
/// * `i` - Set to 1 past end of returned token. Only updated if Ok() returned.
///
/// # Returns
/// Returns the token starting at index `i` in the string `code` (if found).
/// If not found, returns an error.
///
/// # Errors
/// * "Unterminated comment" - A comment (starting with '(*' ) had no ending ( '*)' )
/// * "Unexpected symbol" - A symbol was found that is unknown to the grammar
///
pub fn next_unit_token(code: &str, i: &mut usize) -> Result<String, String> {
    let code_length = code.chars().count();
    if *i >= code_length {
        return Err(String::from("Not found"));
    }

    skip_whitespace_and_comments(code, i)?;

    let start_pos = *i;

    let special_characters = ['/', '*', '[', ']', '^', '-'];

    // special characters
    if special_characters.contains(&code.chars().nth(*i).unwrap()) {
        *i += 1;
        Ok(code.chars().skip(start_pos).take(*i - start_pos).collect())
    } else if code.chars().nth(*i).unwrap().is_digit(10) || code.chars().nth(*i).unwrap() == '-' {
        // number
        while *i < code_length && code.chars().nth(*i).unwrap().is_digit(10) {
            *i += 1;
        }

        Ok(code.chars().skip(start_pos).take(*i - start_pos).collect())
    } else {
        // units
        while *i < code_length
            && !special_characters.contains(&code.chars().nth(*i).unwrap())
            && !whitespace_at_pos(code, *i)
            && !code.chars().nth(*i).unwrap().is_digit(10)
        {
            *i += 1;
        }

        Ok(code.chars().skip(start_pos).take(*i - start_pos).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_token_1() {
        let code = "3x + 20\n";

        assert_eq!(next_token(code, &mut 0).unwrap(), "3");

        assert_eq!(next_token(code, &mut 1).unwrap(), "x");

        assert_eq!(next_token(code, &mut 2).unwrap(), "+");
        assert_eq!(next_token(code, &mut 3).unwrap(), "+");

        assert_eq!(next_token(code, &mut 4).unwrap(), "20");
        assert_eq!(next_token(code, &mut 5).unwrap(), "20");
        assert_eq!(next_token(code, &mut 6).unwrap(), "0");
    }

    #[test]
    fn test_next_token_2() {
        let code = "(* comment *) 1";

        assert_eq!(next_token(code, &mut 0).unwrap(), "1");
    }

    #[test]
    fn test_next_token_3() {
        let code = "(* bad comment";

        assert_eq!(
            next_token(code, &mut 0).unwrap_err(),
            "Unterminated comment"
        );
    }

    #[test]
    fn test_next_token_4() {
        let code = "'name";

        assert_eq!(
            next_token(code, &mut 0).unwrap_err(),
            "Unterminated named identifier"
        );
    }

    #[test]
    fn test_next_token_test_5() {
        let code = "3x + 'myNamedVar' - 801 * 2 = 12";
        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "3");
        assert_eq!(next_token(code, &mut i).unwrap(), "x");
        assert_eq!(next_token(code, &mut i).unwrap(), "+");
        assert_eq!(next_token(code, &mut i).unwrap(), "'myNamedVar'");
        assert_eq!(next_token(code, &mut i).unwrap(), "-");
        assert_eq!(next_token(code, &mut i).unwrap(), "801");
        assert_eq!(next_token(code, &mut i).unwrap(), "*");
        assert_eq!(next_token(code, &mut i).unwrap(), "2");
        assert_eq!(next_token(code, &mut i).unwrap(), "=");
        assert_eq!(next_token(code, &mut i).unwrap(), "12");
    }

    #[test]
    fn test_next_token_6() {
        let code = "≤ ≥ ≠";

        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "<=");
        assert_eq!(next_token(code, &mut i).unwrap(), ">=");
        assert_eq!(next_token(code, &mut i).unwrap(), "<>");
    }

    #[test]
    fn test_next_token_7() {
        let code = "(* (* nested comment *) *) 5";

        assert_eq!(next_token(code, &mut 0).unwrap(), "5");
    }

    #[test]
    fn test_next_token_8() {
        let code = "(* comment1 *) (* comment2 *) 5";

        assert_eq!(next_token(code, &mut 0).unwrap(), "5");
    }

    #[test]
    fn test_next_token_9() {
        let code = "1.73 + 1.8 * .9 * 1.749.3";

        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "1.73");
        assert_eq!(next_token(code, &mut i).unwrap(), "+");
        assert_eq!(next_token(code, &mut i).unwrap(), "1.8");
        assert_eq!(next_token(code, &mut i).unwrap(), "*");
        assert_eq!(next_token(code, &mut i).unwrap(), ".9");
        assert_eq!(next_token(code, &mut i).unwrap(), "*");
        assert_eq!(next_token(code, &mut i).unwrap(), "1.749");
        assert_eq!(next_token(code, &mut i).unwrap(), ".3");
    }

    #[test]
    fn test_next_token_10() {
        // no whitespace
        let code = "5≤7";

        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "5");
        assert_eq!(next_token(code, &mut i).unwrap(), "<=");
        assert_eq!(next_token(code, &mut i).unwrap(), "7");
    }


    #[test]
    fn test_next_unit_token_1() {
        let code = "(* comment *) kg";

        assert_eq!(next_unit_token(code, &mut 0).unwrap(), "kg");
    }

    #[test]
    fn test_next_unit_token_2() {
        let code = "(* bad comment";

        assert_eq!(
            next_unit_token(code, &mut 0).unwrap_err(),
            "Unterminated comment"
        );
    }

    #[test]
    fn test_next_unit_token_3() {
        let code = "kg m/s^2";
        let mut i: usize = 0;

        assert_eq!(next_unit_token(code, &mut i).unwrap(), "kg");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "m");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "/");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "s");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "^");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "2");
    }

    #[test]
    fn test_next_unit_token_4() {
        let code = "kilogram meter/second^2";
        let mut i: usize = 0;

        assert_eq!(next_unit_token(code, &mut i).unwrap(), "kilogram");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "meter");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "/");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "second");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "^");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "2");
    }

    #[test]
    fn test_next_unit_token_5() {
        let code = "kg^2μm^3";
        let mut i: usize = 0;

        assert_eq!(next_unit_token(code, &mut i).unwrap(), "kg");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "^");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "2");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "μm");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "^");
        assert_eq!(next_unit_token(code, &mut i).unwrap(), "3");
    }
}
