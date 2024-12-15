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
/// If the token is a series of more than ten -'s in a row, it should return only 10
/// (----------)
///
/// # Errors
/// * "Unterminated comment" - A comment (starting with '(*' ) had no ending ( ')' )
/// * "Unterminated named identifier" - A named identifier (starting with '\'') had no matching
/// '\''
///
fn next_token(_code: &str, _i: &mut usize) -> Result<String, String> {
    // TODO - implement function

    // NOTE - since some of our characters are outside ascii range, use code.chars().count() to get
    // length of code, not code.len()
    
    // NOTE - since \n separates statements and is in the grammar, it is a token. No other
    // whitespace is.
    
    Err(String::from("Not implemented"))
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
/// * "Unterminated comment" - A comment (starting with '(*' ) had no ending ( ')' )
/// * "Unexpected symbol" - A symbol was found that is unknown to the grammar
///
fn next_unit_token(_code: &str, _i: &mut usize) -> Result<String, String> {
    // TODO - implement function

    Err(String::from("Not implemented"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_token_test1() {
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
    fn next_token_test2() {
        let code = "(* comment )";

        assert_eq!(next_token(code, &mut 0).unwrap(), "(* comment )");
    }

    #[test]
    fn next_token_test3() {
        let code = "(* bad comment";

        assert_eq!(next_token(code, &mut 0).unwrap_err(), "Unterminated comment");
    }

    #[test]
    fn next_token_test4() {
        let code = "'name";

        assert_eq!(next_token(code, &mut 0).unwrap_err(), "Unterminated named identifier");
    }

    #[test]
    fn next_token_test5() {
        let code = "3x + 'myNamedVar' - 801 * 2 = 12";
        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "3");
        assert_eq!(next_token(code, &mut i).unwrap(), "x");
        assert_eq!(next_token(code, &mut i).unwrap(), "'myNamedVar'");
        assert_eq!(next_token(code, &mut i).unwrap(), "-");
        assert_eq!(next_token(code, &mut i).unwrap(), "801");
        assert_eq!(next_token(code, &mut i).unwrap(), "*");
        assert_eq!(next_token(code, &mut i).unwrap(), "2");
        assert_eq!(next_token(code, &mut i).unwrap(), "=");
        assert_eq!(next_token(code, &mut i).unwrap(), "12");
    }

    #[test]
    fn next_token_test6() {
        let code = "≤ ≥ ≠";

        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "<=");
        assert_eq!(next_token(code, &mut i).unwrap(), ">=");
        assert_eq!(next_token(code, &mut i).unwrap(), "<>");
    }

    #[test]
    fn next_token_test7() {
        let code = "------------------------";

        assert_eq!(next_token(code, &mut 0).unwrap(), "----------");
    }
    
    #[test]
    fn next_token_test8() {
        let code = "(* (* nested comment ) )";

        assert_eq!(next_token(code, &mut 0).unwrap(), "(* (* nested comment ) )");
    }

    #[test]
    fn next_unit_token_test1() {
        let code = "(* comment )";

        assert_eq!(next_token(code, &mut 0).unwrap(), "(* comment )");
    }

    #[test]
    fn next_unit_token_test2() {
        let code = "(* bad comment";

        assert_eq!(next_token(code, &mut 0).unwrap_err(), "Unterminated comment");
    }

    #[test]
    fn next_unit_token_test3() {
        let code = "kg m/s^2";
        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "kg");
        assert_eq!(next_token(code, &mut i).unwrap(), "m");
        assert_eq!(next_token(code, &mut i).unwrap(), "/");
        assert_eq!(next_token(code, &mut i).unwrap(), "s");
        assert_eq!(next_token(code, &mut i).unwrap(), "^");
        assert_eq!(next_token(code, &mut i).unwrap(), "2");
    }

    #[test]
    fn next_unit_token_test4() {
        let code = "kilogram meter/second^2";
        let mut i: usize = 0;

        assert_eq!(next_token(code, &mut i).unwrap(), "kilogram");
        assert_eq!(next_token(code, &mut i).unwrap(), "meter");
        assert_eq!(next_token(code, &mut i).unwrap(), "/");
        assert_eq!(next_token(code, &mut i).unwrap(), "second");
        assert_eq!(next_token(code, &mut i).unwrap(), "^");
        assert_eq!(next_token(code, &mut i).unwrap(), "2");
    }
}

