/// Retrieves the next token in `code` starting at index `i`.
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
}

