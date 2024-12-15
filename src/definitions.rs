// statement   ::=   prompt | function | relation
// function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' 'if' relation '\n' ) + '}' )
// prompt      ::=   relation '?'
// relation    ::=   expression | relation ( '<' | '>' | '<=' | '≤' | '>=' | '≥' | '=' | '<>' | '≠'  ) expression
// expression  ::=   term | expression ( '+' | '-' ) term
// term        ::=   factor | term ( '*' | '/' ) ? factor
// factor      ::=   '(' expression ')' | number | identifier | call
// call        ::=   identifier '(' expression ( ',' expression ) * ')'
// number      ::=   ( '0' | [1-9][0-9]* ) ( '.' [0-9]+ ) ? ( '[' unit ']' ) ?
// unit        ::=   ( baseunit ( '^' [1-9][0-9]* ) ? )+ ( '/' ( baseunit ( '^' [1-9][0-9]* ) ? )+ ) ?
// baseunit    ::=   [a-zA-Zα-ωΑ-Ω]+
// identifier  ::=   ( [a-zA-Zα-ωΑ-Ω] | '\'' [a-zA-Z0-9_ ]+ '\'' )

use regex::Regex;


#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Prompt(Relation),
    Equation(Relation),
    FunctionDefinition(Identifier, Vec<Identifier>, Vec<(Expression, Relation)>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Relation {
    pub operands: Vec<Expression>,
    pub operators: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    pub operands: Vec<Term>,
    pub operators: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Term {
    pub operands: Vec<Factor>,
    pub operators: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Factor {
    Parenthetical(Expression),
    Number(Number),
    Identifier(Identifier),
    Call(Call),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Call {
    pub name: Identifier,
    pub arguments: Vec<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Number {
    pub value: f64,
    pub unit: Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Unit {
    // power of 10 unit is multiplied by
    pub exponent: i8,
    pub numerator: Vec<BaseUnit>,
    pub denominator: Vec<BaseUnit>,

}

#[derive(Debug, Clone, PartialEq)]
pub enum BaseUnit {
    Meter,      // m
    Kilogram,   // kg
    Second,     // s
    Ampere,     // A
    Kelvin,     // K
    Mole,       // mol
    Candela,    // cd
}

#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    value: String,
}


impl Identifier {
    /// Initializes an Identifier by checking it against a regex.
    ///
    /// # Arguments
    /// * `value` - The string to represent an identifier.
    ///
    /// # Returns
    /// An initialized identifier.
    ///
    /// # Errors
    /// * "Invalid identifier" - identifier did not match regex.
    /// '\''
    ///
    pub fn new(value: &str) -> Result<Self, String> {
        if Regex::new(r"^([a-zA-Zα-ωΑ-Ω]|'[a-zA-Z0-9_ ]+')$").unwrap().is_match(value) {
            Ok(Self {
                value: value.to_string(),
            })
        } else {
            Err(String::from("Invalid identifier"))
        }
    }

    /// Returns the inner value
    pub fn value(&self) -> &str {
        &self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifier_test1() {
        let _ = Identifier::new("a").unwrap();
        let _ = Identifier::new("A").unwrap();
        let _ = Identifier::new("b").unwrap();
        let _ = Identifier::new("B").unwrap();
    }

    #[test]
    fn identifier_test2() { 
        let _ = Identifier::new("α").unwrap();
        let _ = Identifier::new("Α").unwrap();
        let _ = Identifier::new("β").unwrap();
        let _ = Identifier::new("Β").unwrap();
    }

    #[test]
    fn identifier_test3() { 
        let _ = Identifier::new("'name'").unwrap();
        let _ = Identifier::new("'name with spaces'").unwrap();
        let _ = Identifier::new("'name_with_underscores'").unwrap();
        let _ = Identifier::new("'NaM3_w1th_numb3rs'").unwrap();
    }

    #[test]
    fn identifier_test4() { 
        let _ = Identifier::new("ab").unwrap_err();
        let _ = Identifier::new("αβ").unwrap_err();
        let _ = Identifier::new("'unterminated").unwrap_err();
        let _ = Identifier::new("0").unwrap_err();
        let _ = Identifier::new("-").unwrap_err();
    }
}
