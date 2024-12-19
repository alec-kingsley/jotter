// statement   ::=   prompt | function | relation
// function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' 'if' relation '\n' ) + '}' )
// prompt      ::=   relation '?'
// relation    ::=   expression | relation ( '<' | '>' | '<=' | '≤' | '>=' | '≥' | '=' | '<>' | '≠'  ) expression
// expression  ::=   term (( '+' | '-' ) term ) *
// term        ::=   factor (( '*' | '/' ) ? factor ) *
// factor      ::=   '(' expression ')' | number | identifier | call
// call        ::=   identifier '(' expression ( ',' expression ) * ')'
// number      ::=   ( '0' | [1-9][0-9]* ) ( '.' [0-9]+ ) ? ( '[' unit ']' ) ?
// unit        ::=   ( baseunit ( '^' [1-9][0-9]* ) ? )+ ( '/' ( baseunit ( '^' [1-9][0-9]* ) ? )+ ) ?
// baseunit    ::=   [a-zA-Zα-ωΑ-Ω]+
// identifier  ::=   ( [a-zA-Zα-ωΑ-Ω] | '\'' [a-zA-Z0-9_ ]+ '\'' )

use regex::Regex;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::ops::*;

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
    // can be + or -
    pub operators: Vec<String>,
}

impl Expression {
    /// "flatten" the `Expression`.
    ///
    /// remove a many parentheticals as possible, such that it's just a sum of terms.
    /// combine like terms.
    ///
    fn flatten(&mut self) {
        for _self_i in 0..self.operands.len() {
            // TODO - multiply/divide through the factors in the term

            // TODO - if it's a singular parenthetical {

            // TODO - flatten contents of parenthetical

            // TODO - add flattened paranthetical contents to father expression

            // } TODO - else if it has a parenthetical denominator {
            
            // TODO - flatten contents of parenthetical denominator

            // }
        }
    }
}

impl Add for Expression {
    type Output = Self;

    /// Operator overload for +.
    ///
    fn add(self, other: Self) -> Self {
        assert!(self.operands.len() > 0);
        assert!(other.operands.len() > 0);
        let mut result = self.clone();
        for operand in &other.operands {
            result.operands.push(operand.clone());
        }
        result.operators.push(String::from("+"));
        for operator in &other.operators {
            result.operators.push(operator.clone());
        }
        result
    }
}

impl AddAssign for Expression {
    /// Operator overload for +=.
    ///
    fn add_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() + other));
    }
}

impl Sub for Expression {
    type Output = Self;

    /// Operator overload for -.
    ///
    fn sub(self, other: Self) -> Self {
        assert!(self.operands.len() > 0);
        assert!(other.operands.len() > 0);
        let mut result = self.clone();
        for operand in &other.operands {
            result.operands.push(operand.clone());
        }
        result.operators.push(String::from("-"));
        for operator in &other.operators {
            result.operators.push(if operator == "-" {
                String::from("+")
            } else {
                String::from("-")
            });
        }
        result
    }
}

impl SubAssign for Expression {
    /// Operator overload for -=.
    ///
    fn sub_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() - other));
    }
}

impl Mul for Expression {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut result = Expression {
            operands: Vec::new(),
            operators: Vec::new(),
        };
        for self_i in 0..self.operands.len() {
            for other_i in 0..other.operands.len() {
                result
                    .operands
                    .push(self.operands[self_i].clone() * other.operands[other_i].clone());
                result.operators.push(
                    // determine if it should be added or subtracted
                    if (if self_i > 0 {
                        self.operators[self_i - 1].clone()
                    } else {
                        String::from("+")
                    }) == (if other_i > 0 {
                        other.operators[other_i - 1].clone()
                    } else {
                        String::from("+")
                    }) {
                        String::from("+")
                    } else {
                        String::from("-")
                    },
                )
            }
        }
        result
    }
}

impl MulAssign for Expression {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Div for Expression {
    type Output = Self;

    /// Operator overload for /.
    ///
    /// Just take every term and divide it by `other` thrown in a parenthetical.
    /// Don't wanna think about math. Dividing by an expression is hard.
    ///
    fn div(self, other: Self) -> Self {
        let mut result = self.clone();
        for self_i in 0..self.operands.len() {
            result.operands[self_i]
                .operands
                .push(Factor::Parenthetical(other.clone()));
            result.operands[self_i].operators.push(String::from("/"));
        }
        result
    }
}

impl DivAssign for Expression {
    /// Operator overload for /=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Term {
    pub operands: Vec<Factor>,
    // can be *, /
    pub operators: Vec<String>,
}

impl Neg for Term {
    type Output = Self;

    fn neg(self) -> Self {
        assert!(self.operands.len() > 0);
        let mut result = self.clone();
        result.operators.push(String::from("*"));
        result.operands.push(Factor::Number(Number {
            value: -1f64,
            unit: Unit {
                exponent: 0,
                constituents: HashMap::new(),
            },
        }));
        result
    }
}

impl Mul for Term {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        for operand in &other.operands {
            result.operands.push(operand.clone());
        }
        if result.operators.len() > 0 {
            result.operators.push(String::from("*"));
        }
        for operator in &other.operators {
            result.operators.push(operator.clone());
        }
        result
    }
}

impl MulAssign for Term {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Factor {
    Parenthetical(Expression),
    Number(Number),
    Identifier(Identifier),
    Call(Call),
}

impl Mul for Factor {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut result: Option<Factor> = None;
        if let Factor::Number(self_number) = self.clone() {
            if let Factor::Number(other_number) = other.clone() {
                result = Some(Factor::Number(self_number * other_number));
            }
        }
        if result == None {
            result = Some(
                if let Factor::Parenthetical(self_expression) = self.clone() {
                    if let Factor::Parenthetical(other_expression) = other.clone() {
                        Factor::Parenthetical(self_expression * other_expression)
                    } else {
                        Factor::Parenthetical(
                            self_expression
                                * Expression {
                                    operands: vec![Term {
                                        operands: vec![other],
                                        operators: Vec::new(),
                                    }],
                                    operators: Vec::new(),
                                },
                        )
                    }
                } else if let Factor::Parenthetical(other_expression) = other.clone() {
                    Factor::Parenthetical(
                        other_expression
                            * Expression {
                                operands: vec![Term {
                                    operands: vec![other],
                                    operators: Vec::new(),
                                }],
                                operators: Vec::new(),
                            },
                    )
                } else {
                    Factor::Parenthetical(Expression {
                        operands: vec![Term {
                            operands: vec![self, other],
                            operators: vec![String::from("*")],
                        }],
                        operators: Vec::new(),
                    })
                },
            );
        }
        result.unwrap()
    }
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

#[derive(Debug, Clone)]
pub struct Unit {
    // power of 10 unit is multiplied by
    pub exponent: i8,
    // map of base units to the power they're raised to
    // if map is missing a key, it's assumed to be to power of 0
    pub constituents: HashMap<BaseUnit, i8>,
}

// Implement PartialEq for Unit
impl PartialEq for Unit {
    fn eq(&self, other: &Self) -> bool {
        let mut result = false;
        if self.exponent == other.exponent && self.constituents.len() == other.constituents.len() {
            for key in self.constituents.keys() {
                result &= self.constituents.get(&key) == other.constituents.get(&key);
            }
        }
        result
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BaseUnit {
    Meter,    // m
    Kilogram, // kg
    Second,   // s
    Ampere,   // A
    Kelvin,   // K
    Mole,     // mol
    Candela,  // cd
}

impl Add for Number {
    type Output = Self;

    /// Operator overload for +.
    ///
    fn add(self, other: Self) -> Self {
        assert!(self.unit == other.unit, "Mismatched types");
        Self {
            value: self.value + other.value,
            unit: self.unit,
        }
    }
}

impl AddAssign for Number {
    /// Operator overload for +=.
    ///
    fn add_assign(&mut self, other: Self) {
        // only add if the other is not equal to 0
        // reason for this is that 0m/s + 3m would sensibly be 3m, even though
        // (m/s + m) is not a valid unit.
        //
        // this does not apply to plus by itself since it's not obvious which should
        // be prioritized.
        if other.value != 0f64 {
            self.clone_from(&(self.clone() + other));
        }
    }
}

impl Sub for Number {
    type Output = Self;

    /// Operator overload for -.
    ///
    fn sub(self, other: Self) -> Self {
        assert!(self.unit == other.unit, "Mismatched types");
        Self {
            value: self.value - other.value,
            unit: self.unit,
        }
    }
}

impl SubAssign for Number {
    /// Operator overload for -=.
    ///
    fn sub_assign(&mut self, other: Self) {
        // only subtract if the other is not equal to 0
        // reason for this is that 3m/s - 0m would sensibly be 3m/s, even though
        // (m/s - m) is not a valid unit.
        //
        // this does not apply to minus by itself since it's not obvious which should
        // be prioritized.
        if other.value != 0f64 {
            self.clone_from(&(self.clone() - other));
        }
    }
}

impl Mul for Number {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut constituents = self.unit.constituents;
        for (base_unit, power) in other.unit.constituents {
            *constituents.entry(base_unit).or_insert(0) += power;
        }
        Self {
            value: self.value * other.value,
            unit: Unit {
                exponent: self.unit.exponent + other.unit.exponent,
                constituents,
            },
        }
    }
}

impl MulAssign for Number {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Div for Number {
    type Output = Self;

    /// Operator overload for /.
    ///
    fn div(self, other: Self) -> Self {
        let mut constituents = self.unit.constituents;
        for (base_unit, power) in other.unit.constituents {
            *constituents.entry(base_unit).or_insert(0) -= power;
        }
        Self {
            value: self.value / other.value,
            unit: Unit {
                exponent: self.unit.exponent - other.unit.exponent,
                constituents,
            },
        }
    }
}

impl DivAssign for Number {
    /// Operator overload for /=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    value: String,
}

impl Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Identifier {
    /// Initializes an `Identifier` by checking it against a regex.
    ///
    /// # Arguments
    /// * `value` - The string to represent an identifier.
    ///
    /// # Returns
    /// An initialized identifier.
    ///
    /// # Errors
    /// * "Invalid identifier" - identifier did not match regex.
    ///
    pub fn new(value: &str) -> Result<Self, String> {
        if Regex::new(r"^([a-zA-Zα-ωΑ-Ω]|'[a-zA-Z0-9_ ]+')$")
            .unwrap()
            .is_match(value)
        {
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
