// statement   ::=   prompt | function | relation
// function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' relation '\n' ) + '}' )
// prompt      ::=   relation '?'
// relation    ::=   expression (( '<' | '>' | '<=' | '≤' | '>=' | '≥' | '=' | '<>' | '≠'  ) expression) *
// expression  ::=   term (( '+' | '-' ) term ) *
// term        ::=   factor (( '*' | '/' ) ? factor ) *
// factor      ::=   '-' ? '(' expression ')' | number | identifier | call
// call        ::=   identifier '(' expression ( ',' expression ) * ')'
// number      ::=   ( '0' | [1-9][0-9]* ) ( '.' [0-9]+ ) ? ( '[' unit ']' ) ?
// unit        ::=   ( baseunit ( '^' [1-9][0-9]* ) ? )+ ( '/' ( baseunit ( '^' [1-9][0-9]* ) ? )+ ) ?
// baseunit    ::=   [a-zA-Zα-ωΑ-Ω]+
// identifier  ::=   ( [a-zA-Zα-ωΑ-Ω] | '\'' [a-zA-Z0-9_ ]+ '\'' )

use regex::Regex;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Display;
use std::ops::*;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Prompt(Relation),
    Equation(Relation),
    /// name, arguments, actual function, and their relations.
    FunctionDefinition(Identifier, Vec<Identifier>, Vec<(Expression, Relation)>),
}

impl Display for Statement {
    /// Format `Statement` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Prompt(relation) => write!(f, "{} ?", relation),
            Statement::Equation(relation) => write!(f, "{} ?", relation),
            Statement::FunctionDefinition(name, arguments, details) => write!(
                f,
                "{}\n}}",
                details.iter().fold(
                    format!(
                        "{}({}) = {{",
                        name,
                        arguments
                            .iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    |acc, (expression, relation)| format!(
                        "{}\n\t{},\t{}",
                        acc, expression, relation
                    )
                )
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Relation {
    /// operands in relation.
    ///
    /// |operands| > 0
    pub operands: Vec<Expression>,

    /// operators which go between operands.
    ///
    /// |operators| = |operands| - 1
    pub operators: Vec<RelationOp>,
}

#[derive(Hash, Debug, Clone, PartialEq, Eq)]
pub enum RelationOp {
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual,
}

impl Display for Relation {
    /// Format `Relation` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let relational_ops_map = HashMap::from([
            (RelationOp::Less, String::from("<")),
            (RelationOp::Greater, String::from(">")),
            (RelationOp::LessEqual, String::from("≤")),
            (RelationOp::GreaterEqual, String::from("≥")),
            (RelationOp::Equal, String::from("=")),
            (RelationOp::NotEqual, String::from("≠")),
        ]);

        let mut result = String::new();
        for i in 0..self.operands.len() {
            if i > 0 {
                let operator = relational_ops_map.get(&self.operators[i - 1]).unwrap();
                result = format!("{} {} {}", result, operator, self.operands[i]);
            } else {
                result = format!("{}", self.operands[0]);
            }
        }
        write!(f, "{}", result)
    }
}

/// get a general true relation
///
pub fn get_true_relation() -> Relation {
    let zero = Expression {
        minuend: HashSet::from([Term {
            numerator: HashSet::from([Factor::Number(Number {
                value: 0f64,
                unit: Unit {
                    exponent: 0,
                    constituents: HashMap::new(),
                },
            })]),
            denominator: HashSet::new(),
        }]),
        subtrahend: HashSet::new(),
    };
    Relation {
        operands: vec![zero.clone(), zero.clone()],
        operators: vec![RelationOp::Equal],
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    /// operands to be added.
    ///
    pub minuend: HashSet<Term>,

    /// operands to be subtracted.
    ///
    pub subtrahend: HashSet<Term>,
}

impl Hash for Expression {
    /// Hash for an `Expression`.
    /// Necesarry since HashSet.hash() does not exist.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        for factor in &self.minuend {
            factor.hash(state);
        }
        for factor in &self.subtrahend {
            factor.hash(state);
        }
    }
}

impl Display for Expression {
    /// Format `Expression` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Format minuend elements, joined by `+`
        let minuend_str = self
            .minuend
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(" + ");

        // Format subtrahend elements, each preceded by `-`
        let subtrahend_str = self
            .subtrahend
            .iter()
            .map(|x| format!("-{}", x))
            .collect::<Vec<_>>()
            .join(" ");

        // Combine the two parts
        if subtrahend_str.is_empty() {
            write!(f, "{}", minuend_str)
        } else if minuend_str.is_empty() {
            write!(f, "{}", subtrahend_str)
        } else {
            write!(f, "{} {}", minuend_str, subtrahend_str)
        }
    }
}

impl Expression {
    /// "flatten" the `Expression`.
    ///
    /// remove a many parentheticals as possible, such that it's just a sum of terms.
    /// combine like terms.
    ///
    fn flatten(&mut self) {
        let mut father_expression = Expression {
            minuend: HashSet::new(),
            subtrahend: HashSet::new(),
        };

        for mut self_term in self.minuend.clone() {
            self_term.flatten();
            if let Factor::Parenthetical(mut child_expression) =
                self_term.numerator.drain().next().unwrap()
            {
                child_expression.flatten();
                for child_term in child_expression.minuend {
                    father_expression.minuend.insert(child_term.clone());
                }
                for child_term in child_expression.subtrahend {
                    father_expression.subtrahend.insert(child_term.clone());
                }
            }
        }

        for mut self_term in self.subtrahend.clone() {
            self_term.flatten();
            if let Factor::Parenthetical(mut child_expression) =
                self_term.numerator.drain().next().unwrap()
            {
                child_expression.flatten();
                for child_term in child_expression.minuend {
                    father_expression.subtrahend.insert(child_term.clone());
                }
                for child_term in child_expression.subtrahend {
                    father_expression.minuend.insert(child_term.clone());
                }
            }
        }
        self.clone_from(&father_expression);
    }

    /// Combine like terms in `Expression`.
    ///
    pub fn combine_like_terms(&mut self) {
        let mut numbers: Vec<Number> = Vec::new();
        let mut terms: Vec<Term> = Vec::new();

        // extract all terms with their numeric factor
        for mut self_term in self.minuend.clone() {
            let number = self_term.extract_number();
            numbers.push(number);
            terms.push(self_term);
        }

        for mut self_term in self.subtrahend.clone() {
            let number = self_term.extract_number();
            numbers.push(-number);
            terms.push(self_term);
        }

        // combine like terms
        for term_i in (0..numbers.len()).rev() {
            for term_j in ((term_i + 1)..terms.len()).rev() {
                if terms[term_i] == terms[term_j] {
                    numbers[term_i] = numbers[term_i].clone() + numbers[term_j].clone();
                    terms.remove(term_j);
                    numbers.remove(term_j);
                }
            }
        }

        // restore self
        let one = Number {
            value: 1f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };

        let zero = one.clone() - one.clone();

        self.minuend.clear();
        self.subtrahend.clear();
        for i in 0..numbers.len() {
            let number = numbers[i].clone();
            let mut operand = terms[i].clone();
            if number != one && number != -one.clone() {
                operand
                    .numerator
                    .insert(Factor::Number(if number > zero.clone() {
                        number.clone()
                    } else {
                        -number.clone()
                    }));
            }
            if number > zero.clone() {
                self.minuend.insert(operand);
            } else {
                self.subtrahend.insert(operand);
            }
        }
    }
}

impl Add for Expression {
    type Output = Self;

    /// Operator overload for +.
    ///
    fn add(self, other: Self) -> Self {
        let mut result = self.clone();
        for operand in &other.minuend {
            result.minuend.insert(operand.clone());
        }
        for operand in &other.subtrahend {
            result.subtrahend.insert(operand.clone());
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
        let mut result = self.clone();
        for operand in &other.minuend {
            result.subtrahend.insert(operand.clone());
        }
        for operand in &other.subtrahend {
            result.minuend.insert(operand.clone());
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
            minuend: HashSet::new(),
            subtrahend: HashSet::new(),
        };
        for self_term in self.minuend {
            for other_term in other.minuend.clone() {
                result.minuend.insert(self_term.clone() * other_term);
            }
            for other_term in other.subtrahend.clone() {
                result.subtrahend.insert(self_term.clone() * other_term);
            }
        }
        for self_term in self.subtrahend {
            for other_term in other.minuend.clone() {
                result.subtrahend.insert(self_term.clone() * other_term);
            }
            for other_term in other.subtrahend.clone() {
                result.minuend.insert(self_term.clone() * other_term);
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

        // Process `minuend`
        result.minuend = result
            .minuend
            .into_iter()
            .map(|mut result_term| {
                result_term
                    .denominator
                    .insert(Factor::Parenthetical(other.clone()));
                result_term
            })
            .collect();

        // Process `subtrahend`
        result.subtrahend = result
            .subtrahend
            .into_iter()
            .map(|mut result_term| {
                result_term
                    .denominator
                    .insert(Factor::Parenthetical(other.clone()));
                result_term
            })
            .collect();

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Term {
    /// operands being multiplied.
    ///
    pub numerator: HashSet<Factor>,

    /// operands being divided.
    ///
    pub denominator: HashSet<Factor>,
}

impl Hash for Term {
    /// Hash for a `Term`.
    /// Necesarry since HashSet.hash() does not exist.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        for factor in &self.numerator {
            factor.hash(state);
        }
        for factor in &self.denominator {
            factor.hash(state);
        }
    }
}

impl Display for Term {
    /// Format `Term` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Format numerator elements, joined by `*`
        let numerator_str = self
            .numerator
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(" * ");

        // Format denominator elements, joined by `*` (to be wrapped in parenthetical)
        let denominator_str = self
            .denominator
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(" * ");

        // Combine the two parts
        if denominator_str.is_empty() {
            write!(f, "{}", numerator_str)
        } else if numerator_str.is_empty() {
            write!(f, "1 / ({})", denominator_str)
        } else {
            write!(f, "{} / ({})", numerator_str, denominator_str)
        }
    }
}

impl Term {
    /// "flatten" the `Term`.
    ///
    /// remove a many parentheticals as possible, such that it's just a sum of terms.
    /// combine like terms.
    ///
    pub fn flatten(&mut self) {
        // initialize numerator and denominator to 1
        let mut numerator = Factor::Number(Number {
            value: 1f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        });
        let mut denominator = numerator.clone();

        for self_factor in self.numerator.clone() {
            if let Factor::Parenthetical(mut self_expression) = self_factor.clone() {
                self_expression.flatten();
                numerator *= Factor::Parenthetical(self_expression);
            } else {
                numerator *= self_factor;
            }
        }

        for self_factor in self.denominator.clone() {
            if let Factor::Parenthetical(mut self_expression) = self_factor.clone() {
                self_expression.flatten();
                denominator *= Factor::Parenthetical(self_expression);
            } else {
                denominator *= self_factor;
            }
        }

        self.clone_from(&Term {
            numerator: HashSet::from([numerator / denominator]),
            denominator: HashSet::new(),
        });
    }

    /// Extract the numeric factor of the `Term`.
    ///
    /// This can be called before comparing terms when combining like terms.
    ///
    pub fn extract_number(&mut self) -> Number {
        // initialize base variables
        let mut value = Number {
            value: 1f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            }
        };

        let mut new_term = Term {
            numerator: HashSet::new(),
            denominator: HashSet::new(),
        };

        // copy over operands
        for operand in self.numerator.clone() {
            if let Factor::Number(number) = operand {
                value *= number;
            } else {
                new_term.numerator.insert(operand);
            }
        }

        for operand in self.denominator.clone() {
            if let Factor::Number(number) = operand {
                value /= number;
            } else {
                new_term.denominator.insert(operand);
            }
        }

        self.clone_from(&new_term);
        value
    }
}

impl Neg for Term {
    type Output = Self;

    fn neg(self) -> Self {
        assert!(self.numerator.len() > 0);
        let mut result = self.clone();
        result.numerator.insert(Factor::Number(Number {
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
        for operand in &other.numerator {
            result.numerator.insert(operand.clone());
        }
        for operand in &other.denominator {
            result.denominator.insert(operand.clone());
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

#[derive(Hash, Debug, Clone)]
pub enum Factor {
    /// Expression within a parenthetical.
    Parenthetical(Expression),
    /// Numeric literal.
    Number(Number),
    /// Identifier (variable / constant name).
    Identifier(Identifier),
    /// Call to a function.
    Call(Call),
}

impl PartialEq for Factor {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        match self {
            Factor::Parenthetical(self_expression) => match other {
                Factor::Parenthetical(other_expression) => self_expression == other_expression,
                _ => false,
            },
            Factor::Number(self_number) => match other {
                Factor::Number(other_number) => self_number == other_number,
                _ => false,
            },
            Factor::Identifier(self_identifier) => match other {
                Factor::Identifier(other_identifier) => self_identifier == other_identifier,
                _ => false,
            },
            Factor::Call(self_call) => match other {
                Factor::Call(other_call) => self_call == other_call,
                _ => false,
            },
        }
    }
}

impl Eq for Factor {}

impl Display for Factor {
    /// Format `Factor` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Factor::Parenthetical(expression) => write!(f, "({})", expression),
            Factor::Number(number) => write!(f, "{}", number),
            Factor::Identifier(identifier) => write!(f, "{}", identifier),
            Factor::Call(call) => write!(f, "{}", call),
        }
    }
}

impl Factor {
    /// Returns true iff the factor is a number with value 1
    ///
    pub fn is_one(self) -> bool {
        if let Factor::Number(number) = self {
            number.is_one()
        } else {
            false
        }
    }

    /// Returns true iff the factor is a number with value 0
    ///
    pub fn is_zero(self) -> bool {
        if let Factor::Number(number) = self {
            number.is_zero()
        } else {
            false
        }
    }
}

impl Mul for Factor {
    type Output = Self;

    /// Operator overload for *.
    ///
    fn mul(self, other: Self) -> Self {
        let mut result: Option<Factor> = None;
        if self.clone().is_one() {
            result = Some(other.clone());
        } else if other.clone().is_one() {
            result = Some(self.clone());
        } else if let Factor::Number(self_number) = self.clone() {
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
                                    minuend: HashSet::from([Term {
                                        numerator: HashSet::from([other]),
                                        denominator: HashSet::new(),
                                    }]),
                                    subtrahend: HashSet::new(),
                                },
                        )
                    }
                } else if let Factor::Parenthetical(other_expression) = other.clone() {
                    Factor::Parenthetical(
                        other_expression
                            * Expression {
                                minuend: HashSet::from([Term {
                                    numerator: HashSet::from([other]),
                                    denominator: HashSet::new(),
                                }]),
                                subtrahend: HashSet::new(),
                            },
                    )
                } else {
                    Factor::Parenthetical(Expression {
                        minuend: HashSet::from([Term {
                            numerator: HashSet::from([self, other]),
                            denominator: HashSet::new(),
                        }]),
                        subtrahend: HashSet::new(),
                    })
                },
            );
        }
        result.unwrap()
    }
}

impl MulAssign for Factor {
    /// Operator overload for *=.
    ///
    fn mul_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() * other));
    }
}

impl Div for Factor {
    type Output = Self;

    /// Operator overload for /.
    ///
    fn div(self, other: Self) -> Self {
        let mut result: Option<Factor> = None;
        if self.clone().is_one() {
            result = Some(
                (Factor::Number(Number {
                    value: 1f64,
                    unit: Unit {
                        exponent: 0i8,
                        constituents: HashMap::new(),
                    },
                })) / other.clone(),
            );
        } else if other.clone().is_one() {
            result = Some(self.clone());
        } else if let Factor::Number(self_number) = self.clone() {
            if let Factor::Number(other_number) = other.clone() {
                result = Some(Factor::Number(self_number / other_number));
            }
        }
        if result == None {
            result = Some(
                if let Factor::Parenthetical(self_expression) = self.clone() {
                    if let Factor::Parenthetical(other_expression) = other.clone() {
                        Factor::Parenthetical(self_expression / other_expression)
                    } else {
                        Factor::Parenthetical(
                            self_expression
                                / Expression {
                                    minuend: HashSet::from([Term {
                                        numerator: HashSet::from([other]),
                                        denominator: HashSet::new(),
                                    }]),
                                    subtrahend: HashSet::new(),
                                },
                        )
                    }
                } else if let Factor::Parenthetical(other_expression) = other.clone() {
                    Factor::Parenthetical(
                        Expression {
                            minuend: HashSet::from([Term {
                                numerator: HashSet::from([other]),
                                denominator: HashSet::new(),
                            }]),
                            subtrahend: HashSet::new(),
                        } / other_expression,
                    )
                } else {
                    Factor::Parenthetical(Expression {
                        minuend: HashSet::from([Term {
                            numerator: HashSet::from([self]),
                            denominator: HashSet::from([other]),
                        }]),
                        subtrahend: HashSet::new(),
                    })
                },
            );
        }
        result.unwrap()
    }
}

impl DivAssign for Factor {
    /// Operator overload for *=.
    ///
    fn div_assign(&mut self, other: Self) {
        self.clone_from(&(self.clone() / other));
    }
}

#[derive(Hash, Debug, Clone)]
pub struct Call {
    /// Name of the function.
    pub name: Identifier,
    /// Ordered arguments for the function call.
    pub arguments: Vec<Expression>,
}

impl PartialEq for Call {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        let mut equal = false;
        if self.name == other.name && self.arguments.len() == other.arguments.len() {
            equal = true;
            for i in 0..self.arguments.len() {
                equal &= self.arguments[i] == other.arguments[i];
            }
        }
        equal
    }
}

impl Display for Call {
    /// Format `Call` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.name,
            self.arguments
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Debug, Clone)]
pub struct Number {
    /// Value of the numeric literal.
    pub value: f64,
    /// Unit of the numeric literal.
    pub unit: Unit,
}

impl Hash for Number {
    /// Hash for a `Number`.
    /// Necesarry since f64.hash() does not exist.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.to_bits().hash(state);
        self.unit.hash(state);
    }
}

impl PartialEq for Number {
    /// Operator overload for ==.
    ///
    fn eq(&self, other: &Self) -> bool {
        self.unit == other.unit && {
            let mut other_clone = other.clone();
            let exp_diff = other_clone.unit.exponent - self.unit.exponent;
            other_clone.unit.exponent -= exp_diff;
            other_clone.value = other_clone.value * (10 as u64).pow(exp_diff as u32) as f64;
            other_clone.value *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
            let epsilon = 1e-8;
            other_clone.value < self.value + epsilon && other_clone.value > self.value - epsilon
        }
    }
}

impl Number {
    /// Returns true iff the number has a value of 1
    ///
    pub fn is_one(self) -> bool {
        self.value * 10f64.powi(self.unit.exponent as i32) as f64 == 1f64
    }

    /// Returns true iff the number has a value of 0
    ///
    pub fn is_zero(self) -> bool {
        self.value == 0f64
    }

    /// Refactor the unit such that its `unit.exponent` is divisible by `subunit_exponent`.
    /// It must also either be divisible by 3 or have a magnitude less than 3.
    ///
    /// # Arguments
    /// * `subunit_exponent` - thing to be divisible by.
    pub fn refactor_exponent(&mut self, subunit_exponent: i8) {
        let mut new_value = self.value;
        let mut new_exponent = self.unit.exponent;
        if new_exponent > 0 {
            while new_exponent > 30 || new_exponent % (3 * subunit_exponent) != 0 {
                new_value *= 10f64;
                new_exponent -= 1;
            }
        } else {
            while new_exponent < -30 || new_exponent % (3 * subunit_exponent) != 0 {
                new_value /= 10f64;
                new_exponent += 1;
            }
        }
        self.value = new_value;
        self.unit.exponent = new_exponent;
    }
}

/// get appropriate SI prefix for a given power of 10
/// and power on the unit.
///
fn get_si_prefix(exponent: i8, unit_power: i8) -> String {
    HashMap::from([
        (30, "Q"), // quetta
        (27, "R"), // ronna
        (24, "Y"), // yotta
        (21, "Z"), // zotta
        (18, "E"), // exa
        (15, "P"), // peta
        (12, "T"), // tera
        (9, "G"),  // giga
        (6, "M"),  // mega
        (3, "k"),  // kilo
        (2, "h"),  // hecto
        (1, "da"), // deka
        (0, ""),
        (-1, "d"),  // deci
        (-2, "c"),  // centi
        (-3, "m"),  // milli
        (-6, "μ"),  // micro
        (-9, "n"),  // nano
        (-12, "p"), // pico
        (-15, "f"), // femto
        (-18, "a"), // atto
        (-21, "z"), // zepto
        (-24, "y"), // yocto
        (-27, "r"), // ronto
        (-30, "q"), // quecto
    ])
    .get(&(exponent / unit_power))
    .expect("No SI prefix for power")
    .to_string()
}

impl Display for Number {
    /// Format `Number` appropriately.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut self_clone = self.clone();
        let unit_abbreviations = HashMap::from([
            (BaseUnit::Meter, "m"),     // m
            (BaseUnit::Kilogram, "kg"), // kg
            (BaseUnit::Second, "s"),    // s
            (BaseUnit::Ampere, "A"),    // A
            (BaseUnit::Kelvin, "K"),    // K
            (BaseUnit::Mole, "mol"),    // mol
            (BaseUnit::Candela, "cd"),  // cd
        ]);

        let mut numerator = String::new();
        let mut denominator = String::new();
        let mut processed_prefix = false;
        for (base_unit, unit_power) in self_clone.unit.constituents.clone() {
            let mut unit_name = unit_abbreviations.get(&base_unit).unwrap().to_string();
            // assign power on first iteration
            if !processed_prefix {
                self_clone.refactor_exponent(unit_power);
                unit_name = if unit_name == "kg" {
                    format!("{}g", get_si_prefix(self.unit.exponent + 3, unit_power))
                } else {
                    format!(
                        "{}{unit_name}",
                        get_si_prefix(self.unit.exponent, unit_power)
                    )
                }
            }
            processed_prefix = true;

            // build units
            if unit_power > 0i8 {
                numerator = if numerator.is_empty() {
                    unit_name
                } else {
                    format!("{numerator} {}", unit_name)
                };
                if unit_power > 1i8 {
                    numerator = format!("{numerator}^{}", unit_power);
                }
            } else if unit_power < 0i8 {
                denominator = if denominator.is_empty() {
                    unit_name
                } else {
                    format!("{denominator} {}", unit_name)
                };
                if unit_power < -1i8 {
                    denominator = format!("{denominator}^{}", -unit_power);
                }
            }
        }

        // write final result depending on numerator/denominator contents
        if numerator.is_empty() {
            if denominator.is_empty() {
                write!(f, "{}", self_clone.value)
            } else {
                write!(f, "{} [1 / {}]", self_clone.value, denominator)
            }
        } else {
            if denominator.is_empty() {
                write!(f, "{} [{}]", self_clone.value, numerator)
            } else {
                write!(f, "{} [{} / {}]", self_clone.value, numerator, denominator)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Unit {
    /// Power of 10 unit is multiplied by
    pub exponent: i8,
    /// Map of base units to the power they're raised to.
    /// If map is missing a key, it's assumed to be to power of 0.
    ///
    /// Unitless: Unit { exponent: 0i8, constituents: HashMap::new(), }
    pub constituents: HashMap<BaseUnit, i8>,
}

impl Hash for Unit {
    /// Hash for a `Unit`.
    /// Necesarry since HashMap.hash() does not exist.
    ///
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.exponent.hash(state);
        for (key, value) in &self.constituents {
            key.hash(state);
            value.hash(state);
        }
    }
}

impl PartialEq for Unit {
    fn eq(&self, other: &Self) -> bool {
        let mut result = true;
        for (key, value) in &self.constituents {
            if *value != 0 {
                result &= other.constituents.contains_key(&key)
                    && value == other.constituents.get(&key).unwrap();
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
        let mut other_clone = other.clone();
        let exp_diff = other_clone.unit.exponent - self.unit.exponent;
        other_clone.unit.exponent -= exp_diff;
        other_clone.value = other_clone.value * (10 as u64).pow(exp_diff as u32) as f64;
        other_clone.value *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
        Self {
            value: self.value + other_clone.value,
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
        //
        // also the initial unit is prioritized for +=
        if !other.clone().is_zero() {
            self.clone_from(&(self.clone() + other));
        }
    }
}

impl Neg for Number {
    type Output = Self;

    /// Operator overload for unary -.
    ///
    fn neg(self) -> Self {
        Self {
            value: -self.value,
            unit: self.unit,
        }
    }
}

impl Sub for Number {
    type Output = Self;

    /// Operator overload for -.
    ///
    fn sub(self, other: Self) -> Self {
        assert!(self.unit == other.unit, "Mismatched types");
        let mut other_clone = other.clone();
        let exp_diff = other_clone.unit.exponent - self.unit.exponent;
        other_clone.unit.exponent -= exp_diff;
        other_clone.value = other_clone.value * (10 as u64).pow(exp_diff as u32) as f64;
        other_clone.value *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
        Self {
            value: self.value - other_clone.value,
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
        //
        // also the initial unit is prioritized for -=
        if !other.clone().is_zero() {
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

impl PartialOrd for Number {
    /// Operator overload for <, >, <=, >=
    ///
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        assert!(self.unit == other.unit, "Mismatched types");

        if self == other {
            Some(Ordering::Equal)
        } else {
            let mut other_clone = other.clone();
            let exp_diff = other_clone.unit.exponent - self.unit.exponent;
            other_clone.unit.exponent -= exp_diff;
            other_clone.value = other_clone.value * (10 as u64).pow(exp_diff as u32) as f64;
            other_clone.value *= 10f64.powi((other.unit.exponent - self.unit.exponent) as i32);
            Some(if self.value < other_clone.value {
                Ordering::Less
            } else {
                Ordering::Greater
            })
        }
    }
}

#[derive(Hash, Debug, Clone, PartialEq)]
pub struct Identifier {
    /// The String representing the identifier.
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

    fn get_number_1() -> Number {
        Number {
            value: 1f64,
            unit: Unit {
                exponent: 0,
                constituents: HashMap::new(),
            },
        }
    }

    #[test]
    fn number_display_test1() {
        assert_eq!(format!("{}", get_number_1()), "1");
    }

    #[test]
    fn number_display_test2() {
        let mut number = get_number_1();
        number.unit.constituents.insert(BaseUnit::Kilogram, 1);
        assert_eq!(format!("{}", number), "1 [kg]");
    }

    #[test]
    fn number_display_test3() {
        let mut number = get_number_1();
        number.unit.constituents.insert(BaseUnit::Ampere, 1);
        assert_eq!(format!("{}", number), "1 [A]");
    }

    #[test]
    fn number_display_test4() {
        let mut number = get_number_1();
        number.unit.constituents.insert(BaseUnit::Second, 1);
        number.unit.exponent = -3;
        assert_eq!(format!("{}", number), "1 [ms]");
    }

    #[test]
    fn number_display_test5() {
        let mut number = get_number_1();
        number.unit.constituents.insert(BaseUnit::Second, -1);
        number.unit.exponent = 3;
        assert_eq!(format!("{}", number), "1 [1 / ms]");
    }

    #[test]
    fn number_display_test6() {
        let mut number = get_number_1();
        number.unit.constituents.insert(BaseUnit::Second, -2);
        number.unit.constituents.insert(BaseUnit::Kilogram, 1);
        assert_eq!(format!("{}", number), "1 [kg / s^2]");
    }

    #[test]
    fn number_display_test7() {
        let mut number = get_number_1();
        number.unit.constituents.insert(BaseUnit::Meter, -2);
        number.unit.exponent = 7;
        assert_eq!(format!("{}", number), "10 [1 / mm^2]");
    }

    #[test]
    fn factor_number_display_test1() {
        assert_eq!(format!("{}", Factor::Number(get_number_1())), "1");
    }

    #[test]
    fn factor_identifier_display_test1() {
        assert_eq!(
            format!("{}", Factor::Identifier(Identifier::new("a").unwrap())),
            "a"
        );
    }

    #[test]
    fn factor_identifier_display_test2() {
        assert_eq!(
            format!("{}", Factor::Identifier(Identifier::new("'test'").unwrap())),
            "'test'"
        );
    }

    #[test]
    fn factor_call_display_test1() {
        let call = Call {
            name: Identifier::new("f").unwrap(),
            arguments: vec![Expression {
                minuend: HashSet::from([Term {
                    numerator: HashSet::from([Factor::Number(get_number_1())]),
                    denominator: HashSet::new(),
                }]),
                subtrahend: HashSet::new(),
            }],
        };
        assert_eq!(format!("{}", call), "f(1)");
    }

    #[test]
    fn factor_call_display_test2() {
        let call = Call {
            name: Identifier::new("g").unwrap(),
            arguments: vec![
                Expression {
                    minuend: HashSet::from([Term {
                        numerator: HashSet::from([Factor::Identifier(Identifier::new("a").unwrap())]),
                        denominator: HashSet::new(),
                    }]),
                    subtrahend: HashSet::new(),
                },
                Expression {
                    minuend: HashSet::from([Term {
                        numerator: HashSet::from([Factor::Number(get_number_1())]),
                        denominator: HashSet::new(),
                    }]),
                    subtrahend: HashSet::new(),
                },
            ],
        };
        assert_eq!(format!("{}", call), "g(a, 1)");
    }

    #[test]
    fn expression_display_test1() {
        let one = get_number_1();
        let two = one.clone() + one.clone();
        let four = two.clone() * two.clone();
        let five = four.clone() + one.clone();
        let expression = Expression {
            minuend: HashSet::from([
                Term {
                    numerator: HashSet::from([Factor::Number(one)]),
                    denominator: HashSet::new(),
                },
                Term {
                    numerator: HashSet::from([Factor::Number(four)]),
                    denominator: HashSet::new(),
                },
            ]),
            subtrahend: HashSet::from([
                Term {
                    numerator: HashSet::from([Factor::Number(two)]),
                    denominator: HashSet::new(),
                },
                Term {
                    numerator: HashSet::from([Factor::Number(five)]),
                    denominator: HashSet::new(),
                },
            ]),
        };
        assert_eq!(format!("{}", expression), "1 + 4 - 2 - 5");
    }
}
