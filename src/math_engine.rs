use crate::math_structs::*;
use std::cmp;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Display;
use std::process;

/// Process the AST of a prompt.
///
/// # Arguments
/// * `model` - The program model for the state of the program.
/// * `prompt` - A Statement::Prompt representing the prompt to evaluate.
///
pub fn process_prompt(model: &ProgramModel, prompt: Relation) {
    let simplified_result = model.simplify_relation(&prompt);
    if simplified_result.is_ok() {
        let simplified = simplified_result.unwrap();
        if prompt.len() > 1 && simplified.len() == 1 && simplified.iter().next().unwrap().len() == 1
        {
            if let Some(true) = simplified.iter().next().unwrap().as_bool() {
                println!("{prompt} ≡ True");
            } else {
                println!("{prompt} ≡ False");
            }
        } else if simplified.len() == 1 {
            println!("{prompt} ≡ {}", simplified.iter().next().unwrap());
        } else {
            println!(
                "{prompt} ∈ {{{}}}",
                simplified
                    .iter()
                    .map(|option| option.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    } else {
        println!("{prompt} : ERROR - {}", simplified_result.unwrap_err());
    }
}

/// Process the AST of a function.
///
/// # Arguments
/// * `model` - The program model for the state of the program.
/// * `name` - The name of the function.
/// * `arguments` - The arguments for the function.
/// * `definition` - The definition for the function.
///
pub fn process_function(
    model: &mut ProgramModel,
    name: Identifier,
    arguments: Vec<Identifier>,
    definition: Vec<(Expression, Relation)>,
) {
    let add_function_result = model.add_function(name, arguments, definition);
    if add_function_result.is_err() {
        eprintln!("WARNING - {}", add_function_result.unwrap_err());
    }
}

/// Process the AST of an equation / relation.
///
/// # Arguments
/// * `model` - The program model for the state of the program.
/// * `equation` - A `Relation` representing the relation to evaluate.
///
pub fn process_equation(model: &mut ProgramModel, relation: Relation) {
    // loop through operators
    for (left, operator, right) in relation.into_iter() {
        // if equality, call add_matrix_row
        if operator == &RelationOp::Equal {
            let equal_result = model.add_matrix_row(left.clone(), right.clone());
            if equal_result.is_err() {
                eprintln!("ERROR - {}", equal_result.unwrap_err());
                process::exit(0);
            }
        } else {
            // else, call add_relation
            model.add_relation(left.clone(), operator.clone(), right.clone());
        }
    }
}

/// Model for program.
///
/// An individual model must be owned by each function call.
/// Includes matrix representing values of all variables.
/// Stores each function.
/// Also stores 'call depth' to keep recursion safe.
///
#[derive(Debug, Clone)]
pub struct ProgramModel {
    /// variables that've been solved for, mapped to a finite solution list
    solved_variables: HashMap<Identifier, HashSet<Number>>,
    /// all variables, in the order they appear in the augmented matrix
    variables: Vec<Identifier>,
    /// description of all known equations in a mathematical augmented matrix
    augmented_matrix: Vec<Vec<Expression>>,
    /// all relations which are not equations
    relations: Vec<Relation>,
    /// function definitions
    functions: HashSet<Statement>,
    /// for functions ; depth of call (to protect against astray recursion)
    call_depth: u16,
}

impl Display for ProgramModel {
    /// Format `ProgramModel` appropriately.
    /// This is mainly for debug purposes.
    ///
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        result.push_str("\nSolved Variables:\n");
        result.push_str(
            self.solved_variables
                .iter()
                .map(|(name, values)| {
                    if values.len() == 1 {
                        format!("{name} = {}", values.iter().next().unwrap().to_string())
                    } else {
                        format!(
                            "{name} ∈ {{{}}}",
                            values
                                .iter()
                                .map(|n| n.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
                .as_str(),
        );
        result.push_str("\nAugmented Matrix:\n");

        // print out the header
        let mut header = self
            .variables
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        header.push_str(
            format!(
                ", _\n{}\n",
                "-".repeat(header.chars().count() + ", _".len())
            )
            .as_str(),
        );

        result.push_str(header.as_str());

        // print out the matrix elements
        for row in 0..self.augmented_matrix.len() {
            for col in 0..self.augmented_matrix[0].len() {
                if col == 0 {
                    result.push_str(format!("{}", self.augmented_matrix[row][col]).as_str());
                } else {
                    result.push_str(format!(", {}", self.augmented_matrix[row][col]).as_str());
                }
            }
            result.push_str("\n");
        }

        // print out the known relations
        if self.relations.len() > 0 {
            result.push_str("Relations:\n");
            for relation in &self.relations {
                result.push_str(format!("{}\n", relation).as_str());
            }
        }

        // print out the defined functions
        if self.functions.len() > 0 {
            result.push_str("Functions:\n");
            for function in &self.functions {
                result.push_str(format!("{}\n", function).as_str());
            }
        }

        result.push_str(format!("Call Depth: {}\n", self.call_depth).as_str());

        write!(f, "{}", result)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum RetrievalLevel {
    /// do not retrieve anything.
    Preserve,
    /// attempt to generate an expression even if it's not simplified.
    All,
    /// only solved variables should be resolved.
    OnlyConstants,
    /// only solved variables which have one solution should be resolved.
    OnlySingleConstants,
}

impl Display for RetrievalLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RetrievalLevel::Preserve => write!(f, "Preserve"),
            RetrievalLevel::All => write!(f, "All"),
            RetrievalLevel::OnlyConstants => write!(f, "OnlyConstants"),
            RetrievalLevel::OnlySingleConstants => write!(f, "OnlySingleConstants"),
        }
    }
}

impl ProgramModel {
    /// Make the call in `call`.
    ///
    /// NOTE - does not check for matching variable names. So the code:
    /// f(x) = x
    /// f(x) ?
    /// would print
    /// f(x) : x
    /// as opposed to an error
    ///
    /// # Arguments
    /// * `call` - The `Call` to make.
    ///
    fn make_call(&self, call: &Call) -> Result<HashSet<Expression>, String> {
        if let Some(Statement::FunctionDefinition(_, arguments, definition)) = self
            .functions
            .iter()
            .find(|stmt| matches!(stmt, Statement::FunctionDefinition(n, _, _) if n == &call.name))
            .cloned()
        {
            if self.call_depth > 100 {
                Err(String::from("Maximum call depth of 100 reached"))
            } else if arguments.len() != call.arguments.len() {
                Err(format!(
                    "Function `{}` takes `{}` arguments, while `{}` were supplied.",
                    call.name,
                    arguments.len(),
                    call.arguments.len()
                ))
            } else {
                let mut model = self.clone();
                model.relations.clear();
                model.augmented_matrix.clear();
                model.call_depth += 1;
                for i in 0..arguments.len() {
                    // assign each variable name to its argument
                    let simplified_expressions = self
                        .simplify_expression(&call.arguments[i], &RetrievalLevel::OnlyConstants)
                        .expect("Failed to simplify call argument");
                    assert_eq!(
                        1,
                        simplified_expressions.len(),
                        "Solving multiple potential systems at once not yet supported"
                    );
                    model
                        .add_matrix_row(
                            simplified_expressions.iter().next().unwrap().clone(),
                            Expression::from_identifier(arguments[i].clone()),
                        )
                        .unwrap();
                }
                // find a true thing to return
                let mut result: Option<HashSet<Expression>> = None;
                for (expression, relation) in definition {
                    if result.is_none() {
                        let evaluated_result = model.simplify_relation(&relation);
                        if evaluated_result.is_ok() {
                            let evaluated = evaluated_result.unwrap();
                            if evaluated.iter().all(|relation| {
                                if let Some(true) = relation.as_bool() {
                                    true
                                } else {
                                    false
                                }
                            }) {
                                result = Some(model.simplify_expression(
                                    &expression,
                                    &RetrievalLevel::OnlyConstants,
                                )?);
                            }
                        }
                    }
                }
                if result.is_none() {
                    Err(format!("Undefined"))
                } else {
                    Ok(result.unwrap())
                }
            }
        } else {
            Err(format!("Function `{}` not found.", call.name))
        }
    }

    /// Evaluate the given `Factor` assuming all constant values.
    ///
    /// # Arguments
    /// * `factor` - The `Factor` to evaluate.
    ///
    fn evaluate_constant_factor(&self, factor: &Factor) -> Result<HashSet<Number>, String> {
        match factor {
            Factor::Parenthetical(expression) => self.evaluate_constant_expression(expression),
            Factor::Number(number) => Ok(HashSet::from([number.clone()])),
            Factor::Identifier(identifier) => Err(format!("Identifier found: {identifier}")),
            Factor::Call(call) => self
                .make_call(call)?
                .iter()
                .map(|expr| self.evaluate_constant_expression(expr))
                .collect::<Result<Vec<_>, _>>()
                .map(|sets| sets.into_iter().flatten().collect::<HashSet<_>>()),
        }
    }

    /// Evaluate the given `Term` assuming all constant values.
    ///
    /// # Arguments
    /// * `term` - The `Term` to evaluate.
    ///
    fn evaluate_constant_term(&self, term: &Term) -> Result<HashSet<Number>, String> {
        // value to return
        let value = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };

        let mut resulting_set = HashSet::from([value]);

        for operand in term.numerator_ref() {
            resulting_set = self
                .evaluate_constant_factor(&operand)?
                .iter()
                .flat_map(|multiplicand| {
                    resulting_set
                        .iter()
                        .map(move |original| original.clone() * multiplicand.clone())
                })
                .collect::<HashSet<_>>();
        }

        for operand in term.denominator_ref() {
            resulting_set = self
                .evaluate_constant_factor(&operand)?
                .iter()
                .flat_map(|divisor| {
                    resulting_set
                        .iter()
                        .map(move |original| original.clone() / divisor.clone())
                })
                .collect::<HashSet<_>>();
        }

        Ok(resulting_set)
    }

    /// Evaluate the given `Expression` assuming all constant values.
    ///
    /// # Arguments
    /// * `expression` - The `Expression` to evaluate.
    ///
    fn evaluate_constant_expression(
        &self,
        expression: &Expression,
    ) -> Result<HashSet<Number>, String> {
        let mut resulting_set: HashSet<Number> = HashSet::new();
        for operand in expression {
            resulting_set = self
                .evaluate_constant_term(&operand)?
                .iter()
                .flat_map(|off| {
                    if resulting_set.is_empty() {
                        vec![off.clone()]
                    } else {
                        resulting_set
                            .iter()
                            .map(move |original| original.clone() + off.clone()).collect::<Vec<_>>()
                    }
                })
                .collect::<HashSet<_>>();
        }
        Ok(resulting_set)
    }

    /// Simplify the given `Factor`.
    ///
    /// # Arguments
    /// * `factor` - The `Factor` to simplify.
    /// * `retrieval_level` - RetrievalLevel for identifiers.
    ///
    fn simplify_factor(
        &self,
        factor: &Factor,
        retrieval_level: &RetrievalLevel,
    ) -> Result<HashSet<Factor>, String> {
        let result = Ok(match factor {
            Factor::Parenthetical(expression) => {
                if expression.len() > 1 {
                    self.simplify_expression(expression, retrieval_level)?
                        .iter()
                        .map(|simplified_expression| {
                            Factor::Parenthetical(simplified_expression.clone())
                        })
                        .collect::<HashSet<_>>()
                } else if expression.len() == 1 {
                    let sub_term = expression.into_iter().next().unwrap();
                    if sub_term.len() == 1 && !sub_term.has_denominator() {
                        // if the parenthetical is just a factor, return it
                        HashSet::from([sub_term.numerator_ref()[0].clone()])
                    } else {
                        self.simplify_term(&sub_term, retrieval_level)?
                            .iter()
                            .map(|simplified_term| {
                                Factor::Parenthetical(Expression::from_term(
                                    simplified_term.clone(),
                                ))
                            })
                            .collect::<HashSet<_>>()
                    }
                } else {
                    HashSet::from([Factor::Number(Number {
                        real: 0f64,
                        imaginary: 0f64,
                        unit: Unit {
                            exponent: 0i8,
                            constituents: HashMap::new(),
                        },
                    })])
                }
            }
            Factor::Number(number) => HashSet::from([Factor::Number(number.clone())]),
            Factor::Identifier(identifier) => {
                match self.retrieve_values(identifier.clone(), retrieval_level) {
                    Ok(values) => values
                        .iter()
                        .map(|value| Factor::Parenthetical(value.clone()))
                        .collect::<HashSet<_>>(),
                    Err(_) => HashSet::from([Factor::Identifier(identifier.clone())]),
                }
            }
            Factor::Call(call) => self
                .make_call(call)?
                .iter()
                .map(|call_result| {
                    self.simplify_expression(&call_result.clone(), retrieval_level)
                        .map(|simplified| {
                            simplified
                                .iter()
                                .map(|simplified_call_result| {
                                    Factor::Parenthetical(simplified_call_result.clone())
                                })
                                .collect::<Vec<_>>()
                        })
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect::<HashSet<_>>(),
        });

        result
    }

    /// Simplify the given `Term`.
    ///
    /// # Arguments
    /// * `term` - The `Term` to simplify.
    /// * `retrieval_level` - RetrievalLevel for identifiers.
    ///
    fn simplify_term(
        &self,
        term: &Term,
        retrieval_level: &RetrievalLevel,
    ) -> Result<HashSet<Term>, String> {
        let mut identifier_counts: HashMap<Identifier, (bool, isize)> = HashMap::new();

        // simplify original factors in term and throw them back in
        let one = Factor::Number(Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        });
        let mut numerator_factors = HashSet::from([one.clone()]);
        let mut denominator_factors = HashSet::from([one.clone()]);
        for operand in term.numerator_ref() {
            let mut add_to_numerator = true;
            if let Factor::Identifier(name) = operand {
                if identifier_counts.contains_key(&name) {
                    let (could_be_0, _) = identifier_counts.get(&name).unwrap();
                    if !could_be_0 {
                        add_to_numerator = false;
                        identifier_counts
                            .entry(name.clone())
                            .and_modify(|(_, ct)| *ct += 1);
                    }
                } else if self.could_be_0(&name) || self.solved_variables.contains_key(&name) {
                    identifier_counts.insert(name.clone(), (true, 0));
                } else {
                    add_to_numerator = false;
                    identifier_counts.insert(name.clone(), (false, 1));
                }
            }
            if add_to_numerator {
                numerator_factors = self
                    .simplify_factor(operand, retrieval_level)?
                    .iter()
                    .flat_map(|multiplicand| {
                        numerator_factors
                            .iter()
                            .map(move |original| original.clone() * multiplicand.clone())
                    })
                    .collect::<HashSet<_>>();
            }
        }
        for operand in term.denominator_ref() {
            let mut add_to_denominator = true;
            if let Factor::Identifier(name) = operand {
                if identifier_counts.contains_key(&name) {
                    let (could_be_0, _) = identifier_counts.get(&name).unwrap();
                    if !could_be_0 {
                        add_to_denominator = false;
                        identifier_counts
                            .entry(name.clone())
                            .and_modify(|(_, ct)| *ct -= 1);
                    }
                }
            }
            if add_to_denominator {
                denominator_factors = self
                    .simplify_factor(&operand, &RetrievalLevel::OnlyConstants)?
                    .iter()
                    .flat_map(|divisor| {
                        denominator_factors
                            .iter()
                            // NOTE - the `*` is intentional
                            .map(move |original| original.clone() * divisor.clone())
                    })
                    .collect::<HashSet<_>>();
            }
        }
        // re-add reserved and cancelled terms
        for (name, (_, mut count)) in identifier_counts {
            while count > 0 {
                numerator_factors = numerator_factors
                    .iter()
                    .map(|original| original.clone() * Factor::Identifier(name.clone()))
                    .collect::<HashSet<_>>();
                count -= 1;
            }
            while count < 0 {
                denominator_factors = denominator_factors
                    .iter()
                    .map(|original| original.clone() * Factor::Identifier(name.clone()))
                    .collect::<HashSet<_>>();
                count += 1;
            }
        }

        let mut new_terms: HashSet<Term> = HashSet::new();
        for numerator_factor in numerator_factors {
            let mut new_term = Term::new();
            let mut no_special_treatment = false;
            if let Factor::Parenthetical(expression) = &numerator_factor {
                if expression.len() == 1 {
                    new_term *= expression.into_iter().next().unwrap();
                } else {
                    no_special_treatment = true;
                }
            } else {
                no_special_treatment = true;
            }
            if no_special_treatment {
                self.simplify_factor(&numerator_factor, &RetrievalLevel::OnlyConstants)?
                    .iter()
                    .for_each(|factor| new_term *= factor.clone());
            }

            for denominator_factor in &denominator_factors {
                let mut new_term = new_term.clone();
                let mut no_special_treatment = false;
                if let Factor::Parenthetical(expression) = &denominator_factor {
                    if expression.len() == 1 {
                        new_term /= expression.into_iter().next().unwrap();
                    } else {
                        no_special_treatment = true;
                    }
                } else {
                    no_special_treatment = true;
                }
                if no_special_treatment {
                    self.simplify_factor(&denominator_factor, &RetrievalLevel::OnlyConstants)?
                        .iter()
                        .for_each(|factor| new_term /= factor.clone());
                }

                // combine all the numeric literals and return if not one
                let number = new_term.extract_number();
                if !number.is_unitless_one() {
                    new_term *= Factor::Number(number);
                }
                new_terms.insert(new_term);
            }
        }

        Ok(new_terms)
    }

    /// Simplify the given `Expression`, using known variable values.
    ///
    /// # Arguments
    /// * `expression` - The `Expression` to simplify.
    /// * `retrieval_level` - RetrievalLevel for identifiers.
    ///
    fn simplify_expression(
        &self,
        expression: &Expression,
        retrieval_level: &RetrievalLevel,
    ) -> Result<HashSet<Expression>, String> {
        let mut new_expressions = HashSet::from([Expression::new()]);

        // re-add the original terms after simplifying
        for operand in expression.minuend_ref() {
            new_expressions = self
                .simplify_term(operand, retrieval_level)?
                .iter()
                .flat_map(|off| {
                    new_expressions.clone().into_iter().map(|mut original| {
                        original += off.clone();
                        original
                    })
                })
                .collect::<HashSet<_>>();
        }

        for operand in expression.subtrahend_ref() {
            new_expressions = self
                .simplify_term(operand, retrieval_level)?
                .iter()
                .flat_map(|off| {
                    new_expressions
                        .clone()
                        .into_iter()
                        .map(move |mut original| {
                            original -= off.clone();
                            original
                        })
                })
                .collect::<HashSet<_>>();
        }

        // remove parentheticals and combine like terms
        new_expressions = new_expressions
            .into_iter()
            .map(|mut expression| {
                expression.flatten();
                expression
            })
            .collect::<HashSet<_>>();

        Ok(new_expressions)
    }

    /// Simplify the given `Relation`, using known variable values.
    /// Makes substitutions when possible. (This is since relation is not repeated in tree)
    ///
    /// NOTE - The other `simplify` expressions return an Ok(HashSet<_>) on Ok. This does not,
    /// since it could either be True or False. A set of "True" and "False" is not useful when a
    /// boolean value is prompted.
    ///
    /// If |relation.operands| > 1 then returned `Relation` may just be 1 for true and 0 for false.
    ///
    /// # Arguments
    /// * `expression` - The `Expression` to simplify.
    /// * `retrieval_level` - RetrievalLevel for identifiers.
    ///
    pub fn simplify_relation(&self, relation: &Relation) -> Result<HashSet<Relation>, String> {
        let mut all_true = relation.len() > 1;
        let mut has_false = false;
        // attempt to evaluate to constant boolean value
        for (left, operator, right) in relation.into_iter() {
            // evaluate left and right
            let left_result = self.evaluate_constant_expression(&left);
            let right_result = self.evaluate_constant_expression(&right);
            if left_result.is_ok() && right_result.is_ok() {
                let left_set = left_result.unwrap();
                let right_set = right_result.unwrap();
                if !left_set
                    .iter()
                    .all(|left| right_set.iter().all(|right| compare(left, operator, right)))
                {
                    // short circuit if any false ones found
                    has_false = true;
                    break;
                }
            } else {
                match operator {
                    RelationOp::Less | RelationOp::Greater => all_true = false,
                    RelationOp::Equal | RelationOp::LessEqual | RelationOp::GreaterEqual => {
                        if left != right {
                            let mut model = self.clone();
                            let logic_result = model.add_matrix_row(left.clone(), right.clone());
                            if logic_result.is_err() || !model.assert_relations_hold() {
                                // stuff breaks if they were to be equal, so they are not equal
                                has_false = true;
                            } else {
                                all_true = false;
                            }
                        }
                    }
                    RelationOp::NotEqual => {
                        if left == right {
                            has_false = true;
                        } else {
                            let mut model = self.clone();
                            let logic_result = model.add_matrix_row(left.clone(), right.clone());
                            if logic_result.is_ok() && model.assert_relations_hold() {
                                // nothing breaks if we add it, so we can't say anything
                                all_true = false;
                            }
                        }
                    }
                }
            }
        }

        Ok(if has_false {
            // return false
            HashSet::from([Relation::from_expression(Expression::new())])
        } else if all_true {
            // return true
            HashSet::from([Relation::from_term(Term::new())])
        } else {
            // return relation as simplified as it can be
            let mut new_relations = self
                .simplify_expression(relation.first_operand(), &RetrievalLevel::All)?
                .iter()
                .map(|simplified| Relation::from_expression(simplified.clone()))
                .collect::<HashSet<_>>();
            // re-add the original expressions after simplifying
            for (_, operator, right) in relation.into_iter() {
                new_relations = self
                    .simplify_expression(right, &RetrievalLevel::All)?
                    .iter()
                    .map(|simplified| {
                        new_relations
                            .iter()
                            .map(|new_relation| {
                                let mut new_relation = new_relation.clone();
                                new_relation.extend(operator.clone(), simplified.clone());
                                new_relation
                            })
                            .collect::<Vec<_>>()
                    })
                    .flatten()
                    .collect::<HashSet<_>>();
            }
            new_relations
        })
    }

    /// Returns true iff the variable with `name` could possibly be 0.
    ///
    fn could_be_0(&self, name: &Identifier) -> bool {
        if self.solved_variables.contains_key(&name) {
            // return true iff any of the solutions are 0
            self.solved_variables
                .get(name)
                .unwrap()
                .iter()
                .find(|x| x.is_zero())
                .is_some()
        } else {
            let mut test_model = self.clone();
            test_model.solved_variables.insert(
                name.clone(),
                HashSet::from([Number {
                    real: 0f64,
                    imaginary: 0f64,
                    unit: Unit {
                        exponent: 0i8,
                        constituents: HashMap::new(),
                    },
                }]),
            );
            // if this breaks, then it can't be 0
            test_model.assert_relations_hold()
        }
    }

    /// Retrieve all expressions for the value(s) of the given identifier from `self.augmented_matrix` and `self.solved_variables`.
    /// Finds the expression in the most simplified form. That is, a non-zero multiplier with
    /// minimum other non-constant terms.
    ///
    /// # Arguments
    /// * `name` - The identifier to search for.
    /// * `retrieval_level` - What sorts of things it should search for.
    ///
    fn retrieve_values(
        &self,
        name: Identifier,
        retrieval_level: &RetrievalLevel,
    ) -> Result<HashSet<Expression>, String> {
        // if it's just preserve, it should return the identifier
        if retrieval_level == &RetrievalLevel::Preserve {
            return Ok(HashSet::from([Expression::from_identifier(name)]));
        }

        // first, attempt to get out of already solved variables
        if self.solved_variables.contains_key(&name) {
            if self.solved_variables.get(&name).unwrap().len() > 1
                || retrieval_level != &RetrievalLevel::OnlySingleConstants
            {
                Ok(self
                    .solved_variables
                    .get(&name)
                    .unwrap()
                    .iter()
                    .map(|number| Expression::from_number(number.clone()))
                    .collect::<HashSet<_>>())
            } else {
                Ok(HashSet::from([Expression::from_identifier(name)]))
            }
        } else {
            let value_col_result = self.variables.iter().position(|var| var == &name);
            if value_col_result.is_none() {
                // TODO - we don't need to give up here. Try to find some term in the augmented matrix
                // which uses this. There could be something.
                Ok(HashSet::from([Expression::from_identifier(name)]))
            } else {
                let value_col = value_col_result.unwrap();
                let row_ct = self.augmented_matrix.len();
                let col_ct = if row_ct == 0 {
                    1
                } else {
                    self.augmented_matrix[0].len()
                };

                let mut best_row: Option<usize> = None;
                let mut min_expressions_plus_values = 0;

                // find the best row
                for row in 0..row_ct {
                    if match self
                        .evaluate_constant_expression(&self.augmented_matrix[row][value_col])
                    {
                        Ok(numbers) => !numbers.iter().all(|number| number.is_zero()),
                        Err(_) => true,
                    } {
                        // possible row. Evaluate for goodness
                        let expressions_plus_values =
                            self.augmented_matrix[row].iter().fold(0, |acc, expr| {
                                acc + match self.evaluate_constant_expression(&expr) {
                                    Ok(numbers) => {
                                        if numbers.iter().all(|number| number.is_zero()) {
                                            0
                                        } else {
                                            1
                                        }
                                    }
                                    Err(_) => 2,
                                }
                            });
                        if best_row == None || expressions_plus_values < min_expressions_plus_values
                        {
                            best_row = Some(row);
                            min_expressions_plus_values = expressions_plus_values;
                        }
                    }
                }

                if best_row == None {
                    return Err(format!("No formula found for `{name}`"));
                }

                // build resulting formula
                let mut result = self.augmented_matrix[best_row.unwrap()][col_ct - 1].clone();
                for col in 0..(col_ct - 1) {
                    if col != value_col {
                        result -= self.augmented_matrix[best_row.unwrap()][col].clone()
                            * Expression::from_identifier(self.variables[col].clone());
                    }
                }
                result /= self.augmented_matrix[best_row.unwrap()][value_col].clone();
                if retrieval_level == &RetrievalLevel::All {
                    self.simplify_expression(&result, &RetrievalLevel::OnlyConstants)
                } else {
                    let resulting_set = self
                        .evaluate_constant_expression(&result)?
                        .iter()
                        .map(|number| Expression::from_number(number.clone()))
                        .collect::<HashSet<_>>();
                    if retrieval_level == &RetrievalLevel::OnlyConstants {
                        Ok(resulting_set)
                    } else {
                        // retrieval_level is only_single_constants
                        if resulting_set.len() == 1 {
                            Ok(HashSet::from([resulting_set
                                .iter()
                                .next()
                                .unwrap()
                                .clone()]))
                        } else {
                            Err(format!("Multiple solutions found for {name}"))
                        }
                    }
                }
            }
        }
    }

    /// Get the row to switch out `row` for.
    /// Returns the first one at or below current one with non-zero constant.
    /// Prioritizes getting a row with all constants.
    ///
    /// # Arguments
    /// * `row` - The row to start at
    /// * `col` - The column of the pivot point
    ///
    fn get_switcher(&self, row: usize, col: usize) -> Option<usize> {
        let row_ct = self.augmented_matrix.len();

        let mut result: Option<usize> = None;
        for switcher in row..row_ct {
            if match self.evaluate_constant_expression(&self.augmented_matrix[switcher][col]) {
                Ok(numbers) => !numbers.iter().all(|number| number.is_zero()),
                Err(_) => false,
            } {
                // we want to prioritize getting a row with all constants
                let all_constants_in_row = self.augmented_matrix[switcher]
                    .iter()
                    .all(|expr| self.evaluate_constant_expression(expr).is_ok());

                if all_constants_in_row {
                    // TODO - this is the preferable case -- that all elements of the row are
                    // constant -- but it'd be worth it as a backup to take something with all 0s
                    // preceding as a switcher. Update accordingly.
                    result = Some(switcher);
                    break;
                }
            }
        }
        result
    }

    /// In echelon form reduction, takes a pivot point as input, sets it to 1, then propogates it down
    /// until only 0s and equations are below it.
    ///
    /// # Arguments
    /// * `row` - The row of the pivot point
    /// * `col` - The column of the pivot point
    ///
    fn setup_pivot(&mut self, row: usize, col: usize) {
        let row_ct = self.augmented_matrix.len();
        let col_ct = self.augmented_matrix[0].len();

        // divide the row by the `col` element to get a 1
        {
            let factor = self.augmented_matrix[row][col].clone();
            for col_update in col..col_ct {
                self.augmented_matrix[row][col_update] /= factor.clone();
            }
        }

        // subtract that row from rows above and below until they're all 0 or undetermined at that pos
        for row_update in 0..row_ct {
            // skip the current row
            if row_update != row {
                let factor = self.augmented_matrix[row_update][col].clone();
                if match self.evaluate_constant_expression(&factor) {
                    // don't subtract anything if it's already 0
                    Ok(numbers) => !numbers.iter().all(|number| number.is_zero()),
                    // don't subtract anything if there's an equation there
                    Err(_) => false,
                } {
                    // only update row if we have a known factor
                    // start at 0 not col since there could be equations
                    for col_update in 0..col_ct {
                        let pivot_row_element = &self.augmented_matrix[row][col_update].clone();
                        self.augmented_matrix[row_update][col_update] -=
                            factor.clone() * pivot_row_element.clone();
                    }
                }
            }
        }
    }

    /// Discover pairs of rows which are lonely, and pair them up.
    /// This is a weird one.
    /// Consider this example of an augmented matrix:
    ///
    /// a | _
    /// -----
    /// b | 6
    /// c | 3
    ///
    /// Let's also say that we know a ≠ 0
    /// In this case, we have that ab = 6 and ac = 3
    /// So we can multiply the second by 2 to get 2ac = 6
    /// Then set 2ac to ab
    /// Then since a ≠ 0, we can say 2c = b
    ///
    /// yielding this new augmented matrix:
    /// a |  b  | c | _
    /// ---------------
    /// b |  0  | 0 | 6
    /// c |  0  | 0 | 3
    /// 0 | -1  | 2 | 0
    ///
    /// This new information can then be used to further develop augmented matrix.
    ///
    fn make_less_lonely(&mut self) -> Result<(), String> {
        let row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        // find lonely groups, i.e., sets of rows which have exactly one column element, for each
        // column except the last.
        let mut lonely_groups: Vec<Vec<usize>> = Vec::with_capacity(col_ct - 1);
        for col in 0..(col_ct - 1) {
            let mut lonely_rows: Vec<usize> = Vec::new();
            for row in 0..row_ct {
                // only consider expressions which cannot evaluate to 0
                let is_zero = if let Ok(numbers) =
                    self.evaluate_constant_expression(&self.augmented_matrix[row][col])
                {
                    numbers.iter().all(|number| number.is_zero())
                } else {
                    false
                };
                if !is_zero {
                    // determine if this row has a lonely column
                    let mut lonely_row = true;
                    for sub_col in 0..(col_ct - 1) {
                        if sub_col == col {
                            continue;
                        }
                        let is_zero = if let Ok(numbers) =
                            self.evaluate_constant_expression(&self.augmented_matrix[row][sub_col])
                        {
                            numbers.iter().all(|number| number.is_zero())
                        } else {
                            false
                        };
                        lonely_row &= is_zero;
                    }
                    if lonely_row {
                        lonely_rows.push(row);
                    }
                }
            }
            lonely_groups.push(lonely_rows);
        }
        // for each lonely group with > 1 element, generate any possible equations
        let mut new_equations: Vec<(Expression, Expression)> = Vec::new();
        for col in 0..(col_ct - 1) {
            // it should only do this if it can guarantee the column variable is not 0
            if !self.could_be_0(&self.variables[col]) {
                if self.solved_variables.contains_key(&self.variables[col])
                    && self
                        .solved_variables
                        .get(&self.variables[col])
                        .unwrap()
                        .len()
                        == 1
                {
                    let value = self
                        .solved_variables
                        .get(&self.variables[col])
                        .unwrap()
                        .iter()
                        .next()
                        .unwrap();
                    for left_idx in 0..lonely_groups[col].len() {
                        let left_row_idx = lonely_groups[col][left_idx];
                        new_equations.push((
                            self.augmented_matrix[left_row_idx][col].clone()
                                * Expression::from_number(value.clone()),
                            self.augmented_matrix[left_row_idx][col_ct - 1].clone(),
                        ));
                    }
                } else if lonely_groups[col].len() > 1 {
                    for right_idx in 1..lonely_groups[col].len() {
                        let left_row_idx = lonely_groups[col][right_idx - 1];
                        let right_row_idx = lonely_groups[col][right_idx];
                        // must multiply each side by the thing the other is equal to so that they're
                        // equal
                        new_equations.push((
                            self.augmented_matrix[left_row_idx][col].clone()
                                * self.augmented_matrix[right_row_idx][col_ct - 1].clone(),
                            self.augmented_matrix[right_row_idx][col].clone()
                                * self.augmented_matrix[left_row_idx][col_ct - 1].clone(),
                        ));
                    }
                }
            }
        }

        // add each equation to the augmented matrix
        // NOTE - this cannot be optimized by throwing this in the previous loop, since it edits
        // the augmented matrix and may delete necessary rows.
        for (left, right) in new_equations {
            self.add_matrix_row(left, right)?;
        }
        Ok(())
    }

    /// Simplify `self.augmented_matrix` by removing meaningless rows. (which are all 0s)
    ///
    fn remove_0s(&mut self) -> Result<(), String> {
        let row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        for row in (0..row_ct).rev() {
            if self.augmented_matrix[row][0..col_ct - 1]
                .iter()
                .all(|expr| match self.evaluate_constant_expression(&expr) {
                    Ok(numbers) => numbers.iter().all(|number| number.is_zero()),
                    Err(_) => false,
                })
            {
                if self
                    .evaluate_constant_expression(&self.augmented_matrix[row][col_ct - 1])
                    .is_ok_and(|numbers| numbers.iter().all(|number| number.is_zero()))
                {
                    self.augmented_matrix.remove(row);
                } else {
                    eprintln!("ERROR: Logical error introduced.");
                    process::exit(1);
                }
            }
        }
        Ok(())
    }

    /// Solve for all solutions of lonely polynomials.
    ///
    fn resolve_lonely_polynomials(&mut self) -> Result<(), String> {
        let row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        for col in 0..(col_ct - 1) {
            let row_ct = self.augmented_matrix.len();
            for row in (0..row_ct).rev() {
                // determine if this row has a lonely column
                let mut lonely_row = true;
                for sub_col in 0..(col_ct - 1) {
                    if sub_col == col {
                        continue;
                    }
                    let is_zero = if let Ok(numbers) =
                        self.evaluate_constant_expression(&self.augmented_matrix[row][sub_col])
                    {
                        numbers.iter().all(|number| number.is_zero())
                    } else {
                        false
                    };
                    lonely_row &= is_zero;
                }
                if lonely_row {
                    let zero_equivalent = self.simplify_expression(
                        &(self.augmented_matrix[row][col].clone()
                            * Expression::from_identifier(self.variables[col].clone())
                            - self.augmented_matrix[row][col_ct - 1].clone()),
                        &RetrievalLevel::OnlySingleConstants,
                    );
                    if zero_equivalent.is_ok() {
                        if let Some((polynomial, name)) = zero_equivalent
                            .unwrap()
                            .iter()
                            .next()
                            .unwrap()
                            .extract_polynomial()
                        {
                            let equivalencies = polynomial.find_roots();
                            self.solved_variables.insert(name.clone(), HashSet::new());
                            self.augmented_matrix.remove(row);
                            let mut test_model = self.clone();
                            for equivalency in equivalencies {
                                // only add if solution does not break pre-order
                                test_model
                                    .solved_variables
                                    .insert(name.clone(), HashSet::from([equivalency.clone()]));
                                if test_model.assert_relations_hold() {
                                    self.solved_variables.entry(name.clone()).and_modify(
                                        |values| {
                                            values.insert(equivalency);
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
    /// Remove rows which are just a pivot and store them.
    ///
    fn store_lonely_pivots(&mut self) {
        let row_ct = self.augmented_matrix.len();
        let col_ct = if row_ct == 0 {
            1
        } else {
            self.augmented_matrix[0].len()
        };

        for row in (0..row_ct).rev() {
            let equivalence_result =
                self.evaluate_constant_expression(&self.augmented_matrix[row][col_ct - 1]);
            if equivalence_result.is_ok() {
                let mut lonely_col_option: Option<(usize, Number)> = None;
                let mut too_many_non_zero_constants = false;
                // determine if row can be thrown into solved variables
                for col in 0..(col_ct - 1) {
                    let constant_result =
                        self.evaluate_constant_expression(&self.augmented_matrix[row][col]);
                    if constant_result.as_ref().is_ok_and(|numbers| {
                        numbers.len() == 1 && !numbers.iter().next().unwrap().is_zero()
                    }) {
                        if lonely_col_option.is_none() {
                            lonely_col_option = Some((
                                col,
                                constant_result.unwrap().iter().next().unwrap().clone(),
                            ));
                        } else {
                            too_many_non_zero_constants = true;
                        }
                    }
                }
                if !too_many_non_zero_constants && lonely_col_option.is_some() {
                    let (lonely_col, constant) = lonely_col_option.unwrap();

                    // throw that sucker in the solved variables!
                    self.solved_variables.insert(
                        self.variables[lonely_col].clone(),
                        equivalence_result
                            .unwrap()
                            .iter()
                            .map(|equivalency| {
                                equivalency.clone() / constant.clone()
                            })
                            .collect::<HashSet<_>>(),
                    );

                    // that information is no longer needed!
                    self.augmented_matrix.remove(row);
                }
            }
        }
    }

    /// Update `self.augmented_matrix` to reduced echelon form.
    ///
    fn reduce(&mut self) -> Result<(), String> {
        assert!(
            self.augmented_matrix.len() > 0 && self.augmented_matrix[0].len() > 0,
            "Empty augmented matrix"
        );

        let row_ct = self.augmented_matrix.len();
        let col_ct = self.augmented_matrix[0].len();

        for col in 0..cmp::min(row_ct, col_ct) {
            // the goal is to get a 1 at each [row, col]
            let row = col;

            match self.get_switcher(row, col) {
                Some(switcher) => {
                    if row < switcher {
                        // swap the rows if they're different
                        self.augmented_matrix.swap(row, switcher);
                    }

                    self.setup_pivot(row, col);
                }
                None => {}
            }
        }

        // simplify all expressions
        for row in 0..row_ct {
            for col in 0..col_ct {
                self.augmented_matrix[row][col] = self
                    .simplify_expression(
                        &self.augmented_matrix[row][col],
                        &RetrievalLevel::OnlySingleConstants,
                    )
                    .unwrap()
                    .iter()
                    .next()
                    .unwrap()
                    .clone();
            }
        }

        // remove expressions which are just a pivot (these are now knowns!)
        self.store_lonely_pivots();

        // try to generate new equations with the gained info
        self.make_less_lonely()?;

        // try to solve any solvable polynomials
        self.resolve_lonely_polynomials()?;

        // remove expressions which are all 0s
        self.remove_0s()?;

        Ok(())
    }

    /// Assert all relations in `self` still hold.
    ///
    fn assert_relations_hold(&self) -> bool {
        let mut all_true = true;
        for relation in &self.relations {
            let simplified_result = self.simplify_relation(relation);
            if simplified_result.is_err() {
                all_true = false;
            } else {
                let simplified = simplified_result.unwrap();
                for element in simplified {
                    if let Some(false) = element.as_bool() {
                        all_true = false;
                    }
                }
            }
        }
        all_true
    }

    /// Get the index of an identifier in `self.variables`, and create it if it does not exist.
    ///
    /// # Arguments
    /// * row_vector - the additional row vector to insert into
    /// * identifier - the `Identifier` to search for.
    ///
    fn get_index(&mut self, row_vector: &mut Vec<Expression>, identifier: Identifier) -> usize {
        let index_option = self.variables.iter().position(|var| var == &identifier);
        if index_option.is_some() {
            index_option.unwrap()
        } else {
            // if the variable is yet to be seen, create an entry for it
            self.variables.insert(0, identifier);
            // expression of value zero to cleanly insert
            let zero_expr = Expression::new();
            for row in &mut self.augmented_matrix {
                row.insert(0, zero_expr.clone());
            }
            row_vector.insert(0, zero_expr.clone());
            0
        }
    }

    /// Add a row to `self.augmented_matrix` based on the provided equality.
    ///
    /// # Arguments
    /// * `left` - The left-hand side of the equality.
    /// * `right` - The right-hand side of the equality.
    ///
    fn add_matrix_row(&mut self, left: Expression, right: Expression) -> Result<(), String> {
        // subtract one side from the other
        let mut zero_equivalent = left.clone() - right.clone();

        // combine like terms
        zero_equivalent.flatten();

        // extract the terms which have no identifiers in numerator
        let mut column_vector_element = Expression::new();

        let zero_expr = Expression::new();

        let mut row_vector = vec![zero_expr.clone(); self.variables.len()];

        // extract terms and place in augmented matrix
        for term in zero_equivalent.minuend_ref() {
            let mut term = term.clone();
            if let Some(identifier) = term.extract_identifier() {
                let index = self.get_index(&mut row_vector, identifier);
                row_vector[index] += term;
            } else {
                column_vector_element -= term;
            }
        }
        for term in zero_equivalent.subtrahend_ref() {
            let mut term = term.clone();
            if let Some(identifier) = term.extract_identifier() {
                let index = self.get_index(&mut row_vector, identifier);
                row_vector[index] -= term;
            } else {
                column_vector_element += term;
            }
        }

        // add to augmented matrix and update information
        row_vector.push(column_vector_element);
        self.augmented_matrix.push(row_vector);
        self.reduce()?;
        if !self.assert_relations_hold() {
            return Err(String::from("Logical error introduced"));
        }
        Ok(())
    }

    /// Add a relation to `self.relations`.
    ///
    /// # Arguments
    /// * `left` - The left-hand side of the relation.
    /// * `right` - The right-hand side of the relation.
    /// * `operator` - The operator between the relation elements.
    ///
    fn add_relation(&mut self, left: Expression, operator: RelationOp, right: Expression) {
        // TODO - for variables with multiple solutions, this should check if it can remove some
        let mut new_relation = Relation::from_expression(left);
        new_relation.extend(operator, right);
        self.relations.push(new_relation);
    }

    /// Add a function to the model.
    ///
    /// # Arguments
    /// * `function` - The function to add.
    /// * `name` - The name of the function.
    /// * `arguments` - The arguments for the function.
    /// * `definition` - The definition for the function.
    ///
    fn add_function(
        &mut self,
        name: Identifier,
        arguments: Vec<Identifier>,
        definition: Vec<(Expression, Relation)>,
    ) -> Result<(), String> {
        let function = Statement::FunctionDefinition(name.clone(), arguments, definition);

        // only insert if it doesn't already exist.
        // note that functions are compared for equality only by their name.
        if let Some(_) = self
            .functions
            .iter()
            .find(|stmt| matches!(stmt, Statement::FunctionDefinition(n, _, _) if n == &name))
            .cloned()
        {
            Err(format!("Function `{name}` already defined"))
        } else {
            self.functions.insert(function);
            Ok(())
        }
    }

    /// Initializes the ProgramModel.
    ///
    /// # Arguments
    /// * `call_depth` - The depth of calls. Safety for recursion.
    ///
    pub fn new(call_depth: u16) -> Self {
        ProgramModel {
            solved_variables: HashMap::new(),
            variables: Vec::new(),
            augmented_matrix: Vec::new(),
            relations: Vec::new(),
            functions: HashSet::new(),
            call_depth,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    #[test]
    fn evaluate_constant_term_test1() {
        let model = ProgramModel::new(0);
        let term = Term::new();
        let expected = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        assert_eq!(
            expected,
            *model
                .evaluate_constant_term(&term)
                .expect("Failed to evaluate")
                .iter()
                .next()
                .unwrap()
        );
    }

    #[test]
    fn evaluate_constant_expression_test1() {
        let model = ProgramModel::new(0);
        let expression = Expression::from_term(Term::new());
        let expected = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        assert_eq!(
            expected,
            *model
                .evaluate_constant_expression(&expression)
                .expect("Failed to evaluate")
                .iter()
                .next()
                .unwrap()
        );
    }

    #[test]
    fn add_matrix_row_test1() {
        let expression_a = parse_expression("a", &mut 0).unwrap();
        let expression_2 = parse_expression("2", &mut 0).unwrap();
        let mut model = ProgramModel::new(0);
        model
            .add_matrix_row(expression_a, expression_2.clone())
            .unwrap();

        let a_expected = Number {
            real: 2f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        assert_eq!(
            a_expected,
            *model
                .solved_variables
                .get(&Identifier::new("a").unwrap())
                .unwrap()
                .iter()
                .next()
                .unwrap()
        );
    }

    #[test]
    fn retrieve_value_test1() {
        let expression_a = parse_expression("a", &mut 0).unwrap();
        let expression_2 = parse_expression("2", &mut 0).unwrap();
        let mut model = ProgramModel::new(0);
        // a = 2
        model
            .add_matrix_row(expression_a, expression_2.clone())
            .unwrap();

        let a = model
            .evaluate_constant_expression(
                &model
                    .retrieve_values(
                        Identifier::new("a").unwrap(),
                        &RetrievalLevel::OnlySingleConstants,
                    )
                    .expect("Failed to retrieve value")
                    .iter()
                    .next()
                    .unwrap(),
            )
            .expect("Failed to evaluate")
            .iter()
            .next()
            .unwrap()
            .clone();
        let a_expected = Number {
            real: 2f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        assert_eq!(a_expected, a)
    }

    #[test]
    fn retrieve_value_test2() {
        let expression_2a = parse_expression("2a", &mut 0).unwrap();
        let expression_2 = parse_expression("2", &mut 0).unwrap();
        let mut model = ProgramModel::new(0);
        // 2a = 2
        model
            .add_matrix_row(expression_2a, expression_2.clone())
            .unwrap();

        let a = model
            .evaluate_constant_expression(
                &model
                    .retrieve_values(
                        Identifier::new("a").unwrap(),
                        &RetrievalLevel::OnlySingleConstants,
                    )
                    .expect("Failed to retrieve value")
                    .iter()
                    .next()
                    .unwrap(),
            )
            .expect("Failed to evaluate")
            .iter()
            .next()
            .unwrap()
            .clone();
        let a_expected = Number {
            real: 1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        assert_eq!(a_expected, a)
    }

    #[test]
    fn retrieve_value_test3() {
        // tests that program can solve basic set of linear equations.
        //
        // given equations:
        // 3x + 2y = 7
        // y - x = -4
        //
        // solve for:
        // x, y
        //
        // expected:
        // x = 3, y = -1
        //

        let expression_3x_plus_2y = parse_expression("3x + 2y", &mut 0).unwrap();
        let expression_7 = parse_expression("7", &mut 0).unwrap();
        let expression_y_minus_x = parse_expression("y - x", &mut 0).unwrap();
        let expression_neg_4 = parse_expression("-4", &mut 0).unwrap();
        println!("{expression_3x_plus_2y} == {expression_7}");
        println!("{expression_y_minus_x} == {expression_neg_4}");
        let mut model = ProgramModel::new(0);
        // 3x + 2y = 7
        model
            .add_matrix_row(expression_3x_plus_2y, expression_7)
            .unwrap();
        // y - x = -4
        model
            .add_matrix_row(expression_y_minus_x, expression_neg_4)
            .unwrap();

        let x = model
            .evaluate_constant_expression(
                &model
                    .retrieve_values(
                        Identifier::new("x").unwrap(),
                        &RetrievalLevel::OnlySingleConstants,
                    )
                    .expect("Failed to retrieve value")
                    .iter()
                    .next()
                    .unwrap(),
            )
            .expect("Failed to evaluate")
            .iter()
            .next()
            .unwrap()
            .clone();
        let x_expected = Number {
            real: 3f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        assert_eq!(x_expected, x);
        let y = model
            .evaluate_constant_expression(
                &model
                    .retrieve_values(
                        Identifier::new("y").unwrap(),
                        &RetrievalLevel::OnlySingleConstants,
                    )
                    .expect("Failed to retrieve value")
                    .iter()
                    .next()
                    .unwrap(),
            )
            .expect("Failed to evaluate")
            .iter()
            .next()
            .unwrap()
            .clone();
        let y_expected = Number {
            real: -1f64,
            imaginary: 0f64,
            unit: Unit {
                exponent: 0i8,
                constituents: HashMap::new(),
            },
        };
        assert_eq!(y_expected, y);
    }
}
