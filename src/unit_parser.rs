use crate::definitions::*;

use crate::tokenizer::*;
use std::collections::HashMap;

/// Parse unit into `Unit`.
///
/// unit ::= ( baseunit ( '^' '-' ? [1-9][0-9]* ) ? )+ ( '/' ( baseunit ( '^' '-' ? [1-9][0-9]* ) ? )+ ) ?
///
/// # Arguments
/// * `code` - A string representing the user program.
/// * `i` - An index within `code` representing a point after the last token processed.
///
/// " Examples
///
/// ```
/// let code = "[kilogram / second ^ 2]";
/// let mut i: usize = 0;
/// let _ = parse_unit(code, &mut i).unwrap();
/// assert!(i == code.chars().count())
/// ```
///
pub fn parse_unit(code: &str, i: &mut usize) -> Result<Unit, String> {
    let mut unit = Unit {
        exponent: 0i8,
        constituents: HashMap::new(),
    };
    let base_units = vec![
        BaseUnit::Meter,    // m
        BaseUnit::Kilogram, // kg
        BaseUnit::Second,   // s
        BaseUnit::Ampere,   // A
        BaseUnit::Kelvin,   // K
        BaseUnit::Mole,     // mol
        BaseUnit::Candela,  // cd
    ];
    let base_unit_suffixes = vec![
        "meter", "gram", "second", "ampere", "kelvin", "mole", "candela",
    ];
    let base_unit_suffix_abbreviations = vec!["m", "g", "s", "A", "K", "mol", "cd"];
    let exponents = vec![
        30, 27, 24, 21, 18, 15, 12, 9, 6, 3, 2, 1, 0, -1, -2, -3, -6, -9, -12, -21, -24, -27, -30,
    ];
    let exponent_prefixes = vec![
        "quetta", "ronna", "yotta", "zotta", "exa", "peta", "tera", "giga", "mega", "kilo",
        "hecto", "deka", "", "deci", "centi", "milli", "micro", "nano", "pico", "femto", "atto",
        "zepto", "yocto", "ronto", "quecto",
    ];
    let exponent_prefix_abbreviations = vec![
        "Q", "R", "Y", "Z", "E", "P", "T", "G", "M", "k", "h", "da", "", "d", "c", "m", "μ", "n",
        "p", "f", "a", "z", "y", "r", "q",
    ];
    let mut token = next_unit_token(code, i)?;
    if token != "[" {
        return Err(format!("Unexpected token: `{token}` (expected `[`)"));
    }
    token = next_unit_token(code, i)?;
    let mut numerator = true;
    while token != "]" {
        if token == "[" {
            *i -= token.chars().count();
            let mut sub_unit = parse_unit(code, i)?;
            token = next_unit_token(code, i)?;
            let mut sub_unit_power = 1;
            if token == "^" {
                token = next_unit_token(code, i)?;
                let i8_result = token.parse::<i8>();
                if i8_result.is_err() {
                    return Err(format!("Unexpected token: `{token}`"));
                }
                sub_unit_power = i8_result.unwrap();
                sub_unit.exponent *= sub_unit_power;
                token = next_unit_token(code, i)?;
            }
            if numerator {
                unit.exponent += sub_unit.exponent;
                for (base_unit, power) in sub_unit.constituents {
                    unit.constituents
                        .entry(base_unit)
                        .and_modify(|pwr| *pwr += power * sub_unit_power)
                        .or_insert(power * sub_unit_power);
                }
            } else {
                unit.exponent -= sub_unit.exponent;
                for (base_unit, power) in sub_unit.constituents {
                    unit.constituents
                        .entry(base_unit)
                        .and_modify(|pwr| *pwr -= power * sub_unit_power)
                        .or_insert(-power * sub_unit_power);
                }
            }
        } else {
            let mut base_unit_option: Option<BaseUnit> = None;
            // base unit expected. parse accordingly.

            let mut abbreviated = false;
            let mut prefix = String::from("");
            for base_unit_index in 0..base_units.len() {
                if base_unit_option.is_none()
                    && token
                        .to_lowercase()
                        .ends_with(base_unit_suffixes[base_unit_index])
                {
                    base_unit_option = Some(base_units[base_unit_index].clone());
                    prefix = token[0..token.len() - base_unit_suffixes[base_unit_index].len()]
                        .to_string();
                }
            }
            if base_unit_option.is_none() {
                for base_unit_index in 0..base_units.len() {
                    if base_unit_option.is_none()
                        && token.ends_with(base_unit_suffix_abbreviations[base_unit_index])
                    {
                        base_unit_option = Some(base_units[base_unit_index].clone());
                        prefix = token[0..token.len()
                            - base_unit_suffix_abbreviations[base_unit_index].len()]
                            .to_string();
                        abbreviated = true;
                    }
                }
            }
            if base_unit_option.is_none() {
                return Err(format!("Failed to parse unit: `{token}`"));
            }

            let mut exponent = 0;
            if prefix.len() > 0 {
                let mut exponent_option: Option<i8> = None;
                if !abbreviated {
                    for exponent_index in 0..exponents.len() {
                        if exponent_option.is_none()
                            && exponent_prefixes[exponent_index] != ""
                            && prefix
                                .to_lowercase()
                                .starts_with(exponent_prefixes[exponent_index])
                        {
                            exponent_option = Some(exponents[exponent_index]);
                        }
                    }
                } else {
                    for exponent_index in 0..exponents.len() {
                        if exponent_option.is_none()
                            && exponent_prefix_abbreviations[exponent_index] != ""
                            && prefix.starts_with(exponent_prefix_abbreviations[exponent_index])
                        {
                            exponent_option = Some(exponents[exponent_index]);
                        }
                    }
                }

                if exponent_option.is_none() {
                    return Err(format!("Failed to parse unit: `{token}`"));
                }
                exponent = exponent_option.unwrap();
            }

            let base_unit = base_unit_option.unwrap();

            if base_unit == BaseUnit::Kilogram {
                exponent -= 3;
            }

            token = next_unit_token(code, i)?;
            let mut power = 1;
            if token == "^" {
                token = next_unit_token(code, i)?;
                let i8_result = token.parse::<i8>();
                if i8_result.is_err() {
                    return Err(format!("Unexpected token: `{token}`"));
                }
                power = i8_result.unwrap();
                exponent *= power;
                token = next_unit_token(code, i)?;
            }

            if !numerator {
                exponent = -exponent;
                power = -power;
            }

            unit.exponent += exponent;
            unit.constituents
                .entry(base_unit)
                .and_modify(|pwr| *pwr += power)
                .or_insert(power);
        }
        if token == "*" {
            numerator = true;
            token = next_unit_token(code, i)?;
            if token == "]" {
                return Err(String::from("Unexpected end of unit token"));
            }
        } else if token == "/" {
            numerator = false;
            token = next_unit_token(code, i)?;
            if token == "]" {
                return Err(String::from("Unexpected end of unit token"));
            }
        } else {
            numerator = true;
        }
    }

    Ok(unit)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_unit_test1() {
        let code = "[meter]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test2() {
        let code = "[m]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test3() {
        let code = "[km]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 3,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test4() {
        let code = "[mm]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: -3,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test5() {
        let code = "[kilogram / second]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Kilogram, 1), (BaseUnit::Second, -1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test6() {
        let code = "[kilogram / second ^ 2]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Kilogram, 1), (BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test7() {
        let code = "[kilogram / [second ^ 2]]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Kilogram, 1), (BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test8() {
        let code = "[kilogram / [second ^ 2 / kilogram]]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn parse_unit_test9() {
        let code = "[[m / s] ^ 2]";
        let mut i: usize = 0;
        let unit = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Meter, 2), (BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }
}
