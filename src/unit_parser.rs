use crate::math_structs::unit::*;

use crate::tokenizer::*;
use std::collections::HashMap;

/// Parse unit into `Unit`.
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
pub fn parse_unit(code: &str, i: &mut usize) -> Result<(Unit, f64), String> {
    let mut unit = Unit::unitless();
    let mut token = next_unit_token(code, i)?;
    if token != "[" {
        return Err(format!("Unexpected token: `{token}` (expected `[`)"));
    }
    token = next_unit_token(code, i)?;
    let mut numerator = true;
    let mut factor = 1f64;
    while token != "]" {
        if token == "[" {
            *i -= token.chars().count();
            let (mut sub_unit, sub_factor) = parse_unit(code, i)?;
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
                factor *= sub_factor;
                for (base_unit, power) in sub_unit.constituents {
                    unit.constituents
                        .entry(base_unit)
                        .and_modify(|pwr| *pwr += power * sub_unit_power)
                        .or_insert(power * sub_unit_power);
                }
            } else {
                unit.exponent -= sub_unit.exponent;
                factor /= sub_factor;
                for (base_unit, power) in sub_unit.constituents {
                    unit.constituents
                        .entry(base_unit)
                        .and_modify(|pwr| *pwr -= power * sub_unit_power)
                        .or_insert(-power * sub_unit_power);
                }
            }
        } else if token == "1" {
            token = next_unit_token(code, i)?;
        } else {
            // base unit expected. parse accordingly.
            let mut abbreviated = false;
            let (sub_unit, sub_factor, prefix) = parse_base_unit(token.as_str(), &mut abbreviated)?;
            let constituents = &mut unit.constituents;

            let mut exponent = parse_unit_prefix(prefix.as_str(), abbreviated)?
                - 3 * sub_unit
                    .constituents
                    .get(&BaseUnit::Kilogram)
                    .unwrap_or_else(|| &0i8);

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

            factor *= sub_factor.powi(power as i32);

            for (base_unit, sub_power) in sub_unit.constituents {
                *constituents.entry(base_unit).or_insert(0) += power * sub_power;
            }
            unit.exponent += exponent;
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

    Ok((unit, factor))
}

/// Parse base unit.
///
/// # Arguments
/// * `token` - The token to parse.
/// * `abbreviated` - Sets to true iff unit was abbreviated. (In this case prefix should be too).
///
/// # Return
/// On Ok, Ok(unit, factor to multiply by, prefix)
///
pub fn parse_base_unit(token: &str, abbreviated: &mut bool) -> Result<(Unit, f64, String), String> {
    let base_unit_suffixes = vec![
        "meter",
        "inch",
        "foot",
        "feet",
        "yard",
        "mile",
        "liter",
        "cup",
        "pint",
        "quart",
        "gallon",
        "gram",
        "pound",
        "second",
        "minute",
        "hour",
        "day",
        "ampere",
        "kelvin",
        "mole",
        "candela",
        "radian",
        "steradian",
        "hertz",
        "newton",
        "pascal",
        "joule",
        "watt",
        "coulomb",
        "volt",
        "farad",
        "ohm",
        "siemens",
        "weber",
        "tesla",
        "henry",
        "lumen",
        "lux",
        "becquerel",
        "gray",
        "sievert",
        "katal",
    ];
    let base_unit_suffix_abbreviations = vec![
        "m", "in", "ft", "ft", "yd", "mi", "l", "c", "pt", "qt", "gal", "g", "lb", "s", "min", "h",
        "d", "A", "K", "mol", "cd", "rad", "sr", "Hz", "N", "Pa", "J", "W", "C", "V", "F", "Ω",
        "S", "Wb", "T", "H", "lm", "lx", "Bq", "Gy", "Sv", "kat",
    ];
    // vec of constituents paired with order
    let base_units: Vec<(HashMap<BaseUnit, i8>, f64)> = vec![
        (HashMap::from([(BaseUnit::Meter, 1)]), 1.0),
        (HashMap::from([(BaseUnit::Meter, 1)]), 0.0254),
        (HashMap::from([(BaseUnit::Meter, 1)]), 0.3048),
        (HashMap::from([(BaseUnit::Meter, 1)]), 0.3048),
        (HashMap::from([(BaseUnit::Meter, 1)]), 0.9144),
        (HashMap::from([(BaseUnit::Meter, 1)]), 1609.344),
        (HashMap::from([(BaseUnit::Meter, 3)]), 0.001),
        (HashMap::from([(BaseUnit::Meter, 3)]), 0.0002365882365),
        (HashMap::from([(BaseUnit::Meter, 3)]), 0.000473176473),
        (HashMap::from([(BaseUnit::Meter, 3)]), 0.000946352946),
        (HashMap::from([(BaseUnit::Meter, 3)]), 0.003785411784),
        (HashMap::from([(BaseUnit::Kilogram, 1)]), 1.0),
        (HashMap::from([(BaseUnit::Kilogram, 1)]), 453.59237),
        (HashMap::from([(BaseUnit::Second, 1)]), 1.0),
        (HashMap::from([(BaseUnit::Second, 1)]), 60.0),
        (HashMap::from([(BaseUnit::Second, 1)]), 60.0 * 60.0),
        (HashMap::from([(BaseUnit::Second, 1)]), 60.0 * 60.0 * 24.0),
        (HashMap::from([(BaseUnit::Ampere, 1)]), 1.0),
        (HashMap::from([(BaseUnit::Kelvin, 1)]), 1.0),
        (HashMap::from([(BaseUnit::Mole, 1)]), 1.0),
        (HashMap::from([(BaseUnit::Candela, 1)]), 1.0),
        (HashMap::from([]), 1.0),
        (HashMap::from([]), 1.0),
        (HashMap::from([(BaseUnit::Second, -1)]), 1.0),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, 1),
                (BaseUnit::Second, -2),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, -1),
                (BaseUnit::Second, -2),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, 2),
                (BaseUnit::Second, -2),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, 2),
                (BaseUnit::Second, -3),
            ]),
            1.0,
        ),
        (
            HashMap::from([(BaseUnit::Second, 1), (BaseUnit::Ampere, 1)]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, 2),
                (BaseUnit::Second, -3),
                (BaseUnit::Ampere, -1),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, -1),
                (BaseUnit::Meter, -2),
                (BaseUnit::Second, 4),
                (BaseUnit::Ampere, 2),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, 2),
                (BaseUnit::Second, -3),
                (BaseUnit::Ampere, -2),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, -1),
                (BaseUnit::Meter, -2),
                (BaseUnit::Second, 3),
                (BaseUnit::Ampere, 2),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, 2),
                (BaseUnit::Second, -2),
                (BaseUnit::Ampere, -1),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Second, -2),
                (BaseUnit::Ampere, -1),
            ]),
            1.0,
        ),
        (
            HashMap::from([
                (BaseUnit::Kilogram, 1),
                (BaseUnit::Meter, 2),
                (BaseUnit::Second, -2),
                (BaseUnit::Ampere, -2),
            ]),
            1.0,
        ),
        (HashMap::from([(BaseUnit::Candela, 1)]), 1.0),
        (
            HashMap::from([(BaseUnit::Candela, 1), (BaseUnit::Meter, -2)]),
            1.0,
        ),
        (HashMap::from([(BaseUnit::Second, -1)]), 1.0),
        (
            HashMap::from([(BaseUnit::Meter, 2), (BaseUnit::Second, -2)]),
            1.0,
        ),
        (
            HashMap::from([(BaseUnit::Meter, 2), (BaseUnit::Second, -2)]),
            1.0,
        ),
        (
            HashMap::from([(BaseUnit::Mole, 1), (BaseUnit::Second, -1)]),
            1.0,
        ),
    ];

    let mut base_unit_option: Option<usize> = None;
    let mut prefix = String::new();
    for base_unit_index in 0..base_units.len() {
        if base_unit_option.is_none()
            || base_unit_suffixes[base_unit_index].len()
                > base_unit_suffixes[base_unit_option.unwrap()].len()
        {
            if token
                .to_lowercase()
                .ends_with(base_unit_suffixes[base_unit_index])
            {
                base_unit_option = Some(base_unit_index);
                prefix =
                    token[0..token.len() - base_unit_suffixes[base_unit_index].len()].to_string();
            } else if token
                .to_lowercase()
                .ends_with((base_unit_suffixes[base_unit_index].to_string() + "s").as_str())
                && base_unit_suffixes[base_unit_index] != "foot"
            {
                base_unit_option = Some(base_unit_index);
                prefix = token[0..token.len() - base_unit_suffixes[base_unit_index].len() - 1]
                    .to_string();
            }
        }
    }
    if base_unit_option.is_none() {
        for base_unit_index in 0..base_units.len() {
            if (base_unit_option.is_none()
                || base_unit_suffix_abbreviations[base_unit_index].len()
                    > base_unit_suffix_abbreviations[base_unit_option.unwrap()].len())
                && token.ends_with(base_unit_suffix_abbreviations[base_unit_index])
            {
                base_unit_option = Some(base_unit_index);
                prefix = token
                    [0..token.len() - base_unit_suffix_abbreviations[base_unit_index].len()]
                    .to_string();
                *abbreviated = true;
            }
        }
    }
    if base_unit_option.is_none() {
        return Err(format!("Failed to parse unit: `{token}`"));
    }
    let (constituents, factor) = base_units.get(base_unit_option.unwrap()).unwrap().clone();
    Ok((
        Unit {
            exponent: 0i8,
            constituents,
        },
        factor,
        prefix,
    ))
}

/// Parse unit prefix.
///
/// # Arguments
/// * `token` - The token to parse.
/// * `abbreviated` - True if should be looking for abbreviation.
///
/// # Return
/// On Ok, Ok(exponent)
///
pub fn parse_unit_prefix(prefix: &str, abbreviated: bool) -> Result<i8, String> {
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
            return Err(format!("Failed to parse prefix: `{prefix}`"));
        }
        exponent = exponent_option.unwrap();
    }
    Ok(exponent)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_unit_1() {
        let code = "[meter]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_2() {
        let code = "[m]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_3() {
        let code = "[km]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 3,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_4() {
        let code = "[mm]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: -3,
            constituents: HashMap::from([(BaseUnit::Meter, 1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_5() {
        let code = "[kilogram / second]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Kilogram, 1), (BaseUnit::Second, -1)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_6() {
        let code = "[kilogram / second ^ 2]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Kilogram, 1), (BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_7() {
        let code = "[kilogram / [second ^ 2]]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Kilogram, 1), (BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_8() {
        let code = "[kilogram / [second ^ 2 / kilogram]]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }

    #[test]
    fn test_parse_unit_9() {
        let code = "[[m / s] ^ 2]";
        let mut i: usize = 0;
        let (unit, _) = parse_unit(code, &mut i).unwrap();
        assert_eq!(i, code.chars().count());
        let unit_expected = Unit {
            exponent: 0,
            constituents: HashMap::from([(BaseUnit::Meter, 2), (BaseUnit::Second, -2)]),
        };
        assert_eq!(unit_expected, unit);
    }
}
