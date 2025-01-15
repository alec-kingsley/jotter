use std::collections::HashMap;
use std::hash::{Hash, Hasher};

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

impl Unit {
    /// Constructor for a unitless `Unit`.
    ///
    pub fn unitless() -> Self {
        Self {
            exponent: 0i8,
            constituents: HashMap::new(),
        }
    }

    /// Returns `true` iff `self` is unitless.
    /// 
    pub fn is_unitless(&self) -> bool {
        self.constituents.len() == 0
    }
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
