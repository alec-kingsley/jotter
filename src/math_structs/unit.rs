use std::hash::Hash;
use std::ops::{Index, IndexMut};

const BASE_UNIT_CT: usize = 7;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BaseUnit {
    Meter,    // m
    Kilogram, // kg
    Second,   // s
    Ampere,   // A
    Kelvin,   // K
    Mole,     // mol
    Candela,  // cd
}

impl BaseUnit {
    pub const ALL: [BaseUnit; BASE_UNIT_CT] = [
        BaseUnit::Meter,
        BaseUnit::Kilogram,
        BaseUnit::Second,
        BaseUnit::Ampere,
        BaseUnit::Kelvin,
        BaseUnit::Mole,
        BaseUnit::Candela,
    ];
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Unit {
    /// Power of 10 unit is multiplied by
    exponent: i8,
    /// Map of base units to the power they're raised to.
    /// If map is missing a key, it's assumed to be to power of 0.
    ///
    /// Map indices correlated with enum `BaseUnit`.
    ///
    /// Unitless: Unit { exponent: 0i8, constituents: HashMap::new(), }
    constituents: [i8; BASE_UNIT_CT],
}

impl Unit {
    /// Constructor for a unitless `Unit`.
    ///
    pub fn unitless() -> Self {
        Self {
            exponent: 0i8,
            constituents: [0; BASE_UNIT_CT],
        }
    }

    /// Returns `true` iff `self` is unitless.
    ///
    pub fn is_unitless(&self) -> bool {
        self.constituents.iter().all(|&x| x == 0)
    }

    /// Returns `self.exponent`.
    ///
    pub fn get_exponent(&self) -> i8 {
        self.exponent
    }

    /// Adds `val` to `self.exponent`.
    ///
    pub fn add_exponent(&mut self, val: i8) {
        self.exponent += val;
    }

    /// Multiplies by `self.exponent` by val.
    ///
    pub fn multiply_exponent(&mut self, val: i8) {
        self.exponent *= val;
    }

    /// Multiplies each constituent by `val`.
    ///
    pub fn multiply_constituents(&mut self, val: i8) {
        for i in 0..BASE_UNIT_CT {
            self.constituents[i] *= val;
        }
    }
}

impl From<Vec<(BaseUnit, i8)>> for Unit {
    fn from(constituents: Vec<(BaseUnit, i8)>) -> Self {
        let mut unit = Unit::unitless();
        for (base_unit, power) in constituents {
            unit[base_unit] = power;
        }
        unit
    }
}

impl Index<BaseUnit> for Unit {
    type Output = i8;

    /// Operator overload for [].
    ///
    fn index(&self, base_unit: BaseUnit) -> &Self::Output {
        &self.constituents[base_unit as usize]
    }
}

impl IndexMut<BaseUnit> for Unit {
    /// Operator overload for [].
    ///
    fn index_mut(&mut self, base_unit: BaseUnit) -> &mut Self::Output {
        &mut self.constituents[base_unit as usize]
    }
}
