//! Three-valued / Three-state logic
//!
//! Three-valued logic is an extension to Boolean logic with three values indicated
//! True, False and some Indeterminate third value.
//!
//! Because of the limitations of logical operator overloading in Rust, AND, OR and XOR operations
//! are implemented with the bitwise `&`, `|` and `^` operators.
//!
//! For more information and the full truth tables of this implementation, see
//! [the Wikipedia page](https://en.wikipedia.org/wiki/Three-valued_logic)

use std::ops::{Not, BitAnd, BitOr, BitXor};

/// Three-state Boolean logic
#[derive(Debug, Clone, Copy, Hash)]
pub enum Tribool {
    /// Truth value
    True,
    /// False value
    False,
    /// Unknown/Indeterminate value
    Indeterminate,
}

pub use Tribool::{True, False, Indeterminate};

impl Tribool {
    /// Returns `true` only if `self` is `True`
    pub fn is_true(self) -> bool {
        match self {
            True => true,
            _ => false,
        }
    }

    /// Returns `true` only if `self` is `False`
    pub fn is_false(self) -> bool {
        match self {
            False => true,
            _ => false,
        }
    }

    /// Returns `true` only if `self` is `Indeterminate`
    pub fn is_indeterminate(self) -> bool {
        match self {
            Indeterminate => true,
            _ => false,
        }
    }

    /// Checks for equality of two `Tribool`s,
    /// returning `Indeterminate` if either are indeterminate.
    pub fn equals(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (False, False) | (True, True) => True,
            (False, True) | (True, False) => False,
            _ => Indeterminate
        }
    }

    /// Checks for inequality of two `Tribool`s,
    /// returning `Indeterminate` if either are indeterminate.
    pub fn not_equals(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (False, False) | (True, True) => False,
            (False, True) | (True, False) => True,
            _ => Indeterminate
        }
    }

    /// Material implication using Kleene Logic.
    ///
    /// This is equivalent to the `OR` operation.
    #[inline]
    pub fn kleene_implication(self, b: Tribool) -> Tribool {
        self | b
    }

    /// Material implication using Łukasiewicz Logic
    ///
    /// The Łukasiewicz Ł3 has the same tables for AND, OR, and NOT as the Kleene logic used elsewhere,
    /// but differs in its definition of implication in that "unknown implies unknown" is true.
    ///
    /// For more information, see [the Wikipedia page and the section on Łukasiewicz Logic](https://en.wikipedia.org/wiki/Three-valued_logic#.C5.81ukasiewicz_logic)
    pub fn lukasiewicz_implication(self, b: Tribool) -> Tribool {
        match (self, b) {
            (True, Indeterminate) | (Indeterminate, False) => Indeterminate,
            (True, False) => False,
            (False, False) => True,
            (_, True) | (_, Indeterminate) => True,
        }
    }
}

impl Not for Tribool {
    type Output = Tribool;

    fn not(self) -> Tribool {
        match self {
            True => False,
            False => True,
            _ => Indeterminate,
        }
    }
}

impl PartialEq<Self> for Tribool {
    #[inline]
    fn eq(&self, rhs: &Tribool) -> bool {
        self.equals(*rhs).is_true()
    }

    #[inline]
    fn ne(&self, rhs: &Tribool) -> bool {
        self.not_equals(*rhs).is_true()
    }
}

impl Eq for Tribool {}

impl PartialEq<bool> for Tribool {
    #[inline]
    fn eq(&self, rhs: &bool) -> bool {
        self.equals(Tribool::from(*rhs)).is_true()
    }

    #[inline]
    fn ne(&self, rhs: &bool) -> bool {
        self.not_equals(Tribool::from(*rhs)).is_true()
    }
}

impl BitAnd<Self> for Tribool {
    type Output = Tribool;

    fn bitand(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (True, True) => True,
            (False, _) | (_, False) => False,
            _ => Indeterminate
        }
    }
}

impl BitOr<Self> for Tribool {
    type Output = Tribool;

    fn bitor(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (False, False) => False,
            (True, _) | (_, True) => True,
            _ => Indeterminate
        }
    }
}

impl BitAnd<bool> for Tribool {
    type Output = Tribool;

    #[inline]
    fn bitand(self, rhs: bool) -> Tribool {
        self.bitand(Tribool::from(rhs))
    }
}

impl BitOr<bool> for Tribool {
    type Output = Tribool;

    #[inline]
    fn bitor(self, rhs: bool) -> Tribool {
        self.bitor(Tribool::from(rhs))
    }
}

impl BitXor<Self> for Tribool {
    type Output = Tribool;

    fn bitxor(self, rhs: Tribool) -> Tribool {
        (self | rhs) & !(self & rhs)
    }
}

impl BitXor<bool> for Tribool {
    type Output = Tribool;

    #[inline]
    fn bitxor(self, rhs: bool) -> Tribool {
        self.bitxor(Tribool::from(rhs))
    }
}

impl From<bool> for Tribool {
    #[inline]
    fn from(value: bool) -> Tribool {
        if value { True } else { False }
    }
}

impl From<Tribool> for bool {
    #[inline]
    fn from(value: Tribool) -> bool {
        value.is_true()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn equality() {
        assert!(True == True);
        assert!(True != False);
        assert!(False != True);
        assert!(False == False);

        assert!(!(Indeterminate == True));
        assert!(!(Indeterminate == False));
        assert!(!(Indeterminate == Indeterminate));
        assert!(!(Indeterminate != True));
        assert!(!(Indeterminate != False));
        assert!(!(Indeterminate != Indeterminate));
    }

    #[test]
    fn bool_equality() {
        assert!(True == true);
        assert!(False == false);
        assert!(True != false);
        assert!(False != true);
        assert!(!(Indeterminate != true));
        assert!(!(Indeterminate != false));
    }

    #[test]
    fn and() {
        assert!((False & False).is_false());
        assert!((False & Indeterminate).is_false());
        assert!((False & True).is_false());

        assert!((Indeterminate & False).is_false());
        assert!((Indeterminate & Indeterminate).is_indeterminate());
        assert!((Indeterminate & True).is_indeterminate());

        assert!((True & False).is_false());
        assert!((True & Indeterminate).is_indeterminate());
        assert!((True & True).is_true());
    }

    #[test]
    fn or() {
        assert!((False | False).is_false());
        assert!((False | Indeterminate).is_indeterminate());
        assert!((False | True).is_true());

        assert!((Indeterminate | False).is_indeterminate());
        assert!((Indeterminate | Indeterminate).is_indeterminate());
        assert!((Indeterminate | True).is_true());

        assert!((True | False).is_true());
        assert!((True | Indeterminate).is_true());
        assert!((True | True).is_true());
    }

    #[test]
    fn xor() {
        assert!((False ^ False).is_false());
        assert!((False ^ True).is_true());
        assert!((False ^ Indeterminate).is_indeterminate());

        assert!((Indeterminate ^ False).is_indeterminate());
        assert!((Indeterminate ^ Indeterminate).is_indeterminate());
        assert!((Indeterminate ^ True).is_indeterminate());

        assert!((True ^ False).is_true());
        assert!((True ^ Indeterminate).is_indeterminate());
        assert!((True ^ True).is_false());
    }

    #[test]
    fn lukasiewicz() {
        assert!(True.lukasiewicz_implication(True).is_true());
        assert!(Indeterminate.lukasiewicz_implication(True).is_true());
        assert!(False.lukasiewicz_implication(True).is_true());

        assert!(True.lukasiewicz_implication(Indeterminate).is_indeterminate());
        assert!(Indeterminate.lukasiewicz_implication(Indeterminate).is_true());
        assert!(False.lukasiewicz_implication(Indeterminate).is_true());

        assert!(True.lukasiewicz_implication(False).is_false());
        assert!(Indeterminate.lukasiewicz_implication(False).is_indeterminate());
        assert!(False.lukasiewicz_implication(False).is_true());
    }
}