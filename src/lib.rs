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

use std::ops::{Not, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use std::str::FromStr;
use std::fmt::{Display, Formatter, Result as FmtResult};

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

impl Default for Tribool {
    #[inline]
    fn default() -> Tribool { Tribool::False }
}

impl FromStr for Tribool {
    type Err = ();

    fn from_str(s: &str) -> Result<Tribool, ()> {
        Ok(match bool::from_str(s) {
            Ok(b) => Tribool::from(b),
            _ => Indeterminate
        })
    }
}

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

impl Display for Tribool {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(match *self {
            True => "True",
            False => "False",
            Indeterminate => "Indeterminate",
        }, f)
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

impl PartialEq<Tribool> for bool {
    #[inline]
    fn eq(&self, rhs: &Tribool) -> bool {
        *rhs == *self
    }

    #[inline]
    fn ne(&self, rhs: &Tribool) -> bool {
        *rhs != *self
    }
}

use std::cmp::Ordering;

impl PartialOrd<Self> for Tribool {
    fn partial_cmp(&self, rhs: &Tribool) -> Option<Ordering> {
        match (*self, *rhs) {
            (Indeterminate, _) | (_, Indeterminate) => None,
            (True, False) => Some(Ordering::Greater),
            (False, True) => Some(Ordering::Less),
            (True, True) | (False, False) => Some(Ordering::Equal)
        }
    }

    fn lt(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (False, True) => true,
            _ => false,
        }
    }

    fn le(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (True, True) | (False, False) | (False, True) => true,
            _ => false,
        }
    }

    fn gt(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (True, False) => true,
            _ => false,
        }
    }

    fn ge(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (True, True) | (False, False) | (True, False) => true,
            _ => false,
        }
    }
}

impl PartialOrd<bool> for Tribool {
    fn partial_cmp(&self, rhs: &bool) -> Option<Ordering> {
        match (*self, *rhs) {
            (Indeterminate, _) => None,
            (True, false) => Some(Ordering::Greater),
            (False, true) => Some(Ordering::Less),
            (True, true) | (False, false) => Some(Ordering::Equal)
        }
    }

    fn lt(&self, rhs: &bool) -> bool {
        match (*self, *rhs) {
            (False, true) => true,
            _ => false,
        }
    }

    fn le(&self, rhs: &bool) -> bool {
        match (*self, *rhs) {
            (True, true) | (False, false) | (False, true) => true,
            _ => false,
        }
    }

    fn gt(&self, rhs: &bool) -> bool {
        match (*self, *rhs) {
            (True, false) => true,
            _ => false,
        }
    }

    fn ge(&self, rhs: &bool) -> bool {
        match (*self, *rhs) {
            (True, true) | (False, false) | (True, false) => true,
            _ => false,
        }
    }
}

impl PartialOrd<Tribool> for bool {
    fn partial_cmp(&self, rhs: &Tribool) -> Option<Ordering> {
        match (*self, *rhs) {
            (_, Indeterminate) => None,
            (true, False) => Some(Ordering::Greater),
            (false, True) => Some(Ordering::Less),
            (true, True) | (false, False) => Some(Ordering::Equal)
        }
    }

    fn lt(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (false, True) => true,
            _ => false,
        }
    }

    fn le(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (true, True) | (false, False) | (false, True) => true,
            _ => false,
        }
    }

    fn gt(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (true, False) => true,
            _ => false,
        }
    }

    fn ge(&self, rhs: &Tribool) -> bool {
        match (*self, *rhs) {
            (true, True) | (false, False) | (true, False) => true,
            _ => false,
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

impl BitXor<Self> for Tribool {
    type Output = Tribool;

    fn bitxor(self, rhs: Tribool) -> Tribool {
        (self | rhs) & !(self & rhs)
    }
}

macro_rules! impl_binary_op {
    ($op:ident => $f:ident, $assign_op:ident => $af:ident) => {
        impl $op<bool> for Tribool {
            type Output = Tribool;

            #[inline]
            fn $f(self, rhs: bool) -> Tribool {
                self.$f(Tribool::from(rhs))
            }
        }

        impl $op<Tribool> for bool {
            type Output = Tribool;

            #[inline]
            fn $f(self, rhs: Tribool) -> Tribool {
                rhs.$f(self)
            }
        }

        impl $assign_op<Self> for Tribool {
            #[inline]
            fn $af(&mut self, rhs: Tribool) {
                *self = self.$f(rhs);
            }
        }

        impl $assign_op<bool> for Tribool {
            #[inline]
            fn $af(&mut self, rhs: bool) {
                *self = self.$f(rhs);
            }
        }

        impl $assign_op<Tribool> for bool {
            #[inline]
            fn $af(&mut self, rhs: Tribool) {
                *self = rhs.$f(*self).is_true()
            }
        }
    }
}

impl_binary_op!(BitAnd => bitand, BitAndAssign => bitand_assign);
impl_binary_op!(BitOr => bitor, BitOrAssign => bitor_assign);
impl_binary_op!(BitXor => bitxor, BitXorAssign => bitxor_assign);

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

// implements the unary operator "op &T"
// based on "op T" where T is expected to be `Copy`able
macro_rules! forward_ref_unop {
    (impl $imp:ident, $method:ident for $t:ty) => {
        impl<'a> $imp for &'a $t {
            type Output = <$t as $imp>::Output;

            #[inline]
            fn $method(self) -> <$t as $imp>::Output {
                $imp::$method(*self)
            }
        }
    }
}

// implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are expected to be `Copy`able
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<$u> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, other)
            }
        }

        impl<'a> $imp<&'a $u> for $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &'a $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(self, *other)
            }
        }

        impl<'a, 'b> $imp<&'a $u> for &'b $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &'a $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    }
}

forward_ref_unop!(impl Not, not for Tribool);

forward_ref_binop!(impl BitAnd, bitand for Tribool, Tribool);
forward_ref_binop!(impl BitOr, bitor for Tribool, Tribool);
forward_ref_binop!(impl BitXor, bitxor for Tribool, Tribool);

forward_ref_binop!(impl BitAnd, bitand for Tribool, bool);
forward_ref_binop!(impl BitOr, bitor for Tribool, bool);
forward_ref_binop!(impl BitXor, bitxor for Tribool, bool);

forward_ref_binop!(impl BitAnd, bitand for bool, Tribool);
forward_ref_binop!(impl BitOr, bitor for bool, Tribool);
forward_ref_binop!(impl BitXor, bitxor for bool, Tribool);

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
    fn ordering() {
        assert!(True > False);
        assert!(True >= False);
        assert!(False < True);
        assert!(False <= True);
        assert!(False <= False);
        assert!(False >= False);
        assert!(True <= True);
        assert!(True >= True);

        assert!(!(True > True));
        assert!(!(False > True));
        assert!(!(False > False));

        assert!(!(Indeterminate < True));
        assert!(!(Indeterminate < False));
        assert!(!(Indeterminate <= True));
        assert!(!(Indeterminate <= False));
        assert!(!(Indeterminate > True));
        assert!(!(Indeterminate > False));
        assert!(!(Indeterminate >= True));
        assert!(!(Indeterminate >= False));
    }

    #[test]
    fn bool_ordering() {
        assert!(True > false);
        assert!(True >= false);
        assert!(False < true);
        assert!(False <= true);
        assert!(False <= false);
        assert!(False >= false);
        assert!(True <= true);
        assert!(True >= true);

        assert!(!(True > true));
        assert!(!(False > true));
        assert!(!(False > false));

        assert!(!(Indeterminate < true));
        assert!(!(Indeterminate < false));
        assert!(!(Indeterminate <= true));
        assert!(!(Indeterminate <= false));
        assert!(!(Indeterminate > true));
        assert!(!(Indeterminate > false));
        assert!(!(Indeterminate >= true));
        assert!(!(Indeterminate >= false));
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