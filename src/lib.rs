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

#[cfg(feature = "serde")]
mod serde;

use std::fmt::{Display, Formatter, Result as FmtResult};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};
use std::str::FromStr;

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

pub use Tribool::{False, Indeterminate, True};

impl Default for Tribool {
    #[inline]
    fn default() -> Tribool {
        False
    }
}

impl FromStr for Tribool {
    type Err = ();

    #[inline]
    fn from_str(s: &str) -> Result<Tribool, ()> {
        Ok(match bool::from_str(s) {
            Ok(value) => Tribool::boolean(value),
            _ => Indeterminate,
        })
    }
}

impl Tribool {
    /// Construct a new non-indeterminate Tribool from a regular boolean value
    #[inline]
    pub const fn boolean(value: bool) -> Tribool {
        match value {
            true => True,
            false => False,
        }
    }

    /// Returns `true` only if `self` is `True`
    ///
    /// # Example
    /// ```
    /// # use tribool::Tribool;
    /// # fn main() {
    /// assert!(Tribool::True.is_true())
    /// # }
    /// ```
    #[inline]
    pub const fn is_true(self) -> bool {
        match self {
            True => true,
            _ => false,
        }
    }

    /// Returns `true` only if `self` is `False`
    ///
    /// # Example
    /// ```
    /// # use tribool::Tribool;
    /// # fn main() {
    /// assert!(Tribool::False.is_false())
    /// # }
    /// ```
    #[inline]
    pub const fn is_false(self) -> bool {
        match self {
            False => true,
            _ => false,
        }
    }

    /// Returns `true` only if `self` is `Indeterminate`
    ///
    /// # Example
    /// ```
    /// # use tribool::Tribool;
    /// # fn main() {
    /// assert!(Tribool::Indeterminate.is_indeterminate())
    /// # }
    /// ```
    #[inline]
    pub const fn is_indeterminate(self) -> bool {
        match self {
            Indeterminate => true,
            _ => false,
        }
    }

    /// Checks for equality of two `Tribool`s,
    /// returning `Indeterminate` if either are indeterminate.
    ///
    /// # Example
    /// ```
    /// # use tribool::Tribool;
    /// # fn main() {
    /// assert!(Tribool::True.equals(Tribool::True).is_true());
    /// assert!(Tribool::True.equals(Tribool::False).is_false());
    /// assert!(Tribool::Indeterminate.equals(Tribool::False).is_indeterminate())
    /// # }
    /// ```
    #[inline]
    pub const fn equals(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (False, False) | (True, True) => True,
            (False, True) | (True, False) => False,
            _ => Indeterminate,
        }
    }

    /// Checks for inequality of two `Tribool`s,
    /// returning `Indeterminate` if either are indeterminate.
    ///
    /// # Example
    /// ```
    /// # use tribool::Tribool;
    /// # fn main() {
    /// assert!(Tribool::True.not_equals(Tribool::True).is_false());
    /// assert!(Tribool::True.not_equals(Tribool::False).is_true());
    /// assert!(Tribool::Indeterminate.not_equals(Tribool::False).is_indeterminate())
    /// # }
    /// ```
    #[inline]
    pub const fn not_equals(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (False, False) | (True, True) => False,
            (False, True) | (True, False) => True,
            _ => Indeterminate,
        }
    }

    /// Material implication using Kleene Logic.
    ///
    /// This is equivalent to `NOT(A) OR B`.
    #[inline]
    pub const fn kleene_implication(self, b: Tribool) -> Tribool {
        self.negate().or(b) // !self | b
    }

    /// Material implication using Łukasiewicz Logic
    ///
    /// The Łukasiewicz Ł3 has the same tables for AND, OR, and NOT as the Kleene logic used elsewhere,
    /// but differs in its definition of implication in that "unknown implies unknown" is true.
    ///
    /// For more information, see [the Wikipedia page and the section on Łukasiewicz Logic](https://en.wikipedia.org/wiki/Three-valued_logic#.C5.81ukasiewicz_logic)
    #[inline]
    pub fn lukasiewicz_implication(self, b: Tribool) -> Tribool {
        match (self, b) {
            (True, Indeterminate) | (Indeterminate, False) => Indeterminate,
            (True, False) => False,
            (False, False) => True,
            (_, True) | (_, Indeterminate) => True,
        }
    }

    /// Logical conjunction
    #[inline]
    pub const fn and(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (True, True) => True,
            (False, _) | (_, False) => False,
            _ => Indeterminate,
        }
    }

    /// Logical disjunction
    #[inline]
    pub const fn or(self, rhs: Tribool) -> Tribool {
        match (self, rhs) {
            (False, False) => False,
            (True, _) | (_, True) => True,
            _ => Indeterminate,
        }
    }

    /// Logical exclusive disjunction
    #[inline]
    pub const fn xor(self, rhs: Tribool) -> Tribool {
        // (self | rhs) & !(self & rhs)
        self.or(rhs).and(self.and(rhs).negate())
    }

    /// Logical negation
    #[inline]
    pub const fn negate(self) -> Tribool {
        match self {
            True => False,
            False => True,
            _ => Indeterminate,
        }
    }

    /// Compares two Tribools similarly to a `bool`, where `true` is greater than `false`
    ///
    /// Indeterminate values cannot be compared to order and therefore return `None`
    #[inline]
    pub const fn compare(self, rhs: Tribool) -> Option<Ordering> {
        match (self, rhs) {
            (Indeterminate, _) | (_, Indeterminate) => None,
            (True, False) => Some(Ordering::Greater),
            (False, True) => Some(Ordering::Less),
            (True, True) | (False, False) => Some(Ordering::Equal),
        }
    }
}

impl Display for Tribool {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        f.write_str(match self {
            True => "True",
            False => "False",
            Indeterminate => "Indeterminate",
        })
    }
}

impl<B: Into<Tribool> + Copy> PartialEq<B> for Tribool {
    #[inline]
    fn eq(&self, rhs: &B) -> bool {
        self.equals((*rhs).into()).is_true()
    }

    #[inline]
    fn ne(&self, rhs: &B) -> bool {
        self.not_equals((*rhs).into()).is_true()
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

impl<B: Into<Tribool> + Copy> PartialOrd<B> for Tribool {
    #[inline]
    fn partial_cmp(&self, rhs: &B) -> Option<Ordering> {
        self.compare((*rhs).into())
    }

    #[inline]
    fn lt(&self, rhs: &B) -> bool {
        match (*self, (*rhs).into()) {
            (False, True) => true,
            _ => false,
        }
    }

    #[inline]
    fn le(&self, rhs: &B) -> bool {
        match (*self, (*rhs).into()) {
            (True, True) | (False, False) | (False, True) => true,
            _ => false,
        }
    }

    #[inline]
    fn gt(&self, rhs: &B) -> bool {
        match (*self, (*rhs).into()) {
            (True, False) => true,
            _ => false,
        }
    }

    #[inline]
    fn ge(&self, rhs: &B) -> bool {
        match (*self, (*rhs).into()) {
            (True, True) | (False, False) | (True, False) => true,
            _ => false,
        }
    }
}

impl Not for Tribool {
    type Output = Tribool;

    #[inline]
    fn not(self) -> Tribool {
        self.negate()
    }
}

impl<B: Into<Tribool>> BitAnd<B> for Tribool {
    type Output = Tribool;

    #[inline]
    fn bitand(self, rhs: B) -> Tribool {
        self.and(rhs.into())
    }
}

impl<B: Into<Tribool>> BitOr<B> for Tribool {
    type Output = Tribool;

    #[inline]
    fn bitor(self, rhs: B) -> Tribool {
        self.or(rhs.into())
    }
}

impl<B: Into<Tribool>> BitXor<B> for Tribool {
    type Output = Tribool;

    #[inline]
    fn bitxor(self, rhs: B) -> Tribool {
        self.xor(rhs.into())
    }
}

macro_rules! impl_binary_op {
    ($op:ident => $f:ident, $assign_op:ident => $af:ident) => {
        impl $op<Tribool> for bool {
            type Output = Tribool;

            #[inline]
            fn $f(self, rhs: Tribool) -> Tribool {
                rhs.$f(self)
            }
        }

        impl<B: Into<Tribool>> $assign_op<B> for Tribool {
            #[inline]
            fn $af(&mut self, rhs: B) {
                *self = self.$f(rhs.into());
            }
        }

        impl $assign_op<Tribool> for bool {
            #[inline]
            fn $af(&mut self, rhs: Tribool) {
                *self = rhs.$f(*self).is_true()
            }
        }
    };
}

impl_binary_op!(BitAnd => bitand, BitAndAssign => bitand_assign);
impl_binary_op!(BitOr => bitor, BitOrAssign => bitor_assign);
impl_binary_op!(BitXor => bitxor, BitXorAssign => bitxor_assign);

impl From<bool> for Tribool {
    #[inline]
    fn from(value: bool) -> Tribool {
        Tribool::boolean(value)
    }
}

/// Error result of `bool::try_from(TriBool::Indeterminate)`
#[derive(Debug, Clone, Copy)]
pub struct IndeterminateError;

impl TryFrom<Tribool> for bool {
    type Error = IndeterminateError;

    #[inline]
    fn try_from(value: Tribool) -> Result<Self, Self::Error> {
        match value {
            True => Ok(true),
            False => Ok(false),
            Indeterminate => Err(IndeterminateError),
        }
    }
}

impl From<Result<Tribool, IndeterminateError>> for Tribool {
    #[inline]
    fn from(value: Result<Tribool, IndeterminateError>) -> Self {
        match value {
            Ok(t) => t,
            Err(_) => Indeterminate,
        }
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
    };
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
    };
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
        assert_eq!(True, True);
        assert_ne!(True, False);
        assert_ne!(False, True);
        assert_eq!(False, False);

        assert!(!(Indeterminate == True));
        assert!(!(Indeterminate == False));
        assert!(!(Indeterminate == Indeterminate));
        assert!(!(Indeterminate != True));
        assert!(!(Indeterminate != False));
        assert!(!(Indeterminate != Indeterminate));
    }

    #[test]
    fn bool_equality() {
        assert_eq!(True, true);
        assert_eq!(False, false);
        assert_ne!(True, false);
        assert_ne!(False, true);
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
    fn kleene() {
        assert!(True.kleene_implication(True).is_true());
        assert!(Indeterminate.kleene_implication(True).is_true());
        assert!(False.kleene_implication(True).is_true());

        assert!(True.kleene_implication(Indeterminate).is_indeterminate());
        assert!(Indeterminate
            .kleene_implication(Indeterminate)
            .is_indeterminate());
        assert!(False.kleene_implication(Indeterminate).is_true());

        assert!(True.kleene_implication(False).is_false());
        assert!(Indeterminate.kleene_implication(False).is_indeterminate());
        assert!(False.kleene_implication(False).is_true());
    }

    #[test]
    fn lukasiewicz() {
        assert!(True.lukasiewicz_implication(True).is_true());
        assert!(Indeterminate.lukasiewicz_implication(True).is_true());
        assert!(False.lukasiewicz_implication(True).is_true());

        assert!(True
            .lukasiewicz_implication(Indeterminate)
            .is_indeterminate());
        assert!(Indeterminate
            .lukasiewicz_implication(Indeterminate)
            .is_true());
        assert!(False.lukasiewicz_implication(Indeterminate).is_true());

        assert!(True.lukasiewicz_implication(False).is_false());
        assert!(Indeterminate
            .lukasiewicz_implication(False)
            .is_indeterminate());
        assert!(False.lukasiewicz_implication(False).is_true());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde() {
        let res_false = serde_json::to_string_pretty(&Tribool::False)
            .expect("serde Serialize impl for False failed");
        let res_true = serde_json::to_string_pretty(&Tribool::True)
            .expect("serde Serialize impl for True failed");
        let res_none = serde_json::to_string_pretty(&Tribool::Indeterminate)
            .expect("serde Serialize impl for Indeterminate failed");

        assert!(serde_json::from_str::<Tribool>(&res_false)
            .expect("serde Deserialize impl for False failed")
            .is_false());
        assert!(serde_json::from_str::<Tribool>(&res_true)
            .expect("serde Deserialize impl for True failed")
            .is_true());
        assert!(serde_json::from_str::<Tribool>(&res_none)
            .expect("serde Deserialize impl for Indeterminate failed")
            .is_indeterminate())
    }
}
