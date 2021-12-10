use crate::Tribool::{self, *};
use serde::de::{Error, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt::Formatter;

// ************************ //
// Serialize implementation //
// ************************ //
impl Serialize for Tribool {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            True | False => serializer.serialize_bool(self.is_true()),
            Indeterminate => serializer.serialize_none(),
        }
    }
}

// ******************************* //
// Boolean visitor for Deserialize //
// ******************************* //
struct NullBoolVisitor;
impl<'de> Visitor<'de> for NullBoolVisitor {
    type Value = Tribool;

    fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
        formatter.write_str("a nullable boolean value")
    }

    fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(Tribool::from(v))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(Tribool::Indeterminate)
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bool(Self)
    }
}

// ************************** //
// Deserialize implementation //
// ************************** //
impl<'de> Deserialize<'de> for Tribool {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_option(NullBoolVisitor)
    }

    fn deserialize_in_place<D>(deserializer: D, place: &mut Self) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        let val = deserializer.deserialize_option(NullBoolVisitor)?;
        *place = val;
        Ok(())
    }
}
