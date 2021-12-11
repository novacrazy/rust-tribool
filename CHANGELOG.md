Changelog
=========

## 0.3.0
* Added `const` versions of all operators
* Added serde support (#5) (`serde` feature)
* Removed `impl From<TriBool> for bool` and replaced it with `impl TryFrom<TriBool> for bool`
    * Use `TriBool::is_true()` for the old `From` behavior

## 0.2.0

* Use `Into<Tribool>` to simplify Tribool/bool operations.
* Remove `Eq` implementation, because `!(Indeterminate == Indeterminate)`

## 0.1.0

* Initial release