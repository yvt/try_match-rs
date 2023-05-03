//! Provides an expression macro `try_match` that matches a pattern on a given
//! expression and returns the bound variables in `Ok(_)` if successful.
//!
//! # Basic Usage
//!
//! ## Explicit Mapping
//!
//! ```
//! use try_match::try_match;
//!
//! #[derive(Copy, Clone, Debug, PartialEq)]
//! enum Enum<T> { Var1(T), Var2 }
//! use Enum::{Var1, Var2};
//!
//! // The right-hand side of `=>` if successful
//! assert_eq!(try_match!(Var1(42),    Var1(x) => x),     Ok(42));
//! assert_eq!(try_match!(Var2::<u32>, Var2    => "yay"), Ok("yay"));
//!
//! // `Err(input)` on failure
//! assert_eq!(try_match!(Var2::<u32>, Var1(x) => x),     Err(Var2));
//! assert_eq!(try_match!(Var1(42),    Var2    => "yay"), Err(Var1(42)));
//!
//! // Supports `if` guard
//! assert_eq!(try_match!(Var1(42), Var1(x) if x < 20 => x), Err(Var1(42)));
//! ```
//!
//! ## Implicit Mapping
//!
//! `=>` and the part that comes after can be omitted (requires `implicit_map`
//! feature, which is enabled by default; you can disable it to skip the
//! compilation of the internal procedural macro):
//!
//! ```
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! // `()` if there are no bound variables
//! assert_eq!(try_match!(Var1(42), Var1(_)), Ok(()));
//!
//! // The bound variable if there is exactly one bound variables
//! assert_eq!(try_match!(Var1(42), Var1(x)), Ok(42));
//! assert_eq!(try_match!(Var1(42), Var1(x) if x < 20), Err(Var1(42)));
//!
//! // An anonymous struct if there are multiple bound variables
//! let vars = try_match!(Var1((12, 34)), Var1((a, b))).unwrap();
//! assert_eq!((vars.a, vars.b), (12, 34));
//! ```
//!
//! It produces a tuple if you name the bound variables like `_0`, `_1`, `_2`,
//! ...:
//!
//! ```
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let (a, b) = try_match!(Var1((12, 34)), Var1((_0, _1))).unwrap();
//! assert_eq!((a, b), (12, 34));
//!
//! try_match!(Var1((12, 34)), Var1((_0, _1)) if _0 == _1).unwrap_err();
//! ```
//!
//! It's an error to specify non-contiguous binding indices:
//!
//! ```compile_fail
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let _ = try_match!(Var1((12, 34)), Var1((_0, _2)));
//! ```
//!
//! # Unstable Features
//!
//! *Requires `unstable` Cargo feature, exempt from semver guarantees.*
//!
//! <details><summary><h3>Partial Application</h3></summary>
//!
//! Tracking issue: [#3](https://github.com/yvt/try_match-rs/issues/3)
//!
//! Omit the scrutinee expression to produce a closure:
//!
//! ```rust
//! # {
//! #![cfg(feature = "unstable")]
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! assert_eq!(try_match!(Var1(42), Var1(x)), Ok(42));
//! //                    ^^^^^^^^  -------
//! assert_eq!(try_match!(, Var1(x))(Var1(42)), Ok(42));
//! //                      -------  ^^^^^^^^
//!
//! // Equivalent to:
//! assert_eq!((|x| try_match!(x, Var1(x)))(Var1(42)), Ok(42));
//! //                             -------  ^^^^^^^^
//! # }
//! ```
//!
//! ```rust
//! # {
//! #![cfg(feature = "unstable")]
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let array = [Var1(42), Var2, Var1(10)];
//! let filtered: Result<Vec<_>, _> = array
//!     .iter()
//!     .map(try_match!(, &Var1(_0) if _0 > 20))
//!     .collect();
//!
//! // `Var2` is the first value that doesn't match
//! assert_eq!(filtered, Err(&Var2));
//! # }
//! ```
//!
//! *Caveat:* Since this mode is implemented by a closure,
//! [the default binding mode][] ([RFC 2005][]), ownership, and control flow
//! may work differently:
//!
//! ```rust
//! # {
//! # #![cfg(feature = "unstable")]
//! # use try_match::try_match;
//! try_match!(&Some(42), Some(_0));
//! try_match!(&Some(42), &Some(ref _0));
//! # }
//! ```
//!
//! ```rust,compile_fail
//! # use try_match::try_match;
//! try_match!(, Some(_0))(&Some(42));
//! // ERROR: expected enum `Option`, found reference
//! ```
//!
//! ```rust
//! # {
//! # #![cfg(feature = "unstable")]
//! # use try_match::try_match;
//! use std::rc::Rc;
//!
//! // `rc2` is conditionally dropped
//! let rc1 = Rc::new(());
//! let rc2 = Rc::clone(&rc1);
//! try_match!(None::<()>, Some(_) => drop(rc2));
//! assert_eq!(Rc::strong_count(&rc1), 2);
//!
//! // `rc2` is unconditionally moved into a closure and dropped
//! let rc1 = Rc::new(());
//! let rc2 = Rc::clone(&rc1);
//! try_match!(, Some(_) => drop(rc2))(None::<()>);
//! assert_eq!(Rc::strong_count(&rc1), 1);
//! # }
//! ```
//!
//! ```rust
//! # {
//! # #![cfg(feature = "unstable")]
//! # use try_match::try_match;
//! fn func_uncurried() {
//!     try_match!((), () => return);
//!     unreachable!();
//! }
//!
//! fn func_curried() -> i32 {
//!     try_match!(, () => return Ok(()))(());
//!     42  // reachable
//! }
//!
//! func_uncurried();
//! func_curried();
//! # }
//! ```
//!
//! [the default binding mode]: https://doc.rust-lang.org/1.69.0/reference/patterns.html#binding-modes
//! [RFC 2005]: https://rust-lang.github.io/rfcs/2005-match-ergonomics.html
//!
//! </details>
//!
//! # Quirks
//!
//! When using implicit mapping, bind variables defined inside macros are
//! not recognized because at the point of `try_match`'s macro expansion,
//! inner macros are not expended yet.
//!
//! This macro moves a value out of the place represented by the input
//! expression to return it on failure. Make sure to pass a reference if this is
//! not desired.
//!
//! ```compile_fail
//! # use try_match::try_match;
//! #[derive(Debug)] struct UncopyValue;
//! let array = [Some(UncopyValue), None];
//! // ERROR: Can't move out of `array[0]`
//! let _: &UncopyValue = try_match!(array[0], Some(ref x)).unwrap();
//! ```
//!
//! ```
//! # use try_match::try_match;
//! # #[derive(Debug)] struct UncopyValue;
//! # let array = [Some(UncopyValue), None];
//! let _: &UncopyValue = try_match!(&array[0], Some(x)).unwrap();
//! ```
//!
//! # Applications
//!
//! ## `Iterator::filter_map`
//!
//! ```rust
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let array = [Var1(42), Var2, Var1(10)];
//! let filtered: Vec<_> = array
//!     .iter()
//!     .filter_map(|x| try_match!(x, &Var1(_0) if _0 > 20).ok())
//!     .collect();
//! assert_eq!(filtered, [42]);
//! ```
//!
//! ## `Iterator::map` + Fallible `Iterator::collect`
//!
//! ```rust
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let array = [Var1(42), Var2, Var1(10)];
//! let filtered: Result<Vec<_>, _> = array
//!     .iter()
//!     .map(|x| try_match!(x, &Var1(_0) if _0 > 20))
//!     .collect();
//!
//! // `Var2` is the first value that doesn't match
//! assert_eq!(filtered, Err(&Var2));
//! ```
//!
//! ## Extract Variants
//!
//! ```rust
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! impl<T> Enum<T> {
//!     fn var1(&self) -> Option<&T> {
//!         try_match!(self, Var1(_0)).ok()
//!     }
//!
//!     fn is_var2(&self) -> bool {
//!         matches!(self, Var2)
//!     }
//! }
//!
//! let enums = [Var1(42), Var2];
//! assert_eq!(enums[0].var1(), Some(&42));
//! assert_eq!(enums[1].var1(), None);
//!
//! assert!(!enums[0].is_var2());
//! assert!(enums[1].is_var2());
//! ```
//!
//! ## Expect Certain Variants
//!
//! ```rust
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! fn this_fn_expects_var1(foo: &Enum<[u8; 4]>) {
//!     let (i0, i1) = try_match!(foo, &Var1([_0, _, _, _1])).unwrap();
//!
//!     // Once RFC 1303 is stabilized, you can do instead:
//!     // let &Var1([i0, _, _, i1]) = foo else { panic!("{:?}", foo) };
//!
//!     assert_eq!((i0, i1), (42, 45));
//! }
//!
//! this_fn_expects_var1(&Var1([42, 43, 44, 45]));
//! ```
//!
//! # Related Work
//!
//! [`matcher::matches!`][] (now incorporated into the standard library as
//! [`core::matches!`][]) is similar but only returns `bool` indicating whether
//! matching was successful or not.
//!
//! ```
//! # use try_match::try_match;
//! let success1 =   matches!(Some(42), Some(_));
//! let success2 = try_match!(Some(42), Some(_)).is_ok();
//! assert_eq!(success1, success2);
//! ```
//!
//! [`bind_match::bind_match!`][] and [`extract::extract!`][] use the same
//! syntax (except for implicit mapping) but return `Some(expr)` on success
//! instead.
//!
//! [`core::matches!`]: https://doc.rust-lang.org/1.56.0/core/macro.matches.html
//! [`matcher::matches!`]: https://crates.io/crates/matches
//! [`bind_match::bind_match!`]: https://crates.io/crates/bind_match
//! [`extract::extract!`]: https://crates.io/crates/extract_macro
//!
#![no_std]
#![forbid(unsafe_code)]

/// Try to match `$in` against a given pattern `$p`. Produces `Ok($out)` if
/// successful; `Err($in)` otherwise.
///
/// `=> $out` can be left out, in which case it's implied based on the number of
/// bound variables in `$p`:
///
/// - If there are no bound variables, it is implied to be `()`.
/// - If there is exactly one bound variable `var`, it is implied to be `var`.
/// - If there are multiple bound variables `var1, var2, ...`, it is implied to
///   be `AnonymousType { var1, var2 }`.
///
/// `AnonymousType` implements `Clone`, `Copy`, and `Debug`.
///
/// See [the crate-level documentation](index.html) for examples.
#[macro_export]
macro_rules! try_match {
    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)? => $out:expr) => {
        match $in {
            $($p)|+ $(if $guard)? => ::core::result::Result::Ok($out),
            in_value => ::core::result::Result::Err(in_value),
        }
    };

    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)?) => {
        $crate::implicit_try_match!($in, $($p)|+ $(if $guard)?)
    };

    // Partial application (requires `unstable` Cargo feature)
    (, $($pattern_and_rest:tt)*) => {
        $crate::assert_unstable!(
            ["partial application"]
            |scrutinee| $crate::try_match!(scrutinee, $($pattern_and_rest)*)
        )
    }
}

#[cfg(feature = "implicit_map")]
#[macro_export]
#[doc(hidden)]
macro_rules! implicit_try_match {
    ($in:expr, $($p:tt)*) => {
        $crate::implicit_try_match_inner!($in, $($p)*)
    };
}

#[cfg(not(feature = "implicit_map"))]
#[macro_export]
#[doc(hidden)]
macro_rules! implicit_try_match {
    ($($_:tt)*) => {
        compile_error!(
            "can't use the implicit mapping form of `try_match!` because \
             the feature `implicit_map` is disabled"
        )
    };
}

#[cfg(feature = "unstable")]
#[macro_export]
#[doc(hidden)]
macro_rules! assert_unstable {
    ([$($msg:tt)*] $($tt:tt)*) => {
        $($tt)*
    }
}

#[cfg(not(feature = "unstable"))]
#[macro_export]
#[doc(hidden)]
macro_rules! assert_unstable {
    ([$($msg:tt)*] $($tt:tt)*) => {
        compile_error!(concat!($($msg)*, " requires `unstable` Cargo feature"))
    }
}

/// Pattern: `$p:pat`
///
/// The produced expression evaluates to `Ok(_)` using bound variables on a
/// successful match on the given value.
///
/// - If there are no bound variables, it generates `()`.
/// - If there is exactly one bound variables `var`, it generates `var`.
/// - If there are multiple bound variables `var1, var2, ...`, it generates
///   `SomeType { var1, var2 }`.
///
/// Otherwise, the expression evaluates to `Err($in)`.
#[cfg(feature = "implicit_map")]
#[doc(hidden)]
pub use try_match_inner::implicit_try_match_inner;
