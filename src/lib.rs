//! Provides an expression macro `try_match` that performs pattern
//! matching and returns the bound variables via `Ok(_)` iff successful.
//!
//! # Examples
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
//! assert_eq!(try_match!(Var1(x) = Var1(42)    => x),     Ok(42));
//! assert_eq!(try_match!(Var2    = Var2::<u32> => "yay"), Ok("yay"));
//!
//! // `Err(input)` on failure
//! assert_eq!(try_match!(Var1(x) = Var2::<u32> => x),     Err(Var2));
//! assert_eq!(try_match!(Var2    = Var1(42)    => "yay"), Err(Var1(42)));
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
//! assert_eq!(try_match!(Var1(_) = Var1(42)), Ok(()));
//!
//! // The bound variable if there is exactly one bound variables
//! assert_eq!(try_match!(Var1(x) = Var1(42)), Ok(42));
//!
//! // An anonymous struct if there are multiple bound variables
//! let vars = try_match!(Var1((a, b)) = Var1((12, 34))).unwrap();
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
//! let (a, b) = try_match!(Var1((_0, _1)) = Var1((12, 34))).unwrap();
//! assert_eq!((a, b), (12, 34));
//! ```
//!
//! It's an error to specify non-contiguous binding indices:
//!
//! ```compile_fail
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let _ = try_match!(Var1((_0, _2)) = Var1((12, 34)));
//! ```
//!
//! ```compile_fail
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let _ = try_match!(Var1((_0, _9223372036854775808)) = Var1((12, 34)));
//! ```
//!
//! # Restrictions
//!
//!  - Macros cannot be used in a supplied pattern.
//!
//! # Related Work
//!
//! [`matches!`][] (now incorporated into the standard library as
//! [`core::matches!`][]) is similar but only returns `bool` indicating whether
//! matching was successful or not.
//!
//! ```
//! # use try_match::try_match;
//! # use if_rust_version::if_rust_version;
//! if_rust_version! { >= 1.42 {
//!     let success1 = matches!(Some(42), Some(_));
//! } }
//! let success2 = try_match!(Some(_) = Some(42)).is_ok();
//! ```
//!
//! [`matches!`]: https://crates.io/crates/matches
//!
#![no_std]

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
    ($(|)? $($p:pat)|+ = $in:expr => $out:expr) => {
        match $in {
            $($p)|+ => ::core::result::Result::Ok($out),
            in_value => ::core::result::Result::Err(in_value),
        }
    };

    // Using `$($in:tt)*` in place of `$in:expr` is a work-around for
    // <https://github.com/dtolnay/proc-macro-hack/issues/46>, which is
    // originally caused by <https://github.com/rust-lang/rust/issues/43081>
    ($(|)? $($p:pat)|+ = $($in:tt)*) => {
        // `$p` needs to be parenthesized for it to work on nightly-2020-05-30
        // and syn 1.0.29
        $crate::implicit_try_match!(($($p)|+) = $($in)*)
    };
}

#[cfg(feature = "implicit_map")]
#[macro_export]
#[doc(hidden)]
macro_rules! implicit_try_match {
    (($($p:tt)*) = $($in:tt)*) => {
        // `$p` needs to be parenthesized for it to work on nightly-2020-05-30
        // and syn 1.0.29
        $crate::implicit_try_match_inner!($($p)* = $($in)*)
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
///
/// `#[proc_macro_hack]` makes it possible to use this procedural macro in
/// expression position without relying on an unstable rustc feature, but with
/// some restrictions. See `proc_macro_hack`'s documentation for more.
#[cfg(feature = "implicit_map")]
#[proc_macro_hack::proc_macro_hack]
#[doc(hidden)]
pub use try_match_inner::implicit_try_match_inner;
