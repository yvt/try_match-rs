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
//! # Related Work: `matches`
//!
//! [`matches!`] is similar but only returns `bool` indicating whether matching
//! was successful or not.
//!
//! ```no_compile
//! let success1 = matches!(Var1(42), Var1(_));
//! let success2 = try_match!(Var1(_) = Var1(42)).is_ok();
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
/// - If there is exactly one bound variables `var`, it is implied to be `var`.
/// - If there are multiple bound variables `var1, var2, ...`, it is implied to
///   be `AnonymousType { var1, var2 }`.
///
/// `AnonymousType` derives `Clone` and `Copy`, and `Debug` if `std` feature is
/// enabled.
///
/// See [the crate-level documentation](index.html) for examples.
#[macro_export]
macro_rules! try_match {
    ($p:pat = $in:expr) => {
        match $in {
            $p => ::core::result::Result::Ok($crate::collect_captures_outer!($p)),
            in_value => ::core::result::Result::Err(in_value),
        }
    };
    ($p:pat = $in:expr => $out:expr) => {
        match $in {
            $p => ::core::result::Result::Ok($out),
            in_value => ::core::result::Result::Err(in_value),
        }
    };
}

/// Given a pattern, creates an expression that includes bound variables.
///
/// - If there are no bound variables, it generates `()`.
/// - If there is exactly one bound variables `var`, it generates `var`.
/// - If there are multiple bound variables `var1, var2, ...`, it generates
///   `SomeType { var1, var2 }`.
///
#[cfg(feature = "std")]
#[doc(hidden)]
#[macro_export]
macro_rules! collect_captures_outer {
    ($p:pat) => { $crate::collect_captures!(std $p) };
}

#[cfg(not(feature = "std"))]
#[doc(hidden)]
#[macro_export]
macro_rules! collect_captures_outer {
    ($p:pat) => { $crate::collect_captures!(no_std $p) };
}

/// `#[proc_macro_hack]` makes it possible to use this procedural macro in
/// expression position without relying on an unstable rustc feature, but with
/// some restrictions. See `proc_macro_hack`'s documentation for more.
#[cfg(feature = "implicit_map")]
#[proc_macro_hack::proc_macro_hack]
#[doc(hidden)]
pub use try_match_inner::collect_captures;

#[cfg(not(feature = "implicit_map"))]
#[macro_export]
macro_rules! collect_captures {
    ($p:pat) => {
        compile_error!(
            "can't use the implicit mapping form of `try_match!` because \
             the feature `implicit_map` is disabled"
        )
    };
}
