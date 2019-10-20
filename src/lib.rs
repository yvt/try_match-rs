//! Provides a procedural expression macro `try_match` that performs pattern
//! matching and returns the bound variables via `Ok(_)` iff successful.
//!
//! # Examples
//!
//! ```
//! use try_match::try_match;
//!
//! // The right-hand side of `=>` if successful
//! assert_eq!(try_match!(Some(x) = Some(42) => x), Ok(42));
//!
//! // `None(input)` on failure
//! assert_eq!(try_match!(Some(x) = None::<u32> => x), Err(None));
//! ```
//!
//! `=>` and the part that comes after can be omitted (requires `implicit_map`
//! feature, which is enabled by default):
//!
//! ```
//! # use try_match::try_match;
//! // `()` if there are no bound variables
//! assert_eq!(try_match!(Some(_) = Some(42)), Ok(()));
//!
//! // The bound variable if there is exactly one bound variables
//! assert_eq!(try_match!(Some(x) = Some(42)), Ok(42));
//!
//! // An anonymous struct if there are multiple bound variables
//! let vars = try_match!(Some((a, b)) = Some((12, 34))).unwrap();
//! assert_eq!((vars.a, vars.b), (12, 34));
//! ```
//!
//! # Restrictions
//!
//!  - Macros cannot be used in a supplied pattern.
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
        if let $p = $in {
            ::core::result::Result::Ok($crate::collect_captures_outer!($p))
        } else {
            ::core::result::Result::Err($in)
        }
    };
    ($p:pat = $in:expr => $out:expr) => {
        if let $p = $in {
            ::core::result::Result::Ok($out)
        } else {
            ::core::result::Result::Err($in)
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
