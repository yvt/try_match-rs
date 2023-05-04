//! Provides expression macros to match a pattern on a given expression.
//!
//! # Basic Usage
//!
//! ## Macros
//!
//! [`try_match!`] returns [`Result`]: `Ok(bindings)` on success or
//! `Err(input)` on failure:
//!
//! ```rust
//! # use try_match::try_match;
//! # #[derive(Copy, Clone, Debug, PartialEq)]
//! # enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! assert_eq!(try_match!(Var1(42), Var1(x)), Ok(42));
//! assert_eq!(try_match!(Var1(42), Var1(x) if x < 20), Err(Var1(42)));
//! ```
//!
//! [`match_ok!`] returns [`Option`]: `Some(bindings)` on success or
//! `None` on failure:
//!
//! ```rust
//! # use try_match::match_ok;
//! # #[derive(Copy, Clone, Debug, PartialEq)]
//! # enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! assert_eq!(match_ok!(Var1(42), Var1(x)), Some(42));
//! assert_eq!(match_ok!(Var1(42), Var1(x) if x < 20), None);
//! ```
//!
//! [`unwrap_match!`] panics on failure:
//!
//! ```rust
//! # use try_match::unwrap_match;
//! # #[derive(Copy, Clone, Debug, PartialEq)]
//! # enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! assert_eq!(unwrap_match!(Var1(42), Var1(x)), 42);
//! ```
//!  
//! ```rust,should_panic
//! # use try_match::unwrap_match;
//! # #[derive(Copy, Clone, Debug, PartialEq)]
//! # enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! unwrap_match!(Var1(42), Var1(x) if x < 20);
//! ```
//!
//! ## Implicit Mapping
//!
//! *Requires `implicit_map` Cargo feature (enabled by default)*
//!
//! ```
//! use try_match::unwrap_match;
//!
//! #[derive(Debug, PartialEq)]
//! enum Enum<T> { Var1(T), Var2 }
//! use Enum::{Var1, Var2};
//!
//! // `()` if there are no bound variables
//! assert_eq!(unwrap_match!(Var1(42), Var1(_)), ());
//!
//! // The bound variable if there is exactly one bound variable
//! assert_eq!(unwrap_match!(Var1(42), Var1(x)), 42);
//!
//! // An anonymous struct if there are multiple bound variables
//! let vars = unwrap_match!(Var1((12, 34)), Var1((a, b)));
//! assert_eq!((vars.a, vars.b), (12, 34));
//! ```
//!
//! It produces a tuple if you name the bound variables like `_0`, `_1`, `_2`,
//! ...:
//!
//! ```
//! # use try_match::unwrap_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let (a, b) = unwrap_match!(Var1((12, 34)), Var1((_0, _1)));
//! assert_eq!((a, b), (12, 34));
//! ```
//!
//! It's an error to specify non-contiguous binding indices:
//!
//! ```compile_fail
//! # use try_match::unwrap_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! unwrap_match!(Var1((12, 34)), Var1((_0, _2)));
//! ```
//!
//! ## Explicit Mapping
//!
//! An optional `=>` clause specifies an explicit output mapping:
//!
//! ```
//! # use try_match::unwrap_match;
//! # #[derive(Copy, Clone, Debug, PartialEq)]
//! # enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! // The right-hand side of `=>` if successful
//! assert_eq!(unwrap_match!(Var1(42),    Var1(x) => x + 1),    43);
//! assert_eq!(unwrap_match!(Var2::<u32>, Var2    => "yay"), "yay");
//! ```
//!
//! ## Partial Application
//!
//! Omit the scrutinee expression to produce a closure:
//!
//! ```rust
//! # use try_match::try_match;
//! # #[derive(Debug, PartialEq)] enum Enum<T> { Var1(T), Var2 }
//! # use Enum::{Var1, Var2};
//! let _:                  Result<i32, _> = try_match!(Var1(42), Var1(x));
//! let _: fn(Enum<i32>) -> Result<i32, _> = try_match!(        , Var1(x));
//!
//! assert_eq!(try_match!(Var1(42), Var1(x)), Ok(42));
//! //                    ^^^^^^^^  -------
//! assert_eq!(try_match!(, Var1(x))(Var1(42)), Ok(42));
//! //                      -------  ^^^^^^^^
//!
//! // Equivalent to:
//! assert_eq!((|x| try_match!(x, Var1(x)))(Var1(42)), Ok(42));
//! //                            -------   ^^^^^^^^
//! ```
//!
//! ```rust
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
//! ```
//!
//! *Caveat:* Since this mode is implemented by a closure,
//! [the default binding mode][] ([RFC 2005][]), ownership, and control flow
//! may work differently.
//!
//! <details><summary>Examples (click to show)</summary>
//!
//! ```rust
//! # use try_match::try_match;
//! try_match!(&Some(42), Some(_0));
//! try_match!(&Some(42), &Some(ref _0));
//! ```
//!
//! ```rust,compile_fail
//! # use try_match::try_match;
//! try_match!(, Some(_0))(&Some(42));
//! // ERROR: expected enum `Option`, found reference
//! ```
//!
//! ```rust
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
//! ```
//!
//! ```rust
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
//! ```
//!
//! </details>
//!
//! [the default binding mode]: https://doc.rust-lang.org/1.69.0/reference/patterns.html#binding-modes
//! [RFC 2005]: https://rust-lang.github.io/rfcs/2005-match-ergonomics.html
//!
//! # Unstable Features
//!
//! *Requires `unstable` Cargo feature, exempt from semver guarantees.*
//!
//! No unstable features are defined in this version.
//!
//! # Quirks
//!
//! ## Macros Inside Patterns
//!
//! When using implicit mapping, bind variables defined inside macros are
//! not recognized because, at the point of `try_match`'s macro expansion,
//! these macros are not expanded yet.
//!
//! ## Input Ownership
//!
//! [`try_match!`] moves a value out of the place represented by the input
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
//! [`match_ok!`] and [`unwrap_match!`] do not have this issue:
//!
//! ```rust
//! # use try_match::match_ok;
//! #[derive(Debug)] struct UncopyValue;
//! let array = [Some(UncopyValue), None];
//! let _: &UncopyValue = match_ok!(array[0], Some(ref x)).unwrap();
//! ```
//!
//! ```rust
//! # use try_match::unwrap_match;
//! #[derive(Debug)] struct UncopyValue;
//! let array = [Some(UncopyValue), None];
//! let _: &UncopyValue = unwrap_match!(array[0], Some(ref x));
//! ```
//!
//! ## Binding/Constant Disambiguation
//!
//! An identifier in a pattern is either a variable binding or a constant
//! pattern, and these cannot be distinguished syntactically. To address this
//! problem, the implicit mapper employs heuristics based on the standard naming
//! conventions ([RFC 430][]).
//!
//! ```rust
//! # use try_match::try_match;
//! const ZERO: i32 = 0;
//!
//! // Binding: `zero` matches regex /^_?[a-z0-9]/
//! assert_eq!(try_match!(42, zero), Ok(42));
//!
//! // Constant: `ZERO` matches regex /^_?[A-Z]/
//! assert_eq!(try_match!(42, ZERO), Err(42));
//!
//! // Binding: Only a binding can have a subpattern
//! assert_eq!(try_match!(42, THE_ANSWER @ _), Ok(42));
//! ```
//!
//! ```rust,compile_fail
//! # use try_match::try_match;
//! // ERROR: ambiguous identifier pattern
//! assert_eq!(try_match!(42, 你好), Ok(42));
//! ```
//!
//! [RFC 430]: https://rust-lang.github.io/rfcs/0430-finalizing-naming-conventions.html
#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(feature = "_doc_cfg", feature(doc_cfg))]

/// Try to match `$in` against a given pattern `$p`. Produces `Ok($out)` if
/// successful; `Err($in)` otherwise.
///
/// ```rust,ignore
/// try_match!($( $in:expr )?, $p:pat_multi $( if $guard:expr )? $( => $out:expr )? $( , )?)
/// ```
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
/// `$in` can be left out to produce a closure ([partial
/// application](crate#partial-application)).
///
/// See [the crate-level documentation](crate#basic-usage) for examples.
#[macro_export]
macro_rules! try_match {
    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)? => $out:expr $(,)?) => {
        match $in {
            $($p)|+ $(if $guard)? => ::core::result::Result::Ok($out),
            in_value => ::core::result::Result::Err(in_value),
        }
    };

    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)? $(,)?) => {
        $crate::implicit_try_match!(
            $in,
            $($p)|+ $(if $guard)?,
            { ::core::result::Result::Ok }
            { in_value => ::core::result::Result::Err(in_value) }
        )
    };

    // Partial application
    (, $($pattern_and_rest:tt)*) => {
        |scrutinee| $crate::try_match!(scrutinee, $($pattern_and_rest)*)
    }
}

/// Try to match `$in` against a given pattern `$p`. Produces `Some($out)` if
/// successful; `None` otherwise.
///
/// ```rust,ignore
/// match_ok!($( $in:expr )?, $p:pat_multi $( if $guard:expr )? $( => $out:expr )? $( , )?)
/// ```
///
/// `=> $out` can be left out, in which case it's implied in the same way as
/// [`try_match!`].
///
/// `$in` can be left out to produce a closure ([partial
/// application](crate#partial-application)).
///
/// See [the crate-level documentation](crate#basic-usage) for examples.
#[macro_export]
macro_rules! match_ok {
    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)? => $out:expr $(,)?) => {
        match $in {
            $($p)|+ $(if $guard)? => ::core::option::Option::Some($out),
            _ => ::core::option::Option::None,
        }
    };

    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)? $(,)?) => {
        $crate::implicit_try_match!(
            $in,
            $($p)|+ $(if $guard)?,
            { ::core::option::Option::Some }
            { _ => ::core::option::Option::None }
        )
    };

    // Partial application
    (, $($pattern_and_rest:tt)*) => {
        |scrutinee| $crate::match_ok!(scrutinee, $($pattern_and_rest)*)
    }
}

/// Try to match `$in` against a given pattern `$p`. Panics on failure.
///
/// ```rust,ignore
/// unwrap_match!(
///     $( $in:expr )?,
///     $p:pat_multi $( if $guard:expr )? $( => $out:expr )?
///     // An optional panic message to replace the default one;
///     // removes the `$in: Debug` requirement
///     $( , $( $( $panic_args:tt )+ $( , )? )? )?
/// )
/// ```
///
/// `=> $out` can be left out, in which case it's implied in the same way as
/// [`try_match!`].
///
/// `$in` can be left out to produce a closure ([partial
/// application](crate#partial-application)).
///
/// See [the crate-level documentation](crate#basic-usage) for examples.
#[macro_export]
macro_rules! unwrap_match {
    ($($in:expr)?, $(|)? $($p:pat)|+ $(if $guard:expr)? $( => $out:expr)?) => {
        // Add a trailing comma
        $crate::unwrap_match!($($in)?, $($p)|+ $(if $guard)? $( => $out)? ,)
    };

    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)? => $out:expr, $($panic_arg:tt)*) => {
        match $in {
            $($p)|+ $(if $guard)? => $out,
            ref in_val => $crate::unwrap_failed!(
                { in_val }
                { $($p)|+ $(if $guard)? }
                { $($panic_arg)* }
            ),
        }
    };

    ($in:expr, $(|)? $($p:pat)|+ $(if $guard:expr)?, $($panic_arg:tt)*) => {
        $crate::implicit_try_match!(
            $in,
            $($p)|+ $(if $guard)?,
            {}
            { ref in_val => $crate::unwrap_failed!(
                { in_val }
                { $($p)|+ $(if $guard)? }
                { $($panic_arg)* }
            ) }
        )
    };

    // Partial application
    (, $($pattern_and_rest:tt)* ) => {
        |scrutinee| $crate::unwrap_match!(scrutinee, $($pattern_and_rest)*)
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

#[macro_export]
#[doc(hidden)]
macro_rules! unwrap_failed {
    (
        { $in_val:tt } { $($pat:tt)* } { $(,)? }
    ) => {
        $crate::unwrap_failed($in_val, $crate::stringify!($($pat)*))
    };
    (
        $in_val:tt $pat:tt { $($arg:tt)* }
    ) => {
        $crate::panic!($($arg)*)
    };
}

// used by `unwrap_failed!`
#[doc(hidden)]
pub use core::{panic, stringify};

#[cold]
#[track_caller]
#[doc(hidden)]
pub fn unwrap_failed(in_val: &(impl core::fmt::Debug + ?Sized), pattern: &str) -> ! {
    panic!(
        "assertion failed: '{:?}' does not match '{}'",
        in_val, pattern
    );
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
