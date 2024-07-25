# try_match

[<img src="https://docs.rs/try_match/badge.svg" alt="docs.rs">](https://docs.rs/try_match/)

Fallible pattern matching with a function-like syntax

## Basic Usage

### Macros

```rust
use try_match::{try_match, match_ok, unwrap_match};

#[derive(Copy, Clone, Debug, PartialEq)]
enum Enum { Var0, Var1(i32), Var2(i32, i32) }

use Enum::*;

// `try_match!` returns `Result`: `Ok(bindings)` on success or
// `Err(input_value)` otherwise
assert_eq!(try_match!(Var1(42), Var1(x)), Ok(42));
assert_eq!(try_match!(Var0,     Var1(x)), Err(Var0));

// `match_ok!` returns `Option`
assert_eq!(match_ok!(Var1(42), Var1(x)), Some(42));
assert_eq!(match_ok!(Var0,     Var1(x)), None);

// `match_or_default!` returns a default value on failure
assert_eq!(match_or_default!(Var1(42), Var1(x)), 42);
assert_eq!(match_or_default!(Var0,     Var1(x)), 0);

// `unwrap_match!` panics on failure:
assert_eq!(unwrap_match!(Var1(42), Var1(x)), 42);
        /* unwrap_match!(Var0,     Var1(x)); */ // this will panic
```

Match guards (`if <expr>`) are supported:

```rust
assert_eq!(match_ok!(Var1(42), Var1(x)),           Some(42));
assert_eq!(match_ok!(Var1(42), Var1(x) if x < 20), None);
```

### Bindings

```rust
// Returns `()` (wrapped by `Ok(_)`) if there are no bound variables
assert_eq!(unwrap_match!(Var1(42), Var1(_)), ());

// ... the bound value if there is exactly one binding
assert_eq!(unwrap_match!(Var1(42), Var1(x)), 42);

// ... an anonymous struct if there are multiple bindings
let vars = unwrap_match!(Var2(12, 34), Var2(a, b));
assert_eq!((vars.a, vars.b), (12, 34));

// ... or a tuple if the binding names are numeric
let (a, b) = unwrap_match!(Var2(12, 34), Var2(_0, _1));
assert_eq!((a, b), (12, 34));

// An optional `=>` clause specifies an explicit mapping
assert_eq!(unwrap_match!(Var1(42), Var1(x) => x + 1), 43);
assert_eq!(unwrap_match!(Var0,     Var0    => "yay"), "yay");
```

### Partial Application

```rust
// Omit the scrutinee expression to produce a closure
let _:             Option<i32> = match_ok!(Var1(42), Var1(x));
let _: fn(Enum) -> Option<i32> = match_ok!(        , Var1(x));
```

## Applications

### `Iterator::filter_map`

```rust
let array = [Var1(42), Var0, Var1(10)];
let filtered: Vec<_> = array
    .iter()
    .filter_map(match_ok!(, &Var1(_0) if _0 > 20))
    .collect();
assert_eq!(filtered, [42]);
```

### `Iterator::map` + Fallible `Iterator::collect`

```rust
let array = [Var1(42), Var0, Var1(10)];
let filtered: Result<Vec<_>, _> = array
    .iter()
    .map(try_match!(, &Var1(_0) if _0 > 20))
    .collect();

// `Var0` is the first value that doesn't match
assert_eq!(filtered, Err(&Var0));
```

### Extract Variants

```rust
impl Enum {
    fn var1(&self) -> Option<&i32> {
        match_ok!(self, Var1(_0))
    }

    fn is_var2(&self) -> bool {
        matches!(self, Var0)
    }
}

let enums = [Var1(42), Var0];
assert_eq!(enums[0].var1(), Some(&42));
assert_eq!(enums[1].var1(), None);

assert!(!enums[0].is_var2());
assert!(enums[1].is_var2());
```

### Expect Certain Variants

```rust
fn this_fn_expects_var2(foo: &Enum) {
    let i = unwrap_match!(foo, &Var2(42, _0));

    // Alternatively, you could use let-else (stabilized in Rust 1.65.0):
    // let &Var2(42, i) = foo else { panic!("{foo:?}") };

    assert_eq!(i, 84);
}

this_fn_expects_var2(&Var2(42, 84));
```

## Related Works

[`matcher::matches!`][] (now incorporated into the standard library as
[`core::matches!`][]) is similar but only returns `bool` indicating whether
matching was successful or not.

```rust
let success1 =  matches!(Some(42), Some(_));
let success2 = match_ok!(Some(42), Some(_)).is_some();
assert_eq!(success1, success2);
```

[`bind_match::bind_match!`][] and [`extract::extract!`][] behave in the same way
as `match_ok!` except for the lack of implicit mapping and partial application.

[`variant::get_variant!`][] from the `extract_variant` crate offers a similar
functionality to `match_ok!`. It supports implicit mapping but uses different
rules to handle multiple bindings.

[`core::matches!`]: https://doc.rust-lang.org/1.56.0/core/macro.matches.html
[`matcher::matches!`]: https://crates.io/crates/matches
[`bind_match::bind_match!`]: https://crates.io/crates/bind_match
[`extract::extract!`]: https://crates.io/crates/extract_macro
[`variant::get_variant!`]: https://crates.io/crates/extract-variant/1.0.0

## License

MIT/Apache-2.0
