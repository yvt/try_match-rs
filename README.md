# try_match

[<img src="https://docs.rs/try_match/badge.svg" alt="docs.rs">](https://docs.rs/try_match/)

Provides an expression macro `try_match` that performs pattern
matching and returns the bound variables via `Ok(_)` iff successful.

## Examples

### Explicit Mapping

```rust
use try_match::try_match;

#[derive(Copy, Clone, Debug, PartialEq)]
enum Enum<T> { Var1(T), Var2 }
use Enum::{Var1, Var2};

// The right-hand side of `=>` if successful
assert_eq!(try_match!(Var1(42),    Var1(x) => x),     Ok(42));
assert_eq!(try_match!(Var2::<u32>, Var2    => "yay"), Ok("yay"));

// `Err(input)` on failure
assert_eq!(try_match!(Var2::<u32>, Var1(x) => x),     Err(Var2));
assert_eq!(try_match!(Var1(42),    Var2    => "yay"), Err(Var1(42)));

// Supports `if` guard
assert_eq!(try_match!(Var1(42), Var1(x) if x < 20 => x), Err(Var1(42)));
```

### Implicit Mapping

`=>` and the part that comes after can be omitted (requires `implicit_map`
feature, which is enabled by default; you can disable it to skip the
compilation of the internal procedural macro):

```rust
// `()` if there are no bound variables
assert_eq!(try_match!(Var1(42), Var1(_)), Ok(()));

// The bound variable if there is exactly one bound variables
assert_eq!(try_match!(Var1(42), Var1(x)), Ok(42));
assert_eq!(try_match!(Var1(42), Var1(x) if x < 20), Err(Var1(42)));

// An anonymous struct if there are multiple bound variables
let vars = try_match!(Var1((12, 34)), Var1((a, b))).unwrap();
assert_eq!((vars.a, vars.b), (12, 34));
```

It produces a tuple if you name the bound variables like `_0`, `_1`, `_2`,
...:

```rust
let (a, b) = try_match!(Var1((12, 34)), Var1((_0, _1))).unwrap();
assert_eq!((a, b), (12, 34));

try_match!(Var1((12, 34)), Var1((_0, _1)) if _0 == _1).unwrap_err();
```

It's an error to specify non-contiguous binding indices:

```rust
let _ = try_match!(Var1((12, 34)), Var1((_0, _2)));
```

```rust
let _ = try_match!(Var1((12, 34)), Var1((_0, _9223372036854775808)));
```

## Restrictions

 - Macros cannot be used in a supplied pattern.

## Related Work

[`matcher::matches!`][] (now incorporated into the standard library as
[`core::matches!`][]) is similar but only returns `bool` indicating whether
matching was successful or not.

```rust
if_rust_version! { >= 1.42 {
    let success1 =   matches!(Some(42), Some(_));
    let success2 = try_match!(Some(42), Some(_)).is_ok();
    assert_eq!(success1, success2);
} }
```

[`bind_match::bind_match!`][] and [`extract::extract!`][] use the same
syntax (except for implicit mapping) but return `Some(expr)` on success
instead.

[`core::matches!`]: https://doc.rust-lang.org/1.56.0/core/macro.matches.html
[`matcher::matches!`]: https://crates.io/crates/matches
[`bind_match::bind_match!`]: https://crates.io/crates/bind_match
[`extract::extract!`]: https://crates.io/crates/extract_macro


License: MIT/Apache-2.0
