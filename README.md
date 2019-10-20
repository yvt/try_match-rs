# try_match

[<img src="https://docs.rs/try_match/badge.svg" alt="docs.rs">](https://docs.rs/try_match/)

Provides an expression macro `try_match` that performs pattern
matching and returns the bound variables via `Ok(_)` iff successful.

## Examples

### Explicit Mapping

```rust
use try_match::try_match;

// The right-hand side of `=>` if successful
assert_eq!(try_match!(Some(x) = Some(42) => x), Ok(42));

// `None(input)` on failure
assert_eq!(try_match!(Some(x) = None::<u32> => x), Err(None));
```

### Implicit Mapping

`=>` and the part that comes after can be omitted (requires `implicit_map`
feature, which is enabled by default; you can disable it to skip the
compilation of the internal procedural macro):

```rust
// `()` if there are no bound variables
assert_eq!(try_match!(Some(_) = Some(42)), Ok(()));

// The bound variable if there is exactly one bound variables
assert_eq!(try_match!(Some(x) = Some(42)), Ok(42));

// An anonymous struct if there are multiple bound variables
let vars = try_match!(Some((a, b)) = Some((12, 34))).unwrap();
assert_eq!((vars.a, vars.b), (12, 34));
```

It produces a tuple if you name the bound variables like `_0`, `_1`, `_2`,
...:

```rust
let (a, b) = try_match!(Some((_0, _1)) = Some((12, 34))).unwrap();
assert_eq!((a, b), (12, 34));
```

It's an error to specify non-contiguous binding indices:

```compile_fail
# use try_match::try_match;
let _ = try_match!(Some((_0, _2)) = Some((12, 34)));
```

```compile_fail
# use try_match::try_match;
let _ = try_match!(Some((_0, _9223372036854775808)) = Some((12, 34)));
```

## Restrictions

 - Macros cannot be used in a supplied pattern.


License: MIT/Apache-2.0
