# try_match

[<img src="https://docs.rs/try_match/badge.svg" alt="docs.rs">](https://docs.rs/try_match/)

Provides an expression macro `try_match` that matches a pattern on a given
expression and returns the bound variables in `Ok(_)` if successful.

## Basic Usage

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

`=>` and the following part can be omitted (requires `implicit_map`
feature, which is enabled by default):

```rust
// `()` if there are no bound variables
assert_eq!(try_match!(Var1(42), Var1(_)), Ok(()));

// The bound variable if there is exactly one bound variable
assert_eq!(try_match!(Var1(42), Var1(x)), Ok(42));
assert_eq!(try_match!(Var1(42), Var1(x) if x < 20), Err(Var1(42)));

// An anonymous struct if there are multiple bound variables
let vars = try_match!(Var1((12, 34)), Var1((a, b))).unwrap();
assert_eq!((vars.a, vars.b), (12, 34));

// A tuple if the variable names are numeric
let (a, b) = try_match!(Var1((12, 34)), Var1((_0, _1))).unwrap();
assert_eq!((a, b), (12, 34));
```

## Applications

### `Iterator::filter_map`

```rust
let array = [Var1(42), Var2, Var1(10)];
let filtered: Vec<_> = array
    .iter()
    .filter_map(|x| try_match!(x, &Var1(_0) if _0 > 20).ok())
    .collect();
assert_eq!(filtered, [42]);
```

### `Iterator::map` + Fallible `Iterator::collect`

```rust
let array = [Var1(42), Var2, Var1(10)];
let filtered: Result<Vec<_>, _> = array
    .iter()
    .map(|x| try_match!(x, &Var1(_0) if _0 > 20))
    .collect();

// `Var2` is the first value that doesn't match
assert_eq!(filtered, Err(&Var2));
```

### Extract Variants

```rust
impl<T> Enum<T> {
    fn var1(&self) -> Option<&T> {
        try_match!(self, Var1(_0)).ok()
    }

    fn is_var2(&self) -> bool {
        matches!(self, Var2)
    }
}

let enums = [Var1(42), Var2];
assert_eq!(enums[0].var1(), Some(&42));
assert_eq!(enums[1].var1(), None);

assert!(!enums[0].is_var2());
assert!(enums[1].is_var2());
```

### Expect Certain Variants

```rust
fn this_fn_expects_var1(foo: &Enum<[u8; 4]>) {
    let (i0, i1) = try_match!(foo, &Var1([_0, _, _, _1])).unwrap();

    // Alternatively, you could use let-else (stabilized in Rust 1.65.0):
    // let &Var1([i0, _, _, i1]) = foo else { panic!("{foo:?}") };

    assert_eq!((i0, i1), (42, 45));
}

this_fn_expects_var1(&Var1([42, 43, 44, 45]));
```

## Related Work

[`matcher::matches!`][] (now incorporated into the standard library as
[`core::matches!`][]) is similar but only returns `bool` indicating whether
matching was successful or not.

```rust
let success1 =   matches!(Some(42), Some(_));
let success2 = try_match!(Some(42), Some(_)).is_ok();
assert_eq!(success1, success2);
```

[`bind_match::bind_match!`][] and [`extract::extract!`][] use the same
syntax (except for implicit mapping) but return `Some(expr)` on success
instead.

[`extract_variant::get_variant!`][] uses the same syntax and supports implicit
mapping. However, it returns `Some(expr)` on success like other similar macros,
and the implicit mapping is defined differently. The `extract_variant` crate
also provides other variations of this macro that handle failure by returning
`Err($closure())` (`try_variant!`) or panicking (`variant!`).

[`core::matches!`]: https://doc.rust-lang.org/1.56.0/core/macro.matches.html
[`matcher::matches!`]: https://crates.io/crates/matches
[`bind_match::bind_match!`]: https://crates.io/crates/bind_match
[`extract::extract!`]: https://crates.io/crates/extract_macro
[`extract_variant::get_variant!`]: https://crates.io/crates/extract-variant/1.0.0

## License

MIT/Apache-2.0
