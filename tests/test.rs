extern crate core as abcdefgh;
extern crate std as ijklmn;
use try_match::try_match;

#[test]
fn input_evaled_only_once() {
    #[derive(Debug)]
    struct A;
    let input = A;

    // `A: !Copy`, so the following line would fail to compile if
    // `input` were evaluated twice
    #[allow(clippy::let_unit_value)]
    let _ = try_match!(input, A => ()).unwrap();
}

#[cfg(feature = "implicit_map")]
#[test]
#[allow(unused_parens)]
fn pat_paren_implicit_map() {
    assert_eq!(try_match!((), (())), Ok(()));
}

#[cfg(feature = "implicit_map")]
#[test]
fn ident_inside_types() {
    trait Tr {
        const C: () = ();
    }

    impl<T> Tr for T {
        const C: () = ();
    }

    assert_eq!(
        try_match!(
            (),
            <[(); {
                #[allow(warnings)]
                match () {
                    // `_4` is a `Pat::Ident`, but `try_match!` should not
                    // consider it as a part of the input pattern
                    _4 => 42,
                }
            }] as Tr>::C
        ),
        Ok(())
    );
}

// requires `inline_const_pat` <https://github.com/rust-lang/rust/issues/76001>
// #[cfg(feature = "implicit_map")]
// #[test]
// fn pat_const_implicit_map() {
//     assert_eq!(try_match!(42, const { 42 }), Ok(()));
// }

#[cfg(feature = "implicit_map")]
#[test]
fn pat_ident_subpat_implicit_map() {
    // Tuple pattern
    assert_eq!(try_match!((), _0 @ _), Ok(()));

    // Single
    assert_eq!(try_match!((), a @ _), Ok(()));

    // Multiple
    let m = try_match!((1, 2), (a @ _, b @ _)).unwrap();
    assert_eq!((m.a, m.b), (1, 2));
}

#[test]
fn guards() {
    assert_eq!(try_match!(Some(12), Some(a) if a < 20 => a), Ok(12));
    assert_eq!(try_match!(Some(42), Some(a) if a < 20 => a), Err(Some(42)));
    assert_eq!(try_match!(None::<u32>, Some(a) if a < 20 => a), Err(None));
}

#[cfg(feature = "implicit_map")]
#[test]
fn guards_implicit_map() {
    assert_eq!(try_match!(Some(12), Some(a) if a < 20), Ok(12));
    assert_eq!(try_match!(Some(42), Some(a) if a < 20), Err(Some(42)));
    assert_eq!(try_match!(None::<u32>, Some(a) if a < 20), Err(None));
}

#[test]
#[allow(unused_variables)]
#[allow(clippy::diverging_sub_expression)]
fn return_in_guard() {
    assert_eq!(try_match!(Some(12), Some(a) if return => a), Ok(42));
    unreachable!();
}

#[cfg(feature = "implicit_map")]
#[test]
#[allow(unused_variables)]
#[allow(clippy::diverging_sub_expression)]
fn return_in_guard_implicit_map() {
    assert_eq!(try_match!(Some(12), Some(a) if return), Ok(42));
    unreachable!();
}

#[cfg(feature = "implicit_map")]
#[test]
fn input_evaled_only_once_implicit_map() {
    #[derive(Debug)]
    struct A;
    let input = A;

    // `A: !Copy`, so the following line should fail to compile if
    // `input` is evaluated twice
    let _ = try_match!(input, A).unwrap();
}

#[cfg(feature = "implicit_map")]
#[test]
fn unwrap_option() {
    assert_eq!(try_match!(Some(42), Some(a)), Ok(42));
    assert_eq!(try_match!(None::<u32>, Some(a)), Err(None));

    let some = MyOption::Some(42);
    let a = try_match!(some, MyOption::Some(a));
    assert_eq!(a, Ok(42));
    assert_eq!(
        try_match!(MyOption::None, MyOption::Some(a)),
        Err(MyOption::None)
    );
    assert_eq!(try_match!(some, MyOption::Some(a)), Ok(42));
    assert_eq!(
        try_match!(MyOption::None, MyOption::Some(a)),
        Err(MyOption::None)
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MyOption {
    Some(u32),
    None,
}

#[cfg(feature = "implicit_map")]
#[test]
fn unwrap_result() {
    assert_eq!(try_match!(Ok(42), Ok(a) | Err(a)), Ok(42));
    assert_eq!(try_match!(Err(42), Ok(a) | Err(a)), Ok(42));

    assert_eq!(try_match!(Ok::<_, &_>(42), Ok(_0) | Err(&_0)), Ok(42));
    assert_eq!(try_match!(Err::<&_, _>(42), Ok(&_0) | Err(_0)), Ok(42));
}
