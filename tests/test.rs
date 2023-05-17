extern crate core as abcdefgh;
extern crate std as ijklmn;
use try_match::{match_ok, try_match, unwrap_match};

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
#[allow(warnings)]
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
#[allow(clippy::redundant_pattern)]
fn pat_ident_subpat_implicit_map() {
    // Tuple pattern
    assert_eq!(try_match!((), _0 @ _), Ok(()));

    // Single
    assert_eq!(try_match!((), a @ _), Ok(()));

    // Multiple
    let m = try_match!((1, 2), (a @ _, b @ _)).unwrap();
    assert_eq!((m.a, m.b), (1, 2));
}

#[cfg(feature = "implicit_map")]
#[test]
#[allow(non_snake_case)]
fn pat_ident_guessed_binding_implicit_map() {
    assert_eq!(try_match!(42, f), Ok(42));
    assert_eq!(try_match!(42, fA), Ok(42));
    assert_eq!(try_match!(42, fは), Ok(42));
    assert_eq!(try_match!(42, _f), Ok(42));
    assert_eq!(try_match!(42, _fA), Ok(42));
    assert_eq!(try_match!(42, _fは), Ok(42));
    assert_eq!(try_match!(42, _0), Ok(42));
    assert_eq!(try_match!(42, r#f), Ok(42));
    assert_eq!(try_match!(42, r#fA), Ok(42));
    assert_eq!(try_match!(42, r#fは), Ok(42));
    assert_eq!(try_match!(42, r#_f), Ok(42));
    assert_eq!(try_match!(42, r#_fA), Ok(42));
    assert_eq!(try_match!(42, r#_fは), Ok(42));
    assert_eq!(try_match!(42, r#_0), Ok(42));
}

#[cfg(feature = "implicit_map")]
#[test]
fn pat_ident_guessed_constant_implicit_map() {
    const F: i32 = 0;
    const FA: i32 = 0;
    const Fは: i32 = 0;
    const _F: i32 = 0;
    const _FA: i32 = 0;
    const _Fは: i32 = 0;

    assert_eq!(try_match!(42, F), Err(42));
    assert_eq!(try_match!(42, FA), Err(42));
    assert_eq!(try_match!(42, Fは), Err(42));
    assert_eq!(try_match!(42, _F), Err(42));
    assert_eq!(try_match!(42, _FA), Err(42));
    assert_eq!(try_match!(42, _Fは), Err(42));
    assert_eq!(try_match!(42, r#F), Err(42));
    assert_eq!(try_match!(42, r#FA), Err(42));
    assert_eq!(try_match!(42, r#Fは), Err(42));
    assert_eq!(try_match!(42, r#_F), Err(42));
    assert_eq!(try_match!(42, r#_FA), Err(42));
    assert_eq!(try_match!(42, r#_Fは), Err(42));
}

#[test]
fn trailing_comma() {
    assert_eq!(try_match!(Some(12), Some(a) => a,), Ok(12));
    assert_eq!(try_match!(Some(12), Some(a) if a < 20 => a,), Ok(12));
    assert_eq!(match_ok!(Some(12), Some(a) => a,), Some(12));
    assert_eq!(match_ok!(Some(12), Some(a) if a < 20 => a,), Some(12));
    assert_eq!(unwrap_match!(Some(12), Some(a) => a,), 12);
    assert_eq!(unwrap_match!(Some(12), Some(a) if a < 20 => a,), 12);
}

#[cfg(feature = "implicit_map")]
#[test]
fn trailing_comma_implicit_map() {
    assert_eq!(try_match!(Some(12), Some(a),), Ok(12));
    assert_eq!(try_match!(Some(12), Some(a) if a < 20,), Ok(12));
    assert_eq!(match_ok!(Some(12), Some(a),), Some(12));
    assert_eq!(match_ok!(Some(12), Some(a) if a < 20,), Some(12));
    assert_eq!(unwrap_match!(Some(12), Some(a),), 12);
    assert_eq!(unwrap_match!(Some(12), Some(a) if a < 20,), 12);
}

#[cfg(feature = "implicit_map")]
#[test]
#[deny(clippy::just_underscores_and_digits)]
fn clippy_just_underscores_and_digits_implicit_map() {
    // A variable binding like `_0` usually triggers
    // `clippy::just_underscores_and_digits`, but we specifically need this
    // family of names for tuple implicit mapping
    unwrap_match!(Some(12), Some(_0 @ _));

    // TODO: Use `#[expect(...)]` to check that the lint is still effective in
    // future toolchains
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
fn struct_expr() {
    struct A {
        _x: i32,
    }
    assert!(matches!(A { _x: 42 }, A { .. }));
    assert_eq!(match_ok!(A { _x: 42 }, A { .. } => 42), Some(42));
}

#[cfg(feature = "implicit_map")]
#[test]
fn struct_expr_implicit_map() {
    struct A {
        _x: i32,
    }
    assert_eq!(match_ok!(A { _x: 42 }, A { .. }), Some(()));
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
    unwrap_match!(input, A);
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

#[cfg(feature = "implicit_map")]
#[test]
#[should_panic = "assertion failed: '42' does not match 'x if x < 20'"]
fn unwrap_match_msg_default1() {
    unwrap_match!(42, x if x < 20);
}

#[cfg(feature = "implicit_map")]
#[test]
#[should_panic = "assertion failed: '42' does not match 'x if x < 20'"]
fn unwrap_match_msg_default2() {
    unwrap_match!(42, x if x < 20,);
}

#[test]
#[should_panic = "assertion failed: '42' does not match 'x if x < 20'"]
fn unwrap_match_msg_default3() {
    unwrap_match!(42, x if x < 20 => ());
}

#[test]
#[should_panic = "assertion failed: '42' does not match 'x if x < 20'"]
fn unwrap_match_msg_default4() {
    unwrap_match!(42, x if x < 20 => (),);
}

#[test]
#[should_panic = "poneyland"]
fn unwrap_match_msg1() {
    unwrap_match!(42, x if x < 20 => (), "poney{}", "land");
}

#[test]
#[should_panic = "poneyland"]
fn unwrap_match_msg2() {
    unwrap_match!(42, x if x < 20 => (), "poney{}", "land",);
}
