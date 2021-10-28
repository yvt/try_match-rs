extern crate core as abcdefgh;
extern crate std as ijklmn;
use try_match::try_match;

#[test]
fn input_evaled_only_once() {
    #[derive(Debug)]
    struct A;
    let input = A;

    // `A: !Copy`, so the following line should fail to compile if
    // `input` is evaluated twice
    let _ = try_match!(input, A => ()).unwrap();
}

#[test]
fn guards() {
    assert_eq!(try_match!(Some(12), Some(a) if a < 20 => a), Ok(12));
    assert_eq!(try_match!(Some(42), Some(a) if a < 20 => a), Err(Some(42)));
    assert_eq!(try_match!(None::<u32>, Some(a) if a < 20 => a), Err(None));
}

#[test]
fn guards_implicit_map() {
    assert_eq!(try_match!(Some(12), Some(a) if a < 20), Ok(12));
    assert_eq!(try_match!(Some(42), Some(a) if a < 20), Err(Some(42)));
    assert_eq!(try_match!(None::<u32>, Some(a) if a < 20), Err(None));
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
