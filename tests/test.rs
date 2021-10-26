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
    let _ = try_match!(A = input => ()).unwrap();
}

#[cfg(feature = "implicit_map")]
#[test]
fn input_evaled_only_once_implicit_map() {
    #[derive(Debug)]
    struct A;
    let input = A;

    // `A: !Copy`, so the following line should fail to compile if
    // `input` is evaluated twice
    let _ = try_match!(A = input).unwrap();
}

#[cfg(feature = "implicit_map")]
#[test]
fn unwrap_option() {
    assert_eq!(try_match!(Some(a) = Some(42)), Ok(42));
    assert_eq!(try_match!(Some(a) = None::<u32>), Err(None));

    let some = MyOption::Some(42);
    let a = try_match!(MyOption::Some(a) = some);
    assert_eq!(a, Ok(42));
    assert_eq!(
        try_match!(MyOption::Some(a) = MyOption::None),
        Err(MyOption::None)
    );
    assert_eq!(try_match!(MyOption::Some(a) = some), Ok(42));
    assert_eq!(
        try_match!(MyOption::Some(a) = MyOption::None),
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
    assert_eq!(try_match!(Ok(a) | Err(a) = Ok(42)), Ok(42));
    assert_eq!(try_match!(Ok(a) | Err(a) = Err(42)), Ok(42));

    assert_eq!(try_match!(Ok(_0) | Err(&_0) = Ok::<_, &_>(42)), Ok(42));
    assert_eq!(try_match!(Ok(&_0) | Err(_0) = Err::<&_, _>(42)), Ok(42));
}
