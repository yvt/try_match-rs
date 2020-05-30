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
}
