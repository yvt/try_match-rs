#[test]
#[cfg(feature = "implicit_map")]
fn fail_tuple_captures() {
    trybuild::TestCases::new().compile_fail("tests/compile-fail/tuple_captures/**/*.rs");
}

#[test]
#[cfg(not(feature = "implicit_map"))]
fn fail_no_implicit_map() {
    trybuild::TestCases::new().compile_fail("tests/compile-fail/no_implicit_map/**/*.rs");
}
