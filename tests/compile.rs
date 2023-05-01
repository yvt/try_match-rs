#[test]
#[cfg(feature = "implicit_map")]
fn fail_tuple_captures() {
    trybuild::TestCases::new().compile_fail("tests/compile-fail/tuple_captures/**/*.rs");
}
