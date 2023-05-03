#[test]
#[cfg(feature = "implicit_map")]
fn fail_ident_disambiguation() {
    trybuild::TestCases::new().compile_fail("tests/compile-fail/ident_disambiguation/**/*.rs");
}

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

#[test]
#[cfg(feature = "implicit_map")]
#[cfg(not(feature = "unstable"))]
fn fail_reserved() {
    trybuild::TestCases::new().compile_fail("tests/compile-fail/reserved/**/*.rs");
}
