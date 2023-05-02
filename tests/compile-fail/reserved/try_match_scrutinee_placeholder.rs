fn main() {
    // scrutinee placeholder is reserved for partial application
    // <https://github.com/yvt/try_match-rs/issues/3>
    let _ = try_match::try_match!(_, Some(_0))(Some(42));
}
