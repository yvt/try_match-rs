fn main() {
    // empty scrutinee is reserved for partial application
    // <https://github.com/yvt/try_match-rs/issues/3>
    let _ = try_match::try_match!(, Some(_0))(Some(42));
}
