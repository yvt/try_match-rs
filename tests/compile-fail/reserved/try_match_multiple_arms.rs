fn main() {
    let _ = try_match::try_match!(Some(42), Some(_) => 1, None => 0);
}
