fn main() {
    let _ = try_match::try_match!(Some((1, 2)), Some((_1, _2)));
}
