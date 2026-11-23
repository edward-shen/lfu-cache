#[cfg(not(miri))] // compile fail tests shouldn't be run by miri
#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
