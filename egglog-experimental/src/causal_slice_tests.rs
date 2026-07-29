use super::*;

#[test]
fn recognizes_explicit_and_output_implied_slicing() {
    for args in [
        vec![OsString::from("egglog"), OsString::from("--slice")],
        vec![
            OsString::from("egglog"),
            OsString::from("--slice-output"),
            OsString::from("out.egg"),
        ],
        vec![
            OsString::from("egglog"),
            OsString::from("--slice-output=out.egg"),
        ],
    ] {
        assert!(requests_slice(&args));
    }
    assert!(!requests_slice(&[
        OsString::from("egglog"),
        OsString::from("--proofs"),
    ]));
}
