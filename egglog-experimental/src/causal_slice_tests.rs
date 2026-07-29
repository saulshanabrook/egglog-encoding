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

#[cfg(feature = "dd-backend")]
#[test]
fn dd_backend_rejects_both_slicing_flags_with_a_flag_neutral_diagnostic() {
    for args in [
        vec![OsString::from("egglog"), OsString::from("--slice")],
        vec![
            OsString::from("egglog"),
            OsString::from("--slice-output"),
            OsString::from("out.egg"),
        ],
    ] {
        assert_eq!(
            slice_request_for_backend(Backend::Dd, &args),
            Err("slicing is supported only with --backend main")
        );
    }
}
