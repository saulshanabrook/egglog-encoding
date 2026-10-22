//! Source certificates lifted by the Lean model in `semantics/`, checked by this
//! crate's proof checker. `lean-certificates.json` is written by `difftest
//! export-fixtures`; `EGGLOG_LEAN_CERTIFICATES` names a fuller export to check
//! instead, such as the whole differential-test corpus.

use egglog::check_certificates;

#[test]
fn lean_certificates_are_judged_alike() {
    let path = std::env::var("EGGLOG_LEAN_CERTIFICATES").unwrap_or_else(|_| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/tests/lean-certificates.json").to_string()
    });
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let verdicts = check_certificates(&json).unwrap();
    let disagreements: Vec<String> = verdicts
        .iter()
        .filter(|v| v.accepted != v.expected)
        .map(|v| {
            format!(
                "{} #{}: Lean {}, Rust {}{}",
                v.case,
                v.certificate,
                verdict(v.expected),
                verdict(v.accepted),
                v.rejection
                    .as_deref()
                    .map(|why| format!(" ({why})"))
                    .unwrap_or_default()
            )
        })
        .collect();
    assert!(disagreements.is_empty(), "{}", disagreements.join("\n"));
    assert!(
        verdicts.iter().any(|v| v.accepted),
        "no certificate was accepted"
    );
    assert!(
        verdicts.iter().any(|v| !v.accepted),
        "no certificate was rejected"
    );
}

fn verdict(accepted: bool) -> &'static str {
    if accepted { "accepts" } else { "rejects" }
}
