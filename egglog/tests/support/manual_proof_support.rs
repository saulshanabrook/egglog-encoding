use std::path::Path;

pub(super) struct ManualProofDisable {
    pub(super) file: &'static str,
    pub(super) reason: &'static str,
}

pub(super) const MANUAL_PROOF_DISABLED_FILES: &[ManualProofDisable] = &[
    ManualProofDisable {
        file: "eggcc-2mm.egg",
        reason: "the full benchmark exceeds the routine proof harness resource budget; the bounded eggcc-2mm-pass1 fixture covers this workload in proof benchmarks",
    },
    ManualProofDisable {
        file: "subsume.egg",
        reason: "proof-testing rewrites a check on a subsumed expression into a prove query that no longer matches",
    },
    ManualProofDisable {
        file: "subsume-relation.egg",
        reason: "proof-testing rewrites a check on a subsumed relation row into a prove query that no longer matches",
    },
];

pub(super) fn manual_proof_disable_reason(path: &Path) -> Option<&'static str> {
    MANUAL_PROOF_DISABLED_FILES
        .iter()
        .find(|disabled| path.ends_with(disabled.file))
        .map(|disabled| disabled.reason)
}
