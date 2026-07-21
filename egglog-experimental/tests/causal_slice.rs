use egglog::causal_slice::causal_slice_replay_program_with_egraph;
use egglog_experimental::{
    new_experimental_egraph_for_proofs, new_experimental_egraph_with_proof_testing,
};
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP_DIRECTORY: AtomicU64 = AtomicU64::new(0);

const EXPERIMENTAL_FOR_PROGRAM: &str = r#"
    (relation Seed (i64))
    (relation Goal (i64))
    (Seed 1)
    (for ((Seed x))
         ((Goal x)))
    (check (Goal 1))
"#;

fn temporary_directory() -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "egglog-experimental-causal-slice-{}-{}",
        std::process::id(),
        NEXT_TEMP_DIRECTORY.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    directory
}

#[test]
fn configured_experimental_egraph_slices_and_strictly_replays() {
    let replay = causal_slice_replay_program_with_egraph(
        Some("experimental-config.egg".to_owned()),
        EXPERIMENTAL_FOR_PROGRAM,
        new_experimental_egraph_for_proofs(),
    )
    .unwrap();
    assert!(replay.source.contains("run-rule-batch"));
    assert!(!replay.source.contains("(run for_ruleset"));

    for mut egraph in [
        new_experimental_egraph_for_proofs(),
        new_experimental_egraph_with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(
                Some("experimental-config-replay.egg".to_owned()),
                &replay.source,
            )
            .unwrap();
    }
}

#[test]
fn experimental_cli_preserves_configuration_for_causal_slice() {
    let directory = temporary_directory();
    let program = directory.join("for.egg");
    std::fs::write(&program, EXPERIMENTAL_FOR_PROGRAM).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .arg("--causal-slice")
        .arg("--proof-testing")
        .arg("--mode")
        .arg("no-messages")
        .arg(&program)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "configured causal CLI failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    std::fs::remove_dir_all(directory).unwrap();
}
