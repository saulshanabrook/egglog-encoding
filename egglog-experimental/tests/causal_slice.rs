use egglog::causal_slice::{
    causal_slice_proof_replay_program_with_egraph, causal_slice_replay_program_with_egraph,
};
use egglog_experimental::{
    new_experimental_egraph_for_proofs, new_experimental_egraph_with_proof_testing,
    new_experimental_egraph_with_proofs,
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
fn configured_positive_check_projection_replays_with_proofs_without_extraction() {
    let replay = causal_slice_proof_replay_program_with_egraph(
        Some("experimental-positive-check.egg".to_owned()),
        EXPERIMENTAL_FOR_PROGRAM,
        new_experimental_egraph_for_proofs(),
    )
    .unwrap();
    assert!(replay.source.contains("(check (Goal 1))"));
    assert!(!replay.source.contains("(prove "));

    for mut egraph in [
        new_experimental_egraph_for_proofs(),
        new_experimental_egraph_with_proofs(),
        new_experimental_egraph_with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(
                Some("experimental-positive-check-replay.egg".to_owned()),
                &replay.source,
            )
            .unwrap();
    }
}

#[test]
fn configured_container_presorts_are_preserved_as_opaque_schemas() {
    let source = r#"
        (sort IntOrBool (Either i64 bool))
        (sort Bound (Maybe IntOrBool))
        (relation Seed (i64))
        (relation Goal (i64))
        (Seed 1)
        (rule ((Seed x)) ((Goal x)) :name "copy")
        (run 1)
        (check (Goal 1))
    "#;

    let replay = causal_slice_replay_program_with_egraph(
        Some("experimental-presorts.egg".to_owned()),
        source,
        new_experimental_egraph_for_proofs(),
    )
    .unwrap();
    assert!(replay.source.contains("(sort IntOrBool (Either i64 bool))"));
    assert!(replay.source.contains("(sort Bound (Maybe IntOrBool))"));

    for mut egraph in [
        new_experimental_egraph_for_proofs(),
        new_experimental_egraph_with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(
                Some("experimental-presorts-replay.egg".to_owned()),
                &replay.source,
            )
            .unwrap();
    }
}

#[test]
fn experimental_cli_preserves_configuration_for_causal_proof_modes() {
    let directory = temporary_directory();
    let program = directory.join("for.egg");
    std::fs::write(&program, EXPERIMENTAL_FOR_PROGRAM).unwrap();

    for proof_flag in ["--proofs", "--proof-testing"] {
        let output = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
            .arg("--causal-slice")
            .arg(proof_flag)
            .arg("--mode")
            .arg("no-messages")
            .arg(&program)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "configured causal CLI failed for {proof_flag}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    std::fs::remove_dir_all(directory).unwrap();
}
