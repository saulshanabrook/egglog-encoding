use std::{path::Path, process::Command};

fn write_program(directory: &Path) -> std::path::PathBuf {
    let path = directory.join("input.egg");
    std::fs::write(&path, "(relation R (i64)) (R 1) (check (R 1))").unwrap();
    path
}

fn egglog() -> Command {
    Command::new(env!("CARGO_BIN_EXE_egglog"))
}

#[test]
fn slice_output_implies_slice_and_strictly_replays() {
    let directory = tempfile::tempdir().unwrap();
    let program = write_program(directory.path());
    let artifact = directory.path().join("slice-replay.egg");
    std::fs::write(&artifact, "old artifact").unwrap();

    let output = egglog()
        .arg("--slice-output")
        .arg(&artifact)
        .arg(&program)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "slice failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!std::fs::read_to_string(&artifact).unwrap().is_empty());
    assert_ne!(std::fs::read_to_string(&artifact).unwrap(), "old artifact");

    let replay = egglog()
        .arg("--proof-testing")
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(
        replay.status.success(),
        "published artifact failed strict replay:\n{}",
        String::from_utf8_lossy(&replay.stderr)
    );
}

#[test]
fn rewrite_root_collision_strictly_replays() {
    let directory = tempfile::tempdir().unwrap();
    let program = directory.path().join("rewrite-collision.egg");
    let artifact = directory.path().join("slice-replay.egg");
    std::fs::write(
        &program,
        r#"
            (datatype E (A i64) (B i64))
            (rewrite (A __rewrite_root) (B __rewrite_root) :name "colliding")
            (let $x (A 1))
            (run 1)
            (check (= $x (B 1)))
        "#,
    )
    .unwrap();

    let output = egglog()
        .arg("--slice-output")
        .arg(&artifact)
        .arg(&program)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "slice failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let artifact = std::fs::read_to_string(artifact).unwrap();
    assert!(
        artifact.contains(r#"(rewrite (A __rewrite_root) (B __rewrite_root) :name "colliding")"#)
    );
    assert!(artifact.contains("(__rewrite_root_1 "));
}

#[test]
fn slice_requires_an_output_and_proofs_remains_optional() {
    let directory = tempfile::tempdir().unwrap();
    let program = write_program(directory.path());
    let proofs = egglog()
        .args(["--slice", "--proofs"])
        .arg(&program)
        .output()
        .unwrap();
    assert!(
        proofs.status.success(),
        "--slice --proofs failed:\n{}",
        String::from_utf8_lossy(&proofs.stderr)
    );

    let bare = egglog().arg("--slice").arg(&program).output().unwrap();
    assert_eq!(bare.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&bare.stderr)
            .contains("--slice requires --proofs or --slice-output")
    );
}

#[test]
fn slice_rejects_parallel_and_serialization_modes() {
    let directory = tempfile::tempdir().unwrap();
    let program = write_program(directory.path());
    for (flags, diagnostic) in [
        (
            vec!["--slice", "--proofs", "--threads", "2"],
            "--slice requires --threads 1",
        ),
        (
            vec!["--slice", "--proofs", "--to-json"],
            "--slice conflicts with --to-json, --to-dot, and --to-svg",
        ),
    ] {
        let output = egglog().args(flags).arg(&program).output().unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(String::from_utf8_lossy(&output.stderr).contains(diagnostic));
    }
}

#[test]
fn slice_output_cannot_alias_an_input_or_report() {
    let directory = tempfile::tempdir().unwrap();
    let program = write_program(directory.path());

    let input_collision = egglog()
        .arg("--slice-output")
        .arg(&program)
        .arg(&program)
        .output()
        .unwrap();
    assert_eq!(input_collision.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&input_collision.stderr).contains("conflicts with input file"));
    assert_eq!(
        std::fs::read_to_string(&program).unwrap(),
        "(relation R (i64)) (R 1) (check (R 1))"
    );

    for report_flag in ["--save-report", "--timing-summary"] {
        let output = egglog()
            .arg("--slice-output")
            .arg(directory.path().join("same.json"))
            .arg(report_flag)
            .arg(directory.path().join("same.json"))
            .arg(&program)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(String::from_utf8_lossy(&output.stderr).contains(report_flag));
    }
}

#[test]
fn removed_capture_only_flag_is_unknown() {
    let output = egglog().arg("--causal-receipts").output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("unexpected argument"));
}

#[test]
fn failed_strict_validation_preserves_existing_output() {
    let directory = tempfile::tempdir().unwrap();
    let artifact = directory.path().join("slice-replay.egg");
    std::fs::write(&artifact, "keep me").unwrap();
    let program = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/web-demo/eqsolve.egg");

    let output = egglog()
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--slice-output")
        .arg(&artifact)
        .arg(program)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr).contains("slice replay validation failed"));
    assert_eq!(std::fs::read_to_string(artifact).unwrap(), "keep me");
}
