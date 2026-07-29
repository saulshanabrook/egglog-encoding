use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

struct TestDir(PathBuf);

impl TestDir {
    fn new() -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        loop {
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("egglog-slice-cli-{}-{id}", std::process::id()));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => panic!("cannot create test directory: {error}"),
            }
        }
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn write_program(directory: &Path) -> std::path::PathBuf {
    let path = directory.join("input.egg");
    std::fs::write(&path, "(relation R (i64)) (R 1) (check (R 1))").unwrap();
    path
}

fn egglog() -> Command {
    Command::new(env!("CARGO_BIN_EXE_egglog"))
}

fn run(directory: &Path, flags: &[&str]) -> std::process::Output {
    let program = write_program(directory);
    egglog().args(flags).arg(program).output().unwrap()
}

fn assert_success(output: &std::process::Output, description: &str) {
    assert!(
        output.status.success(),
        "{description} failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn slice_output_writes_an_artifact_that_the_test_suite_strictly_replays() {
    let directory = TestDir::new();
    let program = write_program(directory.path());
    let artifact = directory.path().join("slice-replay.egg");
    std::fs::write(&artifact, "old artifact").unwrap();

    let output = egglog()
        .arg("--slice-output")
        .arg(&artifact)
        .arg(&program)
        .output()
        .unwrap();
    assert_success(&output, "slice output");
    assert!(!std::fs::read_to_string(&artifact).unwrap().is_empty());
    assert_ne!(std::fs::read_to_string(&artifact).unwrap(), "old artifact");

    let replay = egglog()
        .arg("--proof-testing")
        .arg(&artifact)
        .output()
        .unwrap();
    assert_success(&replay, "strict test replay of the written artifact");
}

#[test]
fn rewrite_root_collision_strictly_replays() {
    let directory = TestDir::new();
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
    assert_success(&output, "rewrite-root slice");
    let artifact = std::fs::read_to_string(artifact).unwrap();
    assert!(
        artifact.contains(r#"(rewrite (A __rewrite_root) (B __rewrite_root) :name "colliding")"#)
    );
    assert!(artifact.contains("(__rewrite_root_1 "));
}

#[test]
fn bare_slice_replays_in_normal_mode() {
    let directory = TestDir::new();
    assert_success(&run(directory.path(), &["--slice"]), "normal slice replay");
}

#[test]
fn slice_composes_with_execution_modes() {
    let directory = TestDir::new();
    for (name, flags) in [
        ("proofs", &["--slice", "--proofs"][..]),
        ("term encoding", &["--slice", "--term-encoding"]),
        ("proof extraction", &["--slice", "--proof-extraction"]),
        ("naive", &["--slice", "--naive"]),
        ("no messages", &["--slice", "--mode", "no-messages"]),
        ("desugar", &["--slice", "--mode", "desugar"]),
        ("interactive", &["--slice", "--mode", "interactive"]),
    ] {
        assert_success(&run(directory.path(), flags), name);
    }

    let proof_testing = run(directory.path(), &["--slice", "--proof-testing"]);
    assert_success(&proof_testing, "proof testing");
    assert!(
        !proof_testing.stdout.is_empty(),
        "proof testing must turn the artifact's checks into displayed proves"
    );
}

#[test]
fn slice_composes_with_serialization() {
    let directory = TestDir::new();
    let program = write_program(directory.path());
    let output = egglog()
        .args(["--slice", "--to-json", "--to-dot"])
        .arg(&program)
        .output()
        .unwrap();
    assert_success(&output, "slice serialization");
    assert!(program.with_extension("dot").exists());
    let json = std::fs::read_to_string(program.with_extension("json")).unwrap();
    serde_json::from_str::<serde_json::Value>(&json).unwrap();
}

#[test]
fn slice_output_composes_without_requesting_replay() {
    let directory = TestDir::new();
    let artifact = directory.path().join("slice-replay.egg");
    let program = write_program(directory.path());
    let output = egglog()
        .args(["--slice-output", artifact.to_str().unwrap(), "--naive"])
        .arg(program)
        .output()
        .unwrap();
    assert_success(&output, "naive output-only slice");
    assert!(artifact.exists());
}

#[test]
fn slice_rejects_parallel_capture() {
    let directory = TestDir::new();
    let output = run(directory.path(), &["--slice", "--threads", "2"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("--slice requires --threads 1"));
}

#[test]
fn removed_capture_only_flag_is_unknown() {
    let output = egglog().arg("--causal-receipts").output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("unexpected argument"));
}
