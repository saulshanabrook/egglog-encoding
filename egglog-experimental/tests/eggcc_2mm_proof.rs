use std::path::Path;
use std::process::Command;

fn read_fixture(fixture_name: &str) -> (std::path::PathBuf, String) {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = manifest_dir.join("tests/fixtures").join(fixture_name);
    let program = std::fs::read_to_string(&fixture).expect("read eggcc 2mm fixture");
    (fixture, program)
}

fn run_fixture_with_proofs(fixture_name: &str) -> String {
    let (fixture, program) = read_fixture(fixture_name);
    let output = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .arg("--proofs")
        .arg(&fixture)
        .output()
        .expect("run egglog-experimental --proofs on eggcc 2mm fixture");

    assert!(
        output.status.success(),
        "egglog-experimental --proofs failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    program
}

#[test]
fn eggcc_2mm_full_export_uses_container_helpers() {
    let (_fixture, program) = read_fixture("eggcc-2mm-pass1-merge-old.egg");

    for required in [
        "pair-min-by-second-i64",
        "maybe-either-i64-bool-min",
        "maybe-either-i64-bool-max",
        "maybe-some",
        "either-left",
        "either-right",
        "either-unwrap-left",
        "either-unwrap-right",
        "https://github.com/egraphs-good/eggcc/pull/796",
        "https://github.com/egraphs-good/egglog-experimental/pull/56",
        "(check (FunctionHasType \"main\"",
    ] {
        assert!(
            program.contains(required),
            "fixture should exercise {required}"
        );
    }

    let non_comment_program = program
        .lines()
        .filter(|line| !line.trim_start().starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !non_comment_program.contains(":no-merge"),
        "full eggcc export should not use :no-merge declarations"
    );
    assert!(
        program.contains(":merge old"),
        "full eggcc export should pin former no-merge functions to :merge old"
    );
}

#[test]
#[ignore = "full eggcc proof canary is too slow for default debug-profile CI"]
fn eggcc_2mm_full_export_runs_with_proofs() {
    run_fixture_with_proofs("eggcc-2mm-pass1-merge-old.egg");
}
