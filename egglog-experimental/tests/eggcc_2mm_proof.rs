use std::path::Path;

fn read_fixture(fixture_name: &str) -> String {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = manifest_dir.join("tests/fixtures").join(fixture_name);
    std::fs::read_to_string(&fixture).expect("read eggcc 2mm fixture")
}

#[test]
fn eggcc_2mm_bounded_export_uses_container_helpers() {
    let program = read_fixture("eggcc-2mm-pass1.egg");

    let non_comment_program = program
        .lines()
        .filter(|line| !line.trim_start().starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n");

    for required in [
        "pair-min-by-second-i64",
        "maybe-either-i64-bool-min",
        "maybe-either-i64-bool-max",
        "maybe-some",
        "either-left",
        "either-right",
        "either-unwrap-left",
        "either-unwrap-right",
        "(check (FunctionHasType \"main\"",
    ] {
        assert!(
            non_comment_program.contains(required),
            "fixture should exercise {required}"
        );
    }

    for required in [
        "https://github.com/egraphs-good/eggcc/pull/796",
        "https://github.com/egraphs-good/egglog-experimental/pull/56",
    ] {
        assert!(
            program.contains(required),
            "fixture should document {required}"
        );
    }

    assert!(
        non_comment_program.contains(":no-merge"),
        "bounded eggcc export should preserve native no-merge declarations"
    );
}
