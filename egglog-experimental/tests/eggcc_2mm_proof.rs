use std::path::Path;

fn read_fixture(fixture_name: &str) -> String {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = manifest_dir.join("tests/fixtures").join(fixture_name);
    std::fs::read_to_string(&fixture).expect("read eggcc 2mm fixture")
}

#[test]
fn eggcc_2mm_bounded_export_uses_constructor_merges_without_containers() {
    // tests/files.rs executes this fixture in proof-testing mode; this test
    // separately checks the imported workload's shape and provenance.
    let program = read_fixture("eggcc-2mm-pass1.egg");

    let non_comment_program = program
        .lines()
        .filter(|line| !line.trim_start().starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n");

    for required in [
        "(constructor Smaller (TermAndCost TermAndCost) TermAndCost)",
        "(function ExtractedExpr (Expr) TermAndCost :merge (Smaller old new))",
        "(constructor TCPair (Term i64) TermAndCost)",
        "(datatype Bound (IntB i64) (BoolB bool) (Dead) (bound-max Bound Bound) (bound-min Bound Bound))",
        ":merge (bound-max old new)",
        ":merge (bound-min old new)",
        "(constructor IVTAnalysisRes (Expr Expr TypeList i64) IVTRes)",
        "(constructor IVTMin (IVTRes IVTRes) IVTRes)",
        ":merge (IVTMin old new)",
        "(check (FunctionHasType \"main\"",
    ] {
        assert!(
            non_comment_program.contains(required),
            "fixture should exercise {required}"
        );
    }

    for required in [
        "https://github.com/egraphs-good/eggcc/commit/16be0063133ef0b8ba21cd75ee377002dc3ecbed",
        "https://github.com/egraphs-good/eggcc/pull/796",
    ] {
        assert!(
            program.contains(required),
            "fixture should document {required}"
        );
    }

    for forbidden in [
        "(Pair ",
        "(Maybe ",
        "(Either ",
        "(Set ",
        "(Map ",
        "(Vec ",
        "(MultiSet ",
        "pair-min-by-second-i64",
        "pair-first",
        "pair-second",
        "maybe-either-i64-bool-",
        "maybe-some",
        "maybe-unwrap",
        "either-left",
        "either-right",
        "either-unwrap-left",
        "either-unwrap-right",
    ] {
        assert!(
            !non_comment_program.contains(forbidden),
            "fixture should not contain built-in container form or helper {forbidden}"
        );
    }

    // `:no-merge` is unsupported by the term/proof encoding, so deterministic
    // helpers in the bounded export use `:merge old` to stay proof-supported.
    assert!(
        non_comment_program.contains(":merge old"),
        "bounded eggcc export should use `:merge old` for its former no-merge functions"
    );
    assert!(
        !non_comment_program.contains(":no-merge"),
        "`:no-merge` is unsupported by the encoding; the bounded export must not use it"
    );
}
