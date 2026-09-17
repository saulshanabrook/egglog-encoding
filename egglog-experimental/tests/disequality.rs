use egglog_experimental::{DisequalityEncoding, new_experimental_egraph_with_options};
use std::{path::Path, process::Command};

#[test]
fn encodings_compose_with_proofs() {
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        for mode in 0..4 {
            let graph = new_experimental_egraph_with_options(false, encoding);
            let mut graph = match mode {
                0 => graph,
                1 => graph.with_term_encoding_enabled(),
                2 => graph.with_proofs_enabled(),
                _ => graph.with_proofs_enabled().with_proof_testing(),
            };
            graph
                .parse_and_run_program(
                    None,
                    "
                (datatype Term (A) (B) (F Term))
                (disequal (F (A)) (F (B)))
                (fail (check-contradiction))
                (union (A) (B))
                (check-contradiction)
            ",
                )
                .unwrap_or_else(|e| panic!("{encoding:?} mode {mode}: {e}"));
        }
    }
}

#[test]
fn included_proofs_and_later_fiats_survive_rollback() {
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        let mut graph = new_experimental_egraph_with_options(false, encoding)
            .with_proofs_enabled()
            .with_proof_testing();
        graph
            .parse_and_run_program(None, "(include \"tests/disequality/congruence.egg\")")
            .unwrap();
        graph
            .parse_and_run_program(
                None,
                "(datatype Later (X) (Y) (Z))
                 (push) (union (X) (Y)) (check (= (X) (Y))) (pop)
                 (fail (check (= (X) (Y))))
                 (union (X) (Z)) (check (= (X) (Z)))",
            )
            .unwrap();
    }
}

#[test]
fn block_inference() {
    // Core term/proof encoding does not support begin blocks, even with union.
    let programs = [
        "(sort VI (Vec i64)) (sort VS (Vec String)) (datatype T (A VI) (B))
         (begin (let xs (vec-empty)) (disequal (A xs) (B)))
         (union (A (vec-empty)) (B)) (check-contradiction)",
        "(sort VI (Vec i64)) (sort VS (Vec String)) (datatype T (A VI) (B))
         (let value (begin (let xs (vec-empty)) (disequal (A xs) (B)) (B)))
         (union (A (vec-empty)) value) (check-contradiction)",
    ];
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        for program in programs {
            new_experimental_egraph_with_options(false, encoding)
                .parse_and_run_program(None, program)
                .unwrap();
        }
    }
}

#[test]
fn rule_inference_and_lazy_declarations() {
    let programs = [
        "(datatype T (A)) (A)
         (rule ((= x (A))) ((let y (unstable-fresh! T)) (disequal x y) (union x y)))
         (run 1) (check-contradiction)",
        "(datatype T (A)) (push) (disequal (A) (A)) (pop) (disequal (A) (A)) (check-contradiction)",
        "(datatype !Term (A) (B)) (disequal (A) (B)) (union (A) (B)) (check-contradiction)",
        "(sort VI (Vec i64)) (sort VS (Vec String)) (datatype T (A VI) (B))
         (rule () ((let xs (vec-empty)) (disequal (A xs) (B))))
         (run 1) (union (A (vec-empty)) (B)) (check-contradiction)",
        "(sort VI (Vec i64)) (sort VS (Vec String)) (datatype T (A VI) (B))
         (rule ((= xs (vec-empty))) ((disequal (A xs) (B))))
         (run 1) (union (A (vec-empty)) (B)) (check-contradiction)",
    ];
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        for program in programs {
            let mut graph = new_experimental_egraph_with_options(false, encoding)
                .with_proofs_enabled()
                .with_proof_testing();
            graph
                .parse_and_run_program(None, program)
                .unwrap_or_else(|e| panic!("{encoding:?}: {program}\n{e}"));
        }
    }
}

#[test]
fn rejects_invalid_disequalities() {
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        for source in [
            "(disequal 1 2)",
            "(datatype T (A)) (datatype S (B)) (disequal (A) (B))",
            "(sort T :no-union) (constructor A () T) (disequal (A) (A))",
            "(datatype T (A)) (disequal (A))",
            "(check-contradiction 1)",
        ] {
            assert!(
                new_experimental_egraph_with_options(false, encoding)
                    .parse_and_run_program(None, source)
                    .is_err(),
                "{encoding:?}: {source}"
            );
        }
        new_experimental_egraph_with_options(false, encoding)
            .with_proofs_enabled()
            .with_proof_testing()
            .parse_and_run_program(
                None,
                "(fail (check-contradiction))
                (datatype T (A)) (disequal (A) (A)) (run 1)
                (check-contradiction)",
            )
            .unwrap();
    }
}

#[test]
fn desugared_snapshots_and_cli_modes() {
    for name in ["congruence", "rules"] {
        let path = Path::new("tests/disequality").join(format!("{name}.egg"));
        let source = std::fs::read_to_string(&path).unwrap();
        for (label, encoding) in [
            ("nee", DisequalityEncoding::Nee),
            ("ee", DisequalityEncoding::Ee),
        ] {
            let mut graph = new_experimental_egraph_with_options(false, encoding);
            let resolved = graph.resolve_program(None, &source).unwrap();
            let desugared = egglog::ast::sanitize_internal_names(&resolved)
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
                + "\n";
            let snapshot = path
                .parent()
                .unwrap()
                .join("snapshots")
                .join(format!("{name}.{label}.desugared.egg"));
            if std::env::var_os("UPDATE_DISEQUALITY_SNAPSHOTS").is_some() {
                std::fs::create_dir_all(snapshot.parent().unwrap()).unwrap();
                std::fs::write(&snapshot, &desugared).unwrap();
            }
            assert_eq!(
                std::fs::read_to_string(&snapshot).unwrap(),
                desugared,
                "{}",
                snapshot.display()
            );
            for input in [&path, &snapshot] {
                for flags in [
                    vec![],
                    vec!["--term-encoding"],
                    vec!["--proofs"],
                    vec!["--proof-extraction"],
                    vec!["--proof-testing"],
                ] {
                    let result = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
                        .args(["--mode", "no-messages", "--disequality-encoding", label])
                        .args(&flags)
                        .arg(input)
                        .output()
                        .unwrap();
                    assert!(
                        result.status.success(),
                        "{} {label} {flags:?}: {}",
                        input.display(),
                        String::from_utf8_lossy(&result.stderr)
                    );
                }
            }
        }
    }
}
