use egglog::ast::Command;
use egglog::util::SymbolGen;
use egglog::*;
use std::path::Path;
use std::sync::{Arc, Mutex};

struct RecordFunctionInputArity {
    name: String,
    seen: Arc<Mutex<Vec<usize>>>,
}

impl CommandMacro for RecordFunctionInputArity {
    fn transform(
        &self,
        command: Command,
        _symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        if let Some(func) = type_info.get_func_type(&self.name) {
            self.seen.lock().unwrap().push(func.input.len());
        }
        Ok(vec![command])
    }
}

#[test]
fn proof_mode_command_macros_see_original_function_arities() {
    let seen = Arc::new(Mutex::new(vec![]));
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .command_macros_mut()
        .register(Arc::new(RecordFunctionInputArity {
            name: "score".to_string(),
            seen: seen.clone(),
        }));

    egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (Num i64))
            (function score (Math) i64 :merge old)
            (let x (Num 1))
            "#,
        )
        .unwrap();

    assert_eq!(*seen.lock().unwrap(), vec![1]);
}

#[test]
fn term_and_proof_modes_lower_input_rows_as_fiat_actions() {
    let directory = std::env::temp_dir().join(format!("egglog_proof_input_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("edges.tsv"), "a\tb\nb\tc\n").unwrap();
    std::fs::write(directory.join("scores.tsv"), "a\t7\n").unwrap();
    std::fs::write(directory.join("seen.tsv"), "a\n").unwrap();

    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph.fact_directory = Some(directory.clone());
        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation Edge (String String))
                (function score (String) i64 :merge old)
                (function seen (String) Unit :merge old)
                (input Edge "edges.tsv")
                (input score "scores.tsv")
                (input seen "seen.tsv")
                (check (Edge "a" "b"))
                (check (= (score "a") 7))
                (check (= (seen "a") ()))
                "#,
            )
            .unwrap();
    }

    std::fs::remove_dir_all(directory).ok();
}

#[test]
fn term_and_proof_modes_reject_no_merge_functions() {
    // `:no-merge` functions are not modeled by the term/proof encoding; a program
    // declaring one is unsupported (it must run on the native backend instead).
    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        let error = egraph
            .parse_and_run_program(None, "(function score () i64 :no-merge)")
            .unwrap_err();
        assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
        assert!(error.to_string().contains("`:no-merge`"));
    }
}

#[test]
fn proof_mode_rejects_fail_wrapped_input() {
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (relation Edge (String String))
            (fail (input Edge "edges.tsv"))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    assert!(
        error
            .to_string()
            .contains("`fail` wrapping an `input` command")
    );
}

#[test]
fn proof_mode_allows_fail_wrapping_set() {
    // A `(fail (set …))` is accepted by proof encoding (it used to be rejected as a
    // non-atomic wrapped command). The set succeeds, so `fail` reports that its
    // wrapped command did not fail.
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (function score () i64 :merge old)
            (fail (set (score) 1))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::ExpectFail(..)));
}

#[test]
fn proof_mode_allows_fail_wrapping_multi_operation_encoding() {
    // A wrapped command that encodes to several commands is now accepted;
    // declaring the function succeeds, so `fail` reports it did not fail.
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(None, "(fail (function score () i64 :merge old))")
        .unwrap_err();

    assert!(matches!(error, Error::ExpectFail(..)));
}

#[test]
fn proof_mode_fail_catches_failure_among_wrapped_commands() {
    // `fail` runs every wrapped command in order and succeeds when any one fails:
    // the set succeeds and the mismatched check fails, so the `fail` passes.
    EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (function score () i64 :merge old)
            (fail (set (score) 1) (check (= (score) 2)))
            "#,
        )
        .unwrap();
}

#[test]
fn pointer_analysis_sample_passes_proof_checking() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("egglog crate should be inside the workspace");
    let mut egraph = EGraph::new_with_proofs().with_proof_testing();
    egraph.fact_directory = Some(repository.join("benchmarks/data/pointer-analysis-small"));
    let program =
        std::fs::read_to_string(repository.join("benchmarks/pointer-analysis-small.egg")).unwrap();

    egraph.parse_and_run_program(None, &program).unwrap();
}

#[test]
fn luminal_benchmark_passes_proof_checking() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("egglog crate should be inside the workspace");
    let program = std::fs::read_to_string(repository.join("benchmarks/luminal-llama.egg")).unwrap();

    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(None, &program)
        .unwrap();
}
