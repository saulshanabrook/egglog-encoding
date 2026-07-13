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
fn proof_mode_inputs_rows_as_fiat_actions() {
    let directory = std::env::temp_dir().join(format!("egglog_proof_input_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("edges.tsv"), "a\tb\nb\tc\n").unwrap();
    std::fs::write(directory.join("scores.tsv"), "a\t7\n").unwrap();

    let mut egraph = EGraph::new_with_proofs().with_proof_testing();
    egraph.fact_directory = Some(directory.clone());
    let result = egraph.parse_and_run_program(
        None,
        r#"
        (relation Edge (String String))
        (function score (String) i64 :no-merge)
        (input Edge "edges.tsv")
        (input score "scores.tsv")
        (check (Edge "a" "b"))
        (check (= (score "a") 7))
        "#,
    );

    std::fs::remove_dir_all(directory).ok();
    result.unwrap();
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
    assert!(error.to_string().contains("`fail` wrapping an `input` command"));
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
