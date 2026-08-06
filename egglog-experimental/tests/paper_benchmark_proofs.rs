use std::path::{Path, PathBuf};

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("egglog-experimental crate should be inside the workspace")
        .to_path_buf()
}

fn math_checkpoint_program(repository: &Path, iterations: usize) -> String {
    let base = std::fs::read_to_string(repository.join("benchmarks/math-microbenchmark/base.egg"))
        .unwrap();
    let wrapper = std::fs::read_to_string(repository.join(format!(
        "benchmarks/math-microbenchmark/math-run-{iterations:03}.egg"
    )))
    .unwrap();
    let (_, checkpoint) = wrapper
        .split_once("\n\n")
        .expect("generated checkpoint should separate its include from commands");
    format!("{base}\n{checkpoint}")
}

#[test]
fn pointer_analysis_initdb_passes_proof_checking() {
    let repository = repository();
    let mut egraph = egglog_experimental::new_experimental_egraph_with_proof_testing();
    egraph.fact_directory = Some(repository.join("benchmarks/data/pointer-analysis-initdb"));
    let program =
        std::fs::read_to_string(repository.join("benchmarks/pointer-analysis-initdb.egg")).unwrap();

    egraph.parse_and_run_program(None, &program).unwrap();
}

#[test]
fn math_checkpoint_zero_passes_proof_checking() {
    let repository = repository();

    egglog_experimental::new_experimental_egraph_with_proof_testing()
        .parse_and_run_program(None, &math_checkpoint_program(&repository, 0))
        .unwrap();
}

#[test]
fn math_checkpoint_ten_passes_proof_checking() {
    let repository = repository();
    let program = math_checkpoint_program(&repository, 10);

    egglog_experimental::new_experimental_egraph_with_proof_testing()
        .parse_and_run_program(None, &program)
        .unwrap();
}
