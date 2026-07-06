use std::{
    fmt,
    path::{Path, PathBuf},
};

use egglog_experimental::{EGraph, new_experimental_egraph_with_proofs};

const CODSPEED_FILES: &[&str] = &[
    "egglog/tests/web-demo/rw-analysis.egg",
    "egglog/tests/integer_math.egg",
    "egglog/tests/web-demo/resolution.egg",
];

#[derive(Clone)]
struct BenchCase {
    name: String,
    filename: String,
    path: PathBuf,
    program: String,
}

impl fmt::Display for BenchCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)
    }
}

fn benchmark_cases() -> Vec<BenchCase> {
    EGraph::set_num_threads(1);

    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("egglog-experimental should live under the workspace root");
    let mut cases = Vec::new();

    for file in CODSPEED_FILES {
        let path = workspace_root.join(file);
        let program = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("could not read {path:?}: {err}"));
        let stem = path
            .file_stem()
            .expect("benchmark file should have a stem")
            .to_string_lossy()
            .replace(['.', '-', ' '], "_");
        cases.push(BenchCase {
            name: format!("{stem}_proofs"),
            filename: path.to_string_lossy().into_owned(),
            path: path.clone(),
            program,
        });
    }
    cases
}

#[divan::bench(args = benchmark_cases())]
fn files(case: &BenchCase) {
    let mut egraph = new_experimental_egraph_with_proofs();
    egraph
        .parse_and_run_program(Some(case.filename.clone()), &case.program)
        .unwrap_or_else(|err| panic!("{} failed: {err}", case.path.display()));
    std::mem::forget(egraph);
}

fn main() {
    divan::main();
}
