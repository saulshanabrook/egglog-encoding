use std::{
    fmt,
    path::{Path, PathBuf},
};

use egglog_experimental::{
    EGraph, new_experimental_egraph, new_experimental_egraph_with_proofs,
    new_experimental_egraph_with_term_encoding,
};

const DEFAULT_FILES: &[&str] = &[
    "egglog/tests/math-microbenchmark.egg",
    "egglog/tests/web-demo/rw-analysis.egg",
    "egglog/tests/integer_math.egg",
    "egglog/tests/web-demo/resolution.egg",
];

#[derive(Clone, Copy)]
enum Treatment {
    Off,
    Term,
    Proofs,
}

impl Treatment {
    fn name(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Term => "term",
            Self::Proofs => "proofs",
        }
    }

    fn egraph(self) -> EGraph {
        match self {
            Self::Off => new_experimental_egraph(),
            Self::Term => new_experimental_egraph_with_term_encoding(),
            Self::Proofs => new_experimental_egraph_with_proofs(),
        }
    }
}

#[derive(Clone)]
struct BenchCase {
    name: String,
    filename: String,
    path: PathBuf,
    program: String,
    treatment: Treatment,
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
    let treatments = [Treatment::Off, Treatment::Term, Treatment::Proofs];
    let mut cases = Vec::new();

    for file in DEFAULT_FILES {
        let path = workspace_root.join(file);
        let program = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("could not read {path:?}: {err}"));
        let stem = path
            .file_stem()
            .expect("benchmark file should have a stem")
            .to_string_lossy()
            .replace(['.', '-', ' '], "_");
        for treatment in treatments {
            cases.push(BenchCase {
                name: format!("{}_{}", stem, treatment.name()),
                filename: path.to_string_lossy().into_owned(),
                path: path.clone(),
                program: program.clone(),
                treatment,
            });
        }
    }
    cases
}

#[divan::bench(args = benchmark_cases(), sample_count = 10)]
fn files(case: &BenchCase) {
    let mut egraph = case.treatment.egraph();
    egraph
        .parse_and_run_program(Some(case.filename.clone()), &case.program)
        .unwrap_or_else(|err| panic!("{} failed: {err}", case.path.display()));
    std::mem::forget(egraph);
}

fn main() {
    divan::main();
}
