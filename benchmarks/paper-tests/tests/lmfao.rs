//! Live directional-view rules on frozen covariance query programs.
use egglog_experimental::slotted::{Compiler, Options, export, new_egraph};
use serde::Deserialize;
use slotted_reference::{Substitution, run_spec};
use std::path::Path;

#[derive(Deserialize)]
struct Fixture {
    multi: String,
}

#[test]
fn logical_views_have_the_same_native_and_encoded_counts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    for name in ["single-root", "roots", "shared"] {
        let path = root.join(format!("benchmarks/lmfao/correctness/{name}.egg"));
        let fixture: Fixture =
            serde_json::from_str(&std::fs::read_to_string(path.with_extension("ref")).unwrap())
                .unwrap();
        let source = std::fs::read_to_string(&path).unwrap();
        let mut compiler = Compiler::new(Options::default());
        let mut graph = new_egraph();
        graph.set_num_threads(1);
        let lowered = compiler
            .compile(Some(path.display().to_string()), &source)
            .unwrap();
        graph
            .parse_and_run_program(None, &lowered)
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        let exported = export::export(&graph).unwrap();
        let native = run_spec(&(fixture.multi + "\ndump\n"), Substitution::Snapshot).unwrap();
        assert_eq!(
            (exported.counts.classes, exported.counts.nodes),
            (native.classes, native.nodes),
            "{name}: validated counts"
        );
        let encoded_plan = lmfao_extract::extract_live(&graph, 5.0).unwrap();
        let native_plan = lmfao_extract::extract_export(
            &serde_json::to_string(&native.graph.unwrap()).unwrap(),
            5.0,
        )
        .unwrap();
        assert_eq!(
            encoded_plan.report["estimated_cost"], native_plan.report["estimated_cost"],
            "{name}: joint DAG cost"
        );
    }
}
