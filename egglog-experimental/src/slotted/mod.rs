//! Source-to-source slotted e-graph encoding.
#![doc = include_str!("LANGUAGE.md")]

use egglog::EGraph;

mod check;
pub mod export;
mod extract;
mod flatten;
mod frontend;
mod layout;
mod maintenance;
mod model;
pub mod proofs;
mod query;
mod rewrite;
mod slots;
mod syntax;
pub use frontend::{Compiler, Options, ProofMode};

mod runtime;

/// An e-graph with the slotted runtime and egglog's built-in schedule semantics.
/// Evaluate [`Compiler::compile`]'s output with this graph.
pub fn new_egraph() -> EGraph {
    let mut graph =
        crate::new_experimental_egraph_with_options(false, crate::DisequalityEncoding::default());
    register(&mut graph);
    graph
}

/// Register the runtime for lowered slotted programs on an experimental e-graph.
/// Generated programs require core schedules, so construct the graph with the
/// extended schedule interpreter disabled.
pub fn register(graph: &mut EGraph) {
    runtime::register(graph);
    graph
        .add_command(
            "slotted-extract".into(),
            std::sync::Arc::new(extract::ExtractCommand),
        )
        .unwrap();
    graph
        .add_command(
            "slotted-check".into(),
            std::sync::Arc::new(check::CheckCommand),
        )
        .unwrap();
    graph
        .add_command(
            "slotted-export".into(),
            std::sync::Arc::new(export::ExportCommand),
        )
        .unwrap();
}

/// An e-graph that lifts encoded slotted proofs and checks them against the source.
pub fn new_egraph_with_proofs() -> EGraph {
    with_proofs(new_egraph())
}

/// Enable proof translation and checking on a registered slotted e-graph.
pub fn with_proofs(mut graph: EGraph) -> EGraph {
    proofs::pipeline::register(&mut graph);
    graph.with_proofs_for_translation()
}
