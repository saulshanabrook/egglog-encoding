#![warn(missing_docs)]
//! # egglog-experimental
//!
//! Experimental extensions to the [`egglog`] language and runtime.
//!
//! Start with [`new_experimental_egraph`] to get an e-graph with every
//! extension registered:
//!
//! ```
//! use egglog_experimental::new_experimental_egraph;
//!
//! let mut egraph = new_experimental_egraph();
//! egraph.parse_and_run_program(
//!     None,
//!     "(datatype Math (Num i64)) (extract (Num 1))",
//! )?;
//! # Ok::<(), egglog_experimental::Error>(())
//! ```
//!
//! ## Language and values
//!
//! - [`RationalSort`] adds exact `Rational` values and numeric primitives.
//! - [`For`] implements `(for (fact...) (action...))`, a rule that runs once
//!   over the current matches.
//! - [`WithRuleset`] groups rules and rewrites with
//!   `(with-ruleset name command...)`.
//! - `(primitive name (InputSort...) OutputSort body)` defines a primitive in
//!   egglog. Body arguments are named `_0`, `_1`, and so on; calls to existing
//!   primitives, functions, and globals determine the required access mode.
//! - `(unstable-fresh! Sort [:cost N] [:unextractable])` creates a fresh value
//!   for each match of a rule action.
//! - [`Subst`] implements `(unstable-subst root map)`, which copies the affected
//!   portion of the constructor sub-e-graph reachable from `root` with each key
//!   e-class replaced by its mapped value.
//!
//! ## Generic containers and callbacks
//!
//! `(sort Name (Maybe T))` declares an optional `T`. The language primitives
//! are `maybe-none`, `maybe-some`, partial `maybe-unwrap`, and
//! `maybe-unwrap-or`. Because `maybe-none` has no value from which to infer its
//! nominal sort, surrounding context must select its type when multiple
//! compatible `Maybe` aliases are in scope:
//!
//! ```text
//! (sort MaybeInt (Maybe i64))
//! (check (= (maybe-unwrap-or (maybe-none) 0) 0))
//! ```
//!
//! `(unstable-catch thunk)` calls a zero-argument `UnstableFn` and returns
//! `maybe-some` for a defined result or `maybe-none` when the call is
//! undefined. `(unstable-maybe-match value on-some default)` applies the unary
//! `on-some` function only when `value` is present; an undefined selected
//! callback makes the match undefined.
//!
//! `(map-fold-kv callback initial map)` invokes `callback` as
//! `(accumulator, key, value) -> accumulator` for each stored entry. Traversal
//! follows opaque, e-graph-local `Value` order rather than a semantic key
//! ordering, so callbacks should be order-insensitive. An undefined callback
//! makes the whole fold undefined.
//!
//! `(f64-is-finite value)` is defined exactly when the built-in `f64` value is
//! neither infinite nor NaN. It can guard rewrites that would otherwise
//! materialize non-finite numeric results.
//!
//! Basic `Maybe` operations support proof mode. `unstable-catch`,
//! `unstable-maybe-match`, and `map-fold-kv` do not currently support proof mode.
//!
//! ## Scheduling and extraction
//!
//! - [`scheduling`] documents the extended `run-schedule` language and named
//!   schedulers.
//! - [`DynamicCostModel`] supports runtime costs declared with
//!   `with-dynamic-cost` and changed with `set-cost`.
//! - [`MultiExtract`] implements `(multi-extract n [:dag] term...)`, returning
//!   one [`MultiExtractOutput`] whose public fields expose shared term storage
//!   and ordered per-root variant IDs.
//! - [`KeepBestCommand`] compacts selected tables to their best terms.
//! - `:extractor greedy-dag` enables heuristic DAG-cost extraction for
//!   `extract`, `multi-extract`, and `keep-best`. Within each independently
//!   costed root or variant, it charges shared subterms once. It does not
//!   support proof/term-encoding view tables.
//!
//! ## Inspection
//!
//! - [`GetSizePrimitive`] implements `(get-size! "table"...)`.
//! - [`GetNodeSizePrimitive`] implements `(get-node-size!)`.
//! - [`PrintTableStatsCommand`] reports table cardinality and out-degree
//!   statistics.
//!
use egglog::ast::Parser;
use egglog::prelude::add_base_sort;
pub use egglog::*;
use std::sync::Arc;

pub mod rational;
pub use rational::*;
pub mod scheduling;
pub use scheduling::*;
mod dag_print;
mod disequality;
mod f64;
mod fresh_macro;
mod map_fold;
mod subst;
mod type_constraints;
pub use subst::Subst;
mod greedy_dag_extract;
mod secondary_map;
pub use disequality::DisequalityEncoding;
pub use greedy_dag_extract::{extract_best_greedy_dag, extract_variants_greedy_dag};

mod set_cost;
pub use set_cost::*;
mod multi_extract;
pub use multi_extract::*;
mod size;
pub use size::*;
mod primitive;
mod table_stats;
pub use table_stats::*;
mod maybe;
mod table_rows;
pub use maybe::*;
mod either;
pub use either::*;
mod container_primitives;
pub use container_primitives::*;

// Sugar modules using parse-time macros
mod sugar;
pub use sugar::*;

mod keep_best;
pub use keep_best::KeepBestCommand;

/// Create an e-graph with all experimental extensions registered.
pub fn new_experimental_egraph() -> EGraph {
    new_experimental_egraph_with_options(true, DisequalityEncoding::default())
}

/// Register extensions with core schedules so term/proof lowering can process them.
pub fn new_experimental_egraph_for_proofs() -> EGraph {
    new_experimental_egraph_with_options(false, DisequalityEncoding::default())
}

/// Construct a graph with the selected disequality encoding. Disable the extended
/// schedule interpreter when enabling term/proof encoding, which lowers schedules.
pub fn new_experimental_egraph_with_options(
    extended_run_schedule: bool,
    disequality_encoding: DisequalityEncoding,
) -> EGraph {
    let mut egraph = EGraph::default();
    add_experimental_extensions(&mut egraph, extended_run_schedule);
    disequality::add_disequality_support(&mut egraph, disequality_encoding);
    egraph
}

/// Create an experimental e-graph with term encoding enabled.
pub fn new_experimental_egraph_with_term_encoding() -> EGraph {
    new_experimental_egraph_for_proofs().with_term_encoding_enabled()
}

/// Create an experimental e-graph with proof generation enabled.
pub fn new_experimental_egraph_with_proofs() -> EGraph {
    new_experimental_egraph_for_proofs().with_proofs_enabled()
}

/// Create an experimental e-graph that extracts and verifies proofs for checks.
pub fn new_experimental_egraph_with_proof_testing() -> EGraph {
    new_experimental_egraph_with_proofs().with_proof_testing()
}

fn add_experimental_extensions(egraph: &mut EGraph, extended_run_schedule: bool) {
    // Set up the parser with experimental parse-time macros
    egraph.parser = experimental_parser();

    // Rational support
    add_base_sort(egraph, RationalSort, span!()).unwrap();

    // Support for set cost
    add_set_cost(egraph);
    egraph.add_read_primitive(GetSizePrimitive, None);
    maybe::add_maybe(egraph);
    egraph.add_read_primitive(GetNodeSizePrimitive, None);
    egraph.add_pure_primitive(map_fold::MapFoldKv, None);
    f64::add_f64_primitives(egraph);
    egraph.add_full_primitive(Subst, None);
    egraph
        .type_info()
        .add_presort::<EitherSort>(span!())
        .unwrap();
    add_container_primitives(egraph);

    // scheduler support
    if extended_run_schedule {
        egraph
            .add_command("run-schedule".into(), Arc::new(RunExtendedSchedule))
            .unwrap();
    }
    egraph
        .add_command("let-scheduler".into(), Arc::new(LetSchedulerCommand))
        .unwrap();

    egraph
        .add_command(
            "multi-extract".into(),
            Arc::new(MultiExtract::new(DynamicCostModel)),
        )
        .unwrap();

    egraph
        .add_command("keep-best".into(), Arc::new(KeepBestCommand))
        .unwrap();

    // Per-column statistics for function tables.
    egraph
        .add_command("print-table-stats".into(), Arc::new(PrintTableStatsCommand))
        .unwrap();
    egraph
        .add_command("primitive".into(), Arc::new(primitive::RegisterPrimitive))
        .unwrap();
}

/// Create a parser with the `for` and `with-ruleset` macros.
pub fn experimental_parser() -> Parser {
    let mut parser = Parser::default();
    parser.add_command_macro(Arc::new(sugar::For));
    parser.add_command_macro(Arc::new(sugar::WithRuleset));
    parser
}
