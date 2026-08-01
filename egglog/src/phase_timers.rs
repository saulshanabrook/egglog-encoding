//! Wall-clock accounting for the work that happens outside rule-set execution.
//!
//! Per-ruleset timing covers only what runs inside a `(run …)`. On programs that
//! build a large graph up front — and under the term/proof encoding, which turns
//! each source command into many encoded ones — most of the wall clock is spent
//! before any rule fires, so a report with only rule-set phases leaves it in one
//! unexplained residual.
//!
//! These phases are disjoint and are charged to the [`EGraph`] that did the work.
//!
//! [`EGraph`]: crate::EGraph

use std::time::Duration;

/// Time spent turning commands into database updates, by phase.
///
/// Disjoint: where one phase nests inside another — the encoder parses the text
/// it generates — the time is charged to the inner one only.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct PhaseTimings {
    /// Text to AST, for the source program and for the text the encoder emits.
    pub parse: Duration,
    /// Typechecking, for the source program and for its encoding.
    pub typecheck: Duration,
    /// Desugaring, removing globals, and shadowing checks: the rest of turning a
    /// command into the commands actually run.
    pub desugar: Duration,
    /// The term/proof encoder rewriting a command, excluding the parse above.
    pub encode: Duration,
    /// Declaring functions and compiling rules into the backend.
    pub install: Duration,
    /// Running top-level actions: the writes that build the initial graph.
    pub actions: Duration,
    /// Interpreting a `run-schedule` — picking rulesets, deciding when a
    /// saturating loop stops — excluding the rule-set time it drives.
    pub schedule: Duration,
    /// Converting a recorded justification into a proof, at a `check`/`prove`.
    pub proof_extraction: Duration,
}

impl PhaseTimings {
    /// Total of every phase.
    pub fn total(&self) -> Duration {
        self.parse
            + self.typecheck
            + self.desugar
            + self.encode
            + self.install
            + self.actions
            + self.schedule
            + self.proof_extraction
    }
}
