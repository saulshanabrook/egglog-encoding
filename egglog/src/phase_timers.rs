//! Wall-clock accounting for the work that happens outside rule-set execution.
//!
//! Per-ruleset timing covers only what runs inside a `(run …)`. On programs that
//! build a large graph up front — and under the term/proof encoding, which turns
//! each source command into many encoded ones — most of the wall clock is spent
//! before any rule fires, so a report with only rule-set phases leaves it in one
//! unexplained residual.
//!
//! These phases are disjoint and are charged to the [`EGraph`] that did the work.
//! What they leave over is the summary's unattributed residual: the driver loop's
//! own per-command work, which grows with the command count, and the commands
//! under no phase at all (a `check`, a print, `extract`).
//!
//! [`EGraph`]: crate::EGraph

use std::time::Duration;

/// Time spent turning commands into database updates, by phase.
///
/// Disjoint: where one phase nests inside another, the time is charged to the
/// inner one only. Rule-set time is subtracted the same way, being reported per
/// rule set instead.
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
    /// Interpreting a `run-schedule`, and every other user-defined command, since
    /// one can replace `run-schedule` entirely. Excludes the rule sets it drives
    /// and the commands it runs, so a user-defined command that does its own work
    /// (extracting, say) is the larger part of this.
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
