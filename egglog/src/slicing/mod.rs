#![doc = include_str!("check_directed_replay.md")]
//!
//! ## Rust API reference
//!
//! [`slice_all_checks`] is the public in-process facade. Its input is the
//! ordinary recording graph after [`EGraph::enable_trace`] was called before
//! rules, facts, or input were installed. Empty declarations may already be
//! present, but callers must replay with a fresh graph factory that installs
//! the same declarations because the artifact does not duplicate them. The
//! facade selects every recorded successful check and returns graph-neutral
//! egglog source that owns no handles or runtime values from the recording
//! graph.
//!
//! The facade only selects, lowers, and renders. It does not run the returned
//! program, validate replay, write a file, or claim that the selected support
//! is globally minimal or is itself a proof. It requires a healthy capture on
//! the concrete main backend and fails closed when selected history cannot be
//! represented as ordinary source.
//!
//! Its error surface is the crate's existing [`enum@crate::Error`]. Internal trace,
//! selection, catalog, input, lowering, and rendering failures are reported as
//! [`crate::Error::BackendError`]; slicing introduces no public error type.

mod backward;
mod replay;

use crate::{EGraph, Error};

/// Render graph-neutral replay source for every successful check in `egraph`.
///
/// Trace capture must have been enabled with [`EGraph::enable_trace`] on the
/// serial main backend before rules, facts, or input were installed. Empty
/// declarations may precede capture only when the caller supplies the same
/// declarations in the fresh replay graph; the rendered artifact omits them.
/// Selection follows the
/// recorded historical cutoffs, preserves complete visible effects of retained
/// source commands and firings, and renders ordinary egglog source suitable for
/// a fresh, equivalently configured graph.
///
/// The returned program is not run, replay-validated, or written anywhere.
/// Callers choose whether to execute it and under which execution mode.
///
/// # Errors
///
/// Returns the existing [`enum@crate::Error`] type. Missing or poisoned capture,
/// unsupported backends or selected constructs, and invalid trace or lowering
/// state are surfaced as
/// [`crate::Error::BackendError`].
pub fn slice_all_checks(egraph: &EGraph) -> Result<String, Error> {
    let invalid = |error: &dyn std::fmt::Display| Error::BackendError(error.to_string());
    let slice = backward::slice_all_checks(egraph).map_err(|error| invalid(&error))?;
    let replay = replay::build_replay_program(egraph, &slice).map_err(|error| invalid(&error))?;
    let commands = replay.to_commands().map_err(|error| invalid(&error))?;
    replay::ReplayProgram::render_commands(&commands).map_err(|error| invalid(&error))
}
