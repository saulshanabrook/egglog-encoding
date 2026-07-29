//! Check-directed execution slicing.
//!
//! Capture records causal evidence during an ordinary run. [`slice_all_checks`]
//! selects the support of every successful check and renders an ordinary
//! egglog program that replays that support on a fresh graph.

mod backward;
mod replay;

use crate::{EGraph, Error};

/// Render the causal support of every successful check in `egraph`.
///
/// Trace capture must have been enabled with [`EGraph::enable_trace`] on the
/// serial main backend before user declarations or input were installed. The
/// returned source is not run or validated; callers choose whether and under
/// which execution mode to run it.
pub fn slice_all_checks(egraph: &EGraph) -> Result<String, Error> {
    let invalid = |error: &dyn std::fmt::Display| Error::BackendError(error.to_string());
    let slice = backward::slice_all_checks(egraph).map_err(|error| invalid(&error))?;
    let replay = replay::build_replay_program(egraph, &slice).map_err(|error| invalid(&error))?;
    let commands = replay.to_commands().map_err(|error| invalid(&error))?;
    replay::ReplayProgram::render_commands(&commands).map_err(|error| invalid(&error))
}
