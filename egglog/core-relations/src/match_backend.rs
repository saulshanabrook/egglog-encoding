//! Optional bulk matching for experimental accelerators. Actions and table
//! commits still run through the ordinary database execution path.

use crate::{Value, Variable};

/// A set of variable assignments. Column names are unique; rows have exactly
/// `variables.len()` values. The zero-column unit relation is `[[]]`.
#[derive(Clone, Debug)]
pub struct MatchRelation {
    pub variables: Vec<Variable>,
    pub rows: Vec<Vec<Value>>,
}

/// Evaluate the natural join of already filtered atom snapshots.
///
/// Inputs include the current plan's seminaive timestamp restrictions and
/// occurrence constraints. Implementations must return the complete set of
/// assignments to the union of input variables, without duplicates. The empty
/// input joins to the unit relation. Matching must have no database effects.
/// Returning `Err` declines this plan before any of its actions execute; the
/// ordinary matcher then evaluates it. Callers should expose fallback counts.
///
/// This interface deliberately leaves schedules, primitives, keyed interning,
/// merge callbacks, and commit boundaries with egglog.
/// The executor retains native matching for decomposed plans and lossy atom
/// projections, so evaluating a full join cannot change action multiplicity.
pub trait MatchBackend: Send + Sync {
    fn evaluate(&self, atoms: Vec<MatchRelation>) -> Result<MatchRelation, String>;

    /// The executor retained native matching, either because this implementation
    /// declined the query or because a physical plan projects away multiplicity.
    fn on_fallback(&self, _reason: &str) {}
}
