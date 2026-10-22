//! Pull-based observation after committed commands, outside merge callbacks.

use crate::{EGraph, EqualityBatch, EqualityMerged, EqualitySubscription};

impl EGraph {
    /// Subscribe to new equalities for an encoded equality sort. Set
    /// `include_existing` to replay retained history. Each reader owns its cursor.
    /// Plain e-graphs and non-equality sorts return `None`.
    pub fn subscribe_equalities(
        &self,
        sort: &str,
        include_existing: bool,
    ) -> Option<EqualitySubscription> {
        let name = self.proof_state.uf_parent.get(sort)?;
        self.backend
            .subscribe_equalities(self.functions.get(name)?.backend_id, include_existing)
    }

    /// Borrow committed equality events. Save the returned `next` cursor only
    /// after consuming the batch. Clearing or restoring a different history
    /// invalidates affected cursors and returns `None`; resubscribe to restart.
    /// Reasons are opaque proof values in proof mode and Unit in term mode.
    pub fn equality_events(&self, subscription: EqualitySubscription) -> Option<EqualityBatch<'_>> {
        self.backend.equality_events(subscription)
    }

    /// The constructor whose collision established this equality, if any.
    /// This observes accepted congruences, not redundant collision attempts.
    pub fn congruence_source(&self, event: &EqualityMerged) -> Option<&str> {
        let id = self.backend.congruence_source(event)?;
        self.functions
            .iter()
            .find_map(|(name, function)| (function.backend_id == id).then_some(name.as_str()))
    }
}
