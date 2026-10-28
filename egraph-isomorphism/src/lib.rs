//! Witnessed isomorphism of ordinary and slotted serialized e-graphs.
//!
//! Accepts [`egraph_serialize::EGraph`] documents with optional [`Slotted`]
//! annotations. Equality preserves operator labels, child order, class types,
//! subsumption, ordered roots, duplicate nodes, and empty classes. IDs, slot
//! spellings, extraction costs, and other class metadata do not affect equality.
//!
//! Slotted nodes are compared up to private-slot renaming and independent
//! symmetry choices for each node and child occurrence.
//!
//! [`find_isomorphism`] returns a verified [`Witness`], an exhaustive mismatch,
//! or an inconclusive result when a work limit is reached. [`verify`] checks a
//! supplied witness without search. Callers must ensure their exports are complete.
//!
//! The input is an [`AnnotatedEGraph`] document, not a live engine e-graph.
//! Engine-specific adapters must reconstruct the logical graph before calling
//! [`Graph::try_from`]; that conversion validates the document and indexes it.
//!
//! Search first assigns **colors**: shared structural labels for classes and live
//! slots. Different colors rule out a pairing; equal colors only identify candidates.
//! It then searches class/slot bijections, pairs nodes modulo symmetries, and verifies
//! the resulting witness. Colors alone never establish isomorphism.
//!
//! A one-slot variable class, including its identity symmetry:
//!
//! ```json
//! {
//!   "nodes": {"v": {"op": "var", "eclass": "C", "children": []}},
//!   "slotted": {
//!     "classes": {"C": {"slots": ["x"], "group": [[0]]}},
//!     "nodes": {"v": {"arguments": [{"kind": "slot", "slot": "x"}]}}
//!   }
//! }
//! ```
//!
//! ```
//! use egraph_isomorphism::{AnnotatedEGraph, Graph, Limits, Outcome, find_isomorphism, verify};
//!
//! let document: AnnotatedEGraph = serde_json::from_str(r#"{
//!   "nodes": {"n": {"op": "constant", "eclass": "c", "children": []}}
//! }"#)?;
//! let graph = Graph::try_from(&document)?;
//! let Outcome::Isomorphic { witness } = find_isomorphism(&graph, &graph, Limits::default())? else {
//!     panic!("a graph must be isomorphic to itself");
//! };
//! verify(&graph, &graph, &witness)?;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

mod graph;
mod search;
mod witness;

pub use egraph_serialize;
pub use graph::{AnnotatedEGraph, Argument, ClassSlots, Graph, NodeSlots, Slotted};
use serde::{Deserialize, Serialize};
pub use witness::{ClassMatch, NodeMatch, Witness, verify};

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct Error(pub String);

/// Search budgets; these do not limit input validation or witness verification.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct Limits {
    /// Maximum class/slot assignments attempted across the search.
    pub search: usize,
    /// Maximum symmetry variants and private-slot assignments per class comparison.
    pub node_variants: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            search: 200_000,
            node_variants: 200_000,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum Outcome {
    /// An explicit correspondence that has passed independent witness verification.
    Isomorphic { witness: Witness },
    /// An invariant differs or exhaustive search found no correspondence.
    Different { reason: String },
    /// A work limit prevented a decision; this does not establish a mismatch.
    Inconclusive { reason: String },
}

/// Find and verify an isomorphism, distinguishing mismatches from work limits.
/// Returns an error if the generated witness fails verification.
pub fn find_isomorphism(left: &Graph, right: &Graph, limits: Limits) -> Result<Outcome, Error> {
    let result = search::search(left, right, limits);
    if let Outcome::Isomorphic { witness } = &result {
        verify(left, right, witness)?;
    }
    Ok(result)
}

#[cfg(test)]
mod tests;
