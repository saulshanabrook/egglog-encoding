//! Compact execution-trace capture for backward slicing.
//!
//! Native commit paths append replay-observable events to short-lived batches and
//! publish them at existing engine barriers. The trace is causal evidence, not
//! a proof object; explanation, slicing, and replay are lazy cold consumers.
//!
//! # Architecture
//!
//! [`Trace`] is the shared capture handle. Its hot path retains raw values,
//! stable identities, compact range handles, and static producer metadata; it
//! does not traverse explanations or eagerly materialize structural terms.
//! Commit-local batches publish at existing engine barriers so a quiescent
//! arena has dense event identities and one global [`HistoryPosition`] order.
//!
//! [`Trace::with_view`] is the cold boundary. It requires quiescent, complete
//! history up to the observation boundary, lends a non-escaping [`TraceView`]
//! to a closure, and lets
//! that view build indexes or project [`ReplayTerm`] nodes only for records the
//! consumer asks for. Borrowing the arena keeps raw slices cheap while
//! preventing capture storage from escaping the checked borrow boundary.
//!
//! A trace records what one execution observed and the causal landmarks needed
//! to reconstruct it. It is therefore evidence from which a slicer can select
//! replay support, not a proof certificate: capture does not establish global
//! minimality, logical validity, or equivalence independently of the engine.
//! Replay generation and proof-mode validation remain separate consumers.
//!
//! # Retained data model
//!
//! | Record family | Retained fields and semantics | Cold consumer | Why it is necessary |
//! |---|---|---|---|
//! | Facts | [`RawFactRecord`] retains [`FactId`], table, creation position, exact [`CauseRef`], and the immutable raw row. [`FactCellRef`] selects one typed occurrence. | [`TraceView::fact`], [`TraceView::fact_cell_at`], and backward premise traversal. | Premises, constructor occurrences, historical values, and structural origins must refer to the exact row that existed, not a later equal row. |
//! | Firings and premises | [`Firing`] retains rule, wave, history/equality cutoffs, premise [`FactId`]s, and prior rows read by merges. Static binding recipes and [`FiringEqualitySource`] layouts describe how source-order bindings and guards map back to those premises. | [`TraceView::firing`], [`TraceView::firing_terms`], and rule replay. | A selected head action is reproducible only with its exact grounded match and the equality state visible to that match. |
//! | Causes | [`CauseRef`] tags either a firing or a shared [`RawCause`] node; non-rule nodes retain source identity, prior facts, merge ancestry, or rebuild/container landmarks. | [`TraceView::cause`] and lazy backward slicing. | Shared causal nodes avoid copying dependency prefixes while preserving the exact reason an effective fact or equality appeared. |
//! | Applied equalities | [`RawAppliedEquality`] retains the typed raw proposal endpoints, the actual native `child -> parent` forest edge, event position, wave, and [`EqualityReason`]. [`ProjectedAppliedEquality`] adds lazily recovered [`EqualityEndpoint`] terms. | [`TraceView::applied_equality`], [`TraceView::project_applied_equality`], and equality explanation. | Proposal syntax names what the program equated; the native edge is what makes historical connectivity and cutoff replay unambiguous. Neither can be reconstructed from the other. |
//! | Structural replay terms | [`ReplayTermId`] identifies interned literal/call [`ReplayTerm`] nodes; [`ReplayConstructorSpec`] and per-row/per-rule origin recipes connect raw values to structural syntax. | [`TraceView::replay_term`], [`TraceView::fact_terms`], [`TraceView::firing_terms`], and replay rendering. | Raw native values are opaque and their representative denotation can change under canonicalization; replay needs stable, typed syntax, but projecting every term on the capture path would make tracing expensive. |
//! | Sources and catalog metadata | [`SourceRef`] identifies one source action or original input row. [`ReplayTableSchema`], binding/equality recipes, table key/kind metadata, constructors, merge origins, and container sorts describe how physical rows encode logical syntax. | [`TraceView::table_schema`], source replay, and structural projection. | Dynamic events alone cannot recover frontend identities, typed columns, keys, constructor structure, or merge-cell provenance. |
//! | Criteria | [`Criterion`] retains the first successful check's premises, typed endpoint pairs, their [`CriterionEndpointOccurrence`]s, and equality cutoff. | [`TraceView::check_root`], [`TraceView::check_roots`], and slice-root selection. | The slicer needs the exact observed success to seed traversal; rerunning a query could choose a different witness. |
//! | Rekeys and changed cells | [`RawRekeyRecord`] retains the affected fact/table, wave, event and equality landmarks, typed [`TypedCellEquality`] changes, and [`RekeyOutcome`]. | [`TraceView::rekey_at`], [`TraceView::fact_cell_at`], and historical key reconstruction. | Canonicalization can change a row's raw key without changing its structural occurrence; collision outcomes also delimit that occurrence's lifetime. |
//! | Tombstones | [`Tombstone`] retains the removed fact, causal firing, and history position for replay-observable keyed tables. | [`TraceView::removal`], liveness checks, and deletion replay. | Immutable fact creation records cannot say when a row stopped being available or which effective action removed it. Presence-relation removals carry no merge-bearing cell and are not retained. |
//! | Alias plans | [`ReplayAliasPlan`] retains an optional exact producer, one readiness frontier, and an optional container freshness floor; selected tombstones supply the liveness end. | [`TraceView::explain_firing_term_availability`] and replay alias scheduling. | A later firing may reuse a checked e-class value after its constructor row disappears; the bounds say when that spelling is justified without treating it as globally timeless. |
//!
//! # Counters
//!
//! Counters are intentionally cold, passive readings. A borrowed view is
//! quiescent, but [`Trace::replay_term_counters`] samples independently locked
//! interner stores and is not an atomic snapshot during concurrent writes.
//! Every public field has the following meaning:
//!
//! | Field | Meaning |
//! |---|---|
//! | [`TraceTotals::facts`] | Published fact records. |
//! | [`TraceTotals::firings`] | Published firing records. |
//! | [`TraceTotals::causes`] | Published shared cause nodes. |
//! | [`TraceTotals::applied_equalities`] | Published effective native equality edges. |
//! | [`TraceTotals::rekeys`] | Retained logical-row relocation records. |
//! | [`TraceTotals::removals`] | Retained keyed-row tombstones. |
//! | [`TraceTotals::check_roots`] | Retained first-success criteria. |
//! | [`TermInternerCounters::interned_nodes`] | Unique nodes in the structural replay-term DAG. |
//! | [`TermInternerCounters::installed_values`] | First-wins typed raw-value-to-term mappings. |
//! | [`TermInternerCounters::table_layouts`] | Registered replay table layouts. |
//! | [`TermInternerCounters::container_anchor_keys`] | Typed raw container identities with explicit structural-version anchors. |
//! | [`TermInternerCounters::container_anchor_terms`] | Structural-version term handles across all container-anchor keys. |

use std::{
    any::TypeId,
    sync::{
        Arc, Mutex, OnceLock, RwLock,
        atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering},
    },
};

use dashmap::mapref::entry::Entry;
use smallvec::SmallVec;

use crate::{
    AtomId, QueryEntry, TableId, Value, Variable,
    common::{DashMap, HashMap, HashSet},
    numeric_id::{DenseIdMap, NumericId},
};

mod capture;
mod model;
mod terms;

pub use capture::*;
pub use model::*;
pub use terms::*;

// Test-only probe for assertions about lazy fact-term projection and memoization.
// It is thread-local so concurrent tests do not share counts; production builds
// contain neither the counter nor its accessors.
#[cfg(test)]
thread_local! {
    static TEST_TERM_PROJECTOR_FACT_EXPANSIONS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_term_projector_fact_expansions() {
    TEST_TERM_PROJECTOR_FACT_EXPANSIONS.set(0);
}

#[cfg(test)]
pub(crate) fn term_projector_fact_expansions() -> usize {
    TEST_TERM_PROJECTOR_FACT_EXPANSIONS.get()
}
