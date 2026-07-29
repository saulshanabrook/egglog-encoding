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
//! does not traverse explanations or eagerly materialize ordinary fact terms.
//! Mutable-container primitives are the bounded exception: their exact
//! structural version is anchored when the primitive returns.
//! Commit-local batches publish at existing engine barriers. A quiescent arena
//! has dense identities for facts, firings, causes, and applied equalities;
//! mutation and check events also have unique [`HistoryPosition`]s. Firings do
//! not consume positions: each carries the inclusive history high-water mark
//! sampled when its batch became effective.
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
//! # Retained and cold-derived data model
//!
//! | Record family | Retained fields and semantics | Cold consumer | Why it is necessary |
//! |---|---|---|---|
//! | Temporal coordinates | [`Wave`] groups effects that share a pre-wave state. [`HistoryPosition`] uniquely orders retained fact, equality, rekey, removal, and check events; a firing stores a sampled inclusive high-water cutoff rather than a unique position. The explainer derives the visible equality prefix by binary-searching equality positions. | Historical lookup, equality explanation, liveness, and replay scheduling. | A wave cannot order events within maintenance, while a position prevents later events from explaining earlier reads. Treating firing cutoffs as events would invent an order between same-batch matches. |
//! | Facts | [`RawFactRecord`] retains [`FactId`], table, creation position, exact [`CauseRef`], and the immutable raw row. [`FactCellRef`] selects one typed occurrence. | [`TraceView::fact`], [`TraceView::fact_cell_at`], and backward premise traversal. | Premises, constructor occurrences, historical values, and structural origins must refer to the exact row that existed, not a later equal row. |
//! | Firings and premises | [`Firing`] retains rule, wave, sampled history high-water cutoff, premise [`FactId`]s, and prior rows read by merges. Static binding recipes and [`FiringEqualitySource`] layouts describe how source-order bindings and guards map back to those premises. | [`TraceView::firing`], [`TraceView::firing_terms`], and rule replay. | A selected head action is reproducible only with its exact grounded match and equality state. `merge_reads` retain the previous keyed rows whose omission could change a selected merge result. |
//! | Causes | [`CauseRef`] tags either a firing or a shared [`RawCause`] node; non-rule nodes retain source identity, prior facts, merge ancestry, or rebuild/container landmarks. | [`TraceView::cause`] and lazy backward slicing. | Shared causal nodes avoid copying dependency prefixes while preserving the exact reason an effective fact or equality appeared. |
//! | Applied equalities | [`RawAppliedEquality`] retains the typed raw proposal endpoints, the actual native `child -> parent` forest edge, event position, wave, and [`EqualityReason`]. [`ProjectedAppliedEquality`] adds lazily recovered [`EqualityEndpoint`] terms. | [`TraceView::applied_equality`], [`TraceView::project_applied_equality`], equality explanation, and cause traversal. | Proposal syntax names what the program equated; the native edge makes historical connectivity unambiguous; the reason identifies the program action, merge, or maintenance cause that must be selected. None can be reconstructed from the other two. |
//! | Structural replay terms | [`ReplayTermId`] identifies interned literal/call [`ReplayTerm`] nodes; [`ReplayConstructorSpec`] and per-row/per-rule origin recipes connect raw values to structural syntax. | [`TraceView::replay_term`], [`TraceView::fact_terms`], [`TraceView::firing_terms`], and replay rendering. | Raw native values are opaque and their representative denotation can change under canonicalization; replay needs stable, typed syntax, but projecting every term on the capture path would make tracing expensive. |
//! | Core replay metadata | [`SourceRef`] identifies one source command or original input row. [`ReplayTableSchema`], binding/equality recipes, table key/kind metadata, constructors, merge origins, and container sorts describe how physical rows encode logical syntax. | [`TraceView::table_schema`], source replay, and structural projection. | Dynamic events alone cannot recover typed columns, keys, constructor structure, or merge-cell provenance. The frontend separately retains normalized and surface commands, stable rule/check/source identities, and input-file identity in its capture catalog because core records deliberately contain no frontend AST. |
//! | Container-version anchors | The structural interner sparsely retains every exact [`ReplayTermId`] version observed for a typed mutable-container value; ordinary raw-value lookup remains first-wins. | Historical term availability and container explanation. | One reused native container id can denote several child versions. A single value-to-term entry would let replay satisfy a later use with an earlier structure. |
//! | Criteria | [`Criterion`] retains the first successful check's wave and event position, premises, typed endpoint pairs, and their [`CriterionEndpointOccurrence`]s. | [`TraceView::check_root`], [`TraceView::check_roots`], slice-root selection, and replay check scheduling. | The slicer needs the exact observed witness and historical state; rerunning a query could choose another witness, and scheduling the check at another position could expose a different row lifetime or equality relation. |
//! | Rekeys and changed cells | [`RawRekeyRecord`] retains the affected fact/table, wave, event and equality landmarks, typed [`TypedCellEquality`] changes, and [`RekeyOutcome`]. | [`TraceView::rekey_at`], [`TraceView::fact_cell_at`], and historical key reconstruction. | Canonicalization can change a row's raw key without changing its structural occurrence; collision outcomes also delimit that occurrence's lifetime. |
//! | Tombstones | [`Tombstone`] retains the removed fact, causal firing, and history position for replay-observable keyed tables. | [`TraceView::removal`], liveness checks, and deletion replay. | Immutable fact creation records cannot say when a row stopped being available or which effective action removed it. Presence-relation removals carry no merge-bearing cell and are not retained. |
//! | Cold historical explanations | [`HistoricalFactCell`] follows one occurrence through selected rekeys. [`RawEqualitySupport`] names the earlier edges, facts, and rekeys sufficient for one raw equality. [`RawTermAvailability`] combines that support with child-first [`ReplayAliasPlan`]s; each plan records an optional producer, readiness frontier, and container freshness floor, while tombstones supply the liveness end. These values are computed by a borrowed view and retained only by the resulting slice, not by the capture arena. | Equality/term explanation, backward closure, and replay alias scheduling. | Structural syntax has state-dependent denotation. These products make the strict pre-event denotation dependency explicit and let a later firing reuse a checked value after its constructor row disappears without treating the spelling as timeless. |
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
