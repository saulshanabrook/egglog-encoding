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
//! “Hot” and “cold” describe when work runs, not measured cost. Capture
//! overhead is workload-dependent and must be established with benchmarks.
//!
//! [`Trace::with_view`] is the cold boundary. It requires quiescent, complete
//! history up to the observation boundary, lends a non-escaping [`TraceView`]
//! to a closure, and lets
//! that view build indexes or project [`ReplayTerm`] nodes only for records the
//! consumer asks for. Borrowing the arena avoids copying raw slices while
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
//! | Stored waves | [`Wave`], [`Firing::wave`], and [`Criterion::wave`] identify a synchronous unit whose effects share one pre-wave state. | Grounded firing grouping and check placement. | Dependency order alone cannot preserve a match that read a cell before another firing overwrote it in the same native round. |
//! | Stored positions | [`HistoryPosition`] uniquely orders retained fact, equality, rekey, removal, and check events. [`Firing::history_cutoff`] is instead a sampled inclusive high-water cutoff, not a unique event position. | Historical lookup, liveness, strict pre-event closure, and chronological replay scheduling. | Waves cannot order maintenance events within one unit. Treating firing cutoffs as unique events would instead invent an order between same-batch matches. |
//! | Derived equality prefix | The visible equality prefix is binary-searched from applied-equality positions at a requested [`HistoryPosition`]; it is not stored as another clock. | Historical equality forests and occurrence/denotation explanation. | A later equality must never justify an earlier observation. Deriving the prefix removes redundant hot-path state while preserving that temporal bound under serial capture. |
//! | Dense record totals | [`TraceTotals`] exposes the published fact, applied-equality, and tombstone bounds derived from the arena lengths. | Cold slice indexing and interference scans. | Dense ids make full cold-pass enumeration cheap without retaining a second list or exposing mutable arena storage. |
//! | Facts | [`FactId`] addresses one arena record; [`RawFactRecord`] retains its table, creation position, exact [`CauseRef`], and immutable raw row. [`FactCellRef`] selects one typed occurrence. An effective scalar merge records its incoming carrier and prior fact; its result projects as a keyed table call, and the successor's creation position ends the prior occurrence. | [`TraceView::fact`], [`TraceView::fact_cell_at`], [`TraceView::fact_replacement`], and backward premise traversal. | Premises, constructor occurrences, computed merge results, historical values, and structural origins must refer to the exact row that existed, not a later equal row. Both merge inputs are dependencies even when the result happens to equal one of them. |
//! | Firings and premises | [`Firing`] retains rule, wave, sampled [`Firing::history_cutoff`], premise [`FactId`]s, and prior rows read by merges. Static binding recipes and [`FiringEqualitySource`] layouts describe how source-order bindings and guards map back to those premises. | [`TraceView::firing`], [`TraceView::firing_terms`], and rule replay. | A selected head action is reproducible only with its exact grounded match and equality state. `merge_reads` retain the previous keyed rows whose omission could change a selected merge result. |
//! | Causes | [`CauseRef`] tags either a firing or a shared [`RawCause`] node; non-rule nodes retain source identity, prior facts, merge ancestry, or rebuild/container landmarks. A [`RawCause::Merge`] also stores the inclusive `history_cutoff` at which its callback read both rows. | [`TraceView::cause`] and lazy backward slicing. Merge endpoint denotation uses the callback cutoff, while the later [`RawAppliedEquality::position`] validates the applied native edge. | Shared causal nodes avoid copying dependency prefixes while preserving the exact reason an effective fact or equality appeared. Separating read time from application time prevents a replacement fact or deferred equality from explaining an earlier callback read. |
//! | Applied equalities | [`RawAppliedEquality`] retains the typed raw proposal endpoints, actual native `child -> parent` forest edge, event position, and [`EqualityReason`]. [`ProjectedEqualityProposal`] supplies the lazily recovered structural [`EqualityEndpoint`] proposal and exact reason, but not the native edge or event position. | [`TraceView::applied_equality`], [`TraceView::project_applied_equality`], equality explanation, and cause traversal. | Proposal syntax names what the program equated; the native edge makes historical connectivity unambiguous; the reason identifies the program action, merge, or maintenance cause that must be selected. None can be reconstructed from the other two. |
//! | Structural replay terms | [`ReplayTermId`] identifies interned literal/call [`ReplayTerm`] nodes; [`ReplayCallSpec`] and per-row/per-rule origin recipes connect raw values to structural syntax. | Lazy internal fact projection, [`TraceView::replay_term`], [`TraceView::firing_terms`], and command lowering. | Raw native values are opaque and their representative denotation can change under canonicalization; replay needs stable, typed syntax, but eager projection would move projection work and storage onto the capture path. |
//! | Core replay schemas | [`ReplayTableSchema`], binding/equality recipes, table key/kind metadata, constructors, scalar merge-result calls, and container sorts describe how physical rows encode logical syntax. | [`TraceView::table_schema`], structural projection, interference selection, and command lowering. | Dynamic events alone cannot recover typed columns, keys, constructor structure, or how to name a computed merge result. |
//! | Source identities | [`SourceRef`] distinguishes one source command from one physical input row and is retained on source-owned effects. The frontend catalog adds each source command's surface ordinal, execution wave, direct immutable-global dependencies, and unsupported boundary. | Dynamic source closure and chronological source-event reconstruction. | Replaying an effect without its exact source carrier can change an action bundle, while retaining all earlier source commands would be an imprecise prefix fallback. |
//! | Captured input rows | The frontend input catalog retains the source command, function, pre-input wave, one-based line, and exact [`ReplayTermId`] literal cells for every nonempty row. | Selected `SourceRef::InputRow` materialization into ordinary literal actions. | A replay program must be independent of later file contents or existence, and floating-point cells must preserve their raw bits. Only selected rows enter the program, but all candidate row literals must be captured before the future criterion is known. |
//! | Captured command catalog | The frontend retains graph-neutral normalized commands, macro-expanded surface commands, stable rule/check/source identities, and catalog ordinals. Command lowering computes a cold provides/requires graph over `Sort`, `Function`, and `Ruleset` names. | Source-carrier restoration and transitive static-declaration closure. | The backend trace deliberately contains no frontend AST. The catalog preserves source forms such as rewrites while the cold closure removes unrelated declarations without leaking normalized implementation commands. |
//! | Container-version anchors | The structural interner sparsely retains every exact [`ReplayTermId`] version observed for a typed mutable-container value; ordinary raw-value lookup remains first-wins. | Historical term availability and container explanation. | One reused native container id can denote several child versions. A single value-to-term entry would let replay satisfy a later use with an earlier structure. |
//! | Criteria | [`Criterion`] retains the first successful check's wave and event position, premises, typed endpoint pairs, and their [`CriterionEndpointOccurrence`]s. | [`TraceView::check_roots`], slice-root selection, and replay check scheduling. | The slicer needs the exact observed witness and historical state; rerunning a query could choose another witness, and scheduling the check at another position could expose a different row lifetime or equality relation. |
//! | Rekeys and changed cells | [`RawRekeyRecord`] retains the affected fact, pre-rekey equality landmark, typed [`TypedCellEquality`] changes, and [`RekeyOutcome`]. [`TraceView::rekey_at`] supplies the event position, and the fact supplies its table. | [`TraceView::rekey_at`], [`TraceView::fact_cell_at`], and historical key reconstruction. | Canonicalization can change a row's raw key without changing its structural occurrence; collision outcomes also delimit that occurrence's lifetime. |
//! | Tombstones | [`Tombstone`] retains the removed fact, causal firing, and history position for replay-observable keyed tables. | [`TraceView::removal`], liveness checks, and deletion replay. | Immutable fact creation records cannot say when a row stopped being available or which effective action removed it. Presence-relation removals carry no merge-bearing cell and are not retained. |
//! | Cold historical explanations | [`HistoricalFactCell`] follows one occurrence through selected rekeys. [`RawEqualitySupport`] names the earlier edges, facts, and rekeys sufficient for one raw equality. [`RawTermAvailability`] combines that support with child-first [`ReplayAliasPlan`]s; each plan records an optional producer, readiness frontier, and container freshness floor, while tombstones and effective-merge successors supply exclusive liveness ends. These values are computed by a borrowed view and retained only by the resulting slice, not by the capture arena. | Equality/term explanation, backward closure, and replay alias scheduling. | Structural syntax has state-dependent denotation. These products make the strict pre-event denotation dependency explicit and let a later firing reuse a checked value after its constructor row disappears without treating the spelling as timeless. Repeated `(f key)` merge results therefore receive distinct occurrence-scoped aliases. |
//!
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
