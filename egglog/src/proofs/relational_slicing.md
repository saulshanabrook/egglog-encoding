# Relational causal slicing for proof replay

Status: proposed; design only

Implementation branch: `agent/relational-proof-slicing`

Clean base: `f72b0dd3823a7f19fd758cfd2039e993477786e5` (`origin/main`, the
base of PR #42 when this branch was created)

Comparison-only reference: PR #42 at
`e9f7b97aa9b8d855286f41d302066bfb68459620`

No code from PR #42 is to be copied into this implementation. The PR is a
behavioral, performance, and code-size reference. At the reference commit it is
205 commits and 142 changed files from the base, with 40,351 insertions and
1,361 deletions.

## Summary

The proposed implementation records causal provenance during an otherwise
ordinary run, computes a backward slice for a successful check, and runs only
that slice on a fresh e-graph using the existing full proof encoding and proof
checker.

The design has four deliberate properties:

1. A semantic table may opt into a stable row identity. For
   `SortedWritesTable`, the identity is a trailing hidden non-key `Value`
   column. It is absent when the feature is disabled.
2. Stable IDs and, in causal mode, exact row-state event IDs flow through
   free-join as ordinary values. Capture-specific rule plans bind the hidden
   metadata columns to private RHS-used variables, so the existing binding,
   factorization, and materialization machinery retains exact premise
   witnesses.
3. Causal records are fixed-width rows in auxiliary append-only
   `FlatStorageTable`s built from the existing row-buffer and index primitives.
   All-match consumers deduplicate exact rows, union additive evidence, and
   decode selected occurrence-addressed controls locally. There is no semantic
   merge/rebuild machinery, global integrity audit, bespoke trace arena, or
   history-position log.
4. Causality is an event DAG with no semantic run, wave, frontier, or global
   history position. A common-key merge transcript records the exact operand DAG
   and each callback's left/right orientation, but introduces no total order
   among independent steps, unrelated keys, or firings.

Replay reuses the existing `Scheduler`/`Matches` abstraction to choose captured
action-visible bindings once their causal parents are available. Reproducing
the exact dynamic body witness or original ruleset batching is not required.
Complete rule heads still run, while congruence, rebuilding, proof construction,
simplification, and proof checking remain delegated to the existing
implementation.

This is a causally sufficient slice, not a claim of globally minimal axioms,
rules, or proof size.

## Goals

- Capture an exact positive causal witness for successful checks without
  eagerly running the full proof encoding over the original database.
- Keep ordinary execution parallel. Event allocation order may vary, but event
  causality and the proof result must not depend on it.
- Reuse `Table`, `SortedWritesTable`, row buffers and indexes, free-join
  variables, rule batching, the scheduler, the term/proof encoding, and the
  proof checker.
- Add no stable-ID column, allocator, causal buffers, or event writes when
  slicing is disabled.
- Record exact event parents and replay only schedules that respect that DAG;
  unrelated ready events may be batched in any order.
- Represent merge callbacks, rebuilding, and congruence as causal events with
  explicit operands; replay algebraically arbitrary proof-compatible value
  merges from an exact local per-key transcript.
- Fail closed when a table, primitive, backend, or source mutation cannot
  provide the evidence required for a valid replay.
- Make PR #42 usable as a contemporaneous performance and code-structure
  comparison without coupling this branch to its implementation.

## Non-goals

- A total order over rule matches, unrelated keys, or all database mutations.
  Per-key merge transcripts retain operand dependencies and left/right roles,
  not a callback sequence.
- Reconstructing proposals discarded before merge semantics. Invoked per-key
  merge steps, including no-op results, are recorded for exact local replay.
- Global proof minimization, top-k explanations, or shortest-proof search.
- A public, stable trace serialization format in the first implementation.
- DD-backend support in the first implementation.
- Silently accepting opaque facts as axioms.
- Expanding the language supported by the existing proof encoding as part of
  this work.

## Terminology and semantic model

The design distinguishes several identities that must not be conflated.

### Physical `RowId`

The existing `RowId` is an offset into a row buffer. A major table generation
invalidates it, and compaction can renumber it. It remains an internal scan and
index coordinate.

### `StableRowId`

A `StableRowId` identifies a logical row lineage in one semantic table. A full
reference is table-qualified:

```text
StableRowRef = (TableId, StableRowId)
```

The owning `CausalSession` is the implicit namespace and is never encoded in a
semantic or causal row. A numeric stable ID has no meaning outside its owning
table and session.

The stable ID survives:

- physical buffer relocation;
- hash-table rehash and compaction;
- a pure canonicalizing rekey when the row is not absorbed by another row.

It does not survive:

- deletion followed by recreation;
- an effective user merge that produces a semantically new row;
- a semantic refresh whose logical value changed;
- a rekey collision whose merge produces a new result.

IDs are never reused, including after `clear`.

### `EventId`

An `EventId` names one causal event or one version of a logical row. Event IDs
are unique within the owning `CausalSession` and are opaque. Their numerical
order is never used as a causal relation.

Preserving a stable row ID across a rekey does not erase the change: the rekey
creates a new row-state event. In causal mode, that exact state event is a
second hidden non-key column in the semantic row:

```text
[logical columns..., StableRowId, EventId]
```

Stable-ID-only mode has just the first hidden column; causal mode has both. A
captured premise records the row-state `EventId`, not merely the stable ID.
Commit and rebuild code can also read the prior state ID directly from the row
it replaces. This avoids a mutable provenance lookup or read-your-writes
overlay.

### Equality witnesses

An equality witness is a typed pair of values whose causal parents are the
exact semantic equality events used when the equality was observed. It is not
itself proof that the values are equal. Union-find edge metadata lets rule and
rebuild capture form this small proof-neutral witness without recording proof
terms. Path compression preserves the causes of the path it abbreviates.

### Causal parents

Every non-source event names the earlier events required to produce or observe
it. There is no `RunId`, `WaveId`, or `FrontierId` in the causal model. Original
ruleset invocation and worker-batch information may be retained as diagnostic
metadata, but it is never an availability relation or replay constraint.

A causal DAG does not uniquely recover the original execution batches: two
unrelated events may have been peers or may have occurred in different bounded
ruleset executions. Action-exact replay does not need that distinction. It may
choose any topological schedule, while per-key transcript and explicit
read/equality causes retain every ordering that can affect selected semantics.

### `MergeTranscriptId`

A `MergeTranscriptId` names one merge group for a `(table, key)`. Every actual
`MergeFn` invocation gets an opaque step `EventId` and names its ordered
left/right operands. References to leaves or other step IDs encode the exact
binary reduction DAG even when independent subtrees were built in parallel.
Replay uses a dependency postorder of that DAG; no step number, timestamp, or
cross-key order is recorded.

The static table catalog classifies a transcript's replay semantics. A
proof-compatible user value merge uses exact callback replay. Constructor
`UnionId` and container-normalization merges retain callback operands for
causal closure and replay diagnostics but use their dedicated
equality/congruence or normalization
witness during fresh replay; raw union-find representatives are not portable
value-merge results.

## The causal graph

The dynamic graph is a proof-neutral causal hypergraph:

```text
premise row states / equality events
                  |
                  v
            firing or source
                  |
                  v
       proposal / merge / rebuild
                  |
                  v
             row state event
```

Some event kinds have multiple required predecessors. Those are AND edges.
Alternative successful check witnesses are OR choices at root selection; after
choosing a root, equality witnesses and other event parents are exact.

The syntax DAG needed for replay is not recorded eagerly. It is reconstructed
only for selected values from source metadata, selected constructor facts, and
the base/container value registries. Its size is expected to track the selected
value closure in the common case, plus hash-consing/index overhead; no hard
asymptotic bound relative to the final proof is claimed.

## Optional stable row identity

### Physical layout

`TableSpec` gains one validated metadata-layout field rather than two
independent optional column indices:

```rust,ignore
pub enum RowMetadataLayout {
    None,
    Stable,
    Causal,
}

pub struct TableSpec {
    pub n_keys: usize,
    /// Logical, writer-visible non-key columns only.
    pub n_vals: usize,
    row_metadata: RowMetadataLayout,
    // existing fields...
}

impl TableSpec {
    /// Arity accepted from ordinary writers and exposed by logical APIs.
    pub fn write_arity(&self) -> usize { self.n_keys + self.n_vals }

    /// Physical scan/query arity, including the validated metadata suffix.
    pub fn arity(&self) -> usize {
        self.write_arity() + self.row_metadata.width()
    }
}
```

Hidden metadata forms a trailing physical suffix. In stable-ID-only mode the
stable ID is the final column. In causal mode the stable ID is followed by the
row-state event ID. Neither is a key, sort, or rebuildable column. Ordinary
merge callbacks receive and produce only `write_arity()` values. Validated
constructors derive the exact suffix `ColumnId`s; causal layout necessarily
implies stable identity, so malformed partial layouts cannot be represented.
Existing callers may continue to interpret `n_vals` as the logical non-key
count.

`SortedWritesTable::new` remains identity-disabled. A separate builder or
constructor enables the extra column. This prevents an accidental fixed cost
for existing users.

### Reads and writes

- Scans used by core query planning see the physical row, which permits a
  capture plan to bind the hidden column.
- Ordinary atom builders validate and bind only `write_arity()` columns.
- Bridge/public row iteration continues to expose only the declared function
  columns and its existing timestamp/subsume interpretation.
- Core `Table::get_row` and `get_row_column` remain physical operations, so a
  `ColumnId` continues to index `Row::vals` and capture code can read metadata.
  `TableSpec` supplies a logical-prefix projection, and `predict_val`, bridge
  lookup, and public iteration explicitly return only that projection.
- Predicted and committed rows therefore have the same logical shape at the
  `ExecutionState` and bridge APIs even though committed storage has metadata.
- Plain `stage_insert` stays source-compatible and does not pretend to return a
  committed row ID.

A staged candidate is not a fact. Its key may already exist, another candidate
in the same commit group may supersede it, or the merge function may reject it.
Stable IDs are allocated only when merge commits an effective fresh or
replacement row.

Captured mutation buffers carry an opaque `PendingCause` beside each candidate.
The cause is the exact head/source effect or maintenance producer event, not
merely its enclosing firing/action block. If synchronous correlation is useful,
the API may expose an opaque `MutationTicket`; it must never expose a
`StableRowId` before commit.

The mutation-buffer extension is deliberately defaultable for custom tables:

```rust,ignore
fn stage_insert_with_cause(
    &mut self,
    row: &[Value],
    cause: PendingCause,
) -> Result<(), UnsupportedCausalMutation>;

fn stage_remove_with_cause(
    &mut self,
    key: &[Value],
    cause: PendingCause,
) -> Result<(), UnsupportedCausalMutation>;

fn relocate_row_with_cause(
    &mut self,
    expected: (StableRowId, EventId),
    old_key: &[Value],
    rebuilt_logical_row: &[Value],
    cause: PendingCause,
) -> Result<RelocateOutcome, CausalMutationError>;
```

The paired relocation operation is a rebuild/commit operation, not an
independent remove followed by insert. It verifies the expected identity and
prior state, resolves any new-key collision, and reports the exact preserve,
absorb, or replacement outcome atomically.

### Identity transitions

| Operation | Stable identity | Row-state event |
|---|---|---|
| Fresh key accepted | allocate fresh | commit caused by exact effect; store new event ID in row |
| Existing key, merge is no-op | retain existing | no new state event |
| Existing key, merge changes row | allocate fresh result | merge depends on old state and incoming effect/maintenance producer |
| Existing key, callback reports changed with equal projection | allocate fresh result | replacement commit records the authoritative callback outcome |
| Delete | retire | retirement depends on deleting cause and last state |
| Recreate same key/value | allocate fresh | new commit |
| Pure rebuild rekey, no collision | preserve | replace row event ID with rekey depending on prior state/equalities |
| Rekey collision, merge changes row | allocate fresh result | merge depends on both row states |
| Rekey collision, winner unchanged | winner retained; loser retired | coalescence depends on both states |
| Semantic refresh | fresh unless proved representation-only | refresh depends on prior state |
| Rehash/compaction | preserve | no causal event |
| Clear | retire every live identity in capture mode | clear event plus retirement effects |

This separates durable row lineage from exact causal versions. It also avoids
using an execution counter as a row version.

Even an identity-preserving rekey never mutates a key or row-state event in
place. It marks the old physical row stale and appends a fully formed successor
row, advances `TableVersion.minor`, updates indexes/subset tracking, and reports
both removal and addition so `updates_since` observes the transition. The
logical `StableRowId` is the value that survives.

The current parallel insertion path appends staged output before resolving a
collision with the live hash row. Identified/traced paths must be reordered:
resolve each same-key candidate group against its live shard first, decide the
final logical outcome, then allocate metadata and append the complete physical
row. Provisional stable IDs are not permitted. Plain tables retain their
existing fast path.

### Off-mode representation

The disabled path must use the current physical row width and current pending
queues. Do not attach an `Option<PendingCause>` or a counter to every ordinary
row or staged proposal. Select distinct plain/identified/traced buffer and
merge implementations once at table construction so the plain hot loop does
not branch on capture mode. Optional state should be boxed conceptually as:

```rust,ignore
enum TableCaptureState {
    Plain,
    Identified(Box<IdentifiedState>),
    Traced(Box<TracedState>),
}
```

The feature still adds a small fixed layout discriminant to a table/spec; the
no-overhead claim is specifically no extra physical column, per-row/proposal
storage, heap capture state, allocator activity, causal writes, or hot-loop
mode branch when disabled. The benchmark plan measures any remaining fixed
cost.

The stable-ID allocator belongs to table commit state, not mutation-buffer
handles. Parallel merge shards reserve blocks only while committing effective
outcomes. Allocation checks exhaustion before reaching the `Value` stale
sentinel or wrapping; unused entries in a reserved block may create opaque
gaps, but IDs are never reused. Event allocation follows the same checked
rule, as do auxiliary transcript/equality-witness IDs encoded as `Value`s.
Uniqueness matters; allocation order does not.

## Exact premise capture through free-join

The hidden columns are useful because they can use the existing query data path.
Add a capture-specific atom API conceptually equivalent to:

```rust,ignore
add_atom_with_causal_row(
    table,
    logical_entries,
    stable_id_var,
    row_state_event_var,
)
```

Each table atom in a capture-enabled source rule receives distinct private
stable-ID and row-state variables. They are marked RHS-used by the causal
recorder. From that point they are ordinary `Value`s:

- free-join refinement keeps the row subset as today;
- leaf expansion binds the hidden ID column;
- factorized bindings carry it;
- `MatSpec` retains it because it is RHS-used;
- serial and scoped materializers preserve it in their existing row buffers;
- action batching receives it along with the source variables.

No physical-`RowId` witness sidecar is needed in `BindingInfo`, frame updates,
or decomposed materializations.

When a rule match is materialized, the row-state column names the exact
committed state read by that match. The firing recorder stores those event IDs
and checks their stable/table metadata directly from the co-resident hidden
columns and typed capture handles; it does not read the flat store. Duplicate
matches remain distinct by firing `EventId` even if they name the same row
state.

The static capture specification for a rule contains:

- a stable catalog ID, not just a possibly duplicated rule name;
- the table and static source-atom site corresponding to each private ID;
- catalog-declared free-variable slots and types;
- recipes for equality and primitive witnesses;
- a complete-head layout identifying keyed writes/reads by opaque catalog site
  IDs and declaring its fixed effect/read arities;
- the original resolved rule needed for replay.

A match allocates an opaque firing `EventId` and finalizes its immutable
`events` and `event_causes_D` rows from the LHS premise states and equality
witnesses before its complete head is committed. The catalog predeclares that
fixed cause arity. Head effects and reads receive their own event IDs, so later
observations never require mutating the firing row. Every positive keyed LHS
premise also registers a key-state observation for cold scheduling.

Each supported complete-head effect gets its own `EventId`; the firing's
`owner_effects_A` row packs those IDs into one fixed-arity dense row. Each effect
causally depends on its firing/source owner. Each explicit hit/miss likewise
gets a read `EventId` that depends on the observed key state; the consuming
effect depends on that read. These identities distinguish repeated effects and
reads without ordering them. The event descriptor's catalog origin identifies
the static action/read site; no dynamic site number is stored.

Selecting one firing replays its complete head, so capture records the prior
row-state hit or supported key-local absence witness observed by every head
action that consults a keyed table. This includes an existing row read by a
merge that ultimately returns no-op. Such an observation is a parent of the
corresponding effect even when no output event points back to it; otherwise
omitting that old row could turn a captured no-op sibling action into an
insertion during replay. Capture retains invoked merge steps but does not
promote them to row states or retain proposals discarded before any
callback/commit semantics. Action-local tickets are owned by effect IDs; a
later effect that consumes an earlier staged result names that producer effect
as an `event_causes_D` parent. The ordinary complete-head executor reconstructs
the typed local dataflow while replaying the original actions; the causal store
does not archive or inject the intermediate value. Constructs whose dataflow
cannot be reconstructed from the original head plus the producer dependency are
rejected at preflight.

When table commit assigns a candidate to a transcript leaf, its mutation ticket
emits `action_merge_leaf(effect_event -> leaf)`, and the leaf names that exact
effect as its `producer_event`. Non-action candidates likewise name their exact
source or rebuild producer. Backward closure can therefore start from either a
committed result or a selected complete-head action and recover the exact
common-key group in both directions.

Rules that require a table without stable identity fail capture preflight
unless that occurrence has a dedicated sound witness mechanism.

## Auxiliary relational causal store

`CausalStore` is a registry of append-only `FlatStorageTable`s owned by a
`CausalSession`. It is not a semantic core-relations `Database`.

`FlatStorageTable` is intentionally smaller than `Table` and
`SortedWritesTable`. It stores one fixed-width schema in `RowBuffer` storage and
provides only:

- fresh worker-local append buffers backed by the existing concurrent
  pending-buffer pattern;
- quiescent drain/consolidation using `ParallelRowBufWriter` when worthwhile;
- freeze, scan, and row-count operations;
- cold indexes over requested column tuples that return every matching row.

It has no key/value split, functional dependency, merge callback, timestamp,
stale row, deletion, seminaive version, rebuild, or `ExecutionState`. Physical
relations are bags. Consumers deduplicate exact rows, union additive evidence,
and locally decode occurrence-addressed replay controls only when selected. The
type reuses `RowBuffer`, column tuples, the parallel writer, and hash-index
builders; it should not implement the full semantic `Table` trait merely to
inherit operations the causal log does not need.

The existing lower `TupleIndex` storage can be reused after a small refactor
that separates row ingestion from the current `WrappedTableRef`/`TableVersion`
refresh wrapper. `ColumnIndex` is suitable only for a single indexed column; its
multi-column operation is a union, not an exact tuple key. The simplest first
implementation freezes one consolidated `RowBuffer` per physical schema and
builds indexes lazily on that immutable buffer. This is lower-level index reuse,
not an emulation of table versions.

This separation is intentional. It prevents causal rows from changing:

- semantic `TableId` allocation;
- user-visible table enumeration and tuple counts;
- `total_size_estimate` and parallelization heuristics;
- semantic change/saturation reporting;
- main-database dependency strata;
- clear/rebuild behavior;
- trace recursion.

Rule workers and parallel merge shards append through scoped
`FlatWriteBuffer`s, so they do not contend on semantic table shards or a shared
trace mutex. Each worker owns one local `RowBuffer` and returns it after its task
joins. Physical row width is checked before append. Pending buffers may be
consolidated at ordinary engine barriers for memory use, but capture never reads
that mutable storage. Where the execution API cannot borrow scoped writers, a
fresh `Arc<PendingBatch>` plus `Arc::try_unwrap` before draining provides the
same join check: a retained writer prevents the drain without generation
tokens, live-writer counters, or a recovery protocol.

`CausalSession::finish_root` requires every sharing database instance to be at a
quiescent barrier, drains all remaining buffers, and freezes the store before
closure begins. Frozen flat storage has no mutation, stale marking, clear, or
compaction API. The first implementation makes this terminal for the capture
session. Supporting later capture can add immutable segments and snapshot their
directories, but is not required for proof slicing.

There is no causal publication transaction, store-wide candidate manifest, or
integrity-audit phase. Missing data, a reachable cycle, or unusable replay
control is discovered only if the selected slice reaches it. Those conditions
produce a local extraction/replay error; they do not justify validating every
unselected causal row. Normal storage bounds such as physical arity and
`RowBuffer`/index capacity remain checked by the flat table API.

This does not move proof soundness into the flat store. Causal rows only select
authenticated source/rule work and control re-executed operations; archived
results are never injected as axioms. Extra additive rows can only enlarge the
slice, while missing or incompatible selected data causes local
extraction/replay failure. The independent proof checker remains authoritative.
A structural whole-store audit could not prove that capture recorded every
semantic cause anyway.

Flat causal tables themselves never opt into stable-row identity or recursively
capture their own writes.

### Core relations

The exact column encodings should remain private, but the logical schema is:

```text
events(event -> kind, catalog_origin)
event_causes_0(event)
event_causes_1(event -> parent)
event_causes_2(event -> parents{2})
...
event_causes_D(event -> parents{D})

row_state(event -> table, stable_row_id)
row_state_value_N(event -> logical_values{N})             // cold/archive form
row_retired(event -> table, stable_row_id, prior_state)
initial_absence_K(state_event -> table, key{K})
key_transition_K(event -> table, key{K}, prior_key_state,
                 next_presence, next_row_state_or_absent)

firing_P_B(event -> rule, premise_states{P}, bindings{B})
source_event(event -> source_item_id)
owner_effects_A(owner_event -> effect_events{A})
action_merge_leaf(effect_event -> leaf)
merge_transcript_K(transcript -> table, key{K}, observed_key_state,
                   outcome_event)
merge_leaf_N(leaf -> transcript, producer_event, values{N})
merge_step_N(step_event -> transcript,
             left_ref, right_ref, changed, result_values{N})
merge_outcome(event -> transcript, root_ref, next_key_state_or_noop)
commit_event(event -> table, prior_state_or_absent, accepted_ref)
read_hit_K(read_event -> table, key{K}, present_key_state)
read_miss_K(read_event -> table, key{K}, absent_key_state)
equality_witness(event -> sort, lhs, rhs)
rekey_R(event -> table, row, prior_state, witnesses{R})

equality_event(event -> sort, lhs_term_ref, rhs_term_ref, reason)
congruence_C(event -> left_row_state, right_row_state,
                        child_witnesses{C})

check_P_B(event -> check_catalog_id, premise_states{P}, bindings{B})
```

The arrows in this logical notation only separate lookup/discriminator columns
from payload columns for readability. `FlatStorageTable` treats every column as
ordinary data and enforces neither keys nor functional dependencies. Braces
abbreviate that many physical columns in one concrete fixed-width schema; no
count, position, or item-number column is stored in a row.

Every lookup is all-match. Exact duplicates are idempotent. Distinct rows in an
additive evidence relation add parents or constraints; they do not compete for
a privileged definition. Dynamic action multiplicity never comes from row
count; it is carried by distinct firing/effect/read/step `EventId`s and opaque
merge-leaf IDs.

Positive evidence such as cause rows, equality witnesses, and observation
constraints is additive. Addressed replay controls are different: after exact-
row deduplication, two incompatible operational descriptors for one event,
archived values for one row state, normalized `owner_effects_A` sets for one
owner, a transcript header/outcome, or records for one step ID, leaf ID, effect
event, read event, or `(transition_event, table, key)` cannot both define one
exact replay. That conflict is rejected only if the selected slice reaches it.
It is not a reason to impose uniqueness on all flat relations or validate
unrelated rows.

Every dynamic firing, source item, head effect, explicit read, and merge
callback has an opaque identity; identity preserves multiplicity without
implying order. `owner_effects_A` stores the fixed complete-head effect set in
one arity-specific dense row. Each effect descriptor's `catalog_origin` carries
its action-site identity, so the packing columns have no identity or ordering
meaning. For a selected owner, the consumer normalizes matching rows to a set,
requires one effect identity for each expected catalog action site, and rejects
incompatible sets locally. Read events are causal parents of their consuming
effects, and their `catalog_origin` identifies the static read site, so no
owner/read-position row is needed. A runtime-variable list, if a supported
construct needs one, is represented by a fixed-fan-in list DAG rather than
normalized position/item rows. A selected effect executes once per effect
`EventId`, regardless of how many physical rows repeat its descriptor.

`catalog_origin` is an opaque typed catalog identity: depending on `kind`, it
names a rule, source item, action site, read site, table/merge declaration, or
maintenance recipe. Its numeric representation has no ordering meaning.

Selected effect decoding enforces reciprocal identity coherence locally. An
effect ID belongs to exactly one dynamic owner set, that owner is one of the
effect's causal parents, and the effect's catalog action site is valid for the
owner layout. Read-event parents must realize the catalog-declared read-site
layout for that effect; singleton sites have exactly one dynamic read ID, while
explicitly repeatable sites use distinct read IDs. If
`action_merge_leaf(effect, leaf)` exists, the selected `merge_leaf_N` row must
name the same effect as `producer_event`, and the static action kind determines
whether zero or one candidate leaf is expected. Any mismatch fails only when
the effect or leaf is selected. Exact duplicate physical rows remain
idempotent.

`D`, `N`, `K`, `P`, `B`, `R`, `C`, and `A` are prospective arities known from
table/rule registration. `ArityTableFamily` is a thin registry that creates one
`FlatStorageTable` per required physical schema during single-threaded
registration/preflight; the registry is frozen before capture and workers never
add tables. In the event-cause family, arity `D` has physical width `D + 1`:
one child event followed by `D` parent events.

Event parents deliberately use a dense row in `event_causes_D` for each captured
parent tuple, not normalized edge rows. The child event is the indexed lookup
column; the remaining columns are dense packing only. Closure probes every
preflight-registered cause family for the selected event and unions every parent
`EventId` from every matching row, so repeated parents and packing permutations
are idempotent. Semantic roles such as merge left/right belong in the
kind-specific payload, not the generic cause row.
A runtime-unbounded conjunction is expressed as a balanced DAG of fixed-fan-in
cause events, so capture never mutates the table registry. Other genuinely
unbounded non-causal payload lists use the same fixed-fan-in list-DAG pattern.

Merge operand/root references are tagged references to the prior committed row,
a candidate leaf, or another step in the same transcript. `left` and
`right` preserve the callback's `old`/`new` orientation. Each step `EventId`
names one callback result, and operand references form the local dependency DAG.
The root reference determines exactly which steps matter; replay evaluates them
in dependency postorder, with no sequence number between independent subtrees.
`changed` and `result_values` archive the observed callback result for replay
validation; for `changed = false`, the result signature is the retained `old`
operand rather than unused output scratch. They are evidence, never values that
replay may inject as facts.

Static table IDs and premise-site layouts do not need to be repeated in
every firing row; the rule catalog supplies them.

The `table` fields above encode a stable semantic `CatalogTableId`. Flat-store
schema slots and physical row coordinates never appear as provenance payloads,
which keeps semantic and causal-storage identities unambiguous and allows
replay-local remapping.

Before any row-state `EventId` ceases to be live, its complete logical row is
archived in `row_state_value_N`. This includes effective merge/refresh,
identity-preserving rekey, delete, clear, and collision/coalescence, and occurs
before compaction or `maybe_rehash` can discard the stale physical row. Live
row values can be obtained through a cold stable-ID index. Recording every
committed state is a simpler valid first implementation; a later measured
optimization may use archive-on-state-supersession, never merely
archive-on-identity-retirement.

### Key-local state versions

The event DAG records positive causality, but a replay scheduler must also avoid
moving a selected read of an old or absent key state after a selected transition
away from that state. Traced keyed tables therefore expose a local MVCC-style
state reference:

```text
KeyStateRef = (state_event, table, logical_key)
```

- a present state names the committed row-state event;
- an initially absent state is allocated lazily and described by
  `initial_absence_K`; an absence produced by delete/rekey is described by that
  transition's `key_transition_K` row;
- every read hit, supported miss, and merge transcript names the exact state it
  observed;
- every effective insert, replacement, delete, or rekey records the state
  transition it performed.

For the row's full `(table, key)` address, the transition `EventId` becomes the
next key-state token; `next_row_state_or_absent` says whether that state exposes
a present semantic row and, if so, which row-state event. Most events advance
one key; rekey/coalescence may emit several `key_transition_K` rows for the same
event, such as old-key-to-absent and new-key-to-present transitions. Their full
addresses distinguish them without ordering the affected keys. Present LHS
premise rows are observations just like explicit action-side hits. The traced
semantic table keeps its current `KeyStateRef` alongside its existing key index;
a durable causal-mode tombstone map retains absent states across delete, clear,
and quiescent clone. This cursor is mutable table state, not part of the
append-only causal log.

During cold replay planning, all selected observations of state `S` are
scheduled before any selected transition `S -> S'`. That is a key-local
anti-dependency, not a global history edge, and it does not cause backward
closure to retain unrelated observations. Until a table can provide this
contract, action-side misses are rejected at preflight.

### Event allocation and parallel capture

Workers reserve blocks of opaque event IDs from a session counter. A block is
only a uniqueness optimization; it is not a time interval.

Captured table buffers preserve candidate ticket/cause alignment. Every
candidate that participates in a merge group becomes a transcript leaf, and
every actual callback invocation becomes a `merge_step_N`, including a
`changed = false` step. This is necessary because a no-op action may later be
part of a selected firing's complete head.

Current `SortedWritesTable` ownership already serializes actual callbacks for a
key inside its hash shard, so capture can allocate opaque leaf/step identities
and connect operands without another lock. `StagedOutputs` carries candidate
batches and any precombined operand subtree; when the owning shard resolves the
live collision, it stitches that material into the `(table, key)` transcript and
remaps temporary references to final leaf and step IDs. The format also remains
correct if a future reducer builds independent same-key subtrees in parallel:
explicit left/right references preserve the actual DAG even though flat rows
have no sequence.

After resolving the transcript root against the live row, an effective
`commit_event` allocates final metadata and is the only event inserted into
`row_state` for that outcome. Merge-step event IDs never carry `StableRowId`s
and never appear in semantic rows. A no-op outcome has no new row state, but its
transcript remains available if closure reaches one of its candidate owners or
dedicated equality/normalization effects.

Only a common-key transcript, key-state anti-dependency, and action-local
dataflow impose replay order. Unrelated keys, shards, and firings remain
unordered. For the exact user-value path, the initial proof-slicing gate rejects
callbacks with user-semantic database reads, nested user writes, or shared
mutable state, so the transcript remains key-local. This restriction does not
reject the built-in constructor `UnionId`/union-find or container-normalization
paths: they use the
dedicated equality, congruence, and normalization events described below and
ordinary fresh proof rebuild. If the proof gate later admits other effects, the
current step can serve as their owner/cause, but a wider visibility-boundary
design is required before enabling them. Gaps in event IDs are valid.

There is no whole-store integrity audit. During backward slicing, a selected
event must have at least one interpretable descriptor, every selected parent
must resolve, and every matching additive record is followed. The selected
scheduler detects cycles in the resulting union graph. When a selected merge,
key-state transition, or other addressed replay structure is decoded, its
identities, references, multiplicity, and result shape are validated before use.
An unreachable missing or conflicting record is irrelevant; an exact duplicate
is idempotent; and a distinct additive duplicate only enlarges the slice.

## Execution boundaries

Ruleset, source-batch, and rebuild boundaries remain ordinary engine control
flow but are not causal entities. A firing records the exact row/equality/read
events it observed; an output records the firing, transcript, or maintenance
events that produced it. Feed-forward rebuild work likewise records explicit
parents from container normalization, table rekey, equality, and congruence.

Top-level action blocks and native input rows retain resolved actions or parsed
values as stable `SourceItemId` entries in the source catalog; a filename alone
is not sufficient provenance. Each dynamic source item gets its own `EventId`,
so repeated inputs/effects need no row position to preserve multiplicity. A
capture-aware check records its successful witnesses after the state it
observes. Multiple checks may have shared support cones, but source command order
is checker-context metadata rather than causal availability.

## Equality, congruence, and rebuilding

`DisplacedTable` is deliberately not forced into the generic stable-row
contract. Union requests, canonical representatives, path compression, and
displaced edges do not map one-to-one to durable ordinary rows.

Instead, effective equality changes emit typed equality events. In causal mode,
each live displaced parent edge also retains the `EventId` that justifies that
edge (as UF-specific metadata, not a `StableRowId`). This lets path compression
and later rebuild work consume an exact equality cause even before auxiliary
event tables are flushed at the enclosing barrier. Physical UF maintenance
preserves or replaces that event metadata according to the equality operation.

### Explicit union

An effective union records its typed endpoints and depends on the firing or
source event that requested it. A redundant union produces no new semantic
equality event; a later equality witness may use the retained causes on the
existing union-find path.

Path compression is not an independent semantic equality axiom. Its edge
metadata either depends on the equality path it abbreviates or is omitted from
the cold semantic equality graph and treated only as representation
maintenance.

### Equality used by a rule

The static rule capture specification identifies equality requirements among
term occurrences. For a captured firing, the exact premise states and typed
bindings determine the endpoints. Capture reads the causal metadata on the
union-find paths actually used and creates a typed equality-witness event whose
parents are those equality causes. Longer paths are combined through binary
fixed-fan-in witness events, so parent arities remain predeclared. The cold
slicer follows that exact witness rather than searching all equalities that
happened to exist elsewhere in the run.

### Canonicalizing a row

For each ID-typed cell changed by rebuild, record the old/new typed values and
the exact equality witness read from union-find causal metadata. A pure rekey
event depends on:

- the prior row-state event;
- the relevant equality-witness events;
- any container normalization event used by the rebuild.

It preserves `StableRowId` but replaces the row's hidden state-event column
with the rekey event.

### Congruence collision

Suppose two constructor/view rows become the same key after their children are
canonicalized but have different output e-classes. Both pre-collision row
values are archived before either row is absorbed. The congruence event depends
on:

- both pre-collision row-state events;
- the child equality witnesses that made their keys equal;
- the constructor/view declaration in the static catalog.

It produces the parent equality event. A later merge/rebuild event may consume
that equality. This is the causal encoding of congruence; no global rebuild
position is required.

### Replay interpretation

The slice does not replay native rekeys or path-compression operations as
commands. It follows them backward to their source facts, rule firings, and
equality causes. The fresh proof-mode e-graph then runs its existing rebuild
machinery and re-derives the congruence. This keeps maintenance as derived
reasoning rather than a new axiom.

### Containers and custom merges

Container rebuild records structural element equality dependencies and a
normalization kind. Custom merges use the same identified operand DAG and
retain the resolved static merge expression/configuration. A final merge that
returns the existing logical row produces a no-op outcome; otherwise ordinary
commit creates a fresh row state. No algebraic declaration is required for the
exact path.

An external function or custom table that reads hidden database state must
declare a causal-read contract. Without one, any slice reaching it is
unsupported. It must never be converted silently to a source/fiat event.

The prior row in an ordinary keyed collision—including a no-op merge—is an
explicit transcript operand and is supported without a separate read contract.
Other built-in action-side reads that do not appear as LHS atoms, such as
`Lookup*` instructions, need a causal lookup variant that returns the logical
value together with its stable and row-state IDs. It allocates a read `EventId`,
records `read_hit_K`, makes the observed state a cause of that read, and makes
the read a cause of the consuming effect. A miss does the same with
`read_miss_K` and the exact absent key-state event. Replay recomputes the real
key and performs the lookup against the fresh table; the captured row only
schedules and validates the observation and never authorizes a synthesized
default or result. A default insert links its effect ID, read ID, mutation
ticket, and absent-to-present transition. Until these hit/miss paths and their
proof-mode behavior exist, preflight rejects every such built-in read rather
than relying on public lookup APIs that project the hidden event column away.
Lookup/function expressions inside `MergeFn` remain initially rejected by the
merge purity and existing proof-support gates.

## Root selection and backward slicing

### Root capture

A successful check witness contains:

- the check catalog ID;
- exact row-state premise events;
- typed free-variable bindings;
- exact equality witnesses derived from its static layout.

The capture query appends every successful witness to its flat check-witness
table. The query returns an instance-bound `CheckEventHandle` that privately
owns the exact witness `EventId`s produced by this dynamic check invocation and
the database-instance token. This ephemeral capability is not a causal row,
scope ID, or ordering relation. Root selection considers only that set, so a
repeated static check or sibling clone cannot contribute a witness through a
global table scan.

Within that invocation-local set, a cold index deduplicates normalized typed
bindings and stable-row references before choosing deterministically by causal
cost and then a semantic lexicographic tie break; raw event allocation order is
excluded, as are raw stable-ID values. The tie signature uses typed values,
static catalog/source IDs, declared layout slots, and normalized structural provenance; two
witnesses identical under that signature are observationally interchangeable.
If retaining every witness proves too expensive, any bounded policy must itself
be deterministic and exposed as explicit truncation, not an asynchronous
"first match" accident.

### Closure algorithm

The fixed-arity cause family is the canonical representation of unconditional
event-to-event AND edges. The slicer maintains event and static-declaration
worklists:

1. Seed with a successful check witness.
2. Exact-deduplicate the matching `events[event]` headers and require them to
   agree before kind dispatch. Then probe every registered `event_causes_D`
   family and enqueue the union of every matching row's parent columns.
3. Every matching additive kind-specific payload adds its static
   rule/source/table declaration and non-event replay obligations. Addressed
   operational payloads are exact-row deduplicated and must agree if selected.
4. A firing or source event follows its dense `owner_effects_A` row so the
   complete head is retained. The normalized effect set must agree with the
   static owner layout, and every effect must reciprocally name that owner as a
   cause and satisfy its declared read-site layout. Each effect then follows its
   addressed payload and its coherently decoded `action_merge_leaf` mapping, if
   that effect staged a candidate.
5. A selected merge outcome or leaf exact-deduplicates the matching transcript
   controls. Coherent rows locate its transcript; incompatible addressed rows
   fail local decoding. The transcript adds its prior state and every leaf/step
   needed for the observed group outcome. Each selected leaf explicitly
   enqueues its `producer_event`; for an action leaf that producer is the exact
   effect `EventId`. Step-event causal parents are traversed through the cause
   rows, while tagged operand references drive the exact local DAG traversal.
6. A selected read observation adds its present/absent key-state scheduling
   constraint to `SlicePlan` without pulling unrelated observations of that
   state into closure.
7. Repeat until no new events or declarations are selected.

A visited `EventId` set and exact-row sets make duplicate evidence idempotent
and closure linear in the distinct selected graph after root choice.
Parent-before-child postorder supplies the causal base order. Cold planning then
adds key-state observation-before-transition edges and transcript/complete-head
cluster constraints, collapses co-stageable strongly connected components, and
topologically schedules the resulting graph. It fails closed on an incomplete
trace or an SCC containing a genuine causal dependency that cannot be satisfied
before staging. A transient reverse index is built only for that cold scheduling
and diagnostics.

The result contains exact dynamic events plus a static declaration dependency
closure. It reports selected/total counts for sources, rules, firings, facts,
equality events, merge transcripts, and bytes.

### Slice selection guarantee

The policy chooses one producer for each current row state and one supported
check-root alternative according to the cold cost heuristic. The result is
a causally sufficient support under the supported replay contract; it is not
guaranteed minimal even within that policy, and is not a globally smallest
database, smallest rule set, or shortest proof. Selecting a merge outcome—or a
candidate from a selected complete head—may intentionally pull the whole
common-key transcript required to reproduce that action group.

## Cold syntax reconstruction

Raw ordinary-run `Value`s cannot be reused in a fresh proof-encoded e-graph.
The slicer converts only selected typed values to `ReplayValue`s:

- base values become exact literals through `BaseValues`;
- equality-sort values follow selected constructor row states to natural terms;
- container values recursively record their selected elements and
  normalization recipe;
- source input rows retain parsed literals or are regenerated from the selected
  row values;
- merge leaves and intermediate results use their typed operand/read origins
  plus the resolved merge expression to form portable validation signatures;
  a raw equality-sort `Value` is never treated as a portable result;
- unsupported opaque values stop extraction with a typed error.

Hash-cons these values into a slice-local syntax DAG. This is the "weird syntax
DAG" layer, but it is cold and slice-sized rather than a hot global history.

The frontend already retains resolved declarations and the pre-proof program.
A small static `CausalCatalog` maps stable IDs to resolved rules, functions,
merge expressions, source commands, and checks. Static metadata is stored once
per program entity, not once per firing.

Runtime `TableId`s are never assumed to survive fresh replay. The catalog maps
each traced table to a stable program entity/layout ID, and `SlicePlan` builds a
new mapping to replay-local tables after installing the declaration closure.
The same rule applies to external-function IDs and other registration-order
handles.

## Replay and proof production

### Replay artifact

The internal `SlicePlan` contains:

- required sort, datatype, function, relation, merge, and ruleset declarations;
- selected source actions and exact selected input rows;
- selected source rules;
- selected firings in causal parent-before-child order;
- selected per-key merge transcripts, effect/leaf identity mappings, and
  portable intermediate-result signatures;
- selected present/absent key-state observations and transitions;
- replay clusters derived from transcript incidence and complete-head coupling;
- the final check/prove root;
- portable replay binding signatures for action-visible selection;
- the resolved command prefix ending at the root observation and the single
  resolved final check/prove wrapper;
- immutable runtime and extension configuration needed to create a fresh
  replay graph;
- provenance statistics and unsupported warnings.

The first API can keep this in memory. A debug printer may emit an auditable
program, but its format is not initially stable or public.

The replay factory contract is stronger than "clone the original database."
It must construct a semantically empty graph with equivalent primitive, type,
container, and deterministic configuration registrations, then install only
the selected source state. Mutable extension state is never inherited. A
time-, randomness-, environment-, or configuration-dependent operation is
unsupported unless its semantics have a replay-deterministic captured-input
contract accepted by both replay and proof checking.

### Causal action-exact proof production

The initial implementation has one replay path: action-exact replay. It reuses
the existing frontend scheduler rather than adding a low-level grounded
executor:

1. Create a semantically empty e-graph from the captured deterministic replay
   configuration, enable the existing full proof encoding, and install the
   static declaration closure.
2. Load one selected action-visible binding request per captured firing
   `EventId`, already converted to portable replay terms by cold slicing, along
   with its locally decoded catalog-site-to-effect-ID map. The opaque firing ID
   is a selector token, not a replay order.
3. Replay source events once their causal parents are satisfied.
4. After replaying a firing's selected causal producers, resolve its terms
   read-only in the fresh proof-mode e-graph and obtain its local typed values.
5. A `CausalReplayScheduler` receives the existing `Matches` for a rule and
   satisfies only the selected firing-token/binding requests in the next
   causally ready replay cluster.
6. `step_rules_with_scheduler` applies the chosen matches with their complete
   original rule heads. Generated proof/rebuild maintenance remains unfiltered.
7. Continue until the selected check root is available, then execute its stored
   check/prove wrapper, simplify, and independently verify the `ProofStore`.

A replay cluster is derived cold, not captured as a run or wave. Firings whose
actions provide leaves to one common-key transcript must reach that table commit
together. Complete-head coupling unions those transcript groups when one firing
touches several of them. The planner also schedules every selected observation
of key state `S` before a selected transition `S -> S'`. All causal parents of
the cluster must already be available. It computes strongly connected
components after adding these local constraints: a peer cycle such as “A misses
`y` then writes `x`; B misses `x` then writes `y`” becomes one co-staged cluster
rather than an arbitrary order. An SCC containing a genuine causal dependency
that cannot be satisfied before staging is an unschedulable-slice error.
Independent ready components may execute in any order or in parallel.

Selector resolution must never construct a missing equality-sort term,
`set-if-empty` a view, or install a top-level Fiat solely to make filtering
work. Base literals may use normal literal interning; equality-sort anchors must
already exist from selected source/firing replay, or the slice is incomplete.
Comparing a portable syntax signature derived read-only from each candidate
`Match` is an acceptable alternative.

The scheduler path is preferable to synthetic selector facts because it does
not change the rule's logical premise list seen by the proof checker. Proof-mode
instrumentation must retain a mapping from original source free variables to
the values exposed to the scheduler.

This is **action-exact**, not an exact replay of the captured dynamic body
witness. If multiple body witnesses have the same action-visible binding, the
scheduler may use any deterministic witness available in the reduced replay
because it instantiates the same complete rule head and the resulting proof is
checked independently. It must still apply each selected firing/effect identity
exactly once. Distinct identities preserve multiplicity for non-idempotent
effects such as an associative/commutative sum merge, while duplicate physical
rows never multiply execution. If a body distinction can change any action, the
capture specification must include it in the selector. Exact dynamic-premise
replay is deferred unless premise identities are also carried into the replay
executor.

The existing scheduler needs a narrow replay extension rather than a fork:

- carry the selected firing `EventId` as a private request token, so even a
  zero-action-variable match has a nonempty identity-bearing selector row;
- project source-visible selector slots while retaining the complete
  proof-instrumented match tuple for action instantiation;
- retain the firing token in the scheduler's decided relation so ordinary set
  semantics do not collapse repeated action-visible tuples;
- choose body witnesses deterministically while consuming every distinct
  selected firing token exactly once;
- pass the firing's catalog-site-to-effect-ID map through the existing action
  executor, so staged candidates and read validators receive opaque identities
  by static site rather than by runtime position;
- retain each selected binding occurrence that appears early as a residual
  until its causal parents and replay cluster are ready, then consume it exactly
  once;
- discard ordinary unselected residuals rather than allowing them to fire in a
  later replay cluster.

Replay calls the dedicated term/proof-encoding cleanup, path-compression,
rebuild, and delete/subsume schedule only at a derived safe cut. A cut is safe
when every selected observation of a key state that maintenance may advance has
already been consumed and every co-staged transcript cluster is complete. The
planner unions otherwise independent clusters when necessary to reach such a
cut. Calling `step_rules_with_scheduler` does not append frontend maintenance
automatically; maintenance remains unfiltered once invoked. If it advances a
selected key before its recorded observations, replay fails instead of silently
choosing a different schedule.

### Exact local value-merge replay

For selected-action replay of a proof-compatible user value merge,
`SortedWritesTable` receives a cold `PerKeyMergeReplayPlan` alongside its
ordinary pending candidates. This is a controller for the existing merge path,
not a second table or grounded-rule executor:

1. Every replayed source/action occurrence stages its logical candidate with
   the captured transcript and opaque leaf ID. Multiplicity is the set of
   distinct effect/leaf identities.
2. At the merge barrier, the table verifies the replay-local prior row against
   the captured prior-state signature and verifies the exact candidate-leaf
   multiset. A missing, extra, or mis-keyed leaf fails replay.
3. Starting at the transcript root reference, the controller evaluates the
   selected `merge_step_N` operand DAG in dependency postorder and memoizes each
   step `EventId`. Operand references select the replay-local prior row,
   candidate value, or actual result of another step. It invokes the
   corresponding fresh replay graph's proof-instrumented `MergeFn`, derived from
   the same catalog declaration, with the same left/right operand orientation
   and a proof-mode `ExecutionState`.
4. Each invocation must reproduce the captured changed/no-op bit and portable
   user-semantic result projection. Proof-generated IDs and term/proof-table
   writes have no ordinary-capture counterpart and remain unfiltered. Captured
   result values are comparison evidence only; they are never copied into the
   semantic or proof graph.
5. The verified root is committed through the ordinary append/version/index
   path. Fresh replay-local stable/event IDs may differ from capture.

Direct outcomes are explicit: an absent prior plus one leaf commits that leaf
without invoking `MergeFn`; `changed = false` aliases the prior row and appends
nothing; `changed = true` takes the ordinary replacement path even when the
user-semantic projected values happen to compare equal. Validation always
projects away replay-only proof columns, IDs, and timestamps.

The same controller covers source/user commits and ordinary value-table
collisions produced by selected rebuild maintenance. User candidates map by
their exact effect/leaf identities; pure value-rebuild candidates map by
portable prior-row/rebuild-witness signatures. Fresh proof-mode rebuild still
re-derives those candidates; the plan controls only their merge invocations once
they exist.

This must replay the recorded operand DAG, not merely left-fold raw
candidates. For a non-associative merge, `old ⊗ (a ⊗ b)` is not interchangeable
with `(old ⊗ a) ⊗ b`. Different keys may still replay in parallel; no database-
wide merge sequence is introduced.

"Arbitrary" here means no associativity, commutativity, or idempotence
requirement for a user value merge. It includes `old`, `new`, and deterministic
non-associative or non-commutative merge expressions. The initial callback must
still be pure and key-separable: its user-semantic result may depend on its
left/right-oriented operands and immutable captured configuration, but not on shared
`PredictedVals`, counters, early-stop state, mutable extensions, database reads,
or nested user writes. Time, randomness, I/O, and opaque Rust closures are
likewise rejected. These are already outside today's proof-encoding gate; exact
operand-DAG replay removes algebraic restrictions, not the checker/language
gate.

If full proof mode later admits declared merge reads or nested semantic writes,
the causal model must add their real table-dependency visibility boundary and
hold nested buffers until that boundary completes. That wider cross-key
schedule is deliberately not machinery paid by the initial pure-merge path.
Generated proof-helper writes use the existing unfiltered maintenance path and
do not become semantic transcript leaves.

`UnionId` is not treated as a forbidden arbitrary side-effecting merge. Its
collision records the two constructor/value causes and the resulting typed
equality event. Backward closure follows that equality/congruence witness, and
fresh proof replay runs the ordinary proof union-find and rebuild. Likewise,
container normalization follows its specialized structural witness. These
paths may retain local callback records for replay diagnostics, but the
controller neither forces nor compares raw representative IDs, and it does not
replace the dedicated congruence proof with a captured merge result.

Associative/commutative certification remains useful only as an optional fast
path that lets replay use the ordinary reducer after checking the candidate
multiset. It is not the soundness or language-support boundary. Proof soundness
comes from re-executing the catalog-equivalent merge under fresh proof
instrumentation and checking the resulting proof; the captured transcript
controls evaluation but is not a proof axiom.

### Performance hypothesis

The original run carries one hidden metadata `Value` per opted-in row in
stable-ID-only mode and two (`StableRowId` plus row-state `EventId`) in causal
mode, together with compact causal relation rows. It does not allocate AST,
proof-list, congruence, transitivity, or proof-normalization terms for every
derived fact.

The expensive full proof encoding then runs only on selected sources and
action-exact firing occurrences, plus unfiltered proof/rebuild maintenance. The
intended win is to do proof work on a smaller state, not to make individual
proof nodes cheaper. Capture and replay can outweigh that saving on dense
slices; only the end-to-end benchmarks below establish whether the hypothesis
holds.

Replay remains independently checked by the existing proof checker. The causal
store is therefore a selector, not a new trusted proof axiom.

The checker context is the captured resolved command prefix ending at the
selected observation, not the reduced replay graph's incidental helper rules
or the whole source file. Later rule declarations and later global
`let`/`set`/`union` actions are excluded because the checker otherwise treats
global actions non-temporally. Scheduler query/action helpers are excluded.
The final check-to-prove wrapper is desugared and resolved once; that same
stored command is used for replay and appears exactly once in the checker
prefix, so generated names and premise shapes agree without re-resolution.

## Thread safety and determinism

Parallel capture is a design requirement, not a serial fallback.

- Stable-ID allocators use per-table atomic block reservation.
- Event allocators use per-worker blocks.
- Each worker/shard uses a fresh flat causal append handle.
- Pending row/cause metadata remains aligned through sharding and local
  same-key reduction.
- A scoped or uniquely owned `PendingBatch` ensures every producing task joins
  before its buffers are drained; no live reader overlaps consolidation.
- Causal readers inspect only the final immutable store returned by
  `finish_root`.
- Numeric stable/event IDs may differ with thread count.

Tests and debug output compare normalized semantic records, never raw allocation
order. Capture records each actual per-key reduction DAG with explicit
left/right orientation, not a local or database-wide linearization. Exact
value-merge replay drives the existing merge callback from that transcript;
specialized equality and normalization merges follow their dedicated witnesses.
Algebraically order-sensitive value results may legitimately differ across
executions if the base engine exposes a different candidate reduction; each
captured proof must reproduce and justify the observed run, while capture
instrumentation must not itself change that reduction.

## Special operations

### Delete and subsume

Deletion retires the current row state and records the deleting event.
Subsumption is a semantic row-state change and records its predecessor.
Selected-action binding replay is required whenever omitting or adding a peer
action could change later positive derivations.

### `clear`

Capture-aware `Database::clear_table` enumerates and retires live stable rows,
drops never-effective pending candidates, performs the existing clear, and does
not reset the table-local allocator. It first reaches a verified no-live-buffer
barrier, then replaces the pending-state generation so an old weak buffer
cannot repopulate the cleared table on `Drop`. The allocator lives outside that
replaceable pending state and remains monotone. A late old-generation semantic
buffer is rejected and cannot repopulate the table. Flat records from abandoned
work remain harmless bag rows unless a selected root reaches an incomplete
addressed record, which then fails locally. Direct `Table::clear` is unsupported
while exact causal capture is active because it lacks the session context.

### Clone, push, and pop

`Database::try_clone_causal` first requires merged semantic pending queues and a
quiescent causal append batch. It preserves hidden stable and row-state IDs, UF
causal metadata, and present/absent key-state cursors while sharing the causal
session, append-only store, catalog, and allocators. The clone receives a fresh private
database-instance token and the two semantic databases may then diverge.
`PendingCause` and `CheckEventHandle` are unforgeable, instance-bound handles,
so one sibling cannot attach the other's new event as a cause or select its
check root. Inherited events remain valid in both clones through their copied
row/key-state metadata.

The ordinary infallible `Clone` path is unavailable/fails closed while causal
capture is active; plain and stable-ID-only clones retain their normal behavior.
A detached clone into a new causal session is unsupported until it can copy and
translate the reachable causal closure; minting snapshot source events would
incorrectly turn derived state into axioms.

There is no per-instance publication lease. Siblings may submit disjoint,
instance-bound causal records through the same concurrent flat store. Freezing
for `finish_root` is session-wide and requires every sibling capture operation
and append batch to be quiescent; after that terminal freeze, further capture is
rejected.

Push/pop is strictly unsupported in the initial implementation and is rejected
at preflight. Event causality alone is insufficient because the current proof
checker treats its resolved global-action context non-temporally; discarded-
branch globals could incorrectly authorize a proof after `pop`. Future support
requires save/restore of semantic and key-state cursors without rewinding
allocators plus a branch-filtered checker context that excludes discarded
globals.

### Native input

Every selected input row must be replayable without rereading mutable external
state. Capture retains parsed literals or a content-addressed immutable row
snapshot. File paths alone are diagnostic metadata.

### Custom tables

`TableSpec` defaults to `RowMetadataLayout::None`. A custom table opts in only
if it implements the full write-arity, stable identity, rebuild, clear, clone,
and causal-mutation contract. `DisplacedTable` and ephemeral semantic helper
tables remain opted out; flat causal storage is outside the `Table` trait.

Capture preflight examines every enabled rule and check occurrence, not only
the occurrences that a later slice happens to select. If a premise requires
row identity from an opted-out custom table and no specialized sound causal
witness exists, capture is rejected with the table and premise location. This
eager failure prevents a run from producing a trace that only later turns out
to be incomplete.

## API and CLI

Proof semantics and proof strategy should be separate:

```rust,ignore
pub enum ProofStrategy {
    Eager,
    Sliced,
}
```

The CLI shape should make slicing a strategy modifier to existing modes:

```text
--proofs --proof-strategy sliced
--proof-extraction --proof-strategy sliced
--proof-testing --proof-strategy sliced
```

Compatibility wrappers may initially expose `--proof-slicing`, but it must
require one of the existing proof modes. `CommandOutput::ProveExists` and the
public proof types remain unchanged.

Sliced capture must be selected before semantic tables and rules are
registered. Unsupported backends reject the strategy during configuration,
before loading or mutating the program.

Useful internal APIs are:

```rust,ignore
CaptureConfig::Off
CaptureConfig::StableIds
CaptureConfig::Causal(CausalSessionConfig)

CausalSession::finish_root(CheckEventHandle) -> Result<SlicePlan, SliceError>
SlicePlan::replay(factory, ProofConfig) -> Result<CommandOutput, SliceError>
```

`StableIds` is primarily a test and microbenchmark mode, not necessarily a
public CLI treatment.

## Soundness argument

The implementation should maintain and test these invariants.

1. **Projection equivalence.** Removing hidden stable IDs and causal tables from
   a captured run yields the same semantic rows and outputs as capture-off
   execution.
2. **Stable identity.** Every live opted-in row has one unique table-local ID;
   physical movement preserves it; retirement prevents reuse.
3. **Observation fidelity.** Every firing premise, equality test, keyed hit/miss,
   and merge names the exact row, witness, or present/absent key state it
   observed.
4. **Relational event soundness.** Capture emits interpretable descriptors,
   dense cause rows, and kind-specific payloads for each effective event. Closure
   unions all matching additive evidence; selected addressed controls
   exact-deduplicate and must decode coherently. Every row-state commit, merge
   step, rekey, equality, and congruence event names its exact effective causes.
   Merge steps never masquerade as committed row states.
5. **Acyclic causality.** Event parent edges form a DAG independent of numeric
   `EventId` order. Replay augments it only with key-local observation-before-
   transition and co-staging constraints; an unsatisfiable augmented schedule
   fails closed.
6. **Root completeness.** An instance-bound successful check handle has at least
   one complete invocation-local witness and all exact equality witnesses needed
   to justify it.
7. **Closure sufficiency.** Following the union of matching additive operands
   and every coherently decoded selected control reaches the source facts/rules
   needed to recreate the selected root.
8. **Replay fidelity.** Selected source events and action-visible bindings run
   in an augmented causal topological schedule with complete rule heads, exact
   transcript clusters, key-state constraints, and maintenance only at safe
   cuts. A valid alternative body witness may supply a selected action.
9. **Merge fidelity.** Each selected exact value-merge key has the prior state,
   candidate leaf/effect identities, oriented callback operands/results, and
   final outcome reproduced by the catalog-equivalent replay merge after
   semantic projection. Specialized union/congruence and normalization merges
   reproduce their typed causal obligations through ordinary proof-mode
   maintenance, never by importing a captured representative or result.
10. **Quiescent visibility.** Flat buffers are drained only after their producers
    join, and slicing reads only the terminal immutable store returned by
    `finish_root`.
11. **Independent proof validity.** The existing proof checker accepts the
   replay-produced certificate against the stored resolved observation prefix.

## Error policy

Fail closed with structured diagnostics for:

- activation after semantic state already exists;
- unsupported backend or table;
- push/pop in sliced mode;
- stable/event/auxiliary ID exhaustion;
- a wrong-width flat row, flat `RowId` exhaustion, non-quiescent freeze, or
  append after terminal freeze;
- missing stable premise identity;
- missing or wrong-session row state;
- a wrong-instance `PendingCause` or check-root handle;
- a write to an unregistered fixed-arity cause/effect schema family;
- no interpretable descriptor/cause/payload for a selected event or an
  unresolved selected parent;
- incompatible selected addressed controls, including event headers, archives,
  owner-effect sets, reads, merge mappings/transcripts, initial absences, or
  key-state transitions;
- a selected causal cycle or unschedulable augmented replay constraint graph;
- an opaque source value that cannot become a replay term;
- an external function without the required causal-read/validator contract;
- a present/absent key-state mismatch or violated read-miss observation;
- a missing/extra merge leaf, prior-state mismatch, invalid operand reference,
  or callback result mismatch during local transcript replay;
- a user value merge with nondeterministic, cross-key/shared mutable, nested
  user-effect, or other observations outside its initial pure proof-compatible
  contract;
- malformed source catalogs or a replay rule differing from its source;
- no successful check witness;
- proof replay or independent proof-check failure.

There is no automatic full-program fallback. Such a fallback would conceal
slice bugs and invalidate performance measurements.

## Implementation sequence

### Expected code boundaries

The implementation is intended to stay concentrated in existing abstraction
boundaries:

- `core-relations/src/table_spec.rs`: stable-ID metadata, logical/write arity,
  and default causal-mutation capability;
- `core-relations/src/table/mod.rs`: optional physical column, commit-time ID
  allocation, cause-preserving insert/remove buffers, pre-append collision
  resolution, local transcript capture/replay around the existing `MergeFn`,
  key-state/tombstone cursors, merge outcomes, semantic clear-generation-checked
  writers, and compaction;
- `core-relations/src/table/rebuild.rs`: explicit preserve/rekey versus replace
  outcomes;
- `core-relations/src/query.rs` and `free_join/plan.rs`: private stable-ID atom
  bindings, with the existing RHS-used materialization path doing most work;
- `core-relations/src/action/mod.rs` and `free_join/execute.rs`: pending causal
  context, causal hit/miss lookup, and firing recorder integration, without a
  second witness representation;
- one focused `core-relations/src/flat_storage.rs` module: append-only row
  buffers, scoped parallel pending batches, quiescent consolidation/freeze,
  scans, and cold all-match indexes, deliberately outside the semantic `Table`
  trait;
- one focused `core-relations/src/causal.rs` module: session ownership, flat
  schemas, fixed-arity cause families, event drafts, and selected
  addressed-control decoding;
- `core-relations/src/free_join/mod.rs`: database capture state and the
  quiescent, fallible branch-clone boundary;
- `egglog-bridge/src/lib.rs`, `rule.rs`, and the UF/rebuild integration points:
  table opt-in, source/firing layouts, and specialized equality events;
- frontend `lib.rs`/`scheduler.rs`: check roots, slice construction, proof-mode
  replay, and selected-action scheduling;
- existing proof modules only where replay configuration or original-variable
  mapping is required. Proof construction and checking should not be
  reimplemented.

There should be no new grounded-rule executor and no arena/view/explain stack
parallel to the table system. If implementation pressure starts creating such
a subsystem, the design should be revisited before continuing.

### Phase 1: stable row identity

- Add `StableRowId`, table/spec metadata, and logical versus physical arity.
- Implement the disabled, identified, and traced `SortedWritesTable` layouts.
- Cover fresh/no-op/effective merge, delete/recreate, clear, clone, rehash, and
  compaction semantics.
- Add checked table-owned allocators and semantic clear-generation-checked
  buffer lifetimes.
- Keep physical IDs out of public function rows and merge callbacks.

### Phase 2: rebuild and parallel identity

- Add an explicit identity-preserving rebuild/rekey path rather than unrelated
  remove/insert operations.
- Archive every superseded state and append rekeys through ordinary
  version/index/subset update paths.
- Resolve live collisions before final physical append in identified/traced
  parallel `StagedOutputs`.
- Preserve each callback's left/right-oriented operands and result in merge
  buffers, and stitch/remap parallel `StagedOutputs` operand sub-DAGs at the
  owning key shard.
- Implement atomic block allocators and threshold-crossing concurrent tests.

### Phase 3: flat relational causal store

- Add non-`Table` `FlatStorageTable`, worker-local append handles, scoped pending
  batches, quiescent consolidation, terminal immutable storage, and cold
  all-match indexes.
- Add checked physical widths/capacity and a freeze that cannot succeed while a
  producing task still owns a pending-batch handle.
- Add preflight-frozen payload and dense `event_causes_D` arity families.
- Add private instance-bound handles, exact-row deduplication, additive-evidence
  union, and selected addressed-control decoding.
- Record opaque source/effect/read/leaf/step identities, dense
  `owner_effects_A` families, commit/per-key merge/retirement records, initial
  absence descriptors, and present/absent key-state transitions.

### Phase 4: premise and check capture

- Add hidden-ID atom binding to query construction.
- Generate `RuleCaptureSpec`s and record exact firing premises/bindings through
  direct and decomposed joins.
- Finalize each firing's LHS event before head commit, then emit its locally
  addressed effect set and make each effect depend on its owner, reads, and any
  action-local producer effects.
- Capture built-in action-side read hits/misses or reject them at preflight.
- Record successful check witnesses.
- Verify capture projection against capture-off semantics under deterministic
  schedules, and verify each order-sensitive captured run against its own
  observed result without assuming cross-thread merge invariance.

### Phase 5: equality and maintenance events

- Emit explicit union, equality, rekey, congruence, and container dependencies.
- Add provenance-aware UF lookup and exact fixed-fan-in equality witnesses.
- Ensure maintenance events slice back to semantic causes and are not replayed
  as new axioms.

### Phase 6: closure and causal action replay

- Build `SlicePlan`, static declaration closure, and slice-local replay terms.
- Union every matching selected additive cause/payload row, coherently decode
  only reached addressed controls, and detect cycles without event-ID ordering.
- Build the augmented schedule from event causes, key-state anti-dependencies,
  complete-head/transcript clusters, SCC co-staging, and maintenance-safe cuts.
- Add the semantically empty deterministic replay-factory contract and
  `CausalReplayScheduler` for selected action-visible occurrences.
- Replay on fresh ordinary and proof e-graphs and require independent proof
  checking.

### Phase 7: exact local merge replay

- Map captured source bindings through proof instrumentation.
- Add `PerKeyMergeReplayPlan` to verify leaves and drive the existing merge
  callback through the captured operand DAG with explicit left/right
  references.
- Enable delete/subsume plus algebraically arbitrary pure/key-separable user
  value merges only after their action-exact/transcript fixtures pass; retain
  dedicated proof rebuild for `UnionId` and normalization merges.

### Phase 8: product and benchmark integration

- Add proof-strategy API/CLI validation and benchmark treatments.
- Add trace/slice diagnostics and optional debug rendering.
- Broaden toward the existing proof-compatible corpus as the stable-table,
  causal-read, replay, and merge contracts are implemented. Never silently
  widen the proof support gate.

Each phase should be reviewable and benchmarkable independently. In
particular, stable identity should land before causal capture, and causal
capture before replay/proof integration.

## Validation plan

### Stable table tests

- Feature off has the old physical width, no allocator, and no causal writes.
- Every live opted-in row has a non-missing unique ID.
- Fresh insert, no-op merge, effective merge, delete/recreate, pure rekey,
  rekey collision, semantic refresh, clear, clone, and compaction follow the
  identity table above.
- Lookup, scans, cached indexes, sorting, and rehash agree on ID/value pairing.
- Identity-preserving rekey appends a successor, stales the old physical row,
  advances the minor version, appears in `updates_since`, and archives the
  superseded logical row before compaction.
- Effective merge/refresh, delete, clear, and coalescence likewise archive
  every superseded row state.
- A deterministic state-machine test compares a small reference map after each
  operation.
- Stable/event/auxiliary allocator exhaustion fails before the stale sentinel
  or wraparound, prevents the associated semantic outcome from being appended,
  and never reuses an ID. Flat prefixes from abandoned event/transcript drafts
  may remain physically present. Unreachable prefixes are ignored; any prefix
  reached from a selected root must decode completely or fail locally.
- Capture-aware clone succeeds only at a quiescent barrier, shares the session
  and allocators, copies UF/key-state cursors, and uses instance-bound handles;
  a wrong-instance or sibling-root handle is rejected.
- Concurrent siblings may append to the shared flat store, but terminal freeze
  fails while either sibling owns an active capture batch; instance-bound causes
  and root handles keep their selected cones isolated.
- Clear with an outstanding old-generation semantic buffer cannot repopulate
  the table; a late flush is rejected without changing unrelated causal rows.

### Concurrency tests

- Exercise 1, 2, 4, and 32-thread local Rayon pools.
- Exceed current parallel thresholds with at least 25,000 staged proposals and
  10,000-row database/rebuild cases.
- Cover sorted/unsorted inserts, same-key conflicts, no-op merges, deletes,
  rekeys, and compaction.
- Force the parallel live-collision path and assert metadata is allocated only
  after the final logical result is known and appended.
- For two or more same-key candidates, exercise `old`, `new`, a deliberately
  non-associative/non-commutative merge, and a non-idempotent sum under
  1/2/4/32 threads. Each replay must reproduce its captured operand DAG,
  multiplicity, intermediate signatures, and final result; different captured
  DAGs are not required to agree semantically.
- Compare the optional associative/commutative fast path against exact
  transcript replay for the same captured candidate multiset.
- Assert ID uniqueness and normalized transcript replay fidelity, not equality
  of raw IDs or incidental topological traversal order across executions.
- Concurrent flat writers append one intact row per input and preserve physical
  duplicates. Scoped or uniquely owned pending batches prevent terminal freeze
  until every writer has submitted its local buffer.
- Exercise 0/1/2/high-arity cause-family routing, repeated parent IDs, permuted
  dense parent packing, frozen-arity rejection, diamond closure, and cold
  reverse-index construction.
- Exact duplicate evidence is idempotent; distinct cause rows and rows in
  several arity families for one event union all parents; matching additive
  payloads are followed, while selected addressed descriptors must agree.
- A missing selected descriptor/parent/payload, selected cycle, or incompatible
  addressed transcript record fails locally. The same unreachable bad row does
  not make extraction fail.
- Selected-control corruption covers effect reuse across owners, a missing owner
  cause, missing/duplicate singleton read sites, and a nonreciprocal
  effect-to-leaf/leaf-to-producer mapping. The same unreachable corruption is
  ignored.
- Frozen scans and single-/multi-column exact-tuple indexes return all physical
  duplicates. Wrong row width and reserved-sentinel row-count overflow fail
  before consolidation or freeze.

### Causal DAG fixtures

- one source fact and one rule;
- a source action block with local bindings and multiple same-key writes;
- a multi-action head whose later effect consumes an earlier action-local
  result, reconstructed by the ordinary executor under an explicit producer
  effect dependency;
- irrelevant source and rule branches;
- unrelated peer-firing enablement trap with no recorded execution batch;
- genuine multi-step causal recursion;
- repeated variables and equality guards;
- decomposed join with projected existential variables;
- multiple check roots with shared and disjoint cones;
- effective versus no-op merge;
- a selected firing whose sibling head write was a no-op because of a prior
  row, proving complete-head replay retains that read dependency;
- delete/recreate and subsume;
- rekey/congruence from child equality;
- chained rebuild operations where the second explicitly depends on equality
  from the first;
- two available equality paths where capture retains the exact observed one;
- an exact predecessor equality witness while sibling/later equality is never
  substituted;
- path compression cannot be the sole semantic equality cause;
- input-backed relations and supported containers;
- built-in action-side lookup hit, miss, and miss-then-default-insert, including
  key-local absent-state validation;
- two peer actions that cross-miss and insert each other's keys, requiring one
  co-staged augmented-graph SCC;
- a high-fanout rule that measures scheduler filtering cost;
- unsupported-table preflight before semantic mutation, leaving the database
  unchanged;
- push/pop preflight rejection before semantic mutation, including a fixture
  whose discarded branch would otherwise add a checker-global Fiat;
- a sliced hot pass that proves the eager proof encoding was neither installed
  nor executed.
- invalid proof-strategy/flag combinations, an unsupported backend, and sliced
  activation after preexisting semantic state all fail during eager preflight
  without mutating the database.

Every successful fixture runs:

1. original ordinary execution;
2. current full proof testing;
3. ordinary execution with causal capture;
4. all-match backward closure and selected addressed-control decoding;
5. slice replay on a fresh ordinary graph;
6. slice replay under proof testing, proposition comparison, and independent
   proof checking.

Negative fixtures assert a typed error and no full-program fallback.
Today that includes merge action blocks, function-lookup merges, tuple-output
forms, and opaque Rust closures wherever the existing proof gate rejects them;
exact operand-DAG replay does not widen that gate. Declared merge reads and
nested user writes remain future negative fixtures until both proof checking
and a wider visibility-boundary design support them.

### Replay and checker fixtures

- A zero-action-variable rule retains its private firing `EventId` in the
  scheduler request and decided relation; no count or sentinel is needed.
- Duplicate existential/body witnesses for one action-visible tuple preserve
  every distinct captured firing/effect identity, including for a
  non-idempotent associative/commutative merge. Exact duplicate physical rows
  are idempotent, and each selected identity is consumed once.
- Repeated equal bindings in distinct causal firing events remain distinct
  occurrences. A selected occurrence discovered early remains residual until
  its causal parents and replay cluster are ready and is consumed once;
  unselected residuals never leak into later clusters.
- Projection retains the complete proof-instrumented tuple used for action
  instantiation even though filtering compares only action-visible slots.
- A parallel candidate subtree whose captured shape is
  `old ⊗ (a ⊗ b)` replays that shape rather than a raw-candidate left fold.
- `old`, `new`, non-associative, non-commutative, and changed-false transcripts
  replay through the catalog-equivalent proof-instrumented merge and produce
  independently checked proofs.
- A constructor `UnionId` collision and a container-normalization collision use
  their dedicated equality/congruence or structural witness under fresh proof
  maintenance; replay neither forces nor compares captured raw representatives.
- Direct root cases cover absent-prior/single-leaf without callback,
  changed-false prior alias with no append, and changed-true replacement with
  an equal user-semantic projection.
- Deleting a referenced leaf, redirecting a leaf/step reference, swapping
  operand orientation, changing multiplicity/prior state, or corrupting an
  intermediate value-merge result produces a typed replay failure rather than
  a captured-value insert.
- A missing equality-sort selector anchor fails without constructing a term,
  top-level Fiat, or semantic row.
- Proof/term maintenance at a derived safe cut makes the next selected binding
  visible. Running it early while an old-state observer remains must either
  co-stage that observer or fail replay.
- The independent checker receives the stored resolved observation prefix,
  excludes scheduler helpers and later source commands, and validates the exact
  stored wrapper once for both single- and multi-fact final checks. A negative
  fixture places a global action after the check and proves it cannot authorize
  a Fiat for the earlier observation.
- An exact instance-bound `CheckEventHandle` selects only witnesses from that
  check invocation; a sibling clone's root handle is rejected without scanning
  global alternatives.
- Present LHS rows, explicit hits, misses, no-op transcripts, delete/recreate,
  and rekey all obey observation-before-successor key-state constraints.
- A selected native input row replays from its immutable snapshot after the
  original graph is dropped and the original file is changed or deleted.
- A clean replay factory remaps catalog identities to different runtime
  `TableId`/external-function assignments and still succeeds. A nonempty or
  registration-mismatched factory, inherited mutable extension state, or
  uncaptured nondeterministic configuration fails before installing selected
  source state.

### Repository validation

While iterating, use focused crate and proof tests. Before completion, run the
root-required suite:

```text
make check
```

`make proof-tests` is useful during proof work but is already contained in the
full workspace test, so it should not be redundantly rerun after `make check`.

After benchmark-runner changes, also run `make benchmark-smoke`; it is a
separate public-CLI and cache-isolation check and is not part of `make check`.

CPU-intensive tests and benchmarks must be coordinated with other active
benchmark sessions before execution.

## Benchmark and comparison plan

Measurements must separate four costs:

1. capture disabled versus the clean base;
2. stable IDs only versus capture disabled;
3. causal capture and slice construction;
4. reduced proof replay versus full proof generation/extraction.

The primary symmetric metric is nevertheless end-to-end wall time and peak RSS
for the user-visible result. A sliced observation includes the ordinary causal
run, closure, fresh replay, proof generation, extraction/simplification, and
checking performed by that mode. A full observation includes the corresponding
full-mode run through the same result boundary. Replay-only timings and the
internal phase split are diagnostics, not substitutes for that comparison.

Use symmetric comparisons:

- sliced proof generation versus full `--proofs`;
- sliced check extraction versus full `--proof-extraction`;
- strict sliced proof testing for correctness, not wall-time claims;
- PR #42 sliced/full ratios against the new implementation's sliced/full
  ratios on the same machine and workload hashes.

Report absolute matched-mode end-to-end wall/RSS for both full and sliced runs
in each checkout alongside those ratios. Ratios are secondary: a slower
full-proof baseline must not make a sliced implementation look better. PR #42
and this design may assign work to different internal phase labels, so compare
their phase numbers only where start/end boundaries are demonstrably identical.

For PR comparisons, use the common five-workload cohort (Math, bounded Eggcc,
Pointer, Hardboiled, and Luminal) and report Herbie separately if scope support
differs. Do not compare each checkout's default files if their contents differ.

The benchmark runner needs distinct sliced treatments whose cache identities
include the exact flags. Reports and any copied fact inputs must live under
`/tmp`; `.reports.jsonl` remains untouched. Record:

- wall time and peak RSS;
- capture, closure, replay, extraction, and checking phases;
- stable and event row counts/bytes;
- merge transcript/leaf/step counts and bytes, maximum per-key step count, and
  time spent in exact per-key operand-DAG replay;
- total versus selected sources/rules/firings/facts/events/cause rows;
- flat row/index bytes, physical versus distinct causal-row counts, key-state
  observations/transitions, replay clusters, augmented-graph SCCs, and
  maintenance-safe-cut delays;
- scheduler matches considered versus selected firings;
- proof node count and replay-program size;
- binary SHA, workload/fact hashes, compiler, threads, and platform.

Sampling uses paired, interleaved repetitions on one coordinated idle machine:
build each binary once, rotate treatment order within each workload, and pair
observations by repetition. Report each workload's paired median ratio and a
95% percentile-bootstrap confidence interval; report the cohort as the
geometric mean of workload ratios with a bootstrap interval that resamples
both workloads and their paired repetitions. Raw observations remain
available. A timeout is a failure/lower bound, never an imputed sample; no full
cohort claim is made unless every advertised supported workload completes in
both modes.

Because the public benchmark path is effectively single-threaded for this
purpose, run a separate causal-capture scaling experiment at 1, 2, 4, and 32
threads. It measures semantic equivalence, wall/RSS, trace rows/bytes, and
allocation/contention scaling. Include a hot-key arbitrary-merge case so local
serialization is visible; it does not get mixed into the primary j=1
comparison.

The initial fixed tripwires are:

- disabled-path upper 95% confidence bound no worse than 1.05x base;
- no unexplained fixed RSS increase when disabled;
- end-to-end sliced/full upper 95% confidence bound below 1.0x on the supported
  cohort.

Before performance acceptance, a noise/scale pilot must also freeze explicit
budgets for stable-ID-only overhead, causal-capture overhead, active peak RSS,
trace bytes per effective event, and scheduler/cluster amplification. Those
are required gates, not forever-TBD diagnostics, but choosing numerical limits
before any measurement would be arbitrary. Per-workload regressions are always
reported; an amplification or trace diagnosis explains a failure but does not
waive it without an explicit review decision.

PR #42's historical 0.387-0.393 sliced/full wall-time ratio on five workloads
is context, not a merge gate. Its capture-disabled overhead was not measured
against the clean base, so this design requires that missing comparison.

Code structure is also an explicit comparison. Record changed files and lines,
core hot-path changes, new unsafe blocks, and whether each structure reuses
semantic table, flat row-storage, or index primitives.

## Alternatives considered

### Copy or trim PR #42

Rejected. The branch is intentionally clean-room and seeks a different storage
and ordering model. The PR remains a useful corpus, performance, and failure-
mode reference.

### A global arena plus `HistoryPosition`

Rejected. It duplicates table storage and imposes an order stronger than rule
semantics require. Exact event parents, merge operand orientation, and key-state
observation constraints retain only the dependencies that replay needs.

### Eager proof terms with compact evidence payloads

This would add a third term-encoding payload and lazily materialize proofs from
evidence IDs. It is plausible, but it does not satisfy the central goal of
capturing an ordinary semantic run via stable rows, and it duplicates part of
the proof construction trust boundary. Reduced replay lets the existing proof
encoder and checker remain the authority.

### Rerun selected rule declarations without firing capture

Rejected as the complete solution. It can cross-product unrelated bindings and
can introduce actions absent from the captured event cone. Action-exact replay
uses the existing scheduler for every supported rule.

### Synthetic selector relations in proof rules

Deferred in favor of scheduler filtering. Selector atoms are easy to store but
change the premise list seen by proof construction/checking unless a separate
proof-erasure rule is trusted.

### Use `SortedWritesTable` for the causal log

Viable, but not the recommended first choice. With the complete tuple as its
key and a no-op conflict merge, `SortedWritesTable` would give the same storage
semantics: exact duplicate tuples may coalesce, while distinct tuples remain
available to all-match consumers. Additive relations would still union their
matches, and incompatible selected addressed controls would still fail local
decoding. No correctness argument depends on preserving physical duplicates.

The cost is carrying a primary hash, table versions, stale/delete/rebuild hooks,
and semantic `Table` integration for relations that only append, freeze, scan,
and build cold indexes. `FlatStorageTable` is proposed as the smaller storage
specialization, not as a soundness requirement. The implementation comparison
must measure it; if the flat abstraction recreates comparable machinery or does
not improve capture cost, using all-key `SortedWritesTable`s is the fallback.

`SortedWritesTable` remains the right abstraction for semantic relations and
fresh replay tables: those genuinely need keyed lookup, merge behavior,
versioning, and clone semantics. A present key's current-state cursor is the
hidden event ID on that table's live row and is found through its existing hash.
Absent states live in a separate table-owned, causal-mode-only sharded tombstone
map because delete and clear remove ordinary hash entries. That small mutable
map is neither another `SortedWritesTable` nor part of the flat evidence history.

### Put causal storage in the semantic database

Possible, but not preferred. It perturbs table IDs, change reporting, total-size
heuristics, merge dependencies, and clear/rebuild behavior. A separate flat
store avoids those effects and cannot recursively capture itself.

## Decisions to validate before implementation

The design recommends, but implementation should not begin until we agree on,
these points:

1. `StableRowId` names a logical row lineage; a pure rekey preserves it while a
   separate row-state `EventId` records the new version.
2. Causal relations live in a separate append-only `CausalStore` of
   non-`Table` `FlatStorageTable`s. It reuses row-buffer/parallel-writer/index
   primitives but has no FD, timestamp, merge, delete, or rebuild semantics.
   Lookups exact-deduplicate physical rows, union additive relations, and decode
   selected addressed controls locally; there is no global integrity audit.
3. Parallel capture is required; IDs are nondeterministic and have no ordering
   meaning.
4. The causal schema has no run, wave, or frontier identity. Action-exact replay
   is the sole initial replay path: the existing scheduler consumes captured
   binding occurrences in an augmented event-DAG schedule. Exact dynamic
   body-witness replay remains deferred, while action multiplicity and complete
   heads are preserved.
5. Proof production always occurs through a fresh full-proof replay and the
   existing independent checker, rather than direct causal-to-proof
   materialization.
6. Initial backend/language support is a strict subset of the intersection of
   the reference backend and existing proof-encoding gate: every premise table
   needs stable identity or a specialized witness, action-side reads need an
   explicit causal contract. User value merges must be proof-compatible,
   pure/key-separable, and deterministic under their captured transcript;
   `UnionId` and normalization merges use their specialized proof-maintenance
   paths. Push/pop is outside the initial support gate.
7. Before relying on selected-action scheduler replay, a focused spike must
   demonstrate that scheduler-generated query/action rules under proof
   instrumentation retain justifications checkable as instances of the
   original source rule.
   If they do not, action-exact replay needs a narrower selected-binding hook in
   the existing rule executor; it must not silently introduce selector axioms
   or a general grounded executor.
8. For a proof-compatible user value merge, the recorded key-local callback
   transcript is both causal evidence and replay control. Replay re-invokes the
   catalog-equivalent proof-instrumented merge on its exact operand DAG with
   explicit left/right orientation and validates every semantic result;
   associativity/commutativity are optional fast-path properties, not support
   requirements. Constructor `UnionId` and normalization merges instead use
   their dedicated causal witnesses and ordinary fresh proof maintenance.
9. Capture-aware clones share one causal session/store, copy semantic/UF/key-
   state cursors, and isolate new causes and roots with private instance-bound
   handles. Detached causal clones and push/pop are unsupported.
10. Event parents use one preflight-frozen `event_causes_D` flat table per
    concrete arity. Dense parent columns are packing only; all matching rows
    contribute a set of parent `EventId`s, and there is no normalized general
    dependency-edge table.
11. `finish_root` freezes flat storage only at session-wide quiescence. Missing
    selected records, selected cycles, and incompatible selected addressed
    controls fail during closure/replay; unrelated rows are not validated.
    Unknown effects and built-in action-side reads without hit/miss capture are
    rejected at preflight.

These decisions are the boundary between this design and PR #42's approach.
