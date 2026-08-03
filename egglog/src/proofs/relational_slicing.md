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
3. Causal records are ordinary rows in auxiliary `SortedWritesTable`s. There is
   no bespoke trace arena and no global history-position log.
4. Ordering is represented only at real stable-state boundaries. A bounded
   ruleset execution and each causally feed-forward rebuild stratum form waves.
   Firings in a user wave are peers. The one deliberate local linearization is
   the ordered transcript of merge-callback invocations for a common table key;
   no order is introduced between unrelated keys or firings.

The first replay implementation may conservatively run every selected source
rule once in each selected wave. The action-exact replay path should reuse the
existing `Scheduler`/`Matches` abstraction to choose only captured
action-visible bindings; reproducing the exact dynamic body witness is not an
initial requirement. Both paths keep complete rule heads and delegate
congruence, rebuilding, proof construction, simplification, and proof checking
to the existing implementation.

This is a causally sufficient slice, not a claim of globally minimal axioms,
rules, or proof size.

## Goals

- Capture an exact positive causal witness for successful checks without
  eagerly running the full proof encoding over the original database.
- Keep ordinary execution parallel. Event allocation order may vary, but event
  causality and the proof result must not depend on it.
- Reuse `Table`, `SortedWritesTable`, mutation buffers, free-join variables,
  rule batching, the scheduler, the term/proof encoding, and the proof checker.
- Add no stable-ID column, allocator, causal buffers, or event writes when
  slicing is disabled.
- Preserve exact same-wave semantics: all selected user firings in a wave read
  the same input frontier.
- Represent merge callbacks, rebuilding, and congruence as causal events with
  explicit operands; replay algebraically arbitrary proof-compatible value
  merges from an exact local per-key transcript.
- Fail closed when a table, primitive, backend, or source mutation cannot
  provide the evidence required for a valid replay.
- Make PR #42 usable as a contemporaneous performance and code-structure
  comparison without coupling this branch to its implementation.

## Non-goals

- A total order over rule matches, unrelated keys, or all database mutations.
  Per-key merge callback transcripts are intentionally ordered.
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

### Equality obligations

An equality obligation is a typed pair of values plus the committed input
frontier at which they had to be equal. It is not itself proof that the values
are equal and it does not select one hot-path union edge. Rebuild, congruence,
rule, and check records refer to obligations; the cold slicer chooses a
supporting path of semantic equality events available at the required frontier.

### `RunId` and `WaveId`

A `RunId` groups one frontend/backend bounded operation. A `WaveId` names one
stable-input-to-stable-output transition inside it.

The important boundaries are:

- a source action block or native input batch;
- the user-rule portion of one `Backend::run_rules` call;
- each causally feed-forward container/table rebuild stratum;
- a check observation after a completed state.

A wave has an input frontier, unordered peer firings or source events, an
effective commit/rebuild phase, and an output frontier. A coarse
`wave_depends_on` relation records which completed frontier a wave reads. This
is the only cross-wave ordering required by the model.

A frontier is a small antichain of committed wave heads, not a scalar
timestamp. Availability means graph ancestry from one of those heads. The
common unbranched case has one head, while clone/future join points can have
more without imposing an order between them.

A capture-aware database clone shares its parent's `CausalSession` and forks a
new branch frontier. The catalog and ID allocators are therefore shared;
frontier ancestry determines which inherited or branch-local events a later
wave may consume. Sibling-only events are rejected even though their numeric
IDs come from the same session allocator.

### `MergeTranscriptId`

A `MergeTranscriptId` names the merge work for one `(wave, table, key)` commit
group. Its steps linearly order only actual `MergeFn` invocations for that key.
Each step also names its ordered left/right operands, so the transcript can
represent the actual binary reduction tree even when independent subtrees were
built in parallel. The local ordinal is replay control, not a timestamp or a
cross-key order.

The static table catalog classifies a transcript's replay semantics. A
proof-compatible user value merge uses exact callback replay. Constructor
`UnionId` and container-normalization merges retain callback operands for audit
and causality but use their dedicated equality/congruence or normalization
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
Alternative successful check witnesses or alternative equality paths are OR
choices made by the cold slicer.

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

A staged candidate is not a fact. Its key may already exist, a same-wave write
may supersede it, or the merge function may reject it. Stable IDs are allocated
only when merge commits an effective fresh or replacement row.

Captured mutation buffers carry an opaque `PendingCause` beside each candidate.
The cause may be a firing, source action, or local merge/rebuild draft. If
synchronous correlation is useful, the API may expose an opaque
`MutationTicket`; it must never expose a `StableRowId` before commit.

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
| Fresh key accepted | allocate fresh | commit caused by source/firing; store new event ID in row |
| Existing key, merge is no-op | retain existing | no new state event |
| Existing key, merge changes row | allocate fresh result | merge depends on old state and incoming cause |
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
using a wave number as a row version.

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
rule, as do auxiliary transcript/obligation IDs encoded as `Value`s.
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

At the input frontier for a user wave, the row-state column already names the
committed state visible to the match. The firing recorder stores those exact
event IDs and validates that their stable/table metadata agree. Duplicate
occurrences remain distinct by ordinal even if they name the same row state.

The static capture specification for a rule contains:

- a stable catalog ID, not just a possibly duplicated rule name;
- the table and source occurrence corresponding to each private ID;
- source-order free-variable slots and types;
- recipes for equality and primitive obligations;
- a complete-head action layout identifying every keyed write/read and its
  action ordinal;
- the original resolved rule needed for replay.

Selecting one firing replays its complete head, so capture records the prior
row-state hit or frontier-scoped miss observed by every head action that
consults a keyed table. This includes an existing row read by a merge that
ultimately returns no-op. Such an observation is attached to the firing even
when no output event points back to it; otherwise omitting that old row could
turn a captured no-op sibling action into an insertion during replay. Capture
retains invoked merge steps but does not promote them to row states or retain
proposals discarded before any callback/commit semantics. Action-local tickets
connect a later head operation to an earlier staged result when the language
permits that dataflow.

When table commit assigns a candidate to a transcript leaf, its mutation ticket
publishes the reverse `action_merge_leaf` row. Backward closure can therefore
start from either a committed result or a selected complete-head action and
recover the exact common-key group in both directions.

Rules that require a table without stable identity fail capture preflight
unless that occurrence has a dedicated sound witness mechanism.

## Auxiliary relational causal store

`CausalStore` is a separate core-relations `Database` populated with ordinary
`SortedWritesTable`s. It is owned by a `CausalSession` and is not part of the
semantic database.

This separation is intentional. It prevents causal rows from changing:

- semantic `TableId` allocation;
- user-visible table enumeration and tuple counts;
- `total_size_estimate` and parallelization heuristics;
- semantic change/saturation reporting;
- main-database dependency strata;
- clear/rebuild behavior;
- trace recursion.

Writers use fresh mutation-buffer handles and the same sharded pending queues as
ordinary tables. Rule workers and parallel merge shards can therefore emit
causal rows without a shared trace mutex. Each captured buffer carries a
session/wave generation token and registers as a live writer. Publication
refuses to proceed until all writers explicitly flush/close and the live count
reaches zero. A buffer dropped or flushed after its generation closes discards
its pending rows and permanently invalidates the session; an ordinary public
`Box<dyn MutationBuffer>` is never allowed to smuggle an old `PendingCause`
into a published wave.

Wave publication is ordered:

1. join rule/source workers and close their semantic proposal and causal
   writers;
2. merge/commit the semantic tables while merge/rebuild shards emit through
   their own wave-scoped causal writers;
3. join those shards and close every remaining causal writer;
4. merge all non-marker causal rows;
5. audit the candidate wave against committed predecessor frontiers;
6. stage and merge `wave_committed` as the final state change.

All ordinary causal readers filter out rows whose wave lacks that marker. Rows
from an aborted wave remain unreachable. If a failure occurs after semantic
rows containing new event IDs have committed, the causal session is invalidated
rather than allowing later capture to follow unpublished state.

Every causal table disables both stable-row identity and causal capture.

### Core relations

The exact column encodings should remain private, but the logical schema is:

```text
runs(run -> source_schedule_id)
branches(branch -> fork_frontier)
frontiers(frontier)
frontier_heads(frontier, ordinal -> wave)
waves(wave -> run, branch, kind, input_frontier)
wave_committed(wave -> output_frontier)
wave_depends_on(wave, ordinal -> predecessor_wave)

events(event -> wave, kind, static_origin)
event_depends_on(event, ordinal -> parent_event)

row_state(event -> table, stable_row_id)
row_state_value_N(event -> typed logical values...)       // cold/archive form
row_retired(event -> table, stable_row_id, prior_state)
wave_row_delta(wave, table, stable_row_id -> event_or_retired)

firing_P_B(event -> rule, premise_state[0..P], binding[0..B])
source_event(event -> source_catalog_id, source_row_ordinal)
action_merge_leaf(owner_event, action_ordinal, occurrence_ordinal
                  -> transcript, leaf_ordinal)
merge_transcript_K(transcript -> wave, table, key[0..K],
                   prior_state_or_absent)
merge_leaf_N(transcript, leaf_ordinal -> cause, origin_ordinal,
             occurrence_ordinal, values[0..N])
merge_step_N(event -> transcript, step_ordinal,
             ordered_left_ref, ordered_right_ref,
             changed, result_values[0..N])
merge_outcome(transcript -> root_ref, committed_state_or_noop)
commit_event(event -> table, prior_state_or_absent, accepted_ref)
read_hit_K(owner_event, ordinal -> table, key[0..K], row_state)
read_miss_K(owner_event, ordinal -> table, key[0..K], required_frontier)
equality_obligation(obligation -> sort, lhs, rhs, required_frontier)
rekey_R(event -> table, row, prior_state, obligation[0..R])

equality_event(event -> sort, lhs_term_ref, rhs_term_ref, reason)
congruence_C(event -> left_row_state, right_row_state,
                        child_obligation[0..C])

check_P_B(event -> check_catalog_id, premise_state[0..P], binding[0..B])
```

`N`, `K`, `P`, `B`, `R`, and `C` are prospective arities known from table/rule
registration. `ArityTableFamily` is a thin registry that creates one
`SortedWritesTable` per required physical schema. Families may be populated
lazily only during single-threaded registration/preflight, when mutable
`Database` access exists; every prospective schema is then precreated and the
registry frozen before the first wave. Workers never add tables. This packs hot
firing and archive rows without adding a bespoke variable-length allocation.
Fixed or genuinely unbounded lists use normalized
`(owner, ordinal, value)` tables.

Merge operand/root references are tagged references to the prior committed row,
a candidate leaf, or an earlier step in the same transcript. `left` and
`right` preserve the callback's `old`/`new` orientation. Step ordinals form a
topological linearization local to the transcript: every referenced step is
earlier, while independent subtree callbacks may be numbered in either order.
`changed` and `result_values` archive the observed callback result for replay
validation; for `changed = false`, the result signature is the retained `old`
operand rather than unused output scratch. They are evidence, never values that
replay may inject as facts.

Static table IDs and premise occurrence layouts do not need to be repeated in
every firing row; the rule catalog supplies them.

The `table` fields above encode a stable semantic `CatalogTableId`, not the
auxiliary database's physical `TableId`. Causal-table IDs never appear as
provenance payloads, which keeps the two database namespaces unambiguous and
allows replay-local remapping.

Before any row-state `EventId` ceases to be live, its complete logical row is
archived in `row_state_value_N`. This includes effective merge/refresh,
identity-preserving rekey, delete, clear, and collision/coalescence, and occurs
before compaction or `maybe_rehash` can discard the stale physical row. Live
row values can be obtained through a cold stable-ID index. Recording every
committed state is a simpler valid first implementation; a later measured
optimization may use archive-on-state-supersession, never merely
archive-on-identity-retirement.

### Event allocation and parallel publication

Workers reserve blocks of opaque event IDs from a session counter. A block is
only a uniqueness optimization; it is not a time interval.

Captured table buffers preserve candidate ticket/cause alignment. Every
candidate that participates in a merge group becomes a transcript leaf, and
every actual callback invocation becomes a `merge_step_N`, including a
`changed = false` step. This is necessary because a no-op action may later be
part of a selected firing's complete head.

Current `SortedWritesTable` ownership already serializes actual callbacks for a
key inside its hash shard, so capture can assign local ordinals without a lock.
`StagedOutputs` carries candidate batches and any precombined operand subtree;
when the owning shard resolves the live collision, it stitches that material
into the `(wave, table, key)` transcript, remaps temporary references,
and assigns topological local ordinals. The format also remains correct if a
future reducer builds independent same-key subtrees in parallel: ordered
operand references preserve the actual tree even though publication is a
linear list of callback invocations.

After resolving the transcript root against the live row, an effective
`commit_event` allocates final metadata and is the only event inserted into
`row_state` for that outcome. Merge-step event IDs never carry `StableRowId`s
and never appear in semantic rows. A no-op outcome has no new row state, but its
transcript remains available if closure reaches one of its candidate owners or
dedicated equality/normalization effects.

Only a common-key transcript and action-local dataflow impose within-wave
order. Unrelated keys, shards, and firings remain unordered. For the exact
user-value path, the initial proof-slicing gate rejects callbacks with
user-semantic database reads, nested user writes, or shared mutable state, so
the transcript remains key-local. This restriction does not reject the built-in
constructor `UnionId`/union-find or container-normalization paths: they use the
dedicated equality, congruence, and normalization events described below and
ordinary fresh proof rebuild. If the proof gate later admits other effects, the
current step can serve as their owner/cause, but a wider visibility-boundary
design is required before enabling them. Gaps in event IDs are valid.

Publication audit also checks that transcript keys match every leaf/result,
candidate tickets occur with the captured multiplicity, step ordinals are
unique, operand-step references point backward, the prior row belongs to the
input frontier, exactly one outcome names a valid root, and only a commit/rekey
event—not a step—appears in `row_state`.

## Wave semantics

### User rule wave

One bounded ruleset execution reads the semantic state at its input frontier.
Every match in that invocation resolves premise row states and equality support
against that same frontier. RHS effects are staged. Effective merge results
create the output frontier.

There is no `HistoryPosition` and no attempt to decide which peer firing
"happened first."

### Rebuild waves

Rebuild work is divided at the fixed-point boundaries already present in the
bridge:

1. container rebuild;
2. table value rebuild and merge;
3. dirty-row refresh;
4. repeat if semantic state changed.

Each causally feed-forward maintenance stratum is a maintenance wave. If the
output of one parallel rebuild stratum can be read by the next, the first
publishes its output frontier and the second names it as an input dependency.
Operations within a stratum remain unordered except for explicit same-key
reduction edges. This introduces only real visibility barriers, not an order
among individual rebuilds.

### Source and observation waves

Top-level action blocks and native input batches are source waves. Their
catalog entries retain parsed values or resolved actions; a filename alone is
not sufficient provenance.

A capture-aware check records its successful witnesses after the state it
observed. Its temporary query binds the same hidden stable-ID and state-event
variables as a rule. Multiple checks remain ordered as source observations,
while their support cones may share events.

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
equality event; an equality obligation may use an earlier path.

Path compression is not an independent semantic equality axiom. Its edge
metadata either depends on the equality path it abbreviates or is omitted from
the cold semantic equality graph and treated only as representation
maintenance.

### Equality used by a rule

The static rule capture specification identifies equality obligations among
term occurrences. For a captured firing, the exact premise states and typed
bindings determine the endpoints. The cold slicer finds a supporting path in
the equality-event graph whose events are available through committed-frontier
ancestry from the firing's input frontier. Numeric event IDs and numeric wave
comparison are not availability tests.

If several paths exist, the initial policy chooses the least additional-event
cost with deterministic tie breaking. This is an OR choice, not a claim that
the result is globally minimum.

### Canonicalizing a row

For each ID-typed cell changed by rebuild, record the old/new typed values as an
equality obligation at the rebuild wave's input frontier. The hot native
rebuilder generally does not have one distinguished union edge and should not
invent one. A pure rekey event depends on:

- the prior row-state event;
- the relevant equality obligations, resolved cold to available event paths;
- any container normalization event used by the rebuild.

It preserves `StableRowId` but replaces the row's hidden state-event column
with the rekey event.

### Congruence collision

Suppose two constructor/view rows become the same key after their children are
canonicalized but have different output e-classes. Both pre-collision row
values are archived before either row is absorbed. The congruence event depends
on:

- both pre-collision row-state events;
- the child equality obligations that made their keys equal;
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
normalization kind. Custom merges use the same ordered step transcript and
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
value together with its stable and row-state IDs and attaches a `read_hit_K`
dependency to the current firing.
A miss records `read_miss_K` at the exact input frontier; replay must revalidate
that absence before applying the selected action, and conservative over-firing
is disallowed if it could fill the key. A lookup that stages a default insert
links the miss and its mutation ticket. Until these hit/miss paths and their
proof-mode behavior exist, preflight rejects every such built-in read rather
than relying on public lookup APIs that project the hidden event column away.
Lookup/function expressions inside `MergeFn` remain initially rejected by the
merge purity and existing proof-support gates.

## Root selection and backward slicing

### Root capture

A successful check witness contains:

- the check catalog ID;
- its observation wave;
- exact row-state premise events;
- typed free-variable bindings;
- equality obligations derived from its static layout.

The capture query inserts every successful witness into an ordinary
deduplicating check-witness table keyed by its normalized typed binding and
stable-row references. Cold slicing chooses deterministically by causal cost
and then a semantic lexicographic tie break; raw event allocation order is
excluded, as are raw stable-ID values. The tie signature uses typed values,
static catalog/source ordinals, and normalized structural provenance; two
witnesses identical under that signature are observationally interchangeable.
If retaining every witness proves too expensive, any bounded policy must itself
be deterministic and exposed as explicit truncation, not an asynchronous
"first match" accident.

### Closure algorithm

The slicer maintains worklists for events, row states, candidate causes, and
equality obligations:

1. Seed with a successful check witness.
2. A row state adds its producing commit or rekey event.
3. A firing adds all recorded premise row states, equality obligations,
   action-side read obligations, and complete-head merge-leaf occurrences.
4. A source event selects the exact source action/input row and its merge-leaf
   occurrences.
5. A commit adds its prior row state, if any, and its accepted candidate or
   merge-transcript outcome.
6. A selected merge outcome or leaf promotes its containing transcript. The
   transcript adds its prior state and every leaf/step needed for the observed
   group outcome; steps add ordered operands plus any dedicated equality or
   normalization dependencies, and leaves add their firing/source action
   occurrences.
7. A rekey adds the prior row state and resolves its equality/container
   obligations at the required frontier.
8. An equality path adds each explicit union cause or congruence dependency.
9. A congruence adds its constructor row states and resolves its child
   obligations.
10. A read hit adds the observed row state; a read miss adds a frontier-scoped
   absence constraint to `SlicePlan`.
11. Repeat until no new events are selected.

A visited set makes the AND-only part linear in the selected graph. Equality
path and alternative-root choices use a cold cost search over ordinary causal
tables.

The result contains exact dynamic events plus a static declaration dependency
closure. It reports selected/total counts for sources, rules, firings, facts,
waves, equality events, and bytes.

### Slice selection guarantee

The policy chooses one producer for each current row state and one supported
equality/check alternative according to the cold cost heuristic. The result is
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
- selected firings grouped by original user waves;
- selected per-key merge transcripts, candidate occurrence mappings, and
  portable intermediate-result signatures;
- the required maintenance boundaries;
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

### Conservative rule-granular proof production

The simplest correct path is restricted to an explicitly certified
**extension-safe** fragment:

1. Create a semantically empty e-graph from the captured replay configuration.
2. Enable the existing full proof encoding.
3. Install the static declaration closure.
4. Replay selected source rows/actions in causal order.
5. For each selected user wave, run all selected source rules together for one
   bounded iteration.
6. Invoke the existing term/proof-encoding maintenance schedule between waves.
7. Execute the selected prove/check command.
8. Simplify and independently verify the resulting `ProofStore` as today.

Running the rules together is essential. Sequential one-rule runs would let a
rule consume a same-wave result that was not visible in the captured run.

Whole-rule replay can fire additional matches on the reduced database. A rule
is extension-safe only when, for every reachable replay state, adding such
matches to the captured candidate set cannot retire, replace, rekey, or
otherwise invalidate any selected action result, downstream selected premise,
or target witness. Its actions must be effect-monotone under an explicit
semantic preorder, and all later selected premises and checks must be monotone
under that same preorder.

This is stronger than calling an action or merge "idempotent." Associativity,
commutativity, and idempotence make a merge independent of reduction order for
a fixed candidate set; they do not prove that adding candidates preserves the
selected result. `old` and `new` provide neither property. Function writes are
therefore extension-safe only when all additional candidates have the same
semantic value or the table/merge supplies a separately validated
extension-closure contract. Delete, subsume, panic, opaque action-side reads,
and external side effects are excluded.

This semantic property is not inferred for arbitrary rules. Replay preflight
uses a fail-by-default classifier over resolved actions and every table or
primitive reachable from them. The first implementation has a sealed whitelist
of reviewed built-in `ReplayEffectContract`s (for example, set insertion and
other effects with a defined semantic preorder, extension closure,
determinism, causal-read behavior, and duplicate behavior). An unclassified
effect is unavailable to conservative whole-rule replay. A merge may instead
use selected-action plus exact local-transcript replay if it is deterministic
under captured operands/reads; arbitrary primitives, external functions, and
custom tables still need an explicit replay contract. A future extension
registration may supply the relevant trusted contract, but an annotation with
no implementation-specific review and conformance tests is insufficient. A
frozen corpus records every accepted and rejected rule shape for each replay
path so classifier drift is visible.

Within that certified fragment, over-firing only enlarges the replay and proof
without invalidating the target. The resulting independently checked proof is
valid, but the execution is not an exact replay of the reported dynamic
firings. Replay amplification and proof dependencies on replay-only firings
are measured and reported explicitly.

### Selected-action binding replay

Delete and subsume require selecting the captured semantic actions. An
extension-safe high-fanout rule may use this path as a performance optimization
when conservative replay amplifies too much; fanout alone is not a soundness
classification. Reuse the existing frontend scheduler rather than add a new
low-level grounded executor:

1. Capture source-order action-visible bindings and their occurrence
   multiplicity with each firing.
2. Convert selected bindings to portable replay terms during cold slicing.
3. After replaying their selected causal producers, resolve those terms
   read-only in the fresh proof-mode e-graph and obtain its local typed values.
4. A `CausalReplayScheduler` receives the existing `Matches` for a rule and
   chooses only action-visible binding occurrences selected for the current
   wave.
5. `step_rules_with_scheduler` applies all chosen matches together, preserving
   the wave's common input frontier and the complete original rule head.
6. Generated proof/rebuild maintenance is not filtered.

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
checked independently. It must still apply the action exactly as many times as
captured. That multiplicity matters for non-idempotent effects such as an
associative/commutative sum merge. If a body distinction can change any action,
the capture specification must include it in the selector. Exact dynamic-
premise replay is deferred unless premise-occurrence selectors are also carried
into the replay executor.

The existing scheduler needs a narrow replay extension rather than a fork:

- represent zero-action-variable matches with an explicit occurrence count or
  sentinel instead of dividing a zero-length tuple;
- project source-visible selector slots while retaining the complete
  proof-instrumented match tuple for action instantiation;
- add an internal occurrence ordinal to the scheduler's decided relation so
  ordinary set semantics do not collapse repeated action-visible tuples;
- choose body witnesses deterministically while preserving the captured action
  multiplicity; deduplication is permitted only for an effect certified
  duplicate-idempotent;
- retain each selected binding occurrence that appears early as a residual
  until its captured wave, then consume it exactly once;
- discard ordinary unselected residuals rather than allowing them to fire in a
  later replay wave.

After every selected user action wave, replay calls a dedicated
term/proof-encoding maintenance entrypoint equivalent to the instrumented
cleanup, path-compression, rebuild, and delete/subsume schedule. Calling the
backend through `step_rules_with_scheduler` does not append that frontend
maintenance automatically. Maintenance remains unfiltered.

Until selected-action and local-transcript replay are implemented, replay
preflight accepts only rules and merges classified as rule-granular extension-
safe. It does not silently fall back to the full original program.

### Exact local value-merge replay

For selected-action replay of a proof-compatible user value merge,
`SortedWritesTable` receives a cold `PerKeyMergeReplayPlan` alongside its
ordinary pending candidates. This is a controller for the existing merge path,
not a second table or grounded-rule executor:

1. Every replayed source/action occurrence stages its logical candidate with
   the captured transcript/leaf token. Multiplicity is exact.
2. At the merge barrier, the table verifies the replay-local prior row against
   the captured prior-state signature and verifies the exact candidate-leaf
   multiset. A missing, extra, or mis-keyed leaf fails replay.
3. The controller walks `merge_step_N` in local ordinal order. Operand
   references select the replay-local prior row, candidate value, or actual
   result of an earlier step. It invokes the corresponding fresh replay graph's
   proof-instrumented `MergeFn`, derived from the same catalog declaration,
   with the same ordered operands and a proof-mode `ExecutionState`.
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
collisions produced by a selected rebuild maintenance wave. User candidates map
by source/firing action occurrence; pure value-rebuild candidates map by
portable prior-row/rebuild-obligation signatures. Fresh proof-mode rebuild
still re-derives those candidates; the plan controls only their merge
invocations once they exist.

This must replay the recorded operand tree, not merely left-fold raw
candidates. For a non-associative merge, `old ⊗ (a ⊗ b)` is not interchangeable
with `(old ⊗ a) ⊗ b`. Different keys may still replay in parallel; no database-
wide merge sequence is introduced.

"Arbitrary" here means no associativity, commutativity, or idempotence
requirement for a user value merge. It includes `old`, `new`, and deterministic
non-associative or non-commutative merge expressions. The initial callback must
still be pure and key-separable: its user-semantic result may depend on its
ordered operands and immutable captured configuration, but not on shared
`PredictedVals`, counters, early-stop state, mutable extensions, database reads,
or nested user writes. Time, randomness, I/O, and opaque Rust closures are
likewise rejected. These are already outside today's proof-encoding gate; local
ordering removes algebraic restrictions, not the checker/language gate.

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
paths may retain local callback records for integrity diagnostics, but the
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

The expensive full proof encoding then runs only on the selected sources,
rules, and waves, plus any measured replay-only firings admitted by the
conservative path. The intended win is to do proof work on a smaller state, not
to make individual proof nodes cheaper. Capture and replay can outweigh that
saving on dense slices; only the end-to-end benchmarks below establish whether
the hypothesis holds.

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
- Each worker/shard uses fresh causal mutation-buffer handles.
- Pending row/cause metadata remains aligned through sharding and local
  same-key reduction.
- All tasks join before the wave's causal tables merge and before
  `wave_committed` is published.
- Causal readers only inspect committed predecessor waves.
- Numeric stable/event IDs may differ with thread count.

Tests and debug output compare normalized semantic records, never raw allocation
order. Capture records each actual per-key reduction tree as an ordered local
transcript, not a database-wide linearization. Exact value-merge replay drives
the existing merge callback from that transcript; specialized equality and
normalization merges follow their dedicated witnesses. Algebraically
order-sensitive value results may legitimately differ across executions if the
base engine exposes a different candidate tree; each captured proof must
reproduce and justify the observed run, while capture instrumentation must not
itself change that run's tree.

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
replaceable pending state and remains monotone. A late old-generation buffer
poisons the causal session. Direct `Table::clear` is unsupported while an exact
trace is active because it lacks the session context.

### Clone, push, and pop

`Database::try_clone_at_frontier` first requires merged pending queues, no live
captured buffers, and a committed current wave. It then preserves the hidden
stable and row-state IDs, shares the causal session and allocators, and forks a
branch frontier from the current committed frontier. The two databases may
diverge. The ordinary infallible `Clone` path is unavailable/fails closed while
causal capture is active; plain and stable-ID-only clones retain their normal
behavior. An event from one sibling branch is unavailable to the other unless
an explicit future API joins their frontiers. A detached clone into a new
causal session is unsupported until it can copy and translate the reachable
causal closure; minting snapshot source events would incorrectly turn derived
state into axioms.

Initially, the shared `CausalSession` grants an exclusive wave lease to one
branch at a time. A wave still uses the ordinary parallel rule and table paths,
but sibling branches cannot open or publish waves concurrently; a competing
branch receives a typed busy error before mutation. This keeps auxiliary-table
publication and the shared marker protocol unambiguous without imposing a
worker-level trace lock. Concurrent sibling-wave publication is a future
extension requiring branch-isolated staging and a tested atomic publication
protocol.

Push/pop is strictly unsupported in the initial implementation and is rejected
at preflight. Frontier chronology alone is insufficient: the current proof
checker treats its resolved global-action context non-temporally, so discarded-
branch globals could incorrectly authorize a proof after `pop`. Future support
requires both same-session branch frontiers (save/restore semantic state and
frontier without rewinding allocators) and a branch-filtered checker context
that excludes discarded globals.

### Native input

Every selected input row must be replayable without rereading mutable external
state. Capture retains parsed literals or a content-addressed immutable row
snapshot. File paths alone are diagnostic metadata.

### Custom tables

`TableSpec` defaults to `RowMetadataLayout::None`. A custom table opts in only
if it implements the full write-arity, stable identity, rebuild, clear, clone,
and causal-mutation contract. `DisplacedTable`, causal tables, and ephemeral
helper tables remain opted out.

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

CausalSession::finish_root(CheckId) -> Result<SlicePlan, SliceError>
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
3. **Frontier consistency.** Every firing premise resolves to the row-state
   event visible at the firing wave's input frontier.
4. **Event soundness.** Every row-state commit, merge step, rekey, equality,
   and congruence event names its exact effective causes; merge steps never
   masquerade as committed row states.
5. **Acyclic causality.** Cross-wave edges point to predecessor frontiers;
   within-wave edges follow action-local or same-key dataflow. Event-ID order is
   irrelevant.
6. **Root completeness.** A successful captured check has at least one complete
   witness and all equality obligations needed to justify it.
7. **Closure sufficiency.** Following all required event operands reaches the
   source facts/rules needed to recreate the selected root.
8. **Replay fidelity.** Selected source events and action-visible bindings run
   in the same wave grouping with complete rule heads and existing maintenance
   semantics. A valid alternative body witness may supply a selected action.
9. **Merge fidelity.** Each selected exact value-merge key has the prior state,
   candidate occurrences, ordered callback operands/results, and final outcome
   reproduced by the catalog-equivalent replay merge after semantic projection.
   Specialized union/congruence and normalization merges reproduce their typed
   causal obligations through ordinary proof-mode maintenance, never by
   importing a captured representative or result.
10. **Independent proof validity.** The existing proof checker accepts the
   replay-produced certificate against the stored resolved observation prefix.

## Error policy

Fail closed with structured diagnostics for:

- activation after semantic state already exists;
- unsupported backend or table;
- push/pop in sliced mode;
- stable/event/auxiliary ID exhaustion;
- a late mutation buffer, incomplete publication, or invalidated session;
- missing stable premise identity;
- missing or wrong-session row state;
- a sibling-branch event outside the consumer frontier;
- an event dependency on an uncommitted/future frontier;
- a causal cycle;
- an opaque source value that cannot become a replay term;
- an external function without the required causal-read/validator contract;
- a replayed frontier that violates a captured read-miss obligation;
- a rule outside the extension-safe fragment before selected-action binding
  replay exists;
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
  merge outcomes, generation-checked writers, and compaction;
- `core-relations/src/table/rebuild.rs`: explicit preserve/rekey versus replace
  outcomes;
- `core-relations/src/query.rs` and `free_join/plan.rs`: private stable-ID atom
  bindings, with the existing RHS-used materialization path doing most work;
- `core-relations/src/action/mod.rs` and `free_join/execute.rs`: pending causal
  context, causal hit/miss lookup, and firing recorder integration, without a
  second witness representation;
- one focused `core-relations/src/causal.rs` module: session ownership,
  auxiliary table schemas, arity-family registry, wave writers, and integrity
  audit;
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
- Add checked table-owned allocators and generation-checked buffer lifetimes.
- Keep physical IDs out of public function rows and merge callbacks.

### Phase 2: rebuild and parallel identity

- Add an explicit identity-preserving rebuild/rekey path rather than unrelated
  remove/insert operations.
- Archive every superseded state and append rekeys through ordinary
  version/index/subset update paths.
- Resolve live collisions before final physical append in identified/traced
  parallel `StagedOutputs`.
- Preserve ordered merge operands/results in serial buffers and stitch/remap
  parallel `StagedOutputs` mini-transcripts at the owning key shard.
- Implement atomic block allocators and threshold-crossing concurrent tests.

### Phase 3: relational causal store

- Add `CausalSession`, `CausalStore`, the fixed tables, and preflight-frozen
  arity families.
- Add branch frontiers, ordered publication, session/branch checks,
  referential-integrity audit, and graph cycle detection.
- Record source, commit, per-key merge transcript, retirement, and current-row-
  state transitions.

### Phase 4: premise and check capture

- Add hidden-ID atom binding to query construction.
- Generate `RuleCaptureSpec`s and record exact firing premises/bindings through
  direct and decomposed joins.
- Capture built-in action-side read hits/misses or reject them at preflight.
- Record successful check witnesses.
- Verify capture projection against capture-off semantics under deterministic
  schedules, and verify each order-sensitive captured run against its own
  observed result without assuming cross-thread merge invariance.

### Phase 5: equality and maintenance events

- Emit explicit union, equality, rekey, congruence, and container dependencies.
- Add cold equality-path selection restricted to wave frontiers.
- Ensure maintenance events slice back to semantic causes and are not replayed
  as new axioms.

### Phase 6: closure and conservative replay

- Build `SlicePlan`, static declaration closure, and slice-local replay terms.
- Add the fail-by-default `ReplayEffectContract` classifier and semantically
  empty deterministic replay-factory contract.
- Replay rule-granular extension-safe slices grouped by waves on fresh ordinary
  and proof e-graphs.
- Require independent proof checking and record amplification metrics.

### Phase 7: selected-action and local merge replay

- Map captured source bindings through proof instrumentation.
- Add `CausalReplayScheduler` to choose selected action-visible bindings per
  wave.
- Add `PerKeyMergeReplayPlan` to verify leaves and drive the existing merge
  callback through captured ordered operand steps.
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
  or wraparound, publishes no partial row/event/transcript, and never reuses an
  ID.
- Capture-aware clone succeeds only at a quiescent barrier, shares the session
  and allocators, and forks frontier ancestry; a dangling wrong-session or
  sibling-branch event is rejected.
- The exclusive branch-wave lease permits parallel work within one wave but
  rejects a concurrent sibling wave before mutation; sequential sibling
  publications remain causally isolated.
- Clear with an outstanding old-generation buffer cannot repopulate the table
  and invalidates the session if that buffer later attempts to flush.

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
  1/2/4/32 threads. Each replay must reproduce its captured operand tree,
  multiplicity, intermediate signatures, and final result; different captured
  trees are not required to agree semantically.
- Compare the optional associative/commutative fast path against exact
  transcript replay for the same captured candidate multiset.
- Assert ID uniqueness and normalized transcript integrity, not equality of raw
  IDs or local ordinals across executions.
- Verify no event is visible before its wave is committed.
- Inject failure after semantic commit but before causal publication; assert
  that the session is invalidated and no later extraction or capture can treat
  the wave as complete, while orphan causal rows remain unreachable to normal
  readers.

### Causal and wave fixtures

- one source fact and one rule;
- a source action block with local bindings and multiple same-key writes;
- irrelevant source and rule branches;
- same-wave enablement trap;
- genuine multi-wave recursion;
- repeated variables and equality guards;
- decomposed join with projected existential variables;
- multiple check roots with shared and disjoint cones;
- effective versus no-op merge;
- a selected firing whose sibling head write was a no-op because of a prior
  row, proving complete-head replay retains that read dependency;
- delete/recreate and subsume;
- rekey/congruence from child equality;
- chained rebuild strata where the second consumes equality from the first
  through a published predecessor maintenance wave;
- two alternative equality paths;
- predecessor equality accepted while same-wave/future equality is excluded;
- path compression cannot be the sole semantic equality cause;
- input-backed relations and supported containers;
- built-in action-side lookup hit, miss, and miss-then-default-insert, including
  frontier-scoped absence validation;
- a high-fanout rule that measures replay amplification;
- unsupported-table preflight before semantic mutation, leaving the database
  unchanged;
- push/pop preflight rejection before semantic mutation, including a fixture
  whose discarded branch would otherwise add a checker-global Fiat;
- a frozen accepted/rejected corpus for the fail-by-default
  `ReplayEffectContract` classifier;
- a sliced hot pass that proves the eager proof encoding was neither installed
  nor executed.
- invalid proof-strategy/flag combinations, an unsupported backend, and sliced
  activation after preexisting semantic state all fail during eager preflight
  without mutating the database.

Every successful fixture runs:

1. original ordinary execution;
2. current full proof testing;
3. ordinary execution with causal capture;
4. slice integrity audit;
5. slice replay on a fresh ordinary graph;
6. slice replay under proof testing;
7. proposition comparison and independent proof checking.

Negative fixtures assert a typed error and no full-program fallback.
Today that includes merge action blocks, function-lookup merges, tuple-output
forms, and opaque Rust closures wherever the existing proof gate rejects them;
local transcript ordering does not widen that gate. Declared merge reads and
nested user writes remain future negative fixtures until both proof checking
and a wider visibility-boundary design support them.

### Replay and checker fixtures

- A zero-action-variable rule retains an explicit match count or sentinel.
- Duplicate existential/body witnesses for one action-visible tuple preserve
  the exact captured occurrence count, including a non-idempotent
  associative/commutative merge; only duplicate-idempotent effects may dedup.
- Repeated equal bindings in distinct waves remain distinct occurrences. A
  selected occurrence discovered early remains residual until its captured
  wave and is consumed once; unselected residuals never leak into later waves.
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
- Deleting/reordering a leaf, swapping operand orientation, changing
  multiplicity/prior state, or corrupting an intermediate value-merge result
  produces a typed replay failure rather than a captured-value insert.
- A missing equality-sort selector anchor fails without constructing a term,
  top-level Fiat, or semantic row.
- Explicit proof/term maintenance between waves makes the next selected
  binding visible; omitting it makes the fixture fail.
- The independent checker receives the stored resolved observation prefix,
  excludes scheduler helpers and later source commands, and validates the exact
  stored wrapper once for both single- and multi-fact final checks. A negative
  fixture places a global action after the check and proves it cannot authorize
  a Fiat for the earlier observation.
- Conservative-classifier positives demonstrate extension closure. Negatives
  include `old`/`new` and an associative, commutative, idempotent merge that is
  order-independent but not extension-safe for the selected result; the same
  deterministic merges are positive cases for selected-action/local-
  transcript replay.
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
  time spent in locally serialized transcript replay;
- total versus selected sources/rules/firings/facts/waves;
- replayed matches versus selected firings;
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
trace bytes per effective event, and conservative replay amplification. Those
are required gates, not forever-TBD diagnostics, but choosing numerical limits
before any measurement would be arbitrary. Per-workload regressions are always
reported; an amplification or trace diagnosis explains a failure but does not
waive it without an explicit review decision.

PR #42's historical 0.387-0.393 sliced/full wall-time ratio on five workloads
is context, not a merge gate. Its capture-disabled overhead was not measured
against the clean base, so this design requires that missing comparison.

Code structure is also an explicit comparison. Record changed files and lines,
core hot-path changes, new unsafe blocks, and whether each causal structure is
an ordinary table or a one-off data structure.

## Alternatives considered

### Copy or trim PR #42

Rejected. The branch is intentionally clean-room and seeks a different storage
and ordering model. The PR remains a useful corpus, performance, and failure-
mode reference.

### A global arena plus `HistoryPosition`

Rejected. It duplicates table storage and imposes an order stronger than rule
semantics require. Wave frontiers plus explicit rebuild dependencies and exact
key-local merge transcripts are sufficient; the transcript is the narrow place
where actual callback order can affect semantics.

### Eager proof terms with compact evidence payloads

This would add a third term-encoding payload and lazily materialize proofs from
evidence IDs. It is plausible, but it does not satisfy the central goal of
capturing an ordinary semantic run via stable rows, and it duplicates part of
the proof construction trust boundary. Reduced replay lets the existing proof
encoder and checker remain the authority.

### Rerun selected rule declarations without firing capture

Rejected as the complete solution. It can cross-product unrelated bindings and
is unsafe outside the certified extension-safe fragment. It is retained only
as the first replay stage for that fragment; selected-action replay uses the
existing scheduler.

### Synthetic selector relations in proof rules

Deferred in favor of scheduler filtering. Selector atoms are easy to store but
change the premise list seen by proof construction/checking unless a separate
proof-erasure rule is trusted.

### Put causal tables in the semantic database

Possible, but not preferred. It perturbs table IDs, change reporting, total-size
heuristics, merge dependencies, and clear/rebuild behavior. An auxiliary
`Database` retains the same table abstractions without affecting semantics.

## Decisions to validate before implementation

The design recommends, but implementation should not begin until we agree on,
these points:

1. `StableRowId` names a logical row lineage; a pure rekey preserves it while a
   separate row-state `EventId` records the new version.
2. Causal relations live in an auxiliary `Database` of
   `SortedWritesTable`s, not the main semantic `Database`.
3. Parallel capture is required; IDs are nondeterministic and have no ordering
   meaning.
4. The initial replay milestone accepts only rule-granular extension-safe
   programs; the existing scheduler is the action-exact path for supported
   delete, subsume, and high-amplification cases. Exact dynamic-premise replay
   remains deferred, captured action multiplicity is preserved, and exact
   key-local transcripts handle algebraically arbitrary user value merges.
5. Proof production always occurs through a fresh full-proof replay and the
   existing independent checker, rather than direct causal-to-proof
   materialization.
6. Initial backend/language support is a strict subset of the intersection of
   the reference backend and existing proof-encoding gate: every premise table
   needs stable identity or a specialized witness, action-side reads need an
   explicit causal contract, and replay needs an extension-safe or
   selected-action path. User value merges must be proof-compatible,
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
   catalog-equivalent proof-instrumented merge on its exact ordered operand tree
   and validates every semantic result; associativity/commutativity are optional
   fast-path properties, not support requirements. Constructor `UnionId` and
   normalization merges instead use their dedicated causal witnesses and
   ordinary fresh proof maintenance.
9. Capture-aware clones share one causal session and fork the frontier DAG;
   detached causal clones and push/pop are unsupported. Future push/pop support
   additionally requires a branch-filtered proof-checker context.
10. Conservative replay contracts are fail-by-default reviewed built-ins in
    the first implementation. Unknown effects and built-in action-side reads
    without hit/miss capture are rejected at preflight.

These decisions are the boundary between this design and PR #42's approach.
