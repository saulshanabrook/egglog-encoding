# Container provenance in causal-sliced proof replay

Status: current-architecture handoff, not an accepted implementation RFC

Date: 2026-07-21

Worktree: `/Users/saul/p/wt/egglog-encoding/causal-slice-arena-v0`

Branch checkpoint before this handoff: `cb203b5aacc89cc5c1459f332eaa8e89bfa78812`

Verified PR #23 head and merge base: `4940be37429e7adf16cc43283b38508e692cf045`

## Audience and purpose

This document is for an agent reviewing the causal-slicing architecture against
the current codebase, especially the boundary around mutable container values.
It explains:

- the implemented one-run trace, slice, and replay pipeline;
- how replay witnesses and causal dependencies currently work;
- how native containers are interned and rebuilt;
- what fresh container replay already supports;
- why a stable outer `Value` is not a historical container witness;
- the current conservative rejection and its false-positive scope;
- why Hardboiled is not currently stopped at the container boundary; and
- the smallest evidence that a sound, general container extension still needs.

This is an explanation and investigation brief. It does not authorize changing
the proof checker, adding a second body query, reconstructing history from final
state, or adding a `VecExpr`-specific production path.

## Executive summary

The causal pipeline currently performs one ordinary native execution with trace
capture, builds append-only causal/witness arenas, slices backward from positive
checks, and emits guarded `run-rule-batch` replay. The emitted replay is then run
through the existing strict proof mode and checker.

Fresh container values are not categorically unsupported. A captured `vec-of`
application is replayable through the same typed registered-primitive capability
used by scalar primitives when the exact specialization is:

- `Pure`;
- explicitly marked replay-safe;
- equipped with a proof validator; and
- supplied only replayable operands.

The unsupported case is historical identity across native rebuild. The native
container registry can change a container's semantic contents while retaining
the same outer runtime `Value`. The current trace reports only that stable outer
ID as dirty. It does not report an immutable before/after version, the old and
new contents, the element remaps, or the equality causes of those remaps.

The causal slicer therefore rejects any witnessed container whose outer ID is
reported dirty. This is sound but over-conservative: rejection happens during
elaboration, before backward reachability, so an irrelevant dirty witnessed
container can reject an otherwise valid slice.

Hardboiled has moved past its original fresh-`VecExpr` problem. At the current
working checkpoint it fails on a retained equality of sort `Type` whose raw
successful-union path contains an untyped edge. That is an equality-provenance
boundary, not evidence that its retained proof path needs historical container
versions.

## 1. End-to-end architecture

The implemented path is:

```text
parsed/desugared/typechecked egglog source
                  |
                  v
one ordinary native execution
  - source-command traces
  - schedule rule-match/action traces
  - positive-check match traces
                  |
                  v
causal elaboration
  - ReplayEvent arena
  - DepNode arena
  - WitnessNode arena
  - raw + typed equality forest
  - current row/function sidecars
                  |
                  v
one backward slice from all positive observations
                  |
                  v
schedule-free source emission
  - declarations and retained rules
  - sliced initialization
  - guarded packed run-rule-batch commands
  - original positive checks
                  |
                  v
ordinary replay and unchanged strict proof replay/check
```

Primary entry points are in `egglog/src/causal_slice.rs`:

- `causal_slice_program*` generates and validates retained replay source;
- `causal_slice_proof_replay_program*` projects it for proof execution;
- `run_one_traced_command` executes each source command once with native tracing;
- `elaborate_events` turns trace receipts into events, dependencies, witnesses,
  row producers, and equality labels;
- `observation_roots` selects one actual satisfying match for each positive
  check; and
- `backward_slice` resolves event, conjunction, prefix, and equality dependencies.

The source program is parsed, desugared, typechecked, and registered through the
existing frontend. The causal path models typed source occurrences against the
actual registered rule/action stream rather than reparsing an independent
language.

## 2. Native trace contract

`RuleExecutionTrace` is defined in
`egglog/core-relations/src/free_join/mod.rs`. It currently carries:

| Trace field | Meaning for slicing |
|---|---|
| `globals` | exact source-global values read from the batch pre-state |
| `matches` | native rule match identity and captured named bindings |
| `applications` | table/constructor/relation applications with match origin and instruction lane |
| `primitives` | registered primitive applications with match origin, arguments, result, and instruction |
| `unions` | commit-ordered successful/redundant union receipts and optional rule origin |
| `mutations` | mutable table commit receipts and their origin/cause |
| `rebuilt_containers` | stable outer container IDs whose semantics changed in place |

The trace is captured from the execution already applying the rule. It does not
query each rule body a second time. Rule matches are associated with action lanes
through `RuleMatchId`; mutations and unions retain origins when the native path
has them.

The container field is deliberately documented as insufficient historical
evidence. It is a `Vec<Value>`, not a version or replay witness.

## 3. Causal state and replay witnesses

### 3.1 Dependency arena

`DepNode` in `egglog/src/causal_slice.rs` is append-only:

```rust
enum DepNode {
    Empty,
    Event(EventId),
    And(DepId, DepId),
    Eq { left: TypedEndpoint, right: TypedEndpoint },
    Prefix(EventId),
}
```

An event dependency explains that a source command or effective firing is
needed. `And` composes complete support. `Eq` is resolved lazily through the
successful-union forest during backward slicing. `Prefix` is the reported,
conservative fallback for a boundary whose exact cause is unavailable.

### 3.2 Replay events

`ReplayEvent` represents either a retained source fact or a grounded rule
firing. An effective firing records:

- stable registered rule identity;
- original wave and ordinal;
- complete replay-variable witnesses;
- all prerequisites needed by its body and complete head; and
- every effective output row.

Matched firings whose entire head is a no-op remain diagnostic counts but are
not promoted unless a conservative wave prefix requires them.

### 3.3 Witness arena

`WitnessArena` stores immutable source syntax separately from runtime endpoints.
Its important indexes are:

- syntax node to witness ID;
- typed endpoint to preferred witness;
- typed endpoint to every witness instance;
- `(sort, function)` to application witnesses; and
- per-wave snapshots that limit which witnesses existed in the queried pre-state.

A `WitnessNode::App` names a typed source-level application and child witnesses.
The associated `original_value` is internal match-time identity. Emission walks
the syntax DAG; it never prints the runtime `Value`.

`WaveAppIndex` indexes canonical application signatures by sort, function,
children, and output. It avoids broad linear inverse searches while still
requiring an earlier witnessed application and equality support.

Positive-check constructor reconstruction now has an `Explained` mode: a check
marker establishes the exact matched row, but an alias is accepted only when a
prior same-function witness and complete typed child/output equality paths
establish availability. The check itself is never assigned `DepNode::Empty` as
if it created the row.

## 4. Equality architecture

`EqualityForest` has two related but distinct layers:

1. `commit_parents`/`canonical_parents` record every successful raw native
   union in commit order, including edges whose sort or producer is unknown.
2. `edge_causes` labels only edges for which the causal layer has one typed
   dependency.

Raw connectivity is useful for indexed candidate lookup. It is not sufficient
for a retained proof. `EqualityForest::explain` succeeds only if every edge on
the unique commit-forest path has the requested sort and a causal label.
`backward_slice` rejects a retained `DepNode::Eq` whose path crosses an untyped
or opaque edge.

This split prevents final-state union-find connectivity from being mistaken for
provenance.

## 5. Native container architecture

### 5.1 Interning and identity

`ContainerValues` and `ContainerEnv<C>` live in
`egglog/core-relations/src/containers/mod.rs`.

For each Rust `ContainerValue` type, `ContainerEnv<C>` maintains:

- `to_id: C -> Value`;
- `to_container: Value -> container-entry location`; and
- `val_index: contained Value -> outer container IDs`.

`ContainerValue` exposes:

```rust
fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool;
fn iter(&self) -> impl Iterator<Item = Value> + '_;
```

The trait does not expose an immutable version identifier, a generic serialized
before/after snapshot, positions/keys for every container shape, or causal
dependencies.

### 5.2 Rebuild cases

`ContainerRebuildSummary` distinguishes two facts:

- `changed`: some entry changed, either in contents or outer canonical ID;
- `dirty_ids`: semantics changed while the stored outer ID stayed stable.

The implementation has materially different cases:

| Rebuild outcome | Native behavior | Current causal consequence |
|---|---|---|
| contents and outer ID unchanged | entry stays in place | existing witness remains valid |
| outer ID changes | ordinary table rebuild rewrites parent rows to the new ID | requires ordinary row/equality provenance; not represented by `dirty_ids` |
| contents change, outer ID stays stable | entry is removed/reinserted under the same ID and ID is marked dirty | historical witness becomes ambiguous; causal v0 rejects |
| nested container changes in place | parent containers are found through `val_index` and may also become dirty | one dirty outer ID may summarize transitive nested changes |
| rebuilt containers collide | the container merge function selects/merges IDs during reinsertion | causal cause is not described by the dirty-ID list |

The stable-ID case is explicitly tested by
`nonincremental_dirty_ids_only_include_stable_ids` in
`egglog/core-relations/src/containers/tests.rs`.

### 5.3 Rebuild and table refresh order

The native bridge rebuild loop is in `egglog/egglog-bridge/src/lib.rs`:

1. rebuild container contents;
2. collect `dirty_ids` into `last_rebuilt_containers`;
3. rebuild ordinary tables;
4. retimestamp parent rows containing dirty IDs; and
5. repeat until container rebuild, table rebuild, and refresh all stabilize.

Container rebuild runs before table rebuild because canonicalizing container
elements can be necessary for table-key/value merging. Parent rows containing a
stable dirty ID need explicit refresh because their physical value did not
change, so ordinary table rebuild alone would not create a new seminaive delta.

After the native run, the bridge copies only `last_rebuilt_containers` into
`RuleExecutionTrace::rebuilt_containers`.

## 6. What container replay already supports

Container-valued results are admitted by registered capability, not by sort
name. `PrimitiveEffect` and the replay-safe flag are part of the registered
specialization in `egglog/src/typechecking.rs` and `egglog/src/core.rs`.

`vec-empty` and `vec-of` are registered with
`add_replayable_primitive_with_validator!` in `egglog/src/sort/vec.rs`. Their
validators build the same canonical proof term syntax used by strict replay.

The implemented narrow success case is:

1. a rule applies the exact registered `vec-of` specialization;
2. every element already has replayable syntax at that wave;
3. the native primitive receipt supplies the exact result endpoint;
4. the witness arena records `(vec-of child...)` with its operand availability;
5. no traced rebuild subsequently changes that witnessed outer ID before a
   retained use; and
6. replay evaluates the ordinary registered primitive and the unchanged proof
   validator checks it.

This path has ordinary and strict replay canaries, including a produced
`VecExpr` consumed by a later retained rule. It is generic over exact registered
specializations; it is not a production allowlist for `VecExpr` or `vec-of`.

Stateful or opaque container primitives remain unsupported. Several vector
operations are still registered with ordinary `add_primitive!`, not the stronger
replay-safe + validator capability.

## 7. Current fail-closed boundary

`reject_rebuilt_container_witnesses` in `egglog/src/causal_slice.rs` runs after
each traced wave is elaborated. It intersects:

- the wave's `rebuilt_containers` outer IDs; and
- every currently recorded witness endpoint whose sort is a container sort.

If any intersection exists, it returns:

```text
container witness of sort `<sort>` whose semantic contents changed during
rebuild; replay requires a versioned container dependency
```

This is sound because the slicer refuses to reuse current registry contents as
historical evidence. It is over-conservative because it runs before final
backward reachability and has no per-version dependency node to poison. Thus an
irrelevant dirty witnessed branch can reject a slice whose retained observation
does not depend on it.

The focused canary is
`rebuilt_container_witness_fails_closed_without_a_content_version` in
`egglog/tests/causal_slice.rs`. It creates a vector containing an equality-sort
element, unions that element with another value, and verifies that ordinary
execution succeeds while causal generation rejects the dirty same-ID witness.

## 8. Why common shortcuts are unsound

### Use the final container registry

The final registry answers what the stable ID means after all rebuilds. It does
not answer what it meant when an earlier firing matched. Reconstructing every
binding from final contents can silently replay a different grounding.

### Serialize the outer `Value`

The ID is process-local runtime identity and, in the dirty case, names multiple
semantic versions over time. It is neither source syntax nor a content version.

### Extract a term for every match

Extraction is a separate search over current state, not match-time causal
evidence. It can select syntax that was unavailable at the original firing and
would add prohibitive work to the one-run tracing model.

### Treat `dirty_id` as the causal dependency

The ID says that something changed. It does not identify the old version, new
version, which children changed, why they were equal, whether a nested container
caused the change, or which replay event must be retained.

### Assume proof-mode container rebuild is the native tracer

`egglog/src/proofs/proof_container_rebuild.rs` contains a separate term/proof
encoding that recursively rebuilds encoded containers and constructs congruence
proofs. It is used during the second, full-proof execution. It does not provide
match-time causal receipts to the first ordinary native execution, and changing
it would not repair the missing native history.

## 9. Current Hardboiled result

The Hardboiled fixture originally stopped at a captured `VecExpr`. The following
frontiers have since been crossed:

- fresh `vec-of` witness construction;
- rule-head ordering around multiple primitives and constructors;
- nested body primitives;
- compiler-generated rewrite-root aliases; and
- positive-check `Call` syntax reconstructed through typed congruence.

The current release command is:

```bash
target/release/egglog --mode no-messages -j 1 \
  --causal-slice --proof-testing \
  egglog/tests/hardboiled_conv1d_32.egg
```

It now rejects a retained equality of sort `Type` because the raw successful
union path has an untyped or opaque edge. This result does not show a dirty
container on the retained path. The next evidence-first investigation should
identify that exact raw edge and classify its origin before adding any container
version machinery.

## 10. Adjacent provenance boundaries

Container versioning is not the only rebuild problem.

### 10.1 Relation row rekey

The relation producer sidecar is keyed by the logical `RowKey` recorded at
insertion. If rebuild canonicalizes a relation argument, the final check can see
the canonicalized row while `producers` retains only the old key.

A minimized native-success/causal-fail example is:

```lisp
(datatype Expr (A i64) (B i64) (Wrap Expr))
(relation Seed ())
(relation Result (Expr))
(ruleset derive)
(rule ((Seed))
      ((union (A 1) (B 1)))
      :ruleset derive
      :name "unify")
(Wrap (B 1))
(Result (Wrap (A 1)))
(Seed)
(run-schedule (run derive))
(check (Result (Wrap (B 1))))
```

The causal path currently fails closed because the canonical `Result` row has no
producer entry. The missing transition is conceptually:

```text
canonical row support = old row support AND Eq(old cell, canonical cell)
```

This should not be mislabeled as container history.

### 10.2 Untyped equality edge

The current Hardboiled boundary is raw equality connectivity without a complete
typed edge cause. The missing producer could be a rule union whose typed model
was deferred, an unoriginated congruence/rebuild union, or another opaque commit
path. That classification is still open.

The highest-confidence code-based hypothesis is a constructor-key collision:

- every constructor table uses `MergeFn::UnionId` in `egglog/src/lib.rs`;
- `ResolvedMergeFn::UnionId` stages `[old_output, incoming_output, timestamp]`
  into the shared union-find with ordinary `stage_insert` in
  `egglog/egglog-bridge/src/lib.rs`;
- the union-find records `origin: None` when that mutation buffer has no origin;
  and
- `type_unoriginated_equality` can label the edge only by intersecting the
  endpoint sorts already present in the witness arena.

If an endpoint lacks a typed witness at that commit, the raw forest advances but
the edge receives no causal label. This mechanism matches the observed later
failure, but the exact Hardboiled edge has not yet been instrumented, so treat it
as a hypothesis rather than a confirmed root cause.

The smallest general hook for this class is not a container receipt. It is a
union cause for table-merge unions containing at least the constructor table (or
stable typed output-sort identity), the incoming lane origin, and the colliding
old/incoming rows. Exact support would combine both row dependencies and any
child equalities. A typed table identity with a reported prefix dependency could
be a conservative first step, but endpoint-sort guessing is insufficient.

### 10.3 Container refresh and parent rows

Stable-ID dirty containers cause parent rows to be retimestamped without changing
their stored cell. A complete container design must therefore coordinate the
container version transition with row refresh provenance. Solving only witness
printing would still omit why a later row match became available.

## 11. Smallest sound target extension

The target is an immutable version history internal to tracing and slicing, not
a new user-visible runtime ID.

Conceptually the causal layer needs:

```rust
type ContainerVersionId = u32;

struct ContainerVersion {
    sort: String,
    outer: Value,              // internal identity only
    predecessor: Option<ContainerVersionId>,
    syntax: WitnessId,         // source syntax valid for this version
    availability: DepId,
}

current_container_version[(sort, outer)] -> ContainerVersionId
```

A captured binding snapshots the current `ContainerVersionId`. A rebuild appends
a new immutable version; it never mutates the earlier witness. The new version's
availability must include:

- the prior version's availability;
- every exact equality that changed a contained equality-sort value;
- every nested container-version transition that changed a child;
- any container collision/merge read needed to select the result; and
- the row-refresh or commit dependency that makes later parent matches visible.

Only versions reachable from the final slice are printed. Runtime IDs remain
internal.

### 11.1 Missing native receipt

`ContainerRebuildSummary::dirty_ids()` is not enough to construct that version.
The smallest useful native receipt must let the causal layer distinguish, for
each changed entry:

- container runtime type or stable sort mapping;
- old outer ID and committed outer ID;
- whether semantic contents changed;
- the exact before/after child identities or an equivalent immutable remap
  description;
- whether a nested container transition caused the change;
- collision/merge outcome when reinsertion finds an existing container; and
- ordering relative to union, table rebuild, and parent-row refresh commits.

The current `ContainerValue::iter()` is insufficient as a fully generic
serialization contract: it exposes contained values but not necessarily keys,
positions, multiplicity normalization, or the source syntax of every container
shape. A general design likely needs either:

1. a structured type-erased rebuild receipt emitted while the old and new
   container values are both available; or
2. a sort-level immutable witness/version hook paired with the native receipt.

That choice is an open architecture question. Do not infer the answer by scanning
the final registry.

### 11.2 Integration sequence

A narrow implementation should proceed in this order:

1. Extend the core rebuild result with one structured receipt for a proven
   stable-ID semantic change while both versions are available.
2. Transport that receipt through `egglog-bridge` into `RuleExecutionTrace`.
3. Map the runtime container type to the already registered typed sort without
   primitive-name allowlists.
4. Append a version witness and exact dependencies during `elaborate_events`.
5. Attach any unsupported version transition as a deferred error to the witness
   or consuming event rather than aborting globally.
6. Let backward reachability discard irrelevant dirty branches.
7. Emit source syntax for the retained version and run ordinary plus unchanged
   strict replay.
8. Only after one real retained canary passes, generalize to nested containers,
   collision merges, maps/sets/multisets, and opaque custom container types.

## 12. Required invariants

Any accepted implementation must preserve these constraints:

- one ordinary native execution per generated slice;
- no second rule-body query for tracing;
- no final-state reconstruction of historical versions;
- no raw `Value` in emitted source;
- exact typed registered primitive/sort identity;
- complete head replay at the original guarded wave boundary;
- match-time, not final-time, binding syntax;
- old versions remain immutable after later rebuilds;
- nested version dependencies are conjunctive and complete;
- collision/custom-merge state reads are included or rejected;
- irrelevant unsupported versions may be sliced away;
- retained unsupported versions fail explicitly; and
- the existing proof encoding and checker remain unchanged.

## 13. Capability matrix

| Case | Current status | Evidence or missing evidence |
|---|---|---|
| Fresh `vec-of`/`vec-empty` from replay-safe registered specialization | Supported | exact primitive receipt, child witnesses, validator, ordinary + strict canaries |
| Fresh arbitrary container result from an explicitly replay-safe, pure, validating specialization | Mechanism present; fixture coverage incomplete | generic typed capability path exists; each concrete sort still needs semantic canaries |
| Read-only replay-safe operation over a stable witnessed container | Narrowly supported when the input witness remains valid | validator and exact specialization required |
| Stateful/opaque container primitive | Rejected | dynamic state/effects are not represented as causal syntax |
| Stable outer ID with changed contents | Detected and rejected | only dirty ID is traced; historical version absent |
| Dirty container on irrelevant branch | Incorrectly rejects globally | rejection precedes backward reachability |
| Outer container ID changes during rebuild | Not established generally | ordinary row rebuild handles runtime state; causal row/version provenance remains incomplete |
| Nested dirty container | Unsupported | dirty propagation exists, nested version chain does not |
| Collision/custom merge during container reinsertion | Unsupported | dynamic merge reads/cause are absent from the trace |
| General map/set/multiset historical versions | Unsupported | generic ordered/normalized witness receipt is unspecified |
| Hardboiled retained path requiring container versions | Not demonstrated | current failure is an untyped retained `Type` equality |

## 14. Evidence map for reviewers

| Knowledge unit | Status | Primary evidence |
|---|---|---|
| one-run causal trace | Implemented | `run_one_traced_command`; `RuleExecutionTrace` |
| append-only dependency/witness architecture | Implemented | `DepNode`, `WitnessArena`, `ReplayEvent` in `causal_slice.rs` |
| guarded shared-wave replay | Implemented | `run-rule-batch` parser/typechecker/executor and causal emission tests |
| fresh typed container primitive replay | Implemented narrowly | `PrimitiveEffect`, replay-safe registration, `VecSort::register_primitives`, causal container tests |
| stable-ID semantic mutation | Confirmed native behavior | `ContainerRebuildSummary`, `ContainerEnv::reinsert_incremental`, nonincremental rebuild tests |
| dirty-ID trace transport | Implemented | bridge `last_rebuilt_containers`; `RuleExecutionTrace::rebuilt_containers` |
| historical container version | Absent | no version type/receipt/current-version sidecar exists |
| retained-only dirty rejection | Absent | `reject_rebuilt_container_witnesses` runs during elaboration |
| generic before/after witness receipt | Blocked on interface design | `ContainerValue` exposes only rebuild + flat iteration |
| Hardboiled container necessity | Deferred | re-enter only after its earlier typed-equality boundary is resolved |

## 15. Reproduction and validation commands

Focused dirty-container canary:

```bash
cargo test -p egglog --test causal_slice \
  rebuilt_container_witness_fails_closed_without_a_content_version -- --exact
```

Complete causal-slice suite:

```bash
cargo test -p egglog --test causal_slice
```

Hardboiled frontier:

```bash
cargo build --release -p egglog --bin egglog
target/release/egglog --mode no-messages -j 1 \
  --causal-slice --proof-testing \
  egglog/tests/hardboiled_conv1d_32.egg
```

Repository proof and full gates:

```bash
make proof-tests
make check
git diff --check
```

At the time this handoff was written, the complete causal-slice suite passed all
136 tests, the dirty-container canary passed by rejecting the unsupported
historical witness, and Hardboiled reached the separate untyped-`Type` equality
boundary described above. `make proof-tests` passed 192 reference plus 8
experimental fixtures, and `make check` passed the complete Python, Rust,
Clippy, formatting, doctest, and DD timing-summary gates. Performance was not
remeasured for this semantic checkpoint.

## 16. Recommended next investigation

Do not start by implementing container versions.

1. Instrument or inspect the exact raw union edge on Hardboiled's retained
   `Type` equality path.
2. Classify whether it is rule-originated, congruence/rebuild-originated, or an
   opaque modeled firing.
3. Add the smallest typed equality receipt or preserve a minimized blocker.
4. Rerun Hardboiled.
5. Only if the retained slice then reaches
   `reject_rebuilt_container_witnesses`, use that exact event to design the first
   structured container rebuild receipt.

This sequencing keeps the container work evidence-driven and avoids building a
general mutable-container subsystem for a path that may not need it.
