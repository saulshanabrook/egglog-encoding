# Compiling schedules and rules into the dataflow

## Approved shared-crate roadmap (July 2026)

Four changes outside the dd crate, in payoff order (approved in principle;
sequence them as the compiled path engages):

1. **`Backend::run_schedule` hook** (`egglog-backend-trait` + frontend
   lowering) — DONE on this branch, needs review. Everything below builds on
   it; the reference backend is unchanged by construction.
2. **Primitive metadata** (`ExternalFunction` name/purity flags, populated by
   `add_primitive!`) — turns the dynamic echo-or-unit safety guard into a
   static prepare-time whitelist and unblocks compiling body primitives
   (`!=` guards). Small.
3. **Keyed `get-fresh!`** (term encoding) — the mint takes the hash-cons key
   as arguments; the memo dictionary then coincides with the view's
   key→eclass map, unlocking constructor compilation. Includes deciding
   whether relation epoch columns exist at all for monotone-fire-aware
   backends. Medium.
4. **Shared append-only interner** (`core-relations`) — `Database` clones
   share interner state instead of deep-copying it, making value-creating
   primitives compilable and deleting the clone cost + dynamic guard
   entirely. Medium; wants reference-side benchmarking.

Deliberately NOT planned: widening `Value` to u64 for stateless hashed mints
(the memoizing mint makes it unnecessary).

Needing NO shared-crate changes, and on the critical path first: nested loop
scopes (the spliced rebuild schedule shape) and multi-write-leaf phasing
(the rebuild sequence's cleanup/parent/rebuilding leaves).

Status: investigation (see `tests/rebuild_fixpoint.rs` for a passing prototype
of the rebuild fixpoint). Follows the perf work on `oflatt-dd-perf`.

## Agreed goal (July 2026)

A general compiler from (rules + schedule), as seen through the backend API,
to ONE DD dataflow — including user-rule saturation, not just rebuild. The
host shrinks to: feeding command-level inputs, evaluating impure primitives,
and reading outputs at command boundaries (`check` / `extract` /
`print-size`). One epoch per COMMAND, not per iteration. This also dissolves
the data-duplication question: host tables stop being engine working state
and become at most a read cache for command-boundary queries.

The schedule-node mapping:

| Schedule node | Dataflow construct |
|---|---|
| `(run :ruleset R)` once | bounded region (joins + heads), no feedback |
| `(saturate (run R))` | nested `iterate` scope |
| `(run N :ruleset R)` | `iterate` with feedback gated on round < N |
| `(seq A B)` | data-dependency chaining of regions |

The backend-API extension is IMPLEMENTED (this branch):

- `egglog-backend-trait`: `ScheduleSpec` tree (`Run { ruleset, rules }`,
  `Repeat(n, _)`, `Saturate(_)`, `Sequence(_)`) plus an optional trait hook
  `run_schedule(&mut self, &ScheduleSpec) -> Option<Result<Vec<ScheduleLeafReport>>>`
  defaulting to `None` — the main backend is unchanged by construction.
- The frontend's `run_schedule` lowers `ResolvedSchedule` to `ScheduleSpec`
  and delegates when the backend accepts; the backend returns one report per
  executed `Run` leaf in execution order, and the frontend folds them exactly
  as its own interpreter would (`RunReport::singleton` per leaf, unioned), so
  all reports — including `(print-stats)` — are bit-identical either way.
  Lowering refuses trees containing an `until` clause (it needs a host-side
  fact check per leaf visit) or an unknown ruleset; the recursive interpreter
  then retries delegation per subtree, so plain subtrees still compile.
  Custom `Scheduler` objects (`egglog/src/scheduler.rs`) use a separate entry
  point and never reach this path.
- The DD backend takes every offered tree and (for now) interprets it over
  `run_rules` with the frontend's exact control flow — the seam where
  schedule regions will next compile into native dataflow fixpoints.

### Fresh ids inside the dataflow: the memoizing mint operator

User-rule heads mint fresh ids on lookup-miss, and mints on a DERIVED path
must be replay-stable: DD re-runs operator logic on retraction deltas (delete
rules, rebuild churn today; every `iterate` round in the fixpoint), and a
fresh-counter mint on replay yields a different id — the retraction then
fails to cancel the original insertion, corrupting multiplicities (negative
phantom rows), which is far worse than the semantically-absorbable "duplicate
id that congruence unions away".

Decision: a stateful **memoizing mint operator** — an append-only
`canonical_key -> id` dictionary inside a timely operator, minting from the
shared counter on first sight, returning the memoized id on any replay
(negative deltas never mint; they look up). Properties:

- Retraction-safe by construction: `-match` replays produce the same id, so
  cancellation is exact.
- The dictionary never shrinks, matching egglog's write-only term relations
  (terms outlive their rows so proofs can refer to them).
- Dataflow rebuild (the backend clone path) re-primes the dictionary from the
  existing term relations while seeding inputs — same id space, no re-mints.
- Keeps compact u32 counter ids and exact output parity with the main
  backend. (Deterministic skolem/hash ids remain the stateless fallback, but
  would need 64-bit ids to dodge birthday collisions and cannot promise
  parity; shelved unless the operator's state management proves ugly.)

Termination guard: mints happen only behind an antijoin against the view
(mint-on-MISS) — mint-per-match is the classic non-terminating chase.

Decisions (July 2026): the compiler handles ANY schedule with a mint stage at
every fresh-id site — there is NO "mint-free region" analysis; user rules and
rebuild rules lower the same way. Prototyped mechanisms
(`tests/schedule_regions.rs`): `(run N)` compiles to a `Variable` loop whose
feedback is filtered to rounds `< N` (bounded hops inside one epoch, early
convergence free), and `monotone::memoizing_mint` runs INSIDE saturation
scopes at `Product` timestamps (derived lexicographic `Ord` refines the
lattice order for frontier-complete times), assigning ids deterministically
in round order.

Planned encoding change that makes minting first-class: `get-fresh!` takes
the hash-cons KEY as arguments (constructor/view plus canonical children)
instead of being a nullary counter bump. Minting is then a keyed, declarative
operation: the DD compiler recognizes the primitive (the same way it already
recognizes `set-if-empty`/view-proof ops by `ExternalFunctionId`) and routes
it to the mint stage keyed by the argument tuple — and that key makes the
memo dictionary coincide with the FD view's `key -> eclass` map, so
mint-on-miss IS the view's lookup-or-create rather than a second structure.
It also makes a stateless hashed variant trivial later (hash the args; needs
64-bit ids to dodge birthday collisions, hence not the default in this
u32-lane backend).

### `(delete ...)` is data, not DD retraction

egglog's rules are MONOTONE-FIRE: a match's consequences persist after the
matched row is deleted; delete only hides the row from FUTURE matches. The
host architecture gets this for free (negative binding deltas are ignored;
effects are durable table writes). The in-dataflow compiler must not let
DD's view maintenance un-derive fired effects, so it uses a two-layer model:

- **Table state is the integral of an append-only event stream.** User
  deletes/subsumes append `-` events (forward-only), mirroring the host
  event logs. New matches don't see the row; old consequences stand.
- **Head effects pass through a "rising-edge" operator** — the sibling of
  the memoizing mint: stateful, emits one effect event per 0→positive
  transition of a binding's count and NOTHING on falling edges. This
  reproduces monotone-fire exactly, including refire-on-reinsert (each
  remove-then-reinsert is a new rising edge — today's version-bump
  semantics). Append-only output ⇒ monotone ⇒ safe inside `iterate`.
- **Genuine view-maintenance retraction remains confined to** the match
  computation (a `-` event must cancel stale bindings inside the joins, as
  DD already does for us today) and the rebuild layer, where the FD view
  really is a maintained view of terms + labels — which is why the
  prototype's formulation is correct there.

So the compiler's toolkit is DD's native joins/`iterate` for matching and
rebuild, plus two small history-sensitive operators (memoizing mint,
rising-edge fire) implementing egglog's monotone-fire semantics on top of
DD's view-maintenance substrate.

## Motivation

After the compact-layout and O(delta)-host work, the remaining cost profile of
`math-microbenchmark (run 11)` is dominated by the *architecture*, not any one
phase: every host iteration crosses host → DD → host (diff, feed, step, drain
bindings, apply heads, merge, repeat), and the term encoding's rebuild schedule
(`saturate(cleanup, saturate(parent), rebuilding)`) drives most of those
iterations. At run 11 that is ~225 epochs, ~7.5M delta rows fed (20% of them
remove/reinsert version-bump churn), and ~5M host-side merge sets — almost all
of it rebuild traffic.

FlowLog demonstrates the alternative shape: fixpoints live INSIDE the dataflow
(`iterate` scopes with DD `Variable`s, including replace-per-step semantics for
non-monotone aggregates), and the host only commits input deltas and reads
requested outputs. DD is then doing what it is actually good at — incremental
semi-naive fixpoints — instead of being clocked one bounded hop at a time.

## The formulation (prototyped)

One nested `iterate` scope per equality domain, with a single loop variable:

- `labels(x)`: the canonical leader of id `x`, seeded as the identity mapping.
- Inside the loop, congruence collisions are DERIVED from `labels`:
  canonicalize every term row `(op, c0…cn, e)` through `labels`; rows agreeing
  on `(op, canonical children)` with distinct eclass labels emit union edges
  toward the smallest label (exactly the FD view's `ordering-min` merge).
- `labels' = min(identity, labels over user ∪ congruence union edges)` — min
  label propagation, whose fixpoint is the component minimum: the same leader
  the host union-find's pairwise `ordering-min/max` merges converge to.

Because the collision derivation is a function of the loop variable, the whole
mutual recursion (labels → collisions → edges → labels) fits in ONE
`Collection::iterate`, and DD's own semi-naive machinery runs it to fixpoint
within a single epoch. The prototype confirms two-level congruence cascades
(`a≡b ⇒ f(a)≡f(b) ⇒ g(f(a))≡g(f(b))`) converge in one epoch and extend
incrementally in later epochs.

## What the integrated design would look like

- The encoding-generated `@parent`, `@rebuilding`, `@rebuilding_cleanup`
  rulesets stop lowering to `plan_join` rules. Instead the backend recognizes
  them (they are annotated rulesets) and wires their relations into the
  iterate scope above: term relations in, canonical `labels` + canonicalized
  view rows out.
- The host's `(saturate (run parent))`-style loops still run, but converge on
  the FIRST iteration (the dataflow already reached fixpoint; the second
  iteration reports `changed = false`), so frontend semantics and schedules
  are untouched.
- Canonical view deltas and `labels` deltas are drained like rule bindings
  today and applied directly to the host tables — no host merges for rebuild
  (DD already resolved the FD), shrinking `apply_writes` to user-rule effects.
- User rules can join this incrementally: first keep the current host path
  (their heads mint), then move them in-dataflow via the memoizing mint
  operator (see the goal section above) so whole `run`/`saturate` schedules
  compile into the dataflow.

Expected effect at run 11: epochs collapse from ~225 to roughly one per user
iteration (~30), the remove/reinsert version-bump churn for rebuild rows
disappears (labels update in place inside DD), and the ~5M-row host merge
traffic drops to the user-rule share. This attacks all three of the remaining
cost buckets at once, which per-phase optimization could not.

## Known walls (and their outs)

1. **Proof mode.** Rebuild merges compose proofs host-side (`Trans`/`Congr`/
   `proof-of-min` build proof TERMS, minting ids). Options: (a) run
   in-dataflow rebuild only in term mode; (b) record provenance in-dataflow
   (which union edge came from which rule firing / congruence collision) and
   reconstruct proof terms lazily at `prove` time on the host. (b) is
   attractive independently: it removes proof-term construction from the hot
   loop entirely.
2. **Ordering-min vs insertion order.** The host UF picks leaders by
   `ordering-min` over ids (deterministic by insertion). Component-min labels
   agree with that fixpoint for the id orders the encoding mints. Needs a
   careful argument (or a switch to explicit leader choice) before wiring in.
3. **Deletes/subsumes.** `@delete_subsume_ruleset` retracts and re-keys rows;
   as retraction weights these flow through the same scope, but the
   interaction with `to_subsume` marker re-keying needs design.
4. **Container rebuild.** Container canonicalization runs through registry
   primitives; out of scope for the dataflow (stays host-side, as today).

## Suggested next steps

1. Extend the prototype to emit canonicalized VIEW rows (not just labels) and
   check output parity against the host rebuild on a real term-mode workload
   dump.
2. Wire a term-mode-only path: intercept the three rebuild rulesets, feed the
   existing term relations, drain canonical views into the host tables.
3. Benchmark math-microbenchmark run 11 term mode against the ~70s baseline.
4. Only then tackle proof mode via provenance reconstruction.

## Engine performance work (July 22 2026)

The engine (one stateful `ScheduleEngine` operator driving a PC-based
scheduler; DD does only incremental joins) went from 20-40x slower than the
hybrid to parity with it, with bit-identical outputs at every step.
math-microbenchmark wall times (single thread):

| workload | first working engine | final | hybrid (host-scheduled) | mainline |
|----------|---------------------:|------:|------------------------:|---------:|
| run 9    | 16.6s                | ~1.0s | 0.8s                    |          |
| run 10   | 231s                 | 6.8s  | 5.5s                    |          |
| run 11   | (not attempted)      | ~103s | 70s                     | 5.9s     |

What mattered, in order of measured impact:

1. **Join ordering** (biggest win: run10 71s -> 11.4s). `plan_join` used body
   order; the factorization rule `(Add (Mul a b) (Mul a c))` joined
   `Mul ⋈ Mul` on just `a` — 8.8M intermediate tuples where the final match
   count was 20K (90% of ALL arrangement traffic). `plan_join_with` now takes
   per-view stats (row count + sampled per-column distinct counts), scores
   every permutation (rules have ≤4 atoms) with the standard independence
   model, and picks the cheapest. `EGGLOG_DD_NO_ORDER=1` disables it.
2. **Width ladder for the engine dataflow** (run9 16.6->5.5s, run10 231->82s).
   The engine path ran everything at `RowN<48>` (192-byte rows in every
   arrangement); it now monomorphizes `run_compiled` over {8,16,32,48} like
   the fused path and picks the smallest width covering every binding layout
   and table arity.
3. **Demux + one concatenate** (run9 1.31->0.92s, run10 7.7->5.9s). Timely's
   Tee clones each batch per subscriber: ~85 per-view filters on the full
   engine output stream copied every emission ~85x (20% of the profile in
   `Message::push`). One `partition` by (func, loc) routes each delta once.
   Likewise the per-rule match streams now merge through a single
   `concatenate` instead of ~200 chained binary concats.
4. **Flat root-scope feedback** (~12%). The engine's `Variable` loop lives in
   the root `u32` scope (step 1) instead of a `Product<u32,u64>` subscope:
   4-byte timestamps in every sorted tuple, no nested progress tracking, and
   completion is `probe.done()` after dropping the seed input handles.
5. **Shared arrangements** (run9 16.6->12.9s pre-ladder). One arrangement per
   (view, key-column projection) serves every join site; both sides of each
   rule's first join are shared raw-view arrangements with the slot programs
   fused into the join closure.
6. **Per-timestamp queue buckets in the engine op.** The pending queue held a
   `BinaryHeap` of individual deltas — 73.5M heap ops of 72-byte payloads on
   run 11. Buckets keyed by timestamp cut heap traffic to one op per round.
7. **Quiescent-schedule replay cache.** `print-size`/`print-stats` splice a
   rebuild schedule per command; at run-11 scale each cost ~6s re-seeding
   5.6M rows to fire nothing. A run that applied zero deltas and minted
   nothing is cached keyed on the spec debug string + a global row-event
   watermark (`mutation_counter` bumped in `record_row_event`) and replays
   its reports verbatim. Runs that changed anything are never cached
   (a budget-limited `(run n)` must re-run — caught by the integer_math
   corpus test).

Remaining gap vs the hybrid (run 11: ~103s vs 70s) is measured, not
mysterious: 73.5M match deltas flow through the engine (ingest+turn ≈ 32s at
~0.44µs each, cache-miss-bound), and 56% of that volume is the Add
associativity rule alone — inherent re-derivation churn under incremental
semantics, amplified because one dataflow feeds every ruleset's pipelines all
intermediate waves (the hybrid fed each ruleset folded net windows). The
architectural answer is the persistent cross-invocation dataflow (epoch =
continuing round counter, host deltas fed via event-log cursors), which also
removes the per-invocation reseed entirely.

Profiling: `EGGLOG_DD_ENGINE_DEBUG=1` prints per-phase laps, per-turn gaps and
per-rule match traffic; `EGGLOG_DD_VOLUMES=1` prints per-arrangement input
volumes; building with `--features egglog-experimental-dd/pprof` and setting
`EGGLOG_DD_PROFILE=<path>` writes a flamegraph per schedule invocation
(sampling profiler that works where perf_event_open is blocked).

## Persistent per-spec dataflows (July 22 2026, second commit)

Compiled schedules now keep their dataflow alive across invocations
(thread-local cache keyed by EGraph instance + spec fingerprint; the engine
emits its own seeds on first boot, a BOOT marker resets the scheduler PC per
pass, and a chase loop keeps the input frontier one round ahead until the
engine's done channel fires). Reuse is guarded by three watermarks —
row-event counter, fresh-id position, rules version — and any mismatch drops
the entry and rebuilds, so reuse is exactly as correct as a fresh build.

Measured (all outputs semantically identical to mainline; run9/10/11
single-invocation outputs bit-identical to prior DD refs):

| workload | persistent | no-persist (env kill-switch) |
|---|---:|---:|
| eleven separate `(run 1)` at run-11 scale | **91.6s** | 103.1s |
| nine separate `(run 1)` at run-9 scale | **1.20s** | 1.58s |

(The single `(run 11)` is 95.4s, so split invocations are now free — slightly
cheaper, even, since cross-pass fired flags skip already-fired matches.)

**Fired-flag soundness across passes** (found by integer_math, 341 vs 331
Adds): a fired delete/subsume rule whose row is re-added in the SAME round
never sees its match retract — the -/+ pair cancels in DD consolidation,
where the interpreter's physical row timestamps would re-trigger the rule.
Delete/subsume-capable rules therefore reset their fired flags every pass
(refiring is idempotent on table state); pure writers keep theirs, matching
interpreter seminaive exactly (untouched inputs are not re-searched).

**What v2 (foreign-delta feeding) would take and buy.** Today any host-side
mutation between invocations invalidates. A realistic driver loop (add term,
`(run 1)`, repeat) shows two things in the invocation trace:
1. Per-invocation overhead is already milliseconds (prepare 1-9ms, build
   3-21ms); the remaining rebuild cost is the fresh engine's from-scratch
   match recompute inside `step` — that is what delta-feeding eliminates.
2. Term additions ADD RULES (~36/term from the encoding's term-lowering), so
   a global rules_version invalidates everything; v2 needs per-spec rule
   LIVENESS (the spec's rule ids all still resolve — bodies are immutable
   per id) instead.
The v2 recipe: subscribe the entry's read/write views to the event logs;
at boot, fold each view's window since the entry's cursor and hand the net
transitions to the engine through a channel (begin_pass updates its tables
and re-emits them under the seed LOCs); re-sync the engine's mint counter to
the host's fresh-id position at boot; refresh the engine's Database clone
when foreign deltas exist (the interner is append-only, so a fresh clone
resolves everything). Estimated value: modest at small scale (the driver's
1.2s is mostly real work + DD per-tuple economics, not invocation overhead),
real at large scale (a from-scratch rebuild schedule costs ~6s at 5.6M rows;
the replay cache already covers the exact-no-op case).

## Optimization round 2 (July 23 2026)

Sorted run-fold ingest in the engine (sort each round's raw deltas, net
equal-binding runs sequentially, fetch per-rule state once per group)
replaced the per-delta hash-netting: run 11 **95.4s -> 79.1s**, split-11
driver 91.6 -> 74.7s. Volume ground truth from new counters: 84.3M raw /
62.6M netted match deltas against **17.26M distinct matches** at fixpoint
(4.26x re-derivation multiplier), and the emitted-row classification shows
the churn is dominated by canonicalization rewrites of view rows (@AddView:
1.13M new / 0.47M removed / 0.85M rewritten) — inherent to rebuild, NOT
epoch-column overhead, so the keyed-get-fresh encoding change would not
recover much on math.

Negative result worth keeping: routing matches through an in-dataflow
distinct (presence edges) is semantically exact but nearly DOUBLED wall time
single-threaded — the reduce arrangements on the hottest stream cost more
than the engine bookkeeping they save. It becomes attractive only as the
sharding point under multi-worker execution. Also: differential's
`distinct_total` emitted spurious edges inside this feedback cycle (its
total-order fast path's batch-window bookkeeping); the general reduce-based
distinct was exact. Use `reduce`, not `distinct_total`, in cycles.

Next levers, in order: multi-worker execution (joins + a sharded presence
reduce, engine pinned to one worker), the 7s host-side apply, delta-query
joins for 3-atom rules.
