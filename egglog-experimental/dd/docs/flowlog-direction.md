# The differential-dataflow backend: state, lessons, and the FlowLog direction

A pick-up-later summary of the `oflatt-dd-rebuild-in-dataflow` work. The goal
has been a clean, fast DD backend for egglog: compile rules + schedule into
differential dataflow and saturate entirely in-dataflow. We reached
hybrid-parity performance, then hit a wall that reframed the whole design
around how [FlowLog](https://arxiv.org/abs/2511.00865) (a Datalog→timely/DD
compiler on our exact substrate) structures its dataflow. This document is the
map back in.

## 1. Where things stand

Branches / PRs (against `saulshanabrook/egglog-encoding`):

- **PR #29** — perf pass on the pre-existing (hybrid) DD backend: `211s → 70s`
  on math-microbenchmark run 11 (RowN width ladder + u128 join keys + compiled
  AtomOps; persistent `by_key` index + per-view event logs; shared
  arrangements).
- **PR #31** — the **schedule engine**: a whole schedule (`Run`/`Repeat`/
  `Saturate`/`Sequence`, spliced rebuild included) compiled into ONE dataflow.
  A stateful `ScheduleEngine` operator walks the schedule as a program counter
  and does everything the host interpreter did (mint, hash-cons, merge, delete);
  DD does only the incremental joins; effects feed back through a root-scope
  `Variable`. Persistent per-spec dataflows across invocations. Reached
  ~hybrid parity: run 9/10/11 ≈ `1.0 / 6.8 / 79s` after the sorted run-fold
  ingest optimization.
- **PR #34** — standalone encoding change: a term-mode constructor's
  `get-fresh!` now receives its `(constructor, children)` so a backend can
  content-address the mint. (Being extended by a separate effort into a lossy
  hash-cons; see §7.)

Not committed:

- **Seminaive fix** (fire-on-positive-delta) and the **interpreter removal**
  (`DbHandle`) are stashed on this branch — correct but perf-blocked (§7).
- Prototypes committed on the branch: `tests/rebuild_fixpoint.rs`,
  `tests/monotone_fire.rs`, `tests/schedule_regions.rs`,
  `tests/scope_consolidation.rs`; operators in `src/monotone.rs`.

Note the schedule engine lives only on this branch; `encoding/main` (upstream,
post-#22) has the **hybrid** DD backend (fused per-ruleset workers), no engine.

## 2. The long-term vision: be like FlowLog

Render the **schedule tree itself as nested DD `iterate` scopes**, instead of a
single flat stateful operator. The backend only ever sees four structural
constructors — `Run`, `Repeat(N)`, `Saturate`, `Sequence` (until-clauses are
filtered out upstream) — and they map directly:

| egglog | DD rendering |
|---|---|
| `Saturate(body)` | `iterate` to fixpoint |
| `Repeat(N, body)` | bounded `iterate` (round-gated `Variable` feedback) |
| `Sequence([a, b])` | sibling scopes: `b` reads `a`'s `leave()`d output |
| `Run(ruleset)` | the ruleset's rule bodies as joins feeding `Variable`s |
| rebuild (UF + congruence) | a recursive-`MIN` fixpoint (= connected components) |
| `:merge` (UF `ordering-min`, `lo`/`hi` min/max) | "iterative"/replacement `Variable` + `reduce` |

Rule *bodies* are already DD joins. The egglog-specific *semantics* Datalog
lacks — minting (`get-fresh!`), hash-cons (`set-if-empty`), monotone-fire
deletes — become custom operators inside the scopes (prototyped in
`monotone.rs`: `memoizing_mint`, `first_per_key`, `rising_edge`).

## 3. Why: the churn problem (what forced this)

The flat engine runs **every rule's join at one timestamp**. During the long
rebuild saturation the tables churn hard (canonicalization = delete old row +
insert canonical), and every delta flows through **all** rules' joins — even
the ~130 user rules that won't fire until rebuild finishes.

Measured on a herbie subset:

- **109M tuples** into arrangements, **67M** match-deltas into the engine, to
  produce **172K** real row changes — a **~390×** amplification (math is ~8×).
  The single worst arrangement: one user rule at **27.9M** tuples, for a rule
  whose leaf fires 6 times.
- Full herbie fully-compiled: **>400s** (times out) vs **4.2s** on the hybrid
  fallback vs **0.16s** native. Correct, just catastrophically slow.

The hybrid avoided this by building a dataflow *per ruleset when it ran*, on the
settled state. The flat engine has no boundary where the intermediate churn can
be discarded.

## 4. How FlowLog does it (confirmed in its source + the DD source)

- Each recursive stratum = `scope.iterative` + one `Variable` per recursive
  relation. Sequencing between strata falls out of timely frontiers (a
  downstream stratum stalls until the upstream fixpoint retires); one
  `worker.dataflow` for the whole program.
- Timestamps are `Product<epoch, iter>` — only two levels; strata are siblings.
- **Consolidation is explicit and is the whole trick.** `leave()` re-stamps
  inner-iteration records to the outer time via `to_outer()`, and an explicit
  `consolidate()` right after nets the cancelling ±1s away. DD's `iterate` does
  *not* auto-consolidate — you insert it. FlowLog's own comment: *"Inside the
  scope they can't cancel (different inner timestamps); after `leave()` both
  project to the same outer time, so consolidate nets them out."*
- Rebuild = **recursive `MIN` aggregation** (connected components), which
  FlowLog optimizes by baking `MIN` into the diff monoid `(ℤ, MIN)`. egglog's
  union-find leader *is* the component minimum — same computation.
- FlowLog has **no** value creation; the existential-Datalog→DD lineage (USPTO
  11,656,868) does, and warns that a mutable counter is fragile under
  retraction — use **content-addressed Skolem ids** (hash of rule + position +
  substitution). That is exactly the keyed `get-fresh!` we're building.

The consolidation mechanism is validated in `tests/scope_consolidation.rs`:
min-label propagation (= UF leader) in an `iterate` scope, feeding a downstream
join. With `consolidate()` after the loop the join receives **5** tuples (the
net); without it, **17** (every intermediate label leaks). That 17→5 is the
herbie 67M→172K in miniature.

## 5. What egglog needs beyond FlowLog (the honest gaps)

- **Nested loops → 3 timestamp levels.** `Repeat(N, Seq(user, Saturate(rebuild)))`
  nests a fixpoint inside a bounded loop; FlowLog only ever uses two levels. DD
  supports arbitrary `Product` nesting; FlowLog just never needed it.
- **Minting.** Content-addressed, keyed on `(constructor, canonical children)`
  — see §7 for why both parts are required, and lossy hash-cons for how to make
  it parallel-safe.
- **Proof mode.** Rebuild composes proof terms host-side. Term-mode-first;
  proof mode via provenance reconstruction later.
- **Deletes/subsumes.** Retraction + re-keying interaction needs design.
- **Report parity.** `(print-stats)` wants a per-iteration `changed`/
  `num_matches` stream; a run-to-fixpoint scope hides iteration boundaries, so
  the report shape has to be reconstructed. (Also note: the DD backend never
  filled per-rule `num_matches` — a pre-existing gap.)

## 6. Prototypes that de-risk the plan

- `rebuild_fixpoint.rs` — the entire UF + congruence closure as ONE `iterate`
  scope via label propagation + `reduce` (mints nothing; incremental across
  epochs). This is the rebuild rendering.
- `monotone.rs` + `monotone_fire.rs` — `memoizing_mint` (content-addressed id),
  `first_per_key` (`set-if-empty` as a latch), `rising_edge` (monotone-fire),
  all designed to run *inside* `iterate` scopes.
- `schedule_regions.rs` — `(run N)` as gated feedback, minting inside a
  `Product`-timestamped saturation.
- `scope_consolidation.rs` — the churn-cancellation-at-`leave` mechanism (§4).

## 7. Key lessons (mostly from things that failed)

- **Seminaive is unsound under merges as we had it.** After a congruence merge
  re-canonicalizes a rebuild rule's supporting row, the −1/+1 churn nets to zero
  in a per-round fold, so the rule doesn't re-fire — but egglog re-fires it (the
  row's timestamp bumps). Collapse rules then lag the growth rules and the term
  set explodes (herbie single `(run 6)`). Fix (stashed): **fire on any positive
  delta this round**, not just a 0→positive crossing — matches egglog's
  timestamp seminaive, ~7% cost on math. Uniform; no naive, no name-gating
  (both of which the design rejected).
- **Content-addressed minting must key on `(constructor, children)`.** Keying on
  `(sort, children)` collides sibling constructors — `Add(a,b)` and `Mul(a,b)`
  are both sort `Math`, so they get the same id and wrongly share an e-class →
  congruence collapse → hang. The sort does not identify the term.
- **And on *canonical* children.** Raw-children keying with a persistent memo
  returns stale ids once rebuild merges those ids away (the patent's warning).
  Canonical children need the union-find at construction — which only the
  fixpoint scope has. So **minting is not a clean isolated pre-step; it belongs
  inside the scope rendering.** (This flipped the plan order.)
- **Lossy hash-cons is the right minting model** (matches egglog constructors):
  usually the same id, occasionally two ids for one term under a thread race,
  which rebuild merges. It won't break DD convergence **provided it is
  append-only / eventually-stable** — new ids only on first-insertion races,
  never re-minting an interned term. DD's deterministic partitioning keeps a
  term on one worker → stable id → the fixpoint converges; cross-worker
  duplicates are bounded one-time merges. A global `Mutex<HashMap>` is the wrong
  implementation (serializes all mints); shard it or use a per-worker memo. The
  current single-worker engine has no races anyway.
- **Flattening to a single `u32` scope was a local win, global loss.** It saved
  ~12% (no subgraph layer) but removed the only place churn could consolidate.
  Fine for low-amplification schedules (math), fatal for high (herbie).

## 8. Concrete next steps

1. **Content-addressed minting foundation** — keyed `get-fresh!` (PR #34) +
   lossy, append-only hash-cons. Enables terms to be built inside a fixpoint
   without re-minting each round.
2. **Schedule-tree → scope lowering** — the re-architecture. Render each
   `Saturate`/`Repeat` leaf as a native `iterative` scope with `Variable`s per
   written relation and `consolidate()` after `leave()`; downstream leaves read
   the consolidated output. This is where the churn dies and herbie becomes
   viable; it also shrinks math's rebuild. Rebuild is the first client, rendered
   as the recursive-`MIN` fixpoint — recognized by schedule *structure* (a
   leaf-level loop), not by ruleset name.
3. **Content-address minting within the scope**, keyed on `(constructor,
   canonical children)` where the labels are in hand.
4. **Follow-ons**: subplan sharing (FlowLog's canonical-hash CTE reuse, for the
   many-rule cost), proof mode, deletes/subsumes, report parity.

Sequence-wise, (1) and (2) are more coupled than they first look: the churn win
*requires* a loop's rules to live in their own scope with downstream rules
outside it, which is most of (2). Expect to build the scope skeleton and
content-addressing together.

## 9. Reference points

- Design doc with the rebuild-in-dataflow formulation and walls:
  `docs/rebuild-in-dataflow.md`.
- FlowLog: paper `arxiv.org/abs/2511.00865`; source `github.com/flowlog-rs/flowlog`
  (`codegen/flow/{recursive,non_recursive}.rs`, `codegen/dedup.rs`,
  `stratifier/core.rs`).
- Timely `leave`/`to_outer`: `timely/src/dataflow/operators/core/enterleave.rs`.
- DD `iterate` (note: no auto-consolidate):
  `differential-dataflow/src/operators/iterate.rs`.
