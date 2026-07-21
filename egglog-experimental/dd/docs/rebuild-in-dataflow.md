# Compiling schedules and rules into the dataflow

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
