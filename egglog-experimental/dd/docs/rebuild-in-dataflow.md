# Moving the rebuild fixpoint into the dataflow

Status: investigation (see `tests/rebuild_fixpoint.rs` for a passing prototype
of the core mechanism). Follows the perf work on `oflatt-dd-perf`.

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
- User rules keep the current path: their heads mint fresh ids
  (`lookup_or_create`) and run primitives, which cannot live in the dataflow.

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
