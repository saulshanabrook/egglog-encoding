# Causal Slice v0 Design Validation

Status: Bronze implemented and tested. The exact-plan boundary, mutable-state
sidecar proposal, equality hook, and general sequential-wave claim were
actively falsified rather than silently generalized.

Date: 2026-07-20.

## Steering frame

- Mission: establish or falsify the smallest sound instance of one traced
  native run, one backward causal slice, and one unchanged proof-mode replay.
- Non-goals: minimum slicing, alternative-producer OR nodes, delta debugging,
  DD support, proof/checker redesign, speculative epochs, and per-column
  provenance.
- Exact fetched PR #23 head:
  `4940be37429e7adf16cc43283b38508e692cf045`.
- Worktree:
  `/Users/saul/p/wt/egglog-encoding/causal-slice-arena-v0`.
- Branch: `agent/causal-slice-arena-v0`.
- One implementation writer was used. Read-only reviewers audited native
  hooks, equality/witnesses, replay waves, source transformation, and final
  soundness.
- Stop rule: preserve a reduced canary and fail closed when the native path
  lacks match-time or commit-time evidence. Never substitute a final-state
  scan or inverse endpoint search.

## Exact implemented contract

The accepted fragment is intentionally narrow:

- reference/native backend only;
- one non-popped scope;
- immutable set relations over scalar base sorts;
- ground relation insertions as source initialization;
- scalar relation TSV input normalized once into the same ground source facts
  used by traced execution and emitted replay;
- positive relation atoms only in bodies and checks;
- complete heads containing relation insertions only;
- default seminaive rules without subsumed-row matching;
- one automatic computation schedule, followed by one or more positive checks;
- all declarations, rules, source initialization, and checks retained;
- source literals and names must round-trip through the current printer;
- one-atom rules are accepted;
- multi-atom rules are accepted only when they use one native bag (at most two
  body atoms, or an explicit source `:no-decomp`) and every body variable that
  occurs in one atom is also used by the head;
- positive checks have at most two atoms; in a multi-atom check every variable
  must occur in more than one atom.

Those last restrictions match the current planner. One-atom rules use
MinCover. Generic Join projects exactly a variable with one source-atom
occurrence that is unused by the head. Queries with at most two atoms are a
single plan; larger queries can be decomposed unless `:no-decomp` was already
present in the source. The slicer preserves the original plan and planner
flags; it does not normalize tracing to another planner.

The validator rejects unsupported constructs before the traced run, including
equality or primitive filters, functions, constructors, unions, rewrites,
delete, subsume, merges, RHS function lookups, external functions, containers,
extracts, negative checks, push/pop, includes, output/opaque I/O, input
`run-rule`, and DD.

## Design-invariant validation

`Confirmed` means current code plus a focused run. `Falsified` has a reduced
counterexample. `Reasoned only` is not an implemented or empirical claim.

| Proposed invariant | Status | Exact evidence or correction |
|---|---|---|
| PR #23 can replay a captured, fully grounded positive relation firing | Confirmed for Bronze | complete transcript and sliced replay both pass ordinary and unchanged strict proof testing |
| tracing can reuse the ordinary native plan and body search | Confirmed for accepted queries | `run_rules_impl_traced` builds the same cached rule set as ordinary execution; `run_rule_set_traced` records at the final action leaf without a second query |
| trace mode preserves physical parallel ordering | Falsified as a claim | trace mode runs the same plan serially so event order is deterministic; accepted set inserts preserve logical matches and result, but physical parallel order is not claimed |
| final native bindings always contain every source variable | Falsified in general | the projected-variable canary records only `x`; v0 statically rejects the plan shape before execution |
| PR #23 partial `:bind` can replay a projected ordinary firing | Falsified | unbound query sees 1, `:bind ((x 1))` sees 2, and either complete `(x,y)` bind sees 1; no evidence selects one `y` as the projected firing |
| exact source `RowId`s survive factorized final expansion | Falsified | `TaggedRowBuffer` carries a tag, but expansion discards it before `ActionBuffer::push_bindings` and has no source-atom identity |
| decomposed materializations already carry a shadow dependency | Falsified on the current path | materialized rows have no `DepId`; v0 rejects potentially decomposed rules/checks |
| naked `RowId` is a stable sidecar key | Falsified | generation changes, replacement, rebuild/rekey, deletion, compaction, and slot reuse invalidate or recycle IDs |
| action lanes and mutation proposals carry a pending-fire origin | Falsified | `ActionState`, mutation buffers, and staged rows carry values but no `PendingFireId` |
| commit reports which proposal was new, changed, redundant, or deleted | Falsified | current `TableChange` is aggregate and parallel staging may coalesce same-key proposals |
| lookup hits and misses expose row/tombstone evidence | Falsified | vectorized lookup drops row identity and hit/miss provenance; there is no tombstone dependency |
| successful union exposes raw endpoints, origin, and success | Falsified at the public hook | internal insert distinguishes redundant/successful union, but the result and proposal origin are discarded |
| successful raw-endpoint edges form a forest without epochs in one scope | Reasoned only | every successful edge joins two components, so later edges cannot alter an earlier unique path; no end-to-end edge capture exists yet |
| equality IDs are globally stable without epochs | Falsified | push/pop can reuse the same raw `Value` for a different term; cross-scope support needs rollback-aligned arenas or a scope epoch |
| match-time endpoints provide printable witnesses by themselves | Falsified generally | only raw scalar endpoints are captured at the action leaf; literal `WitnessId`s are reconstructed post-run from append-only typed base values |
| scalar literals can be printed without per-match extraction | Confirmed for the exercised `i64` path | typed base-value reconstruction produces source literals; unsafe strings fail closed; application/container witnesses remain unsupported |
| a container outer value identifies immutable contents | Falsified | the same outer ID can survive content rebuild; an immutable container-version witness is required |
| all-no-op firings need persistent replay events | Falsified for Bronze | all matches remain available for the diagnostic transcript, but only first logical producers become persistent fire events |
| one positive check can root one complete actual environment | Confirmed within the planner boundary | one-atom variable check and two-atom constant/repeated-variable checks pass; projected/decomposed checks fail closed |
| sequential grounded leaves preserve the supported monotone fragment | Confirmed | fully grounded set atoms have at most one complete row; prerequisites pre-exist; insertions commute and duplicates are no-ops |
| sequential leaves preserve arbitrary same-wave semantics | Falsified | insert/delete order, delete/subsume query pre-state, and RHS lookup each produce a reduced divergence |
| `:expect` counts post-filter logical matches | Falsified | a false equality/primitive action filter can satisfy `:expect 1` and apply no head; v0 rejects filters |
| scalar relation input requires external files during replay | Falsified for admitted TSV schemas | the slicer parses the file once through the shared native parser, executes those exact source facts, and emits them directly; replay passes after deleting the fact directory |

## Important implementation correction: pending lifetime

The architectural arena is present, but the current trace transport is a debug
spike rather than the final wave-local memory design:

1. the native backend appends every `RuleMatch` and named binding to batches;
2. the frontend keeps all batches through the schedule and checks;
3. after the run, it reconstructs literal witnesses and `PendingFire`s;
4. for a short interval, raw batches and pending firings coexist;
5. only effective fires are promoted into the persistent `EventId` arena;
6. the complete transcript deliberately retains all pending firings until
   source emission.

Therefore temporary tracing memory is `O(all matches + all captured bindings)`,
not wave-local. The lower-bound counter is diagnostic only and excludes vector
capacity and shared symbol allocation. A production patch needs a per-wave
callback/sink that elaborates, promotes, and drops pending matches immediately;
full-transcript retention should be opt-in.

## Why `FactKey` is sound only for Bronze

Bronze uses the complete grounded relation tuple as a stable logical identity.
For immutable set relations there is at most one live row for that tuple, so a
body grounding identifies the exact logical premise without relying on an
unstable physical `RowId`. A match copies the current tuple dependency before
the wave's output map is published.

This does not generalize to functions, mutable rows, container versions,
deletion, subsumption, custom merges, or absence. Those operations require
match/commit evidence and versioned current-state sidecars.

## Reduced planner counterexample

```lisp
(relation R (i64 i64))
(relation S (i64))
(relation Out (i64))
(rule ((R x y) (S x)) ((Out x)) :name "copy")
(R 1 10)
(R 1 20)
(S 1)
```

- ordinary `(run 1)`: one projected logical firing for `x = 1`;
- `(run-rule "copy" :expect 1)`: one match;
- `(run-rule "copy" :bind ((x 1)) :expect 1)`: atomically fails with two;
- either complete `(x 1, y 10)` or `(x 1, y 20)` bind: one match.

Forcing MinCover would create two traced firings and preserve the final state
for idempotent set heads, but it would no longer be the ordinary execution's
grounding multiset. V0 instead rejects this source. Exact support needs a
projection-preserving post-plan selector plus one representative premise-row
witness/dependency for the projected existential.

## Wave result

No batch primitive is required for the declared Bronze fragment. A general
batch is required beyond it. Its minimum semantics are:

1. group fires by original wave;
2. resolve/query every guarded firing against one immutable pre-state;
3. count post-filter logical matches and validate every guard before effects;
4. execute complete heads in captured ordinal order into one shared mutation
   state;
5. commit once with native ordering and rebuild once;
6. preserve dynamic RHS read semantics without synthetic selector premises.

A loop around current `run-rule` does not meet that contract.

## Equality result

The proposed append-only successful-union forest is a plausible one-scope
graph invariant and does not need speculative epochs inside that scope.
However, it is unimplemented and not empirically validated end to end because
the native union path does not expose both success and origin. The existing
canary only establishes that native direct, redundant, and congruence equality
behave under strict proof mode and that the slicer rejects them.

## Experiment ledger

| ID | Question | Result |
|---|---|---|
| E0 | Does exact PR #23 pass focused and repository baselines? | passed: 4 replay tests, proof fixtures, and full `make check` |
| E1 | Can six captured guarded leaves replay with no automatic schedule? | passed in ordinary and strict proof modes |
| E2 | Can one backward slice remove an irrelevant dynamic branch? | passed: 6 matches/effective events become 2 retained events |
| E3 | Does a two-body exact relation grounding carry both logical premises? | passed in ordinary and strict proof modes |
| E4 | Are output programs deterministic and parseable? | passed: independent-process hashes are byte-identical; desugaring succeeds |
| E5 | Does ordinary GJ expose all source variables? | falsified by the projected `y` canary; source rejected |
| E6 | Is sequential replay adequate for Bronze? | passed for fully grounded positive set relations |
| E7 | Does sequential replay preserve mutation waves? | falsified by insert/delete, delete/read, subsume/read, and lookup canaries |
| E8 | Does `:expect` count after primitive filters? | falsified; source rejected before tracing |
| E9 | Is the equality forest available from current hooks? | no; success plus origin is missing |
| E10 | Are source planner flags preserved? | passed; emission preserves absence/presence of `:no-decomp` and validates it in the semantic rule mapping |
| E11 | Are duplicate complete head rows counted once while the full head replays? | passed |
| E12 | Can the public runner measure trace + slice + unchanged strict replay as one treatment? | passed: one release Bronze observation for each strict treatment; timing is point-only |
| E13 | Can scalar relation input become self-contained source provenance? | passed: two TSV rows become source facts and both ordinary/strict replays pass with the directory removed |

## Validation commands

```bash
cargo test -p egglog --test run_rule
cargo test -p egglog --test causal_slice
cargo run -p egglog --example causal_slice -- \
  .codex/causal-slice-v0/bronze.egg
target/debug/egglog /tmp/causal-slice-v0-full.new.egg
target/debug/egglog --proof-testing /tmp/causal-slice-v0-full.new.egg
target/debug/egglog /tmp/causal-slice-v0-slice.new.egg
target/debug/egglog --proof-testing /tmp/causal-slice-v0-slice.new.egg
target/debug/egglog --mode desugar /tmp/causal-slice-v0-slice.new.egg
make check
make proof-tests
cargo fmt --all -- --check
git diff --check
```
