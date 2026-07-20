# Causal Slice v0 Results

## Outcome

One sound end-to-end Bronze slice is implemented:

```text
one traced reference-backend execution using the ordinary query plan
  -> post-run pending-fire and compact dependency/witness/event elaboration
  -> one positive-check-rooted backward slice
  -> deterministic source with guarded run-rule leaves
  -> unchanged full-proof mode and strict checker
```

PR #23 is sufficient as the replay/elaboration leaf for the declared monotone
fragment. It is not sufficient by itself: this branch adds the native trace,
dependency model, observation root, source transformation, and diagnostics.
PR #23 cannot replay a projected ordinary Generic Join firing from partial
bindings; that is the smallest replay counterexample and is now an explicit
fail-closed boundary.

The Bronze fixture contains two initial facts, a two-rule derivation chain,
multiple groundings, an irrelevant rule, and one positive check. Its
computation schedule captures 6 rule matches, and the observation query adds
one match. All 6 rule firings are effective logical set inserts; the backward
slice retains 2. The complete 6-leaf transcript and 2-leaf slice
both pass ordinary execution and the unchanged strict proof checker. No
automatic computation schedule remains in either emitted program.

## Repository state

- PR: #23, branch `agent/run-rule-schedule`.
- Exact fetched base:
  `4940be37429e7adf16cc43283b38508e692cf045`.
- Worktree:
  `/Users/saul/p/wt/egglog-encoding/causal-slice-arena-v0`.
- Local branch: `agent/causal-slice-arena-v0`.
- Toolchain: `rustc 1.91.0`, `cargo 1.91.0`, `uv 0.11.28`.
- The original checkout's unrelated `.DS_Store` and `.codex/` were not
  touched.
- No push, PR creation, or remote mutation was performed.

## User-facing API

Library:

```rust
egglog::causal_slice::causal_slice_program(filename, source)
```

Executable spike:

```bash
cargo run -p egglog --example causal_slice -- SOURCE.egg
cargo run -p egglog --example causal_slice -- --full SOURCE.egg
```

The first form writes the slice to stdout; `--full` writes every captured
grounding. Both write trace/event statistics to stderr. Unsupported source
returns a source-located diagnostic before native execution.

Integrated strict benchmark path:

```bash
target/release/egglog-experimental --causal-slice --proof-testing SOURCE.egg
uv run --locked ./bench.py \
  --compare-treatment proof-testing \
  --treatment causal-proof-testing SOURCE.egg
```

The causal treatment is one measured process: ordinary native trace, slice
construction and source emission, followed by the existing strict proof
replay/checker. `--causal-slice` is reference-backend-only, serial, and
requires exactly one file plus `--proof-testing`.

## Implemented and tested facts

### Native trace

- The reference backend captures raw typed endpoints at the final serial
  native action leaf that executes each complete head.
- It uses the ordinary cached query plan and the same body search; tracing does
  not query a body twice.
- Each bounded ruleset iteration remains a distinct batch, preserving wave
  boundaries and deterministic ordinal order for the serial trace.
- Trace mode disables physical parallel execution. This does not alter the
  logical matches or result for the admitted positive set-insert fragment, but
  physical parallel order is not claimed.
- Potentially decomposed queries and Generic Join shapes that can project a
  required source variable fail closed before the run.

The debug trace currently retains every raw match and binding through the
whole schedule. Literal witnesses and `PendingFire`s are elaborated post-run,
so raw batches and pending data briefly coexist. Persistent `ReplayEvent`s
exclude all-no-op firings, but temporary memory remains
`O(all matches + bindings)`. A production tracer needs a wave callback/sink;
this spike does not claim the intended wave-local memory behavior.

### Arenas and backward slice

- `DepId`, `EventId`, and `WitnessId` are `u32` append-only arena indices.
- Source rows and promoted fires have event dependencies; exact conjunctions
  use immutable `And` nodes.
- Bronze uses one producer dependency per complete grounded relation tuple
  (`FactKey`), the stable logical identity for immutable set relations.
- A match copies all body-tuple dependencies before new outputs from its wave
  are published.
- Every raw firing is classified after the run. A firing becomes a persistent
  event only when at least one complete head tuple is a first logical producer.
- Duplicate facts inside one head count as one effective output row, while the
  emitted rule retains and executes the complete original head.
- One actual satisfying check environment roots every selected logical row;
  roots from multiple checks are combined.
- Backward traversal and chronological emission are deterministic.

### Witnesses and source transformation

- Each captured binding stores a scalar `WitnessId` and its original runtime
  endpoint. Runtime `Value` IDs are never serialized.
- Witness syntax is reconstructed once post-run from typed append-only base
  values, not by per-match extraction or final e-class inverse search.
- Only reachable literal witnesses are printed. Values that the current
  printer cannot round-trip fail closed.
- Anonymous rules receive deterministic source-position/command-ordinal names
  before registration; collisions receive stable suffixes.
- Original rule semantics and source planner flags, including `:no-decomp`,
  are preserved in a source-to-registered mapping and revalidated after
  emission.
- Declarations, rule definitions, initialization, and observations remain in
  source order. The original schedule is replaced, not retained secretly.
- Every replay leaf binds every admitted source variable and uses `:expect 1`.
- Emitted source is reparsed and recursively audited for automatic schedules,
  partial bindings, selectors, changed rule definitions, and unsafe literals.

## Original and emitted example

Original:

```lisp
(relation Seed (i64))
(relation Mid (i64))
(relation Goal (i64))
(relation Irrelevant (i64))
(ruleset derive)
(rule ((Seed x)) ((Mid x)) :ruleset derive :name "seed-to-mid")
(rule ((Mid x)) ((Goal x)) :ruleset derive :name "mid-to-goal")
(rule ((Seed x)) ((Irrelevant x)) :ruleset derive :name "irrelevant")
(Seed 1)
(Seed 2)
(run-schedule (saturate derive))
(check (Goal 2))
```

Sliced schedule:

```lisp
(run-schedule
  (seq
    (run-rule "seed-to-mid" :bind ((x 2)) :expect 1)
    (run-rule "mid-to-goal" :bind ((x 2)) :expect 1)))
```

The complete transcript contains six chronological guarded leaves. The slice
removes the value-1 chain and both firings of `irrelevant`.

Strict proof output for the sliced observation:

```text
Rule(mid-to-goal,
  premises=[Rule(seed-to-mid,
    premises=[Fiat(Seed 2)], substitution=[x=2])],
  substitution=[x=2])
```

No proof encoding, evaluator, checker, or expected proof was weakened.

## Capability matrix

| Capability | Status | Evidence or boundary |
|---|---|---|
| `i64` positive set relations | implemented and tested | full transcript, two-rule slice, two-body conjunction, duplicate/no-op, ordinary and strict proof replay |
| `String`, `bool`, `f64`, `Unit` scalar path | implemented generically, less tested | same typed-literal path; unsafe String printer cases have fail-closed coverage; no separate successful strict slicer canary for every sort |
| one/multiple positive checks | implemented and tested | one actual support per check, combined backward root |
| conjunctive checks | implemented within planner boundary | constants or variables occurring across atoms; more than two atoms and projected variables rejected |
| multi-atom rules | implemented within planner boundary | exact two-body join passes; potentially decomposed and projected-variable shapes rejected |
| deterministic anonymous naming | implemented and tested | parsed AST source location plus ordinal and collision suffix |
| complete manual transcript | implemented and tested | 6 guarded leaves, no automatic schedule |
| dynamic rule-application slice | implemented and tested | 6 promoted events become 2 retained |
| scalar relation `input` | implemented and tested | TSV rows use the shared native parser and are embedded as source facts; replay passes after the fact directory is deleted |
| no-op promotion filtering | implemented and tested | duplicate-rule and duplicate-head canaries |
| strict proof checker | unchanged and passing | exact two-step proof above |
| physical source `RowId` provenance | not implemented | factorized expansion discards tags; Bronze uses grounded logical rows |
| decomposed-join provenance | rejected | intermediate rows have no shadow `DepId` |
| projected existential grounding | rejected | PR #23 partial bind changes match count; missing selector/witness interface |
| equality/congruence slicing | rejected | successful-union success plus origin hook absent |
| extract observation | rejected | selected-term/equality dependency path not implemented; no optimality claim |
| negative check/absence | rejected | no tombstone or exhaustiveness evidence |
| delete/subsume | rejected | state provenance absent and sequential replay diverges |
| functions, merges, RHS lookups | rejected | dynamic read dependencies, proposal origins, and receipts absent |
| application/global/constructor witnesses | rejected | proactive syntax/availability witness hook absent |
| containers | rejected | same outer ID can represent changed contents |
| push/pop | rejected | runtime IDs can be reused after restore |
| output effects, includes, opaque I/O | rejected | reproducibility/hidden schedules unproven; scalar relation input is the one admitted I/O normalization |
| DD backend | rejected | reference backend only |
| globally minimum slice | not attempted | one deterministic actual support only |

## Falsified assumptions and smallest blockers

### Projected ordinary grounding

For `R(x,y), S(x) -> Out(x)` with two `R` rows and one `S` row:

- ordinary run and unbound `run-rule :expect 1` see one projected firing;
- `run-rule :bind ((x 1)) :expect 1` sees two and atomically fails;
- either complete `(x,y)` binding sees one.

Thus neither a partial bind nor arbitrary complete extraction can identify the
ordinary projected firing. The smallest missing interface is a
projection-preserving post-plan grounding selector plus one representative
premise-row witness/dependency for projected existentials. The slicer reports
this at the rule source location.

### Physical rows and mutable state

`TaggedRowBuffer` has a `RowId`, but final factorized expansion loses the tag
and source atom. Naked IDs also become stale after generation changes,
replacement, rebuild/rekey, deletion, compaction, or reuse. General provenance
needs either generation-aware physical identity with exact migration, or the
smallest stable logical identity exposed at match/commit.

The native mutation path additionally lacks lane-aligned `PendingFireId`s,
lookup hit/miss dependencies, proposal origins, and per-proposal commit
receipts (`New`, `Changed`, `NoOp`, `Deleted`, old/new identity).

### Equality

A separate successful-edge arena is a plausible forest within one non-popped
scope: successful edges join distinct components, so later edges cannot change
an earlier unique path. This is a reasoned invariant, not implemented or
end-to-end tested. Current union commit discards success and origin, and native
UF parents path-compress. Congruence would also need both colliding-row
dependencies and child equalities.

No epoch is needed by Bronze because equality and scopes are rejected. The
global no-epoch claim is false: push/pop can reuse `Value(0)` for another term.

### Sequential waves

Sequential guarded leaves are sound for fully grounded positive set relations:
all captured body tuples already exist, each tuple is unique, inserts commute,
and duplicates are no-ops.

They are not a general wave replay:

- insert then delete silently reverses the native shared-commit result;
- delete/subsume then read makes the sequential second guard see zero instead
  of the original pre-state row;
- a prior write changes a later sequential RHS lookup from old to new state.

Therefore `run-rule-batch` is not required for Bronze but is required for the
general architecture. It must query all fires against one pre-state, validate
all post-filter guards before effects, apply complete heads into one shared
mutation state, commit once in native order, and rebuild once.

### Guard/filter boundary

PR #23 counts captured join candidates before primitive/equality action
filters. A false filter can pass `:expect 1` and execute no head. Bronze rejects
all filters; a future batch must guard post-filter logical matches.

## Measurements

These are diagnostic debug-profile toy measurements, not an optimization claim
or worst-case bound.

Event and output volume:

| Metric | Result |
|---|---:|
| input commands / bytes | 12 / 376 |
| traced schedule waves | 3 |
| schedule matches / pending firings | 6 / 6 |
| promoted effective fire events | 6 |
| effective logical output rows | 6 |
| all-no-op firings | 0 |
| retained fire events | 2 |
| unique source events | 2 |
| dependency / witness nodes | 9 / 2 |
| equality edges / Prefix fallbacks | 0 / 0 |
| schedule plus observation matches | 7 |
| raw named bindings | 13 |
| maximum batch | 4 |
| raw trace lower bound | 592 bytes |
| emitted slice / full transcript | 504 / 698 bytes |
| slice SHA-256 | `5186f0f6bf5dd2651a83cf0a830071eabce1452d71a2a657916a9e1c45da7b03` |
| transcript SHA-256 | `2e819eec995bc1ad5b7ea5e4b52bf8a28d910684a3a4173ee7085f97d6b60d8c` |

Independent processes produced each hash twice with byte-identical results.

Process timings (`hyperfine -N`, 30 warmups, 300 runs):

| Process | Mean +/- sigma | Ratio to ordinary |
|---|---:|---:|
| ordinary original | 2.0 +/- 0.1 ms | 1.00x |
| traced run + elaborate + slice + validate + emit | 2.6 +/- 0.1 ms | 1.28x |
| ordinary full-transcript replay | 2.1 +/- 0.1 ms | 1.02x |
| ordinary sliced replay | 2.1 +/- 0.1 ms | 1.01x |
| strict proof replay/check of slice | 3.9 +/- 0.1 ms | 1.90x |

The proposed production total for this process-level toy is about 6.5 ms, or
3.2x the ordinary process baseline (`2.6 + 3.9`). Process startup dominates;
this does not establish a general speedup or the desired 2x target.

Ten serialized `/usr/bin/time -l` samples:

- ordinary maximum RSS: 8,355,840 bytes in every sample;
- slicer median maximum RSS: 8,421,376 bytes;
- median delta: 65,536 bytes (+0.78%);
- observed delta: 16,384 to 147,456 bytes (+0.20% to +1.76%).

RSS is page-granular and toy-specific. More importantly, the implementation
retains all trace batches, so its asymptotic temporary memory is still
`O(all matches + bindings)` even though this tiny process delta is small.

One release-mode public-runner smoke observation compared the new integrated
candidate against strict proof testing of the original Bronze source:

| Metric | Original strict proof | Integrated causal strict proof | Candidate / baseline |
|---|---:|---:|---:|
| wall time | 17.2 ms | 10.6 ms | 0.617x |
| peak RSS | 9.7 MiB | 10.1 MiB | 1.05x |

This is one point-only sample, not speedup evidence. Its purpose was to prove
that the public runner builds, caches, and measures the complete one-process
pipeline under distinct treatment identities.

## Current benchmark frontier

All six default workloads now have an explicit capability frontier. None is
yet admitted end to end; failures remain diagnostics rather than timed rows.

| Workload | Current first boundary | Major subsequent requirements |
|---|---|---|
| `math-microbenchmark.egg` | datatype/application values | rewrite-generated rules, equality/congruence provenance, and a conservative root for print-only observation |
| `pointer-analysis-small.egg` | non-scalar `Allocation` relation | constructor witnesses, equality support, exact projected/decomposed join premises; scalar input provenance is now implemented |
| `herbie.egg` | non-scalar `Math` relation | application witnesses, rewrites, custom merges, primitive filters, and multiple temporal boundaries |
| `luminal-llama.egg` | non-scalar `IList` relation | application/container witnesses, multiple schedules, delete/subsume, and mutable-state batching |
| `hardboiled_conv1d_32.egg` | non-scalar `BinOp` relation | containers, functions, rewrites, filters, broad joins, subsume, and batch replay |
| `eggcc-2mm-pass1.egg` | non-scalar `Type` relation | constructors, functions/merges, broad joins, multiple schedules, globals, delete/subsume, containers, and stateful primitives |

The implementation order selected from these failures is: application/global
witnesses and non-scalar relation tuples; successful-union/equality and
rewrite mapping; exact projected/decomposed premise evidence; immutable
functions; shared-prestate batch plus mutable state; then containers and
opaque/stateful primitives. Pointer analysis is the first intended unmodified
default workload because it avoids delete, subsume, and custom merges.

## Validation status

Baseline on exact PR #23 before changes:

- `cargo test -p egglog --test run_rule`: 4 passed;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `make check`: passed.

Bronze implementation at the initial handoff:

- `cargo test -p egglog --test run_rule`: 4 passed;
- `cargo test -p egglog --test causal_slice`: 24 passed;
- full transcript: ordinary and strict proof replay passed;
- sliced program: ordinary, strict proof replay, and desugaring passed;
- independent-process deterministic hashes passed;
- `make check`: passed, including formatting, Ruff, mypy, Clippy, 169 Python
  tests, the full Rust workspace, 764 file fixtures, doctests, and DD timing;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `cargo fmt --all -- --check` and `git diff --check`: passed.

## Implemented fact, measurement, proposal, and falsification

- Implemented/tested fact: the bounded `i64` Bronze fixture is traced once,
  sliced from a positive check, replayed only through guarded manual leaves,
  and accepted by the unchanged strict checker.
- Empirical measurement: the toy has 6 matched/promoted and 2 retained events;
  traced generation is 1.28x ordinary and strict proof replay is 1.90x ordinary
  at process level.
- Plausible but untested: a one-scope successful-union forest, a streaming
  wave trace sink, generation-aware mutable sidecars, proactive app witnesses,
  and a native shared-pre-state batch.
- Falsified: general complete match bindings, partial-bind replay of projected
  firings, naked `RowId` stability, native origin/receipt availability,
  globally epoch-free equality endpoints, post-filter `:expect`, and general
  sequential-wave equivalence.

## Recommended next patches

The benchmark path and scalar relation inputs are now implemented. The next
capability patches should follow the observed default-suite frontier:

1. capture immutable application/global witnesses at creation time and admit
   non-scalar relation tuples without final extraction;
2. add successful-union receipts, equality dependencies, and deterministic
   rewrite/birewrite source-to-registered-rule mappings;
3. preserve exact logical premise rows and projected variables through Generic
   Join and decomposed plans;
4. stream each native wave into a callback so raw matches do not coexist with
   the entire elaborated arena;
5. add lane-aligned origins, dynamic reads, commit receipts, and guarded
   shared-prestate batch replay before mutation support;
6. add delete/subsume visibility, custom merges, containers, and opaque
   externals only after their focused canaries pass.

## Commit and diff summary

Local reviewable commits:

1. `a8496dac` — record validation contract and experiment ledger;
2. `2bb00ec8` — add one-pass native tracing and Bronze slicer;
3. `3a626532` — add executable fixture and end-to-end replay tests;
4. `84b923d4` — align the prototype with compact pending/event/dependency/
   witness arenas and add falsification canaries;
5. `aff5345c` — preserve ordinary planner semantics, fail closed on projected
   or decomposed cases, preserve source planner flags, and fix duplicate-output
   accounting;
6. `984c9fa6` — record the validated boundary and initial final runs;
7. `f292c6a` — add one-process strict causal benchmark treatments and CLI;
8. `f6a9b09` — normalize scalar relation inputs into self-contained replay
   source facts.

The final diff is confined to the reference native trace, the causal-slice
module/example/tests, and `.codex/causal-slice-v0/`. No evaluator/proof-checker
logic changed. Nothing has been pushed.
