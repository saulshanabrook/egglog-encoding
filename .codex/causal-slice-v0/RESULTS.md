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

The implementation has now advanced beyond scalar Bronze through immutable
constructor witnesses, direct successful-union receipts, a one-scope equality
forest, constructor lookup dependencies, and an unmodified real pointer
fixture. Unsupported prerequisite elaboration is delayed until backward
reachability, so an unsupported but causally irrelevant firing does not poison
a sound slice. The same unsupported construct still fails closed when its
event is retained.

The Bronze fixture contains two initial facts, a two-rule derivation chain,
multiple groundings, an irrelevant rule, and one positive check. Its
computation schedule captures 6 rule matches, and the observation query adds
one match. All 6 rule firings are effective logical set inserts; the backward
slice retains 2. The complete 6-leaf transcript and 2-leaf slice
both pass ordinary execution and the unchanged strict proof checker. No
automatic computation schedule remains in either emitted program.

## Current real-fixture result

`benchmarks/pointer-analysis-small.egg` is implemented and tested end to end
with its checked-in scalar fact directory:

- one ordinary/native traced execution produces 706 pending firings;
- 600 firings have an effective row, constructor, or union effect;
- the combined positive observation retains 1 firing;
- the emitted source contains exactly one guarded `run-rule` leaf and no
  original `(run 100000)` schedule;
- ordinary replay and unchanged strict proof replay/check both pass;
- `print-size` commands are preserved as read-only diagnostics and do not add
  slice roots.

The first retained-boundary counterexample is a two-wave chained constructor
lookup. A row created as `ptr_points_to(A "alloc")` may later be matched through
the equal syntax `ptr_points_to(expr_points_to("expr"))`. The native trace
currently records bindings and head applications, but not the exact body table
row used by the match. Searching historical witnesses by final equality would
violate the no-inverse-guessing contract. The slicer therefore rejects this
case when retained, while safely discarding the corresponding unretained load
event in the pointer fixture.

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
- Generic Join shapes that can project a required source variable fail closed
  before the run. Broad rules are admitted when the ordinary native planner
  produces one bag; the tracing hook rejects an actual decomposed plan.

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
- Successful rule-originated unions record raw typed endpoints and their
  applied/redundant commit result. Applied edges enter one append-only
  equality forest; redundant union-only firings remain no-ops.
- Unsupported premise elaboration is attached to the promoted event and
  diagnosed only if backward reachability retains that event. Head effects
  and equality edges are still recorded chronologically for every firing.
- One actual satisfying check environment roots every selected logical row;
  roots from multiple checks are combined.
- Backward traversal and chronological emission are deterministic.

### Witnesses and source transformation

- Each captured binding stores a syntax-specific `WitnessId` and its original runtime
  endpoint. Runtime `Value` IDs are never serialized.
- Literal and immutable constructor-application witnesses are captured from
  native source/head applications with availability dependencies. They are
  not reconstructed by per-match extraction or final e-class inverse search.
- Only reachable witnesses are printed. Values that the current printer
  cannot round-trip and retained constructor lookups lacking exact body-row
  evidence fail closed.
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
| conjunctive checks | implemented within planner boundary | one actual complete environment; projected or decomposed observation plans rejected |
| multi-atom rules | implemented within planner boundary | broad single-plan rule passes; native decomposed plans and projected-variable shapes reject explicitly |
| deterministic anonymous naming | implemented and tested | parsed AST source location plus ordinal and collision suffix |
| complete manual transcript | implemented and tested | 6 guarded leaves, no automatic schedule |
| dynamic rule-application slice | implemented and tested | 6 promoted events become 2 retained |
| scalar relation `input` | implemented and tested | TSV rows use the shared native parser and are embedded as source facts; replay passes after the fact directory is deleted |
| no-op promotion filtering | implemented and tested | duplicate-rule and duplicate-head canaries |
| strict proof checker | unchanged and passing | exact two-step proof above |
| physical source `RowId` provenance | not implemented | factorized expansion discards tags; Bronze uses grounded logical rows |
| decomposed-join provenance | rejected | intermediate rows have no shadow `DepId` |
| projected existential grounding | rejected | PR #23 partial bind changes match count; missing selector/witness interface |
| direct equality/union slicing | implemented and tested | commit receipts retain origin and applied/redundant result; direct and constructor-union slices pass strict proofs |
| congruence/rebuild equality | rejected when causally retained | originless rebuild unions and exact row-rekey support are absent |
| extract observation | rejected | selected-term/equality dependency path not implemented; no optimality claim |
| negative check/absence | rejected | no tombstone or exhaustiveness evidence |
| delete/subsume | rejected | state provenance absent and sequential replay diverges |
| constructor lookups | implemented for exact captured syntax | lookup availability plus output equality path are retained; equal-but-different body syntax needs exact native row evidence |
| mutable functions, merges, other RHS lookups | rejected | dynamic read dependencies, proposal origins, and receipts absent |
| constructor witnesses | implemented and tested | source, rule-created, standalone, nested, and constructor-union canaries; globals remain rejected |
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

The native path now carries rule-match lane origins through head table
applications and union proposals, and union commit returns applied/redundant
receipts. It still lacks exact body-row evidence, general lookup hit/miss
dependencies, and per-proposal row commit receipts (`New`, `Changed`, `NoOp`,
`Deleted`, old/new identity).

### Chained constructor lookup

The reduced two-wave canary creates `ptr_points_to(A "alloc")`, then binds the
same argument through the equal term `expr_points_to("expr")`. The ordinary
run succeeds, but the trace exposes only complete variable bindings at the
action leaf; it does not identify the constructor table row used by the body
lookup. One preferred witness per endpoint cannot recover that syntax.

The exact missing interface is match-time body evidence containing source atom
identity, table identity, a generation-safe row/version identity, and the raw
row values. Factorized expansion currently discards the `TaggedRowBuffer`
source `RowId` before `ActionBuffer::push_bindings`. Retained instances fail
closed. Unretained instances may be dropped after head/equality reachability is
known, without scanning the final database or guessing among witnesses.

### Equality

A separate successful-edge arena is implemented for one non-popped scope.
Union commit records raw endpoints, rule-match origin, and applied/redundant
outcome. Every applied edge joins distinct components; direct and nested
constructor-union canaries recover the unique earlier path and pass strict
proof replay. A later redundant edge is not added.

No epoch is needed for this tested one-scope forest. Congruence/rebuild unions
without an originating firing and relation-row rekeys remain fail-closed when
retained. The global no-epoch claim is still false: push/pop can reuse
`Value(0)` for another term.

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

### Pointer fixture benchmark

Commit `eb68822314c4` was measured with six interleaved release rounds per
treatment, a 120-second timeout, and the same binary/backend/fact directory.
The baseline treatment was unchanged `proof-testing`; the candidate was the
integrated `causal-proof-testing` process. Report cache:
`/tmp/egglog-causal-pointer-20260720.jsonl`.

| Metric | Original strict proof (95% CI) | Integrated causal strict proof (95% CI) | Candidate / baseline |
|---|---:|---:|---:|
| wall time | 358–377 ms | 399–401 ms | 1.06–1.12x |
| peak RSS | 105.2–105.4 MiB | 109.9–110.4 MiB | 1.04–1.05x |

Recorded ruleset phases were faster in the candidate: search decreased by
about 0.37 ms, apply by 0.70 ms, and merge by 2.14 ms. Those gains were
outweighed by approximately +35.9 ms outside recorded rulesets, accounting for
110% of the wall-time increase. This is the first real empirical result: the
tiny slice works, but the current traced-run/elaboration/emission/reparse and
strict replay pipeline does not yet save total time on this fixture.

## Current benchmark frontier

All six default workloads now have an explicit capability frontier. Pointer
analysis is admitted end to end; the remaining failures stay in the validation
bucket rather than being timed as successful rows.

| Workload | Current first boundary | Major subsequent requirements |
|---|---|---|
| `math-microbenchmark.egg` | datatype/application values | rewrite-generated rules, equality/congruence provenance, and a conservative root for print-only observation |
| `pointer-analysis-small.egg` | implemented and benchmarked | 706 pending / 600 effective / 1 retained; ordinary and strict replay pass; retained equal-syntax chained lookups still need exact body-row provenance |
| `herbie.egg` | non-scalar `Math` relation | application witnesses, rewrites, custom merges, primitive filters, and multiple temporal boundaries |
| `luminal-llama.egg` | non-scalar `IList` relation | application/container witnesses, multiple schedules, delete/subsume, and mutable-state batching |
| `hardboiled_conv1d_32.egg` | non-scalar `BinOp` relation | containers, functions, rewrites, filters, broad joins, subsume, and batch replay |
| `eggcc-2mm-pass1.egg` | non-scalar `Type` relation | constructors, functions/merges, broad joins, multiple schedules, globals, delete/subsume, containers, and stateful primitives |

The next implementation order selected from these failures is: attribute the
pointer treatment's outside-ruleset cost; preserve exact body-row evidence for
retained chained lookups; add rewrite-generated rule mapping and a print-only
root for the math fixture; then immutable functions, shared-prestate batch plus
mutable state, containers, and opaque/stateful primitives.

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

Current constructor/equality/pointer continuation:

- `cargo test -p egglog --test causal_slice`: 38 passed, including the
  unmodified pointer fixture in ordinary and unchanged strict proof replay;
- `make rust-nits`: passed after the lazy-prerequisite patch;
- release pointer correctness command: passed;
- benchmark collection: 12/12 fresh runs succeeded (6 per treatment);
- `make check` and `make proof-tests` have not yet been rerun after the latest
  constructor/equality/pointer commits; their last full results are the Bronze
  results above.

## Implemented fact, measurement, proposal, and falsification

- Implemented/tested fact: Bronze plus the pointer fixture are traced once,
  sliced from positive observations, replayed only through guarded manual
  leaves, and accepted by the unchanged strict checker. Direct successful
  unions and immutable constructor witnesses are included.
- Empirical measurement: pointer has 706 pending, 600 effective, and 1 retained
  firing; the integrated treatment is currently 1.06–1.12x slower and
  1.04–1.05x higher RSS than strict proof-testing of the original.
- Plausible but untested: a streaming wave trace sink, generation-aware mutable
  sidecars, exact body-row transport through factorized joins, and a native
  shared-pre-state batch.
- Falsified: general complete match bindings, partial-bind replay of projected
  firings, naked `RowId` stability, one preferred syntax as constructor-body
  provenance, globally epoch-free equality endpoints, post-filter `:expect`,
  and general sequential-wave equivalence.

## Recommended next patches

The benchmark path, scalar inputs, immutable constructor witnesses, direct
unions, and the first real fixture are implemented. The next patches should be:

1. split the integrated pointer treatment into traced-native, elaboration/
   emission/reparse, and strict sliced-replay timers; the measured +35.9 ms
   outside rulesets is the first optimization target;
2. carry exact match-time body atom/table/row-version evidence through
   factorized expansion so retained chained constructor lookups never require
   witness guessing;
3. stream each native wave into a callback so raw matches do not coexist with
   the entire elaborated arena;
4. add deterministic rewrite/birewrite source-to-registered-rule mapping and a
   conservative print-only observation root for `math-microbenchmark.egg`;
5. add dynamic reads, general row commit receipts, and guarded shared-prestate
   batch replay before mutation support;
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
   source facts;
9. `7f5d3158` — record the benchmark enablement frontier;
10. `46d6d0e7`, `338330f0`, `74c1ed84` — trace, replay, and admit immutable
    constructor witnesses;
11. `8e9cb9cb`, `e44d53d9`, `54e05cf0` — retain union commit outcomes, slice
    equality causes, and preserve constructor union origins;
12. `643126ce` — trace exact-syntax constructor lookup dependencies;
13. `2921f364` — admit broad single-plan rules and read-only diagnostics;
14. `f1e632ca` — pin the retained chained-lookup provenance counterexample;
15. `eb688223` — defer unsupported prerequisites until backward slicing while
    preserving fail-closed retained events;
16. `b674b003` — lock the unmodified pointer fixture into ordinary and strict
    sliced replay coverage.

The final diff is confined to the reference native trace, the causal-slice
module/example/tests, and `.codex/causal-slice-v0/`. No evaluator/proof-checker
logic changed. Nothing has been pushed.
