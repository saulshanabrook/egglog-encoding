# Causal Slice v0 Results

## Outcome

One sound end-to-end Bronze slice is implemented:

```text
one traced reference-backend execution using the ordinary query plan
  -> post-run pending-fire and compact dependency/witness/event elaboration
  -> one positive-check-rooted backward slice
  -> deterministic source with one guarded packed rule batch per retained wave
  -> unchanged full-proof mode and strict checker
```

PR #23 is sufficient as the replay/elaboration leaf for the declared monotone
fragment. It is not sufficient by itself: this branch adds the native trace,
dependency model, observation root, source transformation, diagnostics, and a
guarded same-prestate batch required outside the sequential Bronze fragment.
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

The current checkpoint also captures successful unions created by native
rebuild after rule heads commit. These receipts have exact raw endpoints but
no rule origin. Rather than inventing one, the equality forest labels such an
edge with a reported conservative Prefix dependency covering every replayable
firing through that wave. A reduced child-union/parent-congruence example
passes ordinary and unchanged strict proof replay, including an otherwise
no-op firing retained by the Prefix. This is sound fallback infrastructure,
not a small-slice claim.

Independent `push`/`run`/positive-check/`pop` regions are now traced, sliced,
and replayed at their original schedule positions with fresh per-region
arenas. Pure `bigint`/`bigrat` constructors used by a chosen positive check are
reconstructed from that selected match's exact native primitive applications.
Full Herbie now advances through those cases and stops fail-closed at the next
boundary: an exact match-time `Num` row for which no prior replayable syntax
instance was captured.

The current extension also covers visible single-output mutable functions whose
merge expression is syntactically exact `:merge new`. The native sorted-write
commit path reports the exact proposal origin and `Inserted`, `Replaced`, or
`NoOp` outcome; the slicer maintains a pre-wave complete-row dependency
sidecar, attaches lookup dependencies to pending fires, and publishes committed
state only after every match in the wave is elaborated. Ordinary and strict
proof canaries cover unique writes, irrelevant writers, mixed union/set heads,
same-wave old-state reads, and fail-closed equality rekeys.

Grounded packed replay now records the residual-query/head instruction
boundary, evaluates every requested grounding against one shared pre-state,
and validates the complete post-filter binding before any head runs. The
ordinary trace records successful query `Instr::External` lanes without a
second body query. The slicer uses that evidence for one explicitly
whitelisted deterministic query primitive: i64 `+`; BigRat `pow` or `log`; or
BigRat `<`/`>` predicates, including closed `bigint`/`bigrat` arguments.
Failed primitive candidates do not become replay firings. Ordinary and
unchanged strict proof replay pass for all focused cases.

Closed immutable BigInt/BigRat source globals and their later rule/check uses
are now included. Each native traced wave snapshots the zero-key global table
against the same pre-state as its rule query. When a later union changes the
endpoint denoted by a global, the backward slice retains the successful-union
forest path from its definition endpoint to its use-time endpoint. This avoids
both final-state lookup and stale definition-time IDs. A later global that
shadows an earlier `$`-prefixed local remains fail-closed because the unchanged
strict proof checker resolves the replayed spelling as the global.

Anonymous rewrites and birewrites are now lowered through the parsed AST into
deterministically named replayable rules, including stable one-to-many source
mapping. Bare immutable constructor source terms and rewrite-projected source
bindings are captured without final-state extraction. Programs whose only
semantic observations are `print-size` use an explicit conservative prefix
fallback: all effective preceding rule events are retained and the fallback
count is reported. This makes bounded versions of the checked-in math fixture
replay correctly, but it deliberately provides no slicing reduction.

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

### Eggcc fixture result

`egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg` now completes the
entire integrated path: one ordinary traced execution, a schedule-free causal
slice, replay with grounded guarded batches, and the unchanged strict proof
checker. The checked proof concludes `FunctionHasType "main"` with the
expected state tuple. No original computation schedule is used as a fallback.

This extension required configured-EGraph preservation, consecutive schedule
boundaries, effective constructor subsume side effects, deferred rejection of
unreachable opaque/projected firings, exact observation-time constructor rows,
and endpoint-qualified immutable syntax aliases. Observation constructor rows
are captured by trace-only markers on the native check query itself, so this
does not add a second body query or reconstruct a cause from final state.

At commit `31ecaaae3ccd`, six fresh interleaved release rounds measured the
complete causal treatment against unchanged strict `proof-testing`:

| Metric | Original strict proof (95% CI) | Integrated causal strict proof (95% CI) | Candidate / baseline |
|---|---:|---:|---:|
| wall time | 5.31–5.34 s | 2.82–2.83 s | 0.528–0.532x |
| peak RSS | 767.0–775.3 MiB | 486.1–494.0 MiB | 0.629–0.642x |

A separate six-round interleaved report compared the same complete causal
process with ordinary native execution:

| Metric | Ordinary native (95% CI) | Integrated causal strict proof (95% CI) | Candidate / baseline |
|---|---:|---:|---:|
| wall time | 1.11–1.13 s | 2.82–2.82 s | 2.50–2.54x |
| peak RSS | 117.9–124.5 MiB | 488.7–499.7 MiB | 3.96–4.20x |

The reports are
`/tmp/eggcc-strict-vs-causal-31ecaaa.jsonl` and
`/tmp/eggcc-native-vs-causal-31ecaaa.jsonl`. These results establish a large
improvement over full proof execution for this fixture, but not the proposed
approximately-2x-native performance target. Current phase reporting describes
only the final proof EGraph; the 2.81–2.82 s “outside recorded rulesets” cell
still combines traced execution, elaboration, slicing, emission, validation,
and replay setup.

### Luminal fixture result

`benchmarks/luminal-llama.egg` now completes one ordinary traced execution, a
schedule-free causal slice, packed guarded replay, and the unchanged strict
proof checker. The selected equality concludes `Iota = KernelIota`. Its
retained Iota-lowering firing has a mixed `union` plus exact `:merge new` dtype
write; complete-head replay and the dtype row dependency both remain intact.

At commit `53230e7d9fcb`, the trace recorded 12,568 pending firings, 11,698
effective promoted events, 870 all-no-op firings, and 17,850 dependency nodes.
The positive observation retained one firing and four source events. The
emitted program shrank from 455,788 to 392,939 bytes because v0 still preserves
all declarations, rules, and ordinary source initialization.

Six fresh interleaved release rounds compared the complete causal treatment
with unchanged strict `proof-testing`:

| Metric | Original strict proof (95% CI) | Integrated causal strict proof (95% CI) | Candidate / baseline |
|---|---:|---:|---:|
| wall time | 19.0–19.4 s | 18.8–19.2 s | 0.975–1.01x |
| peak RSS | 1.5–1.7 GiB | 1.4–1.4 GiB | 0.837–0.947x |

The same causal samples compared with six ordinary native samples were
42.8–45.2x slower and used 12.3–12.4x the peak RSS. The report is
`/tmp/causal-slice-luminal-smoke-20260721.jsonl`. This is an admission and
source-retention result: the dynamic slice is only 1/11,698 of effective rule
events, but proof time is statistically indistinguishable from the original
because almost the complete source program still enters the proof run.

### Math fixture result

The exact checked-in `benchmarks/math-microbenchmark.egg` source transformation
is implemented: all 24 anonymous rewrites receive stable names, its seven bare
constructor initializers are retained, the original schedule is removed, and
its three `print-size` observations conservatively root the complete effective
prefix. Exact bounded variants through eight waves established semantics before
the compact representation; the exact 11-wave fixture now also passes ordinary
replay and the unchanged strict proof checker.

The checked-in 11-wave workload is now benchmarkable. Packed replay groups
each rule once per wave, shares each closed witness expression through a
per-wave dictionary, resolves all requested groundings against one prestate,
and then applies the captured environments in traced ordinal order. At wave 8
this reduced emitted source from 2.69 MB to 354,913 bytes, generator time from
314 ms to 59.3 ms, and strict replay from 23.56 s to a point sample of 0.12 s.

The exact 11-wave run completes and passes ordinary plus unchanged strict proof
replay. It contains 944,432 pending firings, 836,160 promoted/retained events,
and 1,390,280 witness nodes; it emits 35,945,249 bytes. A serialized release
sample measured 2.82 s generator time and 15.43 s strict replay. The public
benchmark harness measured 20.629 s and 9.254 GB RSS for integrated
`causal-proof-testing`, versus 6.807 s and 3.758 GB for original
`proof-testing`: 3.03x time and 2.46x RSS, point only. Since `print-size`
soundly retains the complete prefix, this is an admission/scale result rather
than evidence of slicing savings.

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
normally exclude all-no-op firings; a conservative Prefix deliberately
promotes them through its boundary. Temporary memory remains
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
- Anonymous rewrites lower through the parsed representation into one stable
  named rule; birewrites lower into two stable distinct rules while preserving
  their shared source-command mapping. Compiler substitution aliases restore
  projected source variables from the exact captured match bindings.
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
| congruence/rebuild equality | conservative Prefix implemented for exact successful rebuild unions | rebuild receipts append after rule-origin unions; an originless applied edge retains every replayable event through that wave and reports one Prefix fallback; exact minimal causes and relation-row rekeys remain absent |
| extract observation | rejected | selected-term/equality dependency path not implemented; no optimality claim |
| negative check/absence | rejected | no tombstone or exhaustiveness evidence |
| delete/subsume | rejected | state provenance absent and sequential replay diverges |
| constructor lookups | implemented for exact captured syntax | lookup availability plus output equality path are retained; equal-but-different body syntax needs exact native row evidence |
| exact single-output `:merge new` functions | implemented and tested | exact lookup rows, proposal origins, `Inserted`/`Replaced`/`NoOp` commit receipts, pre-wave sidecars, rebuild migration, and complete-head replay pass focused ordinary/strict canaries and Luminal |
| custom merges, lookup misses, deletes, and other mutable state | rejected | merge callback reads, tombstones, visibility, and general mutation semantics remain absent |
| constructor witnesses | implemented and tested | source, rule-created, standalone, nested, constructor-union, BigInt/BigRat, and closed-global canaries |
| mutually recursive `datatype*` | implemented and tested | original parsed syntax is preserved; all mutually recursive sorts and constructors are modeled; nested constructor replay passes ordinary and strict proof modes; unsupported inline presorts fail closed |
| rule-head BigRat arithmetic | implemented and tested narrowly | one replay-safe binary `+`, `-`, `*`, `/` or unary `neg`, `abs`, `floor`, `ceil`, `round` application per complete head; exact native evidence and a pre-wave result witness are required |
| query/body primitives | implemented for one deterministic call | successful query `Instr::External` lanes carry exact origin/arguments/result; packed replay validates complete post-filter bindings; i64 `+`, BigRat `pow`/`log`, and BigRat `<`/`>` pass ordinary and strict canaries; arbitrary externals remain rejected |
| dynamic source globals | implemented for closed immutable constructor globals | exact native pre-wave endpoints are captured once per wave; changed endpoints retain their successful-union path; local/global shadowing fails closed |
| inert custom-function and `UnstableFn` schemas | preserved | declarations and unused table schemas may remain in source, while every state read/write/merge and every runtime callback/container value remains rejected without provenance |
| rewrite/birewrite replay | implemented and tested | deterministic parsed lowering, stable source mapping, projected binding aliases, ordinary and strict canaries |
| print-only observations | conservative Prefix fallback | every effective preceding event is retained; each `print-size` root is reported; no size reduction is claimed |
| containers | rejected | same outer ID can represent changed contents |
| push/pop | implemented for independent transactional regions | each `push`/single computation region/positive checks/`pop` is sliced with fresh arenas and replayed at its original schedule; cross-region dependencies and more general nested scope programs remain rejected |
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

The native path carries rule-match lane origins through head table applications
and union proposals. Union commit returns applied/redundant receipts, and the
watched sorted-write path returns exact `Inserted`, `Replaced`, or `NoOp`
receipts with old/new complete rows for single-output `:merge new` functions.
It still lacks exact body-row evidence, lookup-miss/tombstone evidence, delete
and visibility receipts, and provenance for arbitrary custom-merge callback
reads.

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

No epoch is needed inside one tested scope. Native rebuild now appends exact
successful union endpoints after rule-origin receipts; because it does not
expose the colliding-row cause, a retained edge conservatively depends on the
complete event Prefix through that wave. Relation-row rekeys remain
fail-closed. The global no-epoch claim is still false, so supported independent
push/pop regions reset their arenas at scope boundaries.

### Dynamic globals

The first implementation stored only a global's definition-time endpoint. A
two-wave canary applied `union (B) $a` after `$a` was defined as `(A)`: wave 1
reported the applied raw edge `(B, A)`, while wave 2 read `$a` as the canonical
`B` endpoint and reported a redundant `(B, B)`. Reusing the definition endpoint
therefore falsified exact grounding.

The native trace now snapshots every declared zero-key global immediately
before each bounded query and stores those values on the same
`RuleExecutionTrace`. Rule and check models distinguish globals from locals,
exclude them from replay binding schemas, and add the equality-forest support
between definition and use endpoints. A stronger canary makes an earlier union
otherwise irrelevant and confirms backward reachability retains it solely for
a later global-valued head. Both ordinary and unchanged strict replay pass.

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

PR #23's standalone `run-rule` guard still counts captured join candidates
before primitive/equality action filters. A false filter can therefore satisfy
`:expect 1` and execute no head. The packed grounded replay path corrects this
for generated slices: it records the body/head boundary, runs the residual
query once per native candidate, keys on the complete resulting binding, then
checks every exact-one guard before any suffix/head effect. Successful query
`Instr::External` applications are traced in the original run with their exact
origin, inputs, result, and instruction. A canary with successful `pow(2,3)`
and failing `pow(0,-1)` retains only the successful logical firing. This is a
narrow deterministic whitelist, not a claim about arbitrary external side
effects.

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
outweighed by approximately +35.9 ms outside the *final proof EGraph's*
recorded rulesets, accounting for 110% of the wall-time increase. That residual
includes the complete ordinary traced execution in the slicer's separate local
EGraph; it is not pure slicing overhead.

The generator now exposes disjoint stage timings. After one cold release run,
five serialized pointer runs measured:

| Generator stage | Warm observed range |
|---|---:|
| complete generator | 31.2–33.1 ms |
| preparation/modeling | 1.8–2.0 ms |
| ordinary traced execution | 18.6–19.3 ms |
| event/witness elaboration | 3.2–3.3 ms |
| backward slicing | 24–27 µs |
| source emission | 1.3–1.4 ms |
| parsing/validating both emitted programs | 6.1–7.0 ms |

The benchmark report means were 367.612 ms wall / 17.534 ms recorded rulesets
for original `proof-testing` and 400.231 ms wall / 14.213 ms recorded rulesets
for `causal-proof-testing`. The +32.619 ms wall delta closely tracks the
31–33 ms generator. The first optimization targets are therefore the traced
ordinary run and the currently redundant full-transcript/slice validation;
the backward walk is already negligible. The tiny slice works, but the current
complete pipeline does not yet save total time on this fixture.

### Math growth and packed replay measurements

These diagnostic probes changed only the checked-in fixture's `(run 11)`
bound. Every completed variant passed ordinary replay and the unchanged strict
proof checker. The first table records the pre-packed representation and is
retained as the comparison baseline.

| Waves | Pending firings | Effective/retained events | Emitted replay | Generator total | Strict end-to-end test |
|---:|---:|---:|---:|---:|---:|
| 1 | 20 | 19 | 9.6 KB | 13.2 ms | passed |
| 2 | 64 | 47 | 16 KB | 15.4 ms | passed |
| 3 | 129 | 92 | 28 KB | 19.7 ms | passed |
| 5 | 636 | 449 | 141 KB | 37.7 ms | passed |
| 7 | 3,723 | 2,402 | 931 KB | 135 ms | 6.37 s |
| 8 | 8,546 | 5,683 | 2.69 MB | 314 ms | 23.56 s |
| 11 | not completed | not completed | not completed | stopped at 2:27 debug / about 3.2 GiB RSS | not run |

At wave 8 the raw trace lower-bound counter was about 1.44 MB, while emitted
source was 2.69 MB. Backward traversal remains negligible; the prefix has no
events to discard and strict proof replay dominates the completed high-wave
measurements.

After compact grounded batches and one packed batch per wave:

| Workload | Pending | Effective/retained | Source | Generator | Ordinary replay | Strict replay | Peak RSS |
|---|---:|---:|---:|---:|---:|---:|---:|
| wave 8 | 8,546 | 5,683 | 354,913 B | 59.3 ms | 0.36 s | 0.12 s | 91.2 MB strict |
| exact wave 11 | 944,432 | 836,160 | 35,945,249 B | 2.82 s | 3.98 s | 15.43 s | 3.51 GB generator / 7.70 GB strict |

These are serialized point samples from the local release build. The exact
wave-11 public-runner row is stronger for comparison: 20.629 s / 9.254 GB
integrated causal treatment versus 6.807 s / 3.758 GB original strict proof
testing, a 3.03x wall and 2.46x RSS regression. The packed representation
removes the prior completion blocker, but a full Prefix is the wrong workload
shape for demonstrating savings.

Code audit, not yet an A/B measurement, identifies two avoidable peaks before
inventing another witness syntax: generation reparses the entire 35.9 MB source
while traced state and arenas remain live, and the 836,160-fire vector is
deep-cloned during typechecking, proof instrumentation, and schedule
preparation. The emitted file averages only about 43 bytes per retained fire,
so a new witness DAG format is not yet justified by this fixture.

## Current benchmark frontier

All six default workloads now have an explicit capability frontier. Math,
pointer analysis, the real Eggcc proof fixture, and Luminal are admitted end to
end; the remaining failures stay in the validation bucket rather than being
timed as successful rows.

| Workload | Current first boundary | Major subsequent requirements |
|---|---|---|
| `math-microbenchmark.egg` | implemented and benchmarked | exact 11-wave ordinary and strict replay pass; the print-only Prefix retains 836,160 effective events, so the integrated treatment is 3.03x slower and 2.46x higher RSS in one round |
| `pointer-analysis-small.egg` | implemented and benchmarked | 706 pending / 600 effective / 1 retained; ordinary and strict replay pass; retained equal-syntax chained lookups still need exact body-row provenance |
| `herbie.egg` | chosen positive check has an exact `Num` row without a prior replayable syntax instance | scoped regions, fresh BigRat min/max source rows, mixed query/head `bigint`/`bigrat` tapes, rebuild-union Prefix support, and scalar check syntax now pass; exact observation-time constructor provenance or a reported observation Prefix is next |
| `luminal-llama.egg` | implemented and benchmarked | 12,568 pending / 11,698 effective / 1 retained; ordinary and unchanged strict replay pass; 0.975–1.01x strict-proof wall despite a one-fire dynamic slice because 392,939 source bytes remain |
| `hardboiled_conv1d_32.egg` | `Call` body pattern with opaque `VecExpr` at line 234 | inert `UnstableFn` schemas are admitted; versioned container witnesses, functions, filters, broad joins, and subsume provenance remain |
| `eggcc-2mm-pass1.egg` | implemented and benchmarked | ordinary trace, causal slice, guarded replay, and unchanged strict checker pass; integrated causal proof is 0.528–0.532x full strict-proof time but 2.50–2.54x native time; unsupported mutable/container paths not retained by this observation still fail closed when relevant |

The declaration-only, query-primitive, exact `:merge new`, scoped-region, and
rebuild-union Prefix frontiers are now closed. Herbie has reached exact
observation-time constructor provenance; the selected Luminal and Eggcc
observations slice around causally irrelevant unsupported state; and
Hardboiled remains at versioned container values. Guarded post-filter
shared-prestate replay, exact global snapshots, narrow BigRat/i64 primitive
evidence, and exact new-value state receipts are implemented. Custom merges,
lookup misses, delete, general subsume, container versions, and opaque external
provenance remain fail-closed when causally retained.

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

Prior constructor/equality/pointer checkpoint:

- `cargo test -p egglog --test causal_slice`: 38 passed, including the
  unmodified pointer fixture in ordinary and unchanged strict proof replay;
- `make rust-nits`: passed after the lazy-prerequisite patch;
- release pointer correctness command: passed;
- benchmark collection: 12/12 fresh runs succeeded (6 per treatment);
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `make check`: passed, including formatting, Ruff, mypy, Clippy, 170 Python
  tests, the full Rust workspace, 764 file fixtures, doctests, and DD timing;
- `git diff --check`: passed after the final ledger update.

Current packed replay continuation:

- `cargo test -p egglog --test run_rule`: 15 passed;
- `cargo test -p egglog --test causal_slice`: 45 passed, including packed
  emission, one-wave math, pointer, ordinary replay, and unchanged strict proof
  replay;
- exact wave-11 math generation, ordinary replay, strict replay, and the public
  benchmark treatment all succeeded;
- the public-runner report is
  `/tmp/causal-slice-packed-math-20260720.jsonl` and contains one fresh row per
  treatment;
- `cargo fmt --all` and `git diff --check`: passed;
- `make proof-tests` and `make check` have not yet been rerun after the packed
  batch commits; their last complete runs passed before this continuation.

Current global/declaration continuation:

- `cargo test -p egglog --test causal_slice`: 60 passed;
- `cargo test -p egglog --test run_rule`: 16 passed;
- `cargo test -p egglog-core-relations -p egglog-bridge`: 86 unit tests and 2
  doctests passed;
- `cargo clippy -p egglog-core-relations -p egglog-bridge -p egglog --tests --
  -D warnings`, formatting, and `git diff --check`: passed;
- the four unsupported default workloads were rerun at `e15058be`; their exact
  first boundaries are recorded above;
- `make proof-tests` and `make check` remain pending after the newest commits.

Prior primitive/schema checkpoint (superseded by the post-filter continuation below):

- successful primary rule-head primitive lanes now trace their exact origin,
  runtime function identity, arguments, and result; query-side
  `Instr::External` remains intentionally untraced;
- one complete-head BigRat `+`, `-`, `*`, or `/` replays in ordinary and
  unchanged strict proof mode when the retained result has a pre-wave witness;
- `cargo test -p egglog --test causal_slice` passed 72 tests before adding the
  focused Herbie `pow` boundary; the new boundary test passes in isolation;
- core/bridge unit tests, Clippy for the touched Rust crates, formatting, and
  `git diff --check` passed at the preceding primitive commit;
- `make proof-tests` and `make check` remain pending after these commits.

Prior datatype/opaque-schema checkpoint:

- parsed mutually recursive `datatype*` declarations are preserved and their
  schemas modeled without changing source command positions or rule mappings;
- declaration/schema-only `UnstableFn` sorts are preserved as opaque container
  sorts, while dynamic use retains the existing fail-closed diagnostic;
- `cargo test -p egglog --test causal_slice`: 76 passed;
- `cargo clippy -p egglog --test causal_slice -- -D warnings`, formatting, and
  `git diff --check`: passed;
- the exact new fixture frontiers are Luminal line 66 query-side i64 `+` and
  Hardboiled line 234 opaque `VecExpr` use;
- `make proof-tests` and `make check` remain pending after these commits.

Current post-filter/query continuation:

- `cargo test -p egglog --test run_rule`: 20 passed, including complete
  query-result guards, atomic mismatch, shared-prekey/distinct-full-key, and
  unchanged strict BigRat proof replay;
- `cargo test -p egglog --test causal_slice`: 80 passed, including successful
  and failed query candidates, i64 `+`, BigRat `pow`/`log`/`<`/`>`, unary
  BigRat heads, and ordinary plus unchanged strict replay;
- focused core/bridge tests and Clippy with warnings denied passed; formatting
  and `git diff --check` passed;
- fresh real-fixture probes advanced Herbie from line-64 `pow` to line-80
  mutable `lo`, and Luminal from line-66 i64 `+` to the same rule's `subsume`;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `make check`: passed, including formatting, Ruff, mypy, Clippy, 170 Python
  tests, the full Rust workspace, 764 reference file fixtures, experimental/DD
  tests, and doctests;
- `git diff --check`: passed.

Current Eggcc/congruence continuation at `31ecaaae3ccd`:

- `cargo test -p egglog --test causal_slice`: 101 passed;
- `cargo test -p egglog-experimental --test causal_slice`: 3 passed;
- the release `egglog-experimental --causal-slice --proof-testing` Eggcc
  fixture command passed and emitted a strict checked proof;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- Clippy for `egglog` and `egglog-experimental` with warnings denied,
  formatting, and `git diff --check` passed;
- 12/12 fresh runs succeeded in each of the strict-versus-causal and
  native-versus-causal six-round reports;
- `make check` has not yet been rerun after the latest continuation; its last
  complete run passed at the post-filter checkpoint above.

Current mutable/Luminal continuation at `53230e7d9fcb`:

- `cargo test -p egglog --test causal_slice`: 114 passed, including five exact
  `:merge new` state/replay canaries;
- `cargo check -p egglog` and
  `cargo clippy -p egglog --test causal_slice -- -D warnings`: passed;
- the debug `egglog-experimental --causal-slice --proof-testing` Luminal command
  passed and emitted a strict checked proof;
- 12/12 release benchmark runs succeeded for causal versus strict proof, and
  12/12 succeeded for causal versus native, in the same append-only report;
- formatting and `git diff --check` passed before the implementation commit;
- `make proof-tests` and `make check` have not yet been rerun after the mutable
  continuation; their last complete runs passed at the post-filter checkpoint.

Current scoped/rebuild/observation continuation:

- `cargo test -p egglog --test causal_slice`: 121 passed, including independent
  scoped replay, mixed query/head auxiliary scalar tapes, exact positive-check
  BigInt/BigRat applications, fresh custom-merge source insertion, and a
  conservative rebuild-congruence Prefix in ordinary and strict proof modes;
- `cargo test -p egglog-bridge`: 31 passed, including a direct rule union
  followed chronologically by an originless rebuild congruence receipt;
- `cargo check -p egglog`, focused Clippy with warnings denied, formatting, and
  `git diff --check`: passed;
- full Herbie advances beyond BigInt/BigRat observation syntax and fails closed
  at the exact `Num` constructor-row provenance boundary described above;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `make check`: passed, including formatting, Ruff, mypy, workspace Clippy,
  170 Python tests, the full Rust workspace, 764 reference file fixtures,
  experimental/DD tests, and doctests.

## Implemented fact, measurement, proposal, and falsification

- Implemented/tested fact: Bronze plus the pointer fixture are traced once,
  sliced from positive observations, replayed through guarded packed
  same-prestate batches, and accepted by the unchanged strict checker. Direct
  successful unions, immutable constructor witnesses, deterministic rewrite
  lowering, and conservative print-prefix replay are included. Exact wave-11
  math now passes the unchanged checker and the public benchmark runner.
- Implemented/tested fact: closed BigInt/BigRat globals can appear in source
  facts, rule bodies, complete heads, constructor lookups, rewrites, unions,
  and positive checks. Their native pre-wave values and equality causes are
  exact; inert custom-function declarations are preserved without admitting
  mutable table behavior.
- Implemented/tested fact: exact successful rule-head and whitelisted
  query-primitive applications are carried by the native trace. Complete
  post-filter bindings replay through packed same-prestate batches, including
  successful/failing query candidates. This does not admit arbitrary external
  functions or mutable reads.
- Implemented/tested fact: mutually recursive datatype declarations and inert
  `UnstableFn` schemas can be preserved without introducing replay events;
  constructor applications still use native table evidence, and runtime
  container/callback values still fail closed.
- Implemented/tested fact: visible single-output functions with syntactically
  exact `:merge new` carry exact pre-wave row dependencies and per-proposal
  commit outcomes. Effective writes promote their firing, duplicate writes keep
  the prior support, and exact rebuild receipts migrate current state or fail
  closed. Luminal uses this path end to end.
- Implemented/tested fact: exact originless rebuild unions conservatively retain
  a reported event Prefix, scoped regions use independent arenas, and selected
  check BigInt/BigRat syntax comes from exact match-time primitive receipts.
- Empirical measurement: pointer has 706 pending, 600 effective, and 1 retained
  firing; the integrated treatment is currently 1.06–1.12x slower and
  1.04–1.05x higher RSS than strict proof-testing of the original. Exact math
  is 3.03x slower and 2.46x higher RSS in one public-runner round because its
  sound Prefix retains every effective firing.
- Empirical measurement: on Eggcc, integrated causal strict proof is
  0.528–0.532x the wall time and 0.629–0.642x the RSS of unchanged full strict
  proof mode across six interleaved rounds. It remains 2.50–2.54x native wall
  time and 3.96–4.20x native RSS.
- Empirical measurement: Luminal retains 1/11,698 effective firings and reduces
  source from 455,788 to 392,939 bytes, yet six rounds measure 0.975–1.01x
  unchanged strict-proof wall time. Peak RSS improves to 0.837–0.947x. Versus
  native, the integrated path is 42.8–45.2x slower and 12.3–12.4x higher RSS.
- Plausible but untested: source-level declaration/rule/initializer slicing,
  proof-mode compile reuse, a streaming wave trace sink, exact body-row
  transport through factorized joins, and sharing the 836,160-fire tape across
  typecheck/proof/preparation AST transformations.
- Falsified: general complete match bindings, partial-bind replay of projected
  firings, naked `RowId` stability, one preferred syntax as constructor-body
  provenance, globally epoch-free equality endpoints, standalone
  pre-filter `:expect`, deriving a successful query result from `RuleMatch`
  alone, and general sequential-wave equivalence.

## Recommended next patches

The benchmark path, scalar inputs, immutable constructor/global witnesses,
direct unions, guarded shared-prestate batches, exact `:merge new` state, and
four real fixtures are implemented. The next patches should be:

1. slice causally unused rule definitions and source initialization, or reuse
   the already parsed/typechecked program when entering proof replay, then
   remeasure Luminal; its one-fire dynamic slice currently preserves 392,939
   source bytes and is time-neutral versus full proof;
2. expose the existing generator stage timings and retained-event counts in the
   benchmark timing summary without changing the end-to-end headline metric;
3. stream or compact completed native waves so raw matches do not coexist with
   the entire elaborated arena, then remeasure Eggcc and Luminal RSS;
4. capture exact observation-time constructor syntax availability, or use an
   explicitly counted Prefix rooted at the preceding schedule boundary, for
   Herbie's selected `Num` row; do not assign empty availability or infer it
   from final state;
5. add versioned container witnesses and current-version dependencies for the
   first retained Hardboiled `VecExpr` use;
6. avoid reparsing the generated source solely for in-process validation after
   the already-validated parsed/source rule mapping is available;
7. carry exact match-time body atom/table/row-version evidence through
   factorized expansion so retained chained constructor lookups never require
   witness guessing;
8. add lookup-miss/tombstone and delete/subsume visibility evidence only after
   their focused same-wave canaries pass.

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
    sliced replay coverage;
17. `c47b9a3` — record the first integrated pointer benchmark result;
18. `bcd79c9` — format the causal benchmark tests for the final full gate;
19. `facb233` — record the completed initial validation ledger;
20. `590b5f0` — expose disjoint causal generator phase timings and fact-aware
    diagnostics;
21. `d2bf838` — record measured pointer attribution and the corrected benchmark
    frontier;
22. `3367514` — lower rewrites and birewrites into stable replayable named
    rules;
23. `935e18e` — trace bare immutable constructor source terms;
24. `9c4f6cf` — add reported print-prefix replay and exact rewrite binding
    aliases.
25. `a38b245b`, `23d10756` — record the bounded math frontier and rewrite
    validation gates;
26. `397e358c` — skip unused full replay transcripts in the integrated path;
27. `0f3454f3`, `1040154f`, `cc147f8b` — stream prefix emission and share
    replay witnesses;
28. `df849e39` — add guarded same-prestate rule batches;
29. `fd3d8b0e` — add compact grounded batch syntax and execution;
30. `b7be8efd` — emit one compact replay batch per retained wave.
31. `cac77815` — record the exact compact math benchmark;
32. `6ef19b6b`, `b85e13c6` — admit bare equality sorts and immutable BigInt/
    BigRat declaration sorts;
33. `1e02d7f2` — share packed replay fire tapes across AST clones;
34. `dc651847` — replay closed BigInt/BigRat source globals;
35. `f3cb3040`, `6f06f2b0` — model dynamic globals, capture exact pre-wave
    endpoints, and retain endpoint-changing equality causes;
36. `e15058be` — preserve inert custom-function declarations while keeping all
    mutable uses fail-closed.
37. `327b4a81`, `14a76218`, `19a09862`, `375f8302` — replay
    `:unextractable` constructors and preserve inert `Pair`, `Vec`, `Set`, and
    legacy global schemas;
38. `17799692` — replay effective empty-body initializer rules;
39. `a9e67dd6`, `37f434ba`, `71933157` — trace successful rule-head
    primitives and replay retained BigRat `+`, `-`, `*`, and `/` applications.
40. `eabdc894` — preserve the reduced query-primitive/post-filter guard
    counterexample and update the real fixture frontiers;
41. `13327d1d` — preserve and model mutually recursive `datatype*`
    declarations without source lowering;
42. `e8e1172d` — preserve declaration/schema-only `UnstableFn` sorts while
    keeping runtime callback values opaque.
43. `679003ff`, `719ad2af`, `68819ff8` — trace successful query primitives,
    split residual queries from heads, and guard complete post-filter grounded
    batches before effects;
44. `77411307`, `759fdab9`, `c14f22a8`, `0338f314` — replay deterministic
    i64/BigRat query groundings, unary BigRat heads, `log`, and BigRat query
    predicates through the unchanged strict checker.
45. `d5544372`, `da596a34` — record the post-filter results and complete
    validation ledger;
46. `12808083`, `ead55b95` — replay retained constructor subsume side effects
    and consecutive computation schedules;
47. `d61458b6`, `8853cb8e`, `5e0482dd` — defer unreachable unsupported rule
    models while preserving fail-closed opaque prefix/delete boundaries;
48. `227f814b`, `dac5a82a`, `c9ef9853` — preserve configured EGraphs, opaque
    presort schemas, and combined ruleset declarations;
49. `c0ecdf33`, `076e9835`, `31ecaaae` — defer unreachable projected
    groundings and add endpoint-qualified constructor/check provenance through
    equality and congruence boundaries.
50. `ebb35a87`, `5a1989a1`, `53230e7d` — trace exact sorted-write commit
    outcomes, maintain exact `:merge new` row dependencies, and admit the real
    Luminal proof fixture.
51. `d6edba34` — record the measured Luminal benchmark result and source-
    retention bottleneck;
52. `f06e07a` — replay independent scoped regions, trace rebuild-created
    equality edges with a conservative Prefix, admit fresh BigRat min/max
    source rows, and reconstruct exact auxiliary scalar rule/check syntax.

The final diff is confined to reference native tracing/commit receipts,
frontend causal treatment plumbing, the causal-slice module/example/tests, and
`.codex/causal-slice-v0/`. The proof encoding and checker are unchanged.
Nothing has been pushed.
