# Causal Slice v0 Design Validation

Status: Bronze and exact single-output `:merge new` state are implemented and
tested. The exact-plan boundary, general mutable-state sidecar proposal,
equality hook, and general sequential-wave claim were actively falsified
rather than silently generalized.

Date: 2026-07-21.

## Current validated extension beyond Bronze

The initial scalar-only audit below is preserved as the baseline experiment
record. The current implementation additionally confirms:

- native head applications carry exact rule-match lane origins;
- successful union commit exposes raw endpoints, origin, and an
  applied/redundant outcome;
- applied union edges form a working one-scope explanation forest for direct
  and constructor-union slices without epochs;
- immutable literal/application witnesses retain syntax, endpoint, and
  availability separately;
- restricted constructor body lookups retain the exact captured application
  witness and output equality path;
- broad queries are admitted when the native tracer actually selects one bag;
  actual decomposed plans still reject;
- unsupported prerequisite evidence is deferred until reachability: an
  unretained unsupported event is omitted, while a retained one returns the
  same fail-closed diagnostic;
- the unmodified pointer fixture produces 706 pending, 600 effective, and 1
  retained firing and passes ordinary plus unchanged strict proof replay;
- anonymous rewrites/birewrites lower through the parsed AST into stable named
  registered rules, including compiler-substitution aliases needed to recover
  their exact captured source bindings;
- print-only programs use an explicit reported Prefix fallback retaining every
  effective preceding firing;
- guarded packed replay resolves all requested groundings against one shared
  prestate, validates every request before any head, applies captured complete
  environments in original ordinal order, and commits once per wave;
- the exact 11-wave math fixture now passes ordinary and unchanged strict proof
  replay and produces a public benchmark row. Its full Prefix remains a
  measured performance loss rather than a semantic or completion blocker;
- closed immutable source globals are distinguished from local variables and
  excluded from replay bindings. The native trace snapshots their exact
  zero-key values against each wave pre-state; when canonicalization changes a
  value, the slice retains the successful-union path from definition to use;
- inert custom-function declarations are preserved; runtime reads and writes
  remain fail-closed unless they satisfy the exact `:merge new` contract below,
  and every custom merge/default remains fail-closed without its own state
  provenance;
- visible single-output functions with syntactically exact `:merge new` use
  exact sorted-write receipts, pre-wave complete-row dependency sidecars, and
  post-wave publication; five ordinary/strict canaries and the real Luminal
  fixture pass;
- positive-check constructor rows are now captured on the native check query
  itself with complete grounded inputs/output and the chosen match origin;
  observation grounding uses that exact row plus successful-union edges rather
  than parser-generated variable names or final-state inverse lookup;
- immutable witness syntax identity is separated from endpoint-qualified
  instances, so equal printed terms at different points in canonicalization do
  not silently reuse a witness with different match-time children;
- parser-generated wildcard variables are deterministically alpha-normalized
  through the parsed representation before modeling and replay emission;
- the unmodified Eggcc 2mm pass-1 proof fixture now completes traced slicing,
  schedule-free guarded replay, and the unchanged strict proof checker;
- six interleaved release rounds measured causal Eggcc proof at
  0.528–0.532x full strict-proof wall time, while the complete pipeline remains
  2.50–2.54x ordinary native wall time;
- the unmodified Luminal fixture retains 1 of 11,698 effective firings and
  passes strict replay, but six rounds are 0.975–1.01x full strict-proof wall
  time because the emitted program still retains 392,939 of 455,788 source
  bytes.

The strongest newly falsified assumption is that one preferred syntax per
runtime endpoint identifies constructor body provenance. After a union and
rebuild, a lookup may match `ptr_points_to(expr_points_to(u))` using a row
created as `ptr_points_to(A("alloc"))`. The terms are equal, but the trace lacks
the exact body row. Searching the witness arena for a plausible predecessor is
explicitly rejected. The missing native datum is source atom identity plus
table, generation-safe row/version identity, and raw match-time row values.

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

## Initial Bronze contract

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

The initial validator rejected all equality, constructors, unions, and
rewrites. The current extension above admits immutable constructors, direct
unions, restricted constructor lookup binders, parsed rewrite/birewrite
lowering, closed immutable globals, inert custom-function declarations, and a
print-only Prefix fallback. It also admits one exact deterministic query
primitive from the tested i64/BigRat whitelist and narrow proof-validating
BigRat head arithmetic. It also admits exact single-output `:merge new`
function lookups and writes with successful commit/rebuild evidence. It still
rejects custom merges, lookup misses, delete, general subsume, arbitrary
external functions, containers, extracts, negative checks, push/pop, includes,
output/opaque I/O, input `run-rule`, and DD.

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
| action lanes and mutation proposals carry a pending-fire origin | Confirmed for traced head applications, union proposals, and watched sorted writes | traced `ActionState` lanes carry `RuleMatchId`; table applications, union receipts, and exact `:merge new` receipts preserve it; general row mutations remain incomplete |
| commit reports which proposal was new, changed, redundant, or deleted | Confirmed for union outcome and watched exact sorted writes | union reports applied/redundant; watched sorted writes report `Inserted`, `Replaced`, or `NoOp` plus old/new complete rows. Delete and arbitrary custom-merge callback evidence remain absent |
| lookup hits and misses expose row/tombstone evidence | Falsified | vectorized lookup drops row identity and hit/miss provenance; there is no tombstone dependency |
| successful union exposes raw endpoints, origin, and success | Confirmed for traced rule proposals | `UnionReceipt` records raw lhs/rhs, optional `RuleMatchId`, and applied/redundant outcome; originless rebuild/congruence unions remain unsupported |
| successful raw-endpoint edges form a forest without epochs in one scope | Confirmed for direct and constructor-union canaries | applied edges join distinct components, redundant edges are omitted, and strict replay resolves the unique path |
| a chosen positive check exposes its exact internal constructor rows without a second query | Confirmed | trace-only marker calls are attached to canonical constructor atoms in the same native check query and associated with the selected `RuleMatchId`; repeated and prefix-named constructors pass strict replay |
| printed constructor syntax plus output endpoint uniquely determines match-time children | Falsified | the closed congruence canary has the same `Wrap(A 1)` syntax/output with pre- and post-union child endpoints; endpoint-qualified exact witness nodes are required |
| equality IDs are globally stable without epochs | Falsified | push/pop can reuse the same raw `Value` for a different term; cross-scope support needs rollback-aligned arenas or a scope epoch |
| match-time endpoints provide printable witnesses by themselves | Falsified generally | syntax-specific literal/application witnesses are required; one preferred endpoint witness fails for equal-syntax chained lookups |
| scalar literals can be printed without per-match extraction | Confirmed | typed base-value reconstruction produces source literals and unsafe strings fail closed |
| immutable constructor syntax can be captured from native applications | Confirmed | source, rule-created, nested, standalone, and constructor-union canaries pass ordinary and strict replay |
| one definition-time global endpoint remains valid for every later use | Falsified | after an applied union, wave 2 reads the global's canonical endpoint while the saved definition ID is stale |
| one per-wave global snapshot identifies the value queried by every firing in that wave | Confirmed | snapshots are taken immediately before the shared native query; direct, rewrite, lookup-output, redundant-union, and equality-dependency canaries pass strict replay |
| changed global endpoints need no causal dependency | Falsified | a reduced three-rule slice fails without the earlier union; retaining the definition-to-use forest path makes ordinary and strict replay pass |
| one preferred witness identifies a constructor body row after equality | Falsified | retained chained-lookup canary requires exact native body-row/version evidence; witness inverse search is forbidden |
| a container outer value identifies immutable contents | Falsified | the same outer ID can survive content rebuild; an immutable container-version witness is required |
| all-no-op firings need persistent replay events | Falsified for Bronze | all matches remain available for the diagnostic transcript, but only first logical producers become persistent fire events |
| one positive check can root one complete actual environment | Confirmed within the planner boundary | one-atom variable check and two-atom constant/repeated-variable checks pass; projected/decomposed checks fail closed |
| sequential grounded leaves preserve the supported monotone fragment | Confirmed | fully grounded set atoms have at most one complete row; prerequisites pre-exist; insertions commute and duplicates are no-ops |
| sequential leaves preserve arbitrary same-wave semantics | Falsified | insert/delete order, delete/subsume query pre-state, and RHS lookup each produce a reduced divergence |
| standalone `run-rule :expect` counts post-filter logical matches | Falsified | the original guard counts join candidates; generated packed replay instead runs the recorded residual-query prefix, keys the complete resulting binding, and validates every exact-one guard before heads |
| final `RuleMatch` bindings alone explain successful query primitives | Falsified | the match is still pre-primitive; a separate successful-`Instr::External` trace now supplies exact origin, function, arguments, result, and instruction |
| successful rule-head and query primitive lanes expose exact causal evidence | Confirmed narrowly | head primary/fallback and query `External` success carry exact lane evidence; the slicer admits only an explicit deterministic i64/BigRat whitelist and rejects arbitrary externals |
| query/head splitting preserves atomic same-prestate replay | Confirmed for the guarded prefix whitelist | every candidate prefix runs against one prestate, complete guards validate before suffixes, suffixes run in ordinal order, and ordinary plus strict i64/BigRat canaries pass |
| parsed `datatype*` must be rewritten into unrelated source commands | Falsified | v0 preserves the parsed declaration, mirrors its mutually recursive schemas for modeling, and reuses existing constructor table tracing; ordinary and strict replay pass |
| declaration-only `UnstableFn` requires callback provenance | Falsified | the sort and inert schemas replay strictly as opaque declarations; any runtime value use still fails closed through existing opaque-sort checks |
| scalar relation input requires external files during replay | Falsified for admitted TSV schemas | the slicer parses the file once through the shared native parser, executes those exact source facts, and emits them directly; replay passes after deleting the fact directory |
| anonymous rewrite registration is too opaque for stable replay names | Falsified | parsed rewrite/birewrite lowering assigns stable source-position names and preserves one-to-many source mapping; focused ordinary and strict canaries pass |
| print-only observations provide a narrow causal root | Falsified | `print-size` observes aggregate state, so v0 reports a conservative Prefix and retains every effective prior event; no slicing reduction is claimed |
| bounded sequential rewrite replay preserves the math fixture result | Confirmed empirically through wave 8 | historical sequential variants pass ordinary and unchanged strict replay; general same-wave replay is now provided by the guarded batch rather than inferred from this result |
| guarded batch observes one shared prestate | Confirmed | lookup, enabling, delete/insert, subsume, atomic-failure, and proof canaries pass; all requests are captured before any head executes |
| raw equality-sort binding IDs remain stable across replay waves | Falsified | later union/rebuild can displace a representative; packed matching canonicalizes expected and captured ID cells against the same batch prestate |
| compact per-wave replay scales to exact math | Confirmed for completion, falsified for savings | exact wave 11 completes and passes strict replay, but its full Prefix is 3.03x slower and 2.46x higher RSS in one public-runner round |
| causal slicing can reduce a real full-proof workload end to end | Confirmed for Eggcc, not a general claim | six interleaved rounds are 0.528–0.532x full strict-proof wall time and 0.629–0.642x RSS; versus native the complete process is still 2.50–2.54x time and 3.96–4.20x RSS |
| exact `:merge new` mutable state has sufficient commit evidence | Confirmed narrowly | unique write/read, irrelevant writer, mixed union/set, same-wave old-state read, and equality-rekey fail-closed canaries pass; effective receipts promote events and no-op receipts retain prior support |
| a one-fire dynamic slice necessarily makes proof replay cheap | Falsified by Luminal | 1/11,698 effective firings are retained, but preserving 392,939 source bytes yields 0.975–1.01x full strict-proof wall time across six rounds |

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

The append-only successful-union forest is implemented for one non-popped
scope. Native commit reports raw endpoints, rule-match origin, and
applied/redundant outcome. Direct and nested constructor-union slices recover
the unique successful-edge path and pass unchanged strict proof replay;
redundant unions do not add edges or persistent union-only events.

This does not establish general congruence/rebuild support. Originless rebuild
unions and relation-row rekeys lack the required colliding-row and child-
equality transition evidence and fail closed when the affected event is
retained. Push/pop remains outside the no-epoch claim.

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
| E8 | Does standalone `run-rule :expect` count after primitive filters? | falsified; generated packed replay now uses a separate complete post-filter guard path |
| E9 | Is the equality forest available from current hooks? | passed for rule-originated direct unions; originless congruence/rebuild remains unsupported |
| E10 | Are source planner flags preserved? | passed; emission preserves absence/presence of `:no-decomp` and validates it in the semantic rule mapping |
| E11 | Are duplicate complete head rows counted once while the full head replays? | passed |
| E12 | Can the public runner measure trace + slice + unchanged strict replay as one treatment? | passed: one release Bronze observation for each strict treatment; timing is point-only |
| E13 | Can scalar relation input become self-contained source provenance? | passed: two TSV rows become source facts and both ordinary/strict replays pass with the directory removed |
| E14 | Can immutable constructor creation and union be replayed? | passed for source, rule-created, nested, standalone, and constructor-union canaries in ordinary and strict modes |
| E15 | Does one preferred witness identify a later constructor lookup? | falsified by the retained chained-lookup canary; exact body row/version evidence is missing |
| E16 | May an unsupported but causally irrelevant firing be discarded? | passed: prerequisite error is deferred to reachability; retained variant still fails closed |
| E17 | Does the unmodified pointer fixture slice and strictly replay? | passed: 706 pending, 600 effective, 1 retained |
| E18 | Does the first real integrated treatment save time? | no on pointer: 1.06–1.12x wall time and 1.04–1.05x RSS over six rounds |
| E19 | What accounts for the pointer wall regression? | five warm generator runs took 31.2–33.1 ms, dominated by 18.6–19.3 ms ordinary tracing and 6.1–7.0 ms emitted-program validation; slicing itself took 24–27 µs |
| E20 | Can parsed anonymous rewrites and bare constructor terms replay without extraction? | passed: rewrite/birewrite naming, projected binding aliases, and bare source constructors pass focused ordinary and strict canaries |
| E21 | Can the checked-in math fixture use a sound print-only root? | passed through exact wave 11 using a reported full effective Prefix; no reduction is possible for that observation |
| E22 | Is the exact 11-wave math workload benchmark-ready with compact packed replay? | yes: generation, ordinary replay, unchanged strict replay, and one fresh public-runner comparison all succeed |
| E23 | Does exact math save time with the current observation? | no: one public-runner round measured 20.629 s / 9.254 GB causal versus 6.807 s / 3.758 GB original, or 3.03x wall and 2.46x RSS |
| E24 | Are sequential `run-rule` leaves the general replay primitive? | no: reduced mutation/lookup canaries require guarded same-prestate batching; the packed batch implementation passes 15 focused replay tests |
| E25 | Is a source global's definition endpoint sufficient for later waves? | no: the two-wave `(B), $a=(A)` canary reports native redundant `(B,B)` after the first union, not `(B,A)` |
| E26 | Can exact global values be captured without a second body query? | yes: the native bridge snapshots zero-key global tables once immediately before each bounded query |
| E27 | Does backward reachability retain a global's endpoint-changing cause? | yes: an otherwise irrelevant union is retained solely for a later global-valued head; ordinary and strict replay pass |
| E28 | Can inert custom-function declarations be admitted without merge provenance? | yes: declaration-only strict replay passes and the paired dynamic `set` canary remains rejected |
| E29 | Can retained complete-head BigRat binary arithmetic replay strictly? | yes for one `+`, `-`, `*`, or `/` with exact traced operands/result and a pre-wave result witness |
| E30 | Can Herbie's query-side `pow` use a traced post-filter grounding? | yes narrowly: successful and failed `pow` candidates are distinguished from one native run, the result is in the packed grounding, and ordinary/strict replay pass; `RuleMatch` alone remains insufficient |
| E31 | Can mutually recursive `datatype*` declarations remain source-level replay syntax? | yes: two mutually recursive sorts and nested constructors replay in ordinary and unchanged strict proof modes; unsupported inline `Map` fails closed |
| E32 | Can `UnstableFn` be admitted only as an inert opaque schema? | yes: declaration/schema-only replay passes ordinary and strict modes, while a rule body reading the value is rejected |
| E33 | Does the query bridge advance real fixtures? | yes: Herbie advances from line-64 `pow` through unary heads, `log`, and comparisons to mutable `lo`; Luminal advances through query-side i64 `+` and, with exact `:merge new` receipts, completes strict replay |
| E34 | Are failed query primitive candidates replayed as firings? | no: focused `pow(0,-1)`, `log(2)`, and false BigRat predicate candidates produce no retained replay fire, while successful peers replay strictly |
| E35 | Are exact `:merge new` receipts sufficient for mutable row dependencies? | yes narrowly: five focused canaries cover new/replaced/no-op state, complete mixed heads, same-wave prestate, rebuild migration, and the strict-proof rekey boundary |
| E36 | Does Luminal's one-fire dynamic slice save strict-proof time? | no: six rounds retain 1/11,698 effective events but measure 0.975–1.01x full proof wall; source preservation leaves 392,939 bytes to parse/typecheck/instrument |

## Validation commands

```bash
cargo test -p egglog --test run_rule
cargo test -p egglog --test causal_slice
cargo run --release -p egglog --bin egglog -- \
  --mode no-messages -j 1 \
  --fact-directory benchmarks/data/pointer-analysis-small \
  --causal-slice --proof-testing benchmarks/pointer-analysis-small.egg
uv run --locked ./bench.py \
  --target . \
  --compare-treatment proof-testing \
  --treatment causal-proof-testing \
  --rounds 6 --timeout-sec 120 \
  --report /tmp/egglog-causal-pointer-20260720.jsonl \
  --format markdown --detail phases \
  --fact-directory benchmarks/data/pointer-analysis-small \
  benchmarks/pointer-analysis-small.egg
uv run --locked ./bench.py \
  --target . --compare-target . \
  --compare-treatment proof-testing \
  --treatment causal-proof-testing \
  --rounds 1 --timeout-sec 120 --force-run \
  --report /tmp/causal-slice-packed-math-20260720.jsonl \
  --format markdown egglog/tests/math-microbenchmark.egg
target/debug/egglog-experimental \
  --causal-slice --proof-testing benchmarks/luminal-llama.egg
uv run --locked ./bench.py \
  --target . --treatment causal-proof-testing \
  --compare-target . --compare-treatment proof-testing \
  --rounds 6 --timeout-sec 300 \
  --report /tmp/causal-slice-luminal-smoke-20260721.jsonl \
  --format markdown --detail files benchmarks/luminal-llama.egg
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
