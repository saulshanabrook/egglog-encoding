# Causal Slice v0 Results

## Projected replay-key and temporal-Vec checkpoint: 2026-07-21

This checkpoint was developed on top of
`096686177d6fcd44df16fbf746fbb2592a9bf1e9`. The verified PR #23 head and
merge base remain `4940be37429e7adf16cc43283b38508e692cf045`.

### Implemented and tested fact

Grounded firings continue to retain their complete match-time bindings and
dependencies internally. Before committing each traced native wave, the
slicer now chooses one deterministic maximal source-level replay key for each
rule in that wave. Key selection:

- considers every successful original match, including complete-head no-ops;
- considers earlier still-live matches because packed replay freshly queries
  the complete current database;
- deduplicates repeated occurrences of the same complete logical grounding;
- admits an equality/container expression only when its source syntax had one
  raw denotation at that match boundary; and
- emits only the selected variables while preserving `:expect 1` and executing
  the complete recovered rule head.

The packed runtime now has direct ordinary and strict-proof canaries for a
partial key, a zero-variable key, omitted lookup bindings, and atomic rejection
of an ambiguous projected key. A private planner canary proves that two raw
equality endpoints with identical syntax are not used as point selectors, that
a colliding no-op match counts, and that an identical grounding repeated in a
later wave does not create false ambiguity.

An end-to-end causal canary creates two temporal raw denotations for
`Pair(A, A)`, traces a `copy(tag, e)` firing, emits only the exact scalar
`tag` selector, and then recovers `e` to execute the complete `(Out tag e)`
head. Its ordinary and unchanged strict-proof replays both pass.

The retained stable-ID Vec canary also closes. It creates `vec-of (B)`, advances
the later observer's timestamp, unifies `A` and `B`, then requires a later rule
to see the refreshed parent row through `vec-contains ... (A)`. The generated
slice retains four firings and one reported Prefix fallback and passes ordinary
replay plus the unchanged strict proof checker. An irrelevant dirty Vec branch
is discarded. The implementation uses one typed current-support pointer whose
immutable `DepId` is copied by consumers; after rebuild the pointer is replaced
with `old support AND complete replayable prefix`. It does not add a historical
`ContainerVersion` arena.

### Falsified assumption and exact Hardboiled boundary

Point-stable partial bindings are sufficient for several earlier Hardboiled
waves, but not for the full fixture. The current exact failure is the anonymous
type-propagation rule at source lines 273-277, registered as
`__causal_slice_v0_b8339_e8454_c111`. In traced wave 19 it has 84 successful
logical groundings. Only `t` and `bop` are point-stable source columns, and
those columns do not uniquely select each captured grounding:

```text
84 successful groundings of rule `__causal_slice_v0_b8339_e8454_c111` in
traced wave 19 cannot be uniquely identified by replay-stable source bindings
["t", "bop"]; packed logical selectors or a stable match-time endpoint handle
are required
```

A diagnostic fallback that emitted ordinary structural `run-rule-batch`
selectors was semantically promising but reproduced the witness-tree expansion
the packed representation was introduced to avoid. The release Hardboiled
generation terminated after 44.57 s with maximum RSS 2,884,173,824 bytes
(about 2.88 GB). That fallback was reverted. The smallest next interface is a
compact logical selector inside `run-rule-batch-packed` that references the
existing witness DAG, queries every listed fire against one shared pre-state,
checks every exact guard atomically, and then executes complete heads. A stable
match-time endpoint handle would be an alternative.

The final release build with the sound fail-closed planner reaches the same
diagnostic in 4.26 s at 277,839,872 bytes maximum RSS (about 278 MB). This is a
boundary measurement, not a successful causal-proof benchmark.

This is now Hardboiled's first retained boundary; it is not a demonstrated
container-history failure. No new final benchmark cohort was run because the
four-workload completion command would still reject Hardboiled. The previously
recorded Eggcc/Pointer/Luminal timing results therefore remain historical and
must not be attributed to this checkpoint.

### Validation status

Final validation:

- `cargo test -p egglog --test run_rule`: 30 passed;
- `cargo test -p egglog --test causal_slice`: 154 passed;
- the focused private replay-key planner test passed;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `make check`: passed, including Python format/lint/type checks, 179 Python
  tests, warning-denying Rust Clippy, the complete workspace test suite,
  doctests, and the DD timing-summary gate;
- `cargo fmt --all -- --check`: passed; and
- `git diff --check`: passed.

## Observation-congruence checkpoint: 2026-07-21

This checkpoint starts from clean, pushed commit
`cb203b5aacc89cc5c1459f332eaa8e89bfa78812`. The verified live PR #23 head
remains `4940be37429e7adf16cc43283b38508e692cf045`, which is the exact merge
base. Before this change the branch was 92 commits ahead with stable aggregate
patch ID `2775812a3d74a11928074797378ffd28637683ac`; the worktree was clean.

The positive-check constructor path now uses the same wave application index as
rule-body and action reconstruction. It searches prior applications of the same
typed constructor, then accepts an observation alias only when every changed
child and output has a complete typed equality explanation. The check marker
continues to provide row identity only; it is never treated as a producer.

The checked-in `Wrap(A 1)` / `Wrap(B 1)` canary was changed from an expected
failure into a deterministic replay test. It retains the actual union and passes
ordinary replay plus the unchanged strict proof checker. A first implementation
used the hot path's deliberately deferred equality nodes and changed the
fail-closed diagnostic in the retained-subsume canary. That experiment was not
kept. The accepted implementation adds an observation-only `Explained` mode,
leaving the Eggcc-oriented deferred path unchanged.

Fresh validation on the accepted implementation:

- `cargo test -p egglog --test causal_slice`: 136 passed;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `make check`: passed, including formatting, warning-denying Clippy, Python
  checks/tests, the complete Rust workspace suite, doctests, and the DD timing
  summary gate;
- `cargo fmt --all --check`: passed;
- `git diff --check`: passed; and
- the focused observation-congruence and retained-subsume tests both passed
  before the complete causal-slice run.

The fresh release Hardboiled probe moved past the earlier positive-check `Call`
row error. Its current exact boundary is:

```text
retained equality TypedEndpoint { sort: "Type", ... } =
  TypedEndpoint { sort: "Type", ... }
causal slice v0 does not support a successful-union path containing an untyped
or opaque edge
```

This is not a container-version failure. It proves that one equality needed by
the retained observation is connected in the raw native commit forest but one
edge lacks a typed causal label. The exact edge class—rule-originated,
congruence/rebuild, or another opaque producer—has not yet been classified.

Container behavior is unchanged at this checkpoint. Fresh replay-safe `vec-of`
values remain supported. A same-ID container whose contents change during
rebuild is detected from its dirty outer ID and rejected because the trace still
lacks an immutable pre/post version and the equalities responsible for the
change. That rejection is currently program-global rather than retained-slice
local. Hardboiled has still not demonstrated that this container boundary lies
on its retained proof path.

No performance benchmark was run for this semantic checkpoint.

## Hardboiled replay-frontier checkpoint: 2026-07-21

This continuation started from `546a23a177fb1df65c22573fbf0770550ee76593`.
It adds exact registered-alias validation for variable-LHS rewrite roots,
supports multiple ordered replay-safe primitive calls in one head, and records
typed replay-safe primitive occurrences nested inside body constructor
lookups. Focused canaries replay each path in ordinary and unchanged strict
proof-testing modes.

The fresh Hardboiled run now passes the previously reported rewrite-root alias,
multi-primitive head, nested body `(* r-lanes x-lanes)`, and captured
`VecExpr` binding boundaries. It no longer panics by trying to reconstruct a
container through scalar `reconstruct_termdag_base`.

Its current exact failure is later and is not yet a container-rebuild result:

```text
positive check constructor `Call`
causal slice v0 does not support an exact match-time row without prior
constructor-row provenance
```

The observed command was:

```bash
target/release/egglog --mode no-messages -j 1 \
  --causal-slice --proof-testing \
  egglog/tests/hardboiled_conv1d_32.egg
```

Container status at this checkpoint:

- fresh replay-safe `vec-of` syntax remains supported with exact captured
  children and primitive receipts;
- the native rebuild trace reports only the stable outer container IDs whose
  contents changed, not pre/post contents, element remaps, versions, or the
  equality causes of those remaps;
- consequently, a witnessed dirty container still fails closed before final
  backward reachability, so even an irrelevant dirty witnessed branch can
  reject the program; and
- Hardboiled has not yet demonstrated that this versioning boundary is on its
  retained proof path. Its current stop is the positive-check `Call` row above.

The smallest sound container extension remains a structured rebuild receipt
plus a versioned `(sort, outer ID)` witness sidecar. A captured binding would
snapshot the version; a new version would depend on the prior version and the
exact child equalities or nested-container version changes. Runtime IDs would
remain internal and emitted replay would continue to use source syntax.

Validation for this checkpoint:

- `cargo test -p egglog --test causal_slice`: 136 passed;
- `make proof-tests`: 200 passed;
- `make check`: passed, including formatting, warning-denying Clippy, Python
  checks/tests, the complete Rust workspace suite, doctests, and the DD timing
  summary gate;
- the generated nested-body-primitive program is byte-stable and passes
  ordinary plus strict replay; and
- the fresh Hardboiled probe reaches the positive-check row-provenance error
  above.

No performance benchmark was run for this semantic continuation.

## Container witness checkpoint: 2026-07-21

This checkpoint is based on `26c4fd64be4f164e35d94c59df253511c71be995`.
It replaces the earlier conclusion that Hardboiled's first `VecExpr` value is
necessarily a mutable-container provenance problem.

Implemented and tested:

- replay witnesses may now invoke an exact registered primitive specialization
  only when it is `Pure`, provides a proof validator, and explicitly opts into
  the deterministic replay contract; packed replay evaluates that
  specialization through the ordinary runtime registry instead of a
  primitive-name allowlist;
- ordered registered heads preserve primitive, constructor, local-binding, and
  table-action order, including query filters followed by container-valued
  primitive results;
- a reduced ordinary/strict canary uses two query filters, creates a fresh
  `VecExpr` with `vec-of`, wraps it, creates a variable, and consumes that
  variable in a later retained rule;
- scalar equality filters, projected constructor variables, projected unions,
  fresh i64 arithmetic results, and fresh BigRat arithmetic results now have
  positive ordinary and unchanged strict-proof replay coverage; and
- an ordinary custom `Pure` primitive with a validator but without that replay
  capability is rejected; and
- the complete `egglog/tests/causal_slice.rs` binary passes all 133 tests.

The real Hardboiled fixture now advances past the original `vec-of` witness
failure in rules c326 and c315. Its next exact failure is unrelated to
containers:

```text
internal replay variable
`__causal_slice_v0_root_b15585_e15699_c145_r0` on rule
`__causal_slice_v0_rw_b15585_e15699_c145_r0` is not functionally determined
by a constructor lookup
```

That rule is the source rewrite at bytes 15585..15699:

```lisp
(rewrite x (Ramp x (Broadcast (IntImm b 0) l) 1)
  :when ((IsExpr x)
         (has-type x (Int b l))))
```

The current validator classifies the rewrite-lowering root alias as an
internal derived replay variable and applies the constructor-lookup-only
criterion before the later exact substitution/captured-binding seeding path
can resolve it. This is the next Hardboiled blocker.

Container contract at this checkpoint:

| Case | Status | Reason |
|---|---|---|
| Fresh immutable `vec-of` result in a captured head | Supported until a traced rebuild changes that container | exact child witnesses plus the explicitly replay-safe, Pure, proof-validating specialization reconstruct the result at the replay point |
| Other fresh explicitly replay-safe, Pure, proof-validating container constructors | Mechanism implemented; not fixture-complete | the generic registry path has no primitive-name allowlist, but each concrete registration asserts the replay contract and still needs focused semantic coverage |
| Stateful or opaque container primitive | Rejected | replay cannot treat an external state read as a pure syntax witness |
| Same outer container `Value` whose contents change during rebuild | Detected and rejected | the native trace carries exact dirty container IDs; without a historical version, the whole slice fails closed rather than reusing current contents |
| Versioned replay across a container rebuild | Unsupported | the outer runtime ID does not identify historical contents; support needs a versioned commit/rebuild receipt and dependency |

No performance benchmark was run for this semantic checkpoint. It establishes
admission progress, not a timing improvement. The previously recorded
strict-versus-causal measurements below therefore remain the latest
performance evidence.

Validation completed before the checkpoint commit:

- `cargo test -p egglog --test causal_slice`: 133 passed;
- reduced `equality_and_multiple_query_filters_feed_an_ordered_head_witness`
  canary: passed;
- adjacent ordered/nested/query primitive canaries: passed;
- explicit replay-capability rejection and dirty-container-rebuild canaries:
  passed;
- Hardboiled causal proof probe: advanced past `VecExpr`, then failed at the
  rewrite-root alias above;
- `make check`: passed, including Python format/lint/type/test gates, Rust
  formatting and warning-denying Clippy gates, the complete workspace test and
  doctest suite, and the DD timing-summary gate; and
- `git diff --check`: passed.

The exact pushed commit is recorded in the final handoff for this checkpoint.

## Active goal baseline: validator generality, Hardboiled, and Eggcc cost

The continuation goal started from clean commit
`9d89d9e5f656dd13cb0ef2ab56320174149088f4`; its runtime code is identical to
the validated implementation at `0d229525eca197dd3c59938b911736332952508c`.
No implementation change preceded these measurements.

The revised continuation resumed from that same HEAD with two existing
uncommitted files: this ledger and `egglog/src/causal_slice.rs`. The starting
diff was 487 insertions and 12 deletions (85 documentation lines and 414 Rust
lines). A live `gh pr view 23` query on 2026-07-21 reported PR #23 head
`4940be37429e7adf16cc43283b38508e692cf045`; that commit remains an ancestor of
the worktree and the base was not changed.

Focused baseline gates passed:

- `cargo test -p egglog --test run_rule --test causal_slice`: 146 passed;
- `cargo test -p egglog-experimental --test causal_slice`: 3 passed;
- `make proof-tests`: 200 passed.

Two independent release processes emitted byte-identical proof projections,
and every projection passed the unchanged strict proof checker:

| Workload | SHA-256 |
|---|---|
| Eggcc 2mm pass 1 | `66fa8e9ac6485f8567c69f8a581b4d0953602a5310c46d11fb4047748346537c` |
| Pointer analysis | `391fb1ddee90bb7ab77a3f949206f1394583d961d76a91a173d8fe7397021a88` |
| Luminal Llama | `2cd512285720a54619bffa7b4bd72236258edb5bdddb86b798ce378f6a3c71b1` |

The emitted sources and generator logs are under
`/tmp/causal-goal-baseline-9d89d9e5.v0T9IE`. Hardboiled exits 1 with the
expected first boundary: `Call` contains the opaque container sort `VecExpr`
in its positive check.

Fresh balanced six-round release comparisons used 120-second process
timeouts and reversed endpoint order within each of three pairs:

| Comparison | Eggcc wall ratio | Pointer wall ratio | Luminal wall ratio | Serial suite ratio |
|---|---:|---:|---:|---:|
| causal / strict | 1.30–1.32x | 0.129–0.131x | 0.0723–0.0778x | 0.348–0.367x |
| causal / native | 6.09–6.33x | 6.11–6.69x | 3.16–3.28x | 5.33–5.49x |

The append-only reports are
`/tmp/causal-goal-frozen-vs-strict-9d89d9e5.XXXXXX.jsonl` and
`/tmp/causal-goal-frozen-vs-native-9d89d9e5.Xbxlv7`. These are historical
diagnostics, not endpoints for another experiment: the revised goal explicitly
withdraws the old six-round and native-overhead cohorts.

Current performance question: does replacing the family-wide scan in
`congruent_app_availability` with a wave-local canonical application index
materially reduce Eggcc elaboration without changing replay semantics?

- H1: the repeated candidate scan is dominant. Prediction: a lazy index keyed
  by canonical child and output roots cuts generator elaboration substantially
  and produces byte-identical projections.
- H2: endpoint deduplication, snapshot cloning, or string-heavy witness
  bookkeeping dominates instead. Prediction: candidate counts shrink but
  generator elaboration and integrated wall time do not move enough to retain
  the index.
- Initial falsification gate: keep the patch only if all semantic/differential
  tests pass, emitted sources remain byte-identical, and Eggcc's integrated
  generator time improves by at least 20%. Later user steering simplified the
  final public comparison to one shared append-only `/tmp` report and one
  three-round strict `proof-testing` versus `causal-proof-testing` run. Cached
  rows are reused by default; `--force-run` is reserved for replacing noisy or
  contended samples. Native-overhead and separate causal A/B cohorts are no
  longer completion gates.

The first index experiment supports H1 and is retained. A wave-local lazy
index stores witness positions under canonical typed child endpoints and the
canonical output endpoint. It incrementally incorporates same-wave witnesses,
filters positions through the captured snapshot prefix, retries candidates
whose children initially lacked endpoints, preserves reverse insertion
preference, and still runs the original exact dependency construction on every
selected candidate. The old linear candidate enumeration remains only as a
`cfg(test)` differential oracle.

Three release generator runs at `/tmp/causal-index-eggcc.8C9MZ7` measured:

| Phase | Frozen baseline | Indexed | Point change |
|---|---:|---:|---:|
| traced native run | 1.296–1.312 s | 1.294–1.296 s | unchanged |
| elaboration | 5.851–5.871 s | 3.621–3.684 s | about 38% lower |
| generator total | 7.254–7.289 s | 5.023–5.088 s | about 30% lower |

All three Eggcc projections retained SHA-256
`66fa8e9ac6485f8567c69f8a581b4d0953602a5310c46d11fb4047748346537c`
and passed strict replay. Pointer and Luminal also remained byte-identical and
passed strict replay; Luminal's diagnostic generator point improved from
1.403 s to 1.317 s. The 50% elaboration target was not reached, but the
predeclared 20% integrated retention threshold was exceeded. This is a
three-sample phase diagnostic, not the final benchmark comparison.

An independent read-only review found no semantic blocker. The equality forest
is immutable while a wave uses the index, current-wave unions are published
only after every firing is elaborated, and the index is discarded before the
next wave. The differential canary now indexes one candidate, appends another
candidate in the same wave, and proves both snapshot and current selection
still match the linear oracle. Peak-memory cost remains unmeasured: keys own
typed endpoint sort strings and one position per indexed application. The
final strict-versus-causal report must include RSS before this is called a
finished performance result.

Checkpoint validation after the incremental-append canary:

- `cargo test -p egglog --lib causal_slice::tests`: 7 passed;
- `cargo test -p egglog --test causal_slice`: 126 passed;
- `cargo test -p egglog --test run_rule`: 20 passed;
- `cargo test -p egglog-experimental --test causal_slice`: 3 passed;
- `cargo clippy -p egglog --lib --tests -- -D warnings`: passed;
- `cargo fmt --all -- --check` and `git diff --check`: passed.

The previously recorded post-index `make proof-tests` run also passed all 200
tests; the subsequent change touched only the differential unit canary and this
ledger.

## Current checkpoint: positive-check proof projection

Commit `0d229525eca197dd3c59938b911736332952508c` is the current
validated implementation. This section supersedes the older source-retention
and performance claims later in this file; those sections remain as the
chronological experiment ledger.

The integrated proof path now performs:

```text
one ordinary reference-backend execution with native causal tracing
  -> one positive-check-rooted backward slice
  -> one statically closed source projection
  -> one unchanged strict proof-mode replay/check
```

The proof projection keeps every positive `(check ...)` at its original
observation boundary. Proof-testing desugars each retained check into the
existing `ProveExists` machinery, so generated source stays ordinary egglog
syntax rather than inventing a second proof command language. A focused test
with two checks produces two strict `CommandOutput::ProveExists` results.

Unlike the diagnostic/legacy replay API, the proof projection now removes:

- every original automatic schedule;
- causally unused rule applications and source facts;
- unused rule definitions and rulesets;
- unused relation, function, sort, and datatype declarations;
- individual unretained TSV input rows; and
- read-only `print-size` and no-file `print-stats` diagnostics.

It closes transitively over complete retained rules, checks, source actions,
schemas, datatype variants, globals, and every callable in a retained replay
witness DAG. Datatype commands remain atomic. The emitted program is reparsed,
audited for complete guarded replay, and resolved/typechecked without
executing initialization, automatic schedules, or replay heads.
Legacy `causal_slice_replay_program*` APIs intentionally keep the accepted
source envelope for debugging compatibility.

The Eggcc equality regression is also fixed. Every successful native union
receipt now advances a raw commit-order union forest, even when its equality
sort or causal label is unavailable. Typed explanation labels are stored
separately, and a retained path crossing an untyped edge fails closed. Equality
retained constructor-availability `Eq` nodes are resolved lazily during the
backward slice. This restores Eggcc while avoiding the earlier eager
constructor explanation-graph scan.

### Current six-workload admission result

One fresh release run of every named default workload used exact clean commit
`0d229525` and a 120-second timeout. The append-only report is
`/tmp/causal-support-0d229525-20260721.jsonl`.

| Workload | Strict treatment status | Integrated causal proof | Current result |
|---|---|---|---|
| Eggcc 2mm pass 1 | passes | passes | supported; one retained firing |
| Pointer analysis | passes | passes | supported; one retained firing |
| Luminal Llama | passes | passes | supported; one retained firing |
| Math microbenchmark | runs, but has no proof observation | rejects | no positive check, so there is no proof-slice root |
| Hardboiled conv1d | passes | rejects | retained dynamic `VecExpr` container witness is unsupported |
| Herbie | existing strict proof panics | rejects | strict baseline is already invalid; slicer additionally lacks exact prior syntax provenance for the selected `Num` row |

Thus the proof slicer succeeds on 3/6 default workloads, or 3/4 workloads
that both have a positive proof root and pass the existing strict checker.
Failures are explicit rather than plausible-looking fallback programs.

### Current end-to-end performance

Six fresh alternating-order release rounds compared the complete integrated
`causal-proof-testing` process with unchanged `proof-testing` on the three
supported proof workloads. Build time is excluded; causal wall time includes
the traced ordinary run, elaboration, source emission/typechecking, and strict
replay/check. The report is
`/tmp/current-causal-vs-strict-0d229525-20260721.jsonl`.

| Workload | Strict mean | Causal mean | Wall ratio, 95% CI | Strict mean RSS | Causal mean RSS | RSS ratio, 95% CI |
|---|---:|---:|---:|---:|---:|---:|
| Eggcc | 9.33 s | 13.80 s | 0.674–2.73x | 731.8 MiB | 454.7 MiB | 0.572–0.680x |
| Pointer | 610.5 ms | 68.7 ms | 0.0503–0.353x | 113.7 MiB | 22.4 MiB | 0.194–0.200x |
| Luminal | 40.16 s | 1.81 s | 0.0308–0.0703x | 1,477.5 MiB | 216.2 MiB | 0.113–0.207x |
| Serial three-file total | 50.10 s | 15.68 s | **0.163–0.514x** | not additive | not additive | — |

The serial-total point ratio is 0.313x strict proof time, a 68.7% reduction for
this admitted three-workload cohort. Pointer and Luminal are clear wins. Eggcc
is not yet a time win: its interval includes parity and regression, although
its RSS is consistently lower. The machine was noisy, particularly for Eggcc
and full Luminal proofs, so the confidence intervals—not the fastest
individual samples—are the result.

### Current total cost versus ordinary native execution

A separate fresh, balanced six-round cohort compared the complete integrated
causal process with ordinary reference-backend execution at the same exact
commit. This is the production-overhead comparison; report:
`/tmp/current-causal-vs-native-0d229525-20260721.jsonl`.

| Workload | Native mean | Causal mean | Wall ratio, 95% CI | Native mean RSS | Causal mean RSS | RSS ratio, 95% CI |
|---|---:|---:|---:|---:|---:|---:|
| Eggcc | 1.265 s | 7.659 s | 5.73–6.42x | 121.6 MiB | 446.7 MiB | 3.57–3.78x |
| Pointer | 8.02 ms | 47.83 ms | 5.65–6.30x | 10.2 MiB | 22.3 MiB | 2.18–2.22x |
| Luminal | 457.5 ms | 1.505 s | 2.93–3.67x | 118.7 MiB | 218.5 MiB | 1.82–1.86x |
| Serial three-file total | 1.731 s | 9.212 s | **5.08–5.58x** | not additive | not additive | — |

The serial-total point ratio is 5.32x native, so the proposed approximately
2x-native target is not met. This cohort ran during a quieter interval than the
strict-proof cohort above; compare ratios within each balanced cohort and do
not combine their absolute means. The result is still informative: source
projection can remove most strict-proof cost while tracing, elaboration, and
replay remain several times ordinary native execution.

The source and phase split explains the difference:

| Workload | Pending / retained | Source bytes, original -> projected | Traced run | Elaboration | Backward slice | Proof-only replay point |
|---|---:|---:|---:|---:|---:|---:|
| Eggcc | 312,740 / 1 | 254,062 -> 149,101 | 1.51 s | 7.23 s | 15.2 ms | 0.66 s |
| Pointer | 706 / 1 | 5,958 -> 853 | 20.1 ms | 19.6 ms | 42.8 us | below 0.01 s |
| Luminal | 12,568 / 1 | 455,788 -> 4,328 | 496.7 ms | 1.01 s | 1.48 ms | 0.07 s |

These are serialized diagnostic point measurements, not additional A/B
confidence intervals. They show that source projection solved the old Luminal
and Pointer proof-cost bottleneck. Eggcc's projected proof is also cheap;
profiling attributes most causal elaboration to scanning constructor witness
candidates while resolving application availability. The next profile-guided
performance hypothesis is a wave-local canonical child-tuple index rather than
a scan of every `(sort, function)` witness instance.

### Full-proof history comparison

The public runner can compare exact commits directly. Four rounds, with both
endpoint orders represented, compared unchanged strict `proof-testing` at PR
#23 head
`4940be37429e7adf16cc43283b38508e692cf045` and `0d229525` on the five
strict-compatible workloads other than Herbie. Mean serial suite time was
41.08 s at PR #23 and 41.43 s now; the ratio CI was 0.743–1.40x. In other
words, no change was detected in the five-file serial suite total, but the wide
interval does not establish equivalence and permits a meaningful speedup or
regression. Pointer is individually faster and Hardboiled individually slower.
The same-commit causal-versus-strict comparison isolates the measured
projection effect, while the proof encoding and checker remain unchanged. Report:
`/tmp/pr23-vs-current-strict-support-20260721.jsonl`.

### Current architectural conclusion

The technique has clear promise for workloads where a small positive
observation has a small dynamic and static support: two of three admitted real
fixtures are substantially faster than strict proof mode and all three use
substantially less peak RSS than strict proof mode. It is not generally
complete, it is still 5.08–5.58x ordinary native on the admitted cohort, and
Eggcc demonstrates that tracing and elaboration can consume the saved proof
time.

The guarded same-prestate packed batch is already the right replay primitive.
The semantic generality order is native evidence first:

1. carry exact source-atom/table/generation/row evidence through factorized
   final-match expansion, and attach composite/shadow dependency lineage to
   decomposed intermediate rows;
2. add selected-branch provenance for pure `old`, `new`, `min`, and `max`
   merges, then a dynamic-read/effect trace contract for custom merges;
3. attach colliding-row and changed-child causes to congruence/rebuild unions;
4. add immutable version witnesses for one concrete container presort;
5. add delete receipts, tombstones, subsume visibility, and lookup-miss
   dependencies; and
6. replace the primitive name whitelist with an opt-in deterministic replay
   capability describing proof validation, witness rendering, dynamic reads,
   and effects.

Arbitrary stateful Rust primitives, custom callbacks, containers, absence,
and I/O cannot soundly become automatic by default; each needs that evidence
contract or must continue to fail closed.

The spike's monolithic source model is also a maintainability boundary. Before
adding many more semantic families, the native evidence capability and stable
source-to-registered-rule mapping should become shared interfaces owned by the
existing compiler/runtime, rather than additional workload-shaped branches in
the slicer. Extracts, nested/cross-region scopes, includes, and reproducible I/O
belong to a later-work bucket after the evidence contract above.

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

## Pointer fixture result

`benchmarks/pointer-analysis-small.egg` is implemented and tested end to end
with its checked-in scalar fact directory:

- one ordinary/native traced execution produces 706 pending firings;
- 600 firings have an effective row, constructor, or union effect;
- the combined positive observation retains 1 firing;
- the proof projection contains one packed fire with complete bindings and an
  exact-one guard, and no original `(run 100000)` schedule;
- ordinary replay and unchanged strict proof replay/check both pass;
- proof projection drops `print-size`; legacy replay preserves it as a
  read-only diagnostic without adding a slice root.

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

### Historical Luminal source-retention result

This subsection records the pre-projection checkpoint at `53230e7d9fcb`.
The current proof projection and measurements are in the opening checkpoint;
in particular, the old all-source bottleneck described here has been removed.

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

### Historical print-prefix Math result

This subsection records the legacy diagnostic projection. The current
positive-check proof projection intentionally rejects this fixture because it
has no positive check and therefore no proof-slice root.

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
egglog::causal_slice::causal_slice_replay_program(filename, source)
egglog::causal_slice::causal_slice_proof_replay_program(filename, source)
```

Each has a fact-directory form, and the replay APIs also have a configured
`EGraph` form. `causal_slice_program*` retains the diagnostic full transcript;
`causal_slice_replay_program*` emits the legacy source envelope without that
discarded transcript; and `causal_slice_proof_replay_program*` emits the
positive-check-rooted, statically closed proof projection.

Executable spike:

```bash
cargo run -p egglog --example causal_slice -- SOURCE.egg
cargo run -p egglog --example causal_slice -- --full SOURCE.egg
cargo run -p egglog --example causal_slice -- --proof-projection SOURCE.egg
```

The first form writes the legacy slice to stdout; `--full` writes every
captured grounding; `--proof-projection` writes the source-pruned proof
slice. All forms write trace/event statistics to stderr. Unsupported source
returns a source-located diagnostic.

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
- The proof projection retains only the declarations, complete rule
  definitions, source facts, scope boundaries, and positive checks in the
  transitive static/causal closure. Legacy replay intentionally preserves the
  accepted source envelope for diagnostic compatibility.
- Every packed replay fire carries every admitted source-variable binding and
  is validated with exact-one semantics before any head in its batch executes.
- Emitted source is reparsed and recursively audited for automatic schedules,
  partial bindings, selectors, changed rule definitions, and unsafe literals.
- Proof-oriented output is additionally resolved and typechecked without
  executing initialization, automatic schedules, or replay heads; unknown
  closed witness callables therefore fail generation.

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

Current proof projection:

```lisp
(relation Seed (i64))
(relation Mid (i64))
(relation Goal (i64))
(ruleset derive)
(rule ((Seed x)) ((Mid x)) :ruleset derive :name "seed-to-mid")
(rule ((Mid x)) ((Goal x)) :ruleset derive :name "mid-to-goal")
(Seed 2)
(run-schedule
  (run-rule-batch
    :witnesses (2)
    :groups (("seed-to-mid" (x)))
    :fires ((0 0))))
(run-schedule
  (run-rule-batch
    :witnesses (2)
    :groups (("mid-to-goal" (x)))
    :fires ((0 0))))
(check (Goal 2))
```

Each packed fire has complete bindings and is guarded by the batch's exact-one
validation before effects. The legacy complete transcript contains six
chronological guarded firings. The proof projection removes the value-1 source
fact and chain, the `Irrelevant` declaration and rule, and both irrelevant
firings.

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
| positive-check proof source projection | implemented and tested | causally unused source facts, individual TSV rows, rules/rulesets, declarations, datatypes, and diagnostics are removed; retained static dependencies close transitively and the output is typechecked |
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
| delete | rejected | delete outcomes, tombstones, and absence provenance are absent; sequential replay diverges |
| subsume | narrow constructor alias only | complete-head replay admits the tested constructor subsume that aliases a live body constructor and accompanies an independent union; general visibility state and later reads reject |
| constructor lookups | implemented for exact captured syntax | lookup availability plus output equality path are retained; equal-but-different body syntax needs exact native row evidence |
| exact single-output `:merge new` functions | implemented and tested | exact lookup rows, proposal origins, `Inserted`/`Replaced`/`NoOp` commit receipts, pre-wave sidecars, rebuild migration, and complete-head replay pass focused ordinary/strict canaries and Luminal |
| custom merges and other mutable state | fresh source insertion only; dynamic replacement rejected | recognized BigRat min/max source initialization is admitted when no prior row competes; selector choice, callback reads/effects, tombstones, visibility, and general mutation semantics remain absent |
| constructor witnesses | implemented and tested | source, rule-created, standalone, nested, constructor-union, BigInt/BigRat, and closed-global canaries |
| mutually recursive `datatype*` | implemented and tested | original parsed syntax is preserved; all mutually recursive sorts and constructors are modeled; nested constructor replay passes ordinary and strict proof modes; unsupported inline presorts fail closed |
| rule-head BigRat arithmetic | implemented and tested narrowly | one replay-safe binary `+`, `-`, `*`, `/` or unary `neg`, `abs`, `floor`, `ceil`, `round` application per complete head; exact native evidence and a pre-wave result witness are required |
| query/body primitives | implemented for one deterministic call | successful query `Instr::External` lanes carry exact origin/arguments/result; packed replay validates complete post-filter bindings; i64 `+`, BigRat `pow`/`log`, and BigRat `<`/`>` pass ordinary and strict canaries; arbitrary externals remain rejected |
| dynamic source globals | implemented for closed immutable constructor globals | exact native pre-wave endpoints are captured once per wave; changed endpoints retain their successful-union path; local/global shadowing fails closed |
| inert custom-function and `UnstableFn` schemas | retained only when needed | the proof projection drops unused schemas; a retained inert schema is safe, while every dynamic callback/container value remains rejected without provenance |
| rewrite/birewrite replay | implemented and tested | deterministic parsed lowering, stable source mapping, projected binding aliases, ordinary and strict canaries |
| print-only observations | legacy conservative Prefix only | legacy replay can retain every effective preceding event; the proof projection requires a positive check and rejects print-only Math rather than treating diagnostics as proofs |
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

The current positive-check proof projection succeeds on three of the six
named default workloads. It succeeds on three of the four workloads that both
pass unchanged strict proof mode and contain a positive proof root.

| Workload | Admission | Current first boundary or result |
|---|---|---|
| `eggcc-2mm-pass1.egg` | passes | 312,740 pending / 1 retained; proof-only replay is cheap, but witness-availability elaboration currently makes the integrated time interval include a regression |
| `pointer-analysis-small.egg` | passes | 706 pending / 1 retained; source is 853 bytes and six-round wall ratio is 0.0503–0.353x strict proof |
| `luminal-llama.egg` | passes | 12,568 pending / 1 retained; source is 4,328 bytes and six-round wall ratio is 0.0308–0.0703x strict proof |
| `math-microbenchmark.egg` | proof projection rejects | no positive `(check ...)`; the legacy print-prefix transcript remains available only as a diagnostic replay |
| `hardboiled_conv1d_32.egg` | rejects | retained `Call` uses an opaque `VecExpr`; immutable versioned container witnesses are missing |
| `herbie.egg` | strict baseline fails and causal rejects | unchanged strict proof panics; the causal path also lacks prior replayable syntax provenance for the selected exact `Num` row |

The implementation has therefore moved past source retention: positive-check
projection now drops causally and statically unused source. Remaining
admission failures are native witness/provenance gaps. Remaining performance
work is primarily elaboration and trace lifetime, not backward traversal or
proof replay on the projected programs.

## Validation status

Current positive-check proof-projection checkpoint at
`0d229525eca197dd3c59938b911736332952508c`:

- focused proof-projection tests: 5 passed;
- `cargo test -p egglog --test causal_slice`: 126 passed;
- integrated CLI ordinary/strict causal replay tests passed;
- `make proof-tests`: 192 reference plus 8 experimental fixtures passed;
- `make check`: passed, including lockfile validation, Ruff, mypy, workspace
  formatting and Clippy (including DD), 179 Python tests, the full Rust
  workspace, 764 file fixtures, experimental/DD tests, and doctests;
- `make benchmark-smoke`: passed with two fresh successful public-runner rows;
- six default-workload admission runs completed from exact clean commit
  `0d229525`; three causal projections passed and all unsupported cases
  returned explicit diagnostics;
- six balanced alternating-order rounds completed for the supported causal
  versus strict cohort, six more completed for causal versus native, and four
  rounds with both endpoint orders represented completed for strict PR #23
  versus current;
- two independent proof-projection processes emitted byte-identical Bronze
  source with SHA-256
  `7b593ace79557e361fb184b286feaddd3d90157ac6ae34b4dd2ef772f29f11b9`,
  and strict proof replay passed;
- the implementation diff passed `git diff --check` before commit.

The entries below are the chronological validation ledger for earlier
checkpoints; any older line saying a full gate was pending is historical.

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

- Implemented/tested fact: one traced native execution, one positive-check
  backward slice, one transitive static source projection, and one unchanged
  strict proof replay pass end to end on Eggcc, Pointer, and Luminal. Original
  computation schedules are absent, every replay firing is guarded, and each
  retained check enters the existing `ProveExists` path.
- Implemented/tested fact: the proof projection removes unused individual TSV
  rows, source actions, rules/rulesets, schemas, datatypes, and diagnostics.
  Complete retained rules and witness callables close transitively over their
  static dependencies, and emitted source is reparsed and typechecked without
  running initialization, schedules, or replay heads. Legacy replay preserves
  its prior source envelope.
- Implemented/tested fact: successful union receipts advance an immutable raw
  commit-order forest independently of typed causal labels. A retained typed
  path explains through exact dependencies; a path crossing an untyped edge
  rejects rather than disappearing or acquiring an invented cause.
- Implemented/tested fact: closed BigInt/BigRat globals, narrow deterministic
  primitives, exact `:merge new`, scoped regions, and conservative rebuild
  Prefix support remain admitted under their documented contracts. General
  custom callbacks, containers, absence, delete, and subsume visibility remain
  rejected.
- Empirical measurement: on the three admitted positive-proof workloads, six
  alternating-order rounds give a serial total of 15.68 s causal versus 50.10 s
  strict, or 0.313x; the suite ratio 95% CI is 0.163–0.514x.
- Empirical measurement: Pointer is 0.0503–0.353x strict wall time and
  0.194–0.200x strict RSS; Luminal is 0.0308–0.0703x strict wall and
  0.113–0.207x strict RSS. Eggcc's wall interval is 0.674–2.73x and therefore
  does not establish a time win, while its RSS improves to 0.572–0.680x.
- Empirical measurement: strict proof execution at current versus exact PR #23
  has a five-workload suite ratio CI of 0.743–1.40x. No suite-total change was
  detected, but this interval does not establish equivalence. The same-commit
  causal/strict comparison isolates the projection treatment, and the proof
  engine/checker implementation itself is unchanged.
- Empirical measurement: a separate balanced six-round cohort gives 9.212 s
  causal versus 1.731 s native serial total, or 5.32x; the suite ratio CI is
  5.08–5.58x. The approximately-2x-native target is not met.
- Implemented/tested after this historical checkpoint: a canonical
  child-tuple witness index removes about 38% of Eggcc elaboration in the
  three-sample diagnostic recorded at the top of this file.
- Plausible but untested: a streaming wave sink may reduce trace-memory overlap;
  exact match-premise transport may unlock several currently rejected
  equal-row, decomposed-join, and mutable-read cases.
- Falsified: general complete match bindings, partial-bind replay of projected
  firings, naked `RowId` stability, one preferred syntax as constructor-body
  provenance, globally epoch-free equality endpoints, standalone
  pre-filter `:expect`, deriving a successful query result from `RuleMatch`
  alone, and general sequential-wave equivalence.

## Historical recommended next patches

> This ordering predates the active-goal section at the top of the file. Item
> 1 is complete, its proposed six-round rerun is withdrawn, and the remaining
> work is governed by the current capability-interface and Hardboiled plan.

Source projection, guarded shared-prestate replay, scalar inputs, immutable
constructor/global witnesses, direct unions, and exact `:merge new` state are
implemented. The immediate performance experiment comes first; subsequent
items follow the semantic generality order:

1. index constructor-witness availability by canonical child tuple within each
   wave, replacing the full `(sort, function)` candidate scan that dominates
   Eggcc elaboration; then repeat the exact six-round cohort;
2. carry `TracePremise { atom, table, generation, row_id, raw_row }` through
   factorized final-match expansion, preserving source-atom identity, and add
   composite/shadow dependency lineage to decomposed intermediate rows;
3. add selected-branch provenance for pure `old`, `new`, `min`, and `max`
   merges, followed by precise colliding-row/child-equality rebuild causes and
   relation-row rekey transitions;
4. implement one immutable versioned `Vec` witness path to establish the first
   Hardboiled container vertical slice;
5. add delete receipts and tombstones, then separate subsume visibility and
   lookup-miss dependencies before attempting negative checks;
6. replace the primitive name whitelist with an opt-in replay capability for
   determinism, proof validation, witness rendering, dynamic reads, and
   effects;
7. stream or compact completed native waves so raw matches do not coexist with
   the complete elaborated arena; and
8. expose generator phase timings and retained-event counts in public
   benchmark summaries without changing the end-to-end headline metric.

Before broadening further, extract the evidence capability and stable
source-mapping model into shared compiler/runtime interfaces and split the
monolithic slicer by ownership. Extract observations, nested/cross-region
scopes, include expansion, and reproducible external I/O remain later work.

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
53. `8756cf4a` — record the scoped/rebuild validation checkpoint;
54. `2b185b81` — add stable named selectors for all six default workloads to
    the public benchmark runner; and
55. `0d229525` — repair raw/typed equality-forest ordering and add the
    positive-check-rooted, statically closed proof source projection.

The final diff is confined to reference native tracing/commit receipts,
frontend causal treatment plumbing, the causal-slice module/example/tests, and
`.codex/causal-slice-v0/`. The proof encoding and checker are unchanged.
At the time this historical commit list was written, nothing had been pushed;
the latest checkpoint and final handoff supersede that repository-state note.
