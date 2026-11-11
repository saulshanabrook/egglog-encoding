# DD backend performance investigation

Status: complete

## Conclusion

Evidence points to two distinct mechanism families behind DD's slowdown, with
their relative contribution varying by workload:

1. Its physical join is weaker. DD uses a static left-deep chain in source atom
   order. Native defaults to Generic Join, can tree-decompose a query, pushes
   constraints into indexes, and dynamically orders commuting stages. A
   controlled atom-order experiment produced a 2.61x bad/good wall-time ratio
   (61.7% lower with the good order) and a 36.8x RSS ratio at N=1,500 without
   changing the relational semantics; both variants passed the same two checks.
   A six-round reverse-order control at N=500 confirmed the effect.
2. Considerable time is spent around the relational join. On the real pointer
   benchmark, 66% of sampled CPU was under DD's broad `drive_to` path and 55.6%
   of all exclusive samples were on Timely stacks. Progress/frontier
   propagation was the largest measured named component. Fixed 192-byte
   dataflow rows, per-ruleset dataflows, whole-map snapshot synchronization,
   full-table scans to rebuild temporary host indexes, and eager materialization
   add further state and work.

For ordinary seminaive rules, DD is not simply recomputing every join from
scratch: it retains arrangements and feeds signed deltas across epochs. One
caveat is that production DD does not inspect `RuleSpec.seminaive`, so it does
not honor an explicitly naive rule's mode distinction. The performance problem
is the physical plan and the amount of control, representation, and
host-boundary work around the incremental core.

Proof generation is not the root cause. The same large gap exists in `term`
mode, and DD always uses term encoding. Proofs add more work and state, but they
do not explain DD's base disadvantage.

## Source and environment

- Branch: `codex/dd-backend-slowdown-investigation`
- Revision: `ce6a69fa94c185275a820c3e9bb12d54f3b37ce4`
  (`origin/main` fetched on 2026-07-15)
- Release executable SHA-256:
  `30f6581772538539588b675636e9eefe2bb4b6e7d5706c88f488c072620abf05`
- Machine: Apple M4, arm64, macOS 26.3.1, 10 logical CPUs, 16 GiB RAM
- Every benchmark process used `-j 1` and `RUST_LOG=error`. Native and DD were
  therefore compared at the same thread count.
- All rows were forced fresh. Reports were written under `/tmp`; the repository
  benchmark cache was neither read nor appended.
- The worktree is marked dirty only because this report is untracked. There is
  no source-code change, and all benchmark JSONL reports use the release
  executable hash above. The separate symbolized profile binaries have hashes
  `65d6317bba529c45041edf61ed96ada0b82af0e99ce5999ecdf7d81e2b3da379`
  (DD, built with `dd-backend`) and
  `b9e8158cd47436cacf3f0fc1c94f7abae0b2e2d0c77f80a39001815e7929e95b`
  (native, built without that feature).

## Does DD run the existing benchmark suite?

Not by default. `bench.py` defaults to `main`; DD must be selected explicitly
with `--backend dd`. The benchmark-smoke CI job also selects only main/off, and
the CodSpeed benchmark constructs native experimental EGraphs. There is no
routine DD performance signal in CI.

When DD is requested explicitly, two of the six default workloads currently
complete in both term and proof modes: pointer analysis and Herbie. The other
four are a mixture of true slowness, unsupported container actions, and a
resource failure rather than one common timeout problem.

| Default workload | DD term | DD proofs | Classification |
| --- | ---: | ---: | --- |
| Math microbenchmark | >120s | >30s | Genuine performance timeout in term mode |
| Bounded eggcc 2mm | failure at 29.9s, 4.12 GiB | >30s | Term eventually reaches unsupported `@container_rebuild` |
| Pointer analysis | 0.658s | 0.873s | Runs |
| Hardboiled | failure at 1.044s | failure at 1.133s | Unsupported `@container_rebuild1` |
| Luminal | `SIGKILL` at 86.7s, 5.88 GiB | >30s | Resource failure; likely memory pressure, but the signal alone does not prove OOM |
| Herbie | 1.300s | 1.900s | Runs |

The pointer, Hardboiled, and Herbie values are one-round results from the same
30-second six-workload probe. Math, bounded eggcc, and Luminal received an
additional term-only run with the runner's standard 120-second limit. A `>30s`
proof entry means only that the proof cell exceeded the triage bound; it was not
rerun after the corresponding term cell failed to complete successfully.

Three small CodSpeed fixtures (`rw-analysis`, `integer_math`, and `resolution`)
also completed under DD in both modes in 56--113 ms. Those whole-process runs
are startup-dominated canaries, not stable performance comparisons.

The DD parity harness is consistent with an incomplete performance envelope:
it says debug DD is impractically slow and skips a `HANG` list even in release,
including the full `math-microbenchmark.egg`, `eggcc-2mm.egg`, and
`resolution.egg`. The default benchmark's bounded
`eggcc-2mm-pass1.egg` is a different fixture. Fresh runs also found unsupported
container-action failures in Hardboiled and bounded eggcc that are not named in
the harness's current `KNOWN_UNSUPPORTED` list. Conversely, the direct
resolution canary now completes quickly, so its `HANG` entry is stale or
specific to the harness's appended-output execution path.

## Stable measurements on the two successful default workloads

Six forced-fresh rounds, with 95% confidence intervals for ratios:

| Workload / mode | Native mean | DD mean | DD/native wall time | DD/native peak RSS |
| --- | ---: | ---: | ---: | ---: |
| Pointer / term | 0.1673s | 0.6018s | 3.60x `[3.51, 3.69]` | 2.36x `[2.34, 2.38]` |
| Pointer / proofs | 0.3815s | 0.7817s | 2.05x `[1.98, 2.12]` | 1.65x `[1.64, 1.65]` |
| Herbie / term | 0.1748s | 1.2440s | 7.12x `[6.24, 8.27]` | 7.24x `[7.17, 7.31]` |
| Herbie / proofs | 0.3832s | 1.8931s | 4.94x `[4.76, 5.13]` | 3.36x `[3.34, 3.38]` |

Herbie's first native/term sample was a first-sample outlier (0.2218s versus
0.1624--0.1673s for the other five), so its interval is wider. The conclusion
does not depend on that point.

Within DD, proofs cost 1.26--1.34x term on pointer and 1.46--1.58x term on
Herbie. The smaller DD/native ratio in proof mode is not a DD proof advantage;
native's proof treatment adds a larger fraction to its much faster term
baseline. DD remains slower in both treatments.

## Join-algorithm evidence

### Source mechanism

DD's `plan_join` preserves emitted atom order, and `FusedDdJoin::build` starts
from atom 0 and applies `join_core` to atoms 1 through N. A later atom is
arranged only by variables already bound on the left. If none are shared yet,
the key is empty and DD materializes a Cartesian intermediate. Constants and
repeated-variable filters on later atoms are applied only after candidate pairs
reach the remapping closure.

Native instead defaults to worst-case-optimal Generic Join, can tree-decompose
eligible queries, creates constant-filtered subsets, and can reorder commuting
stages according to current subset sizes.

Relevant source locations:

- DD planning/build: `egglog-experimental/dd/src/dd_native.rs:176`, `:507-564`
- DD later-atom filtering: `egglog-experimental/dd/src/dd_native.rs:696-802`
- Native planning: `egglog/core-relations/src/free_join/plan.rs:1-45`, `:390-410`
- Native runtime ordering: `egglog/core-relations/src/free_join/execute.rs:2286`

### Controlled atom-order probe

Two temporary programs differed only in the order of a three-atom rule:

```lisp
; bad: the first binary join is disconnected
(R x y) (S z w) (T y z)

; good: every next atom shares a variable
(R x y) (T y z) (S z w)
```

All three relations contained the same N identity rows. The reordered bodies
have the same relational semantics, and both programs passed the same checks.

| N | Backend | Bad order | Good order | Bad/good wall | Bad/good RSS |
| ---: | --- | ---: | ---: | ---: | ---: |
| 500 (6 rounds) | Native | 0.1109s, 42.7 MiB | 0.1122s, 42.9 MiB | 0.989x `[0.963, 1.015]` | 0.996x `[0.991, 1.001]` |
| 500 (6 rounds) | DD | 0.3212s, 387.9 MiB | 0.1646s, 36.2 MiB | 1.95x `[1.81, 2.10]` | 10.70x `[10.53, 10.88]` |
| 1,500 | Native | 0.2740s, 113.8 MiB | 0.2757s, 113.5 MiB | 0.99x | 1.00x |
| 1,500 | DD | 2.1184s, 3.18 GiB | 0.8114s, 88.5 MiB | 2.61x | 36.8x |

The six-round N=500 run listed the good program first, reversing the original
collection order; the effect persisted with tight intervals. Tripling N grew
bad-order DD RSS about 8.4x, close to the expected quadratic intermediate
trend, while good-order DD RSS grew about 2.4x. Native showed no material
atom-order difference in these measurements. The N=1,500 rows are point
estimates, and that fixture's explicit checks cover shared outputs 0 and 499
rather than all 1,500 possible outputs.

This synthetic probe deliberately exposes a worst case. It proves source-order
sensitivity and the intermediate-state mechanism, but does not show that the
same Cartesian shape dominates every real benchmark. Even with the good order,
DD was 2.94x slower than native at N=1,500, so join ordering is not the entire
gap.

## What the real-workload profile says

Optimized Samply profiles used the same pointer workload and term treatment.
They were separately built: DD includes the `dd-backend` feature and native does
not, so their normalized CPU comparison is directional rather than a fully
matched binary comparison. DD calibration selected 13 iterations; the resulting
profile observed 7.866 CPU-seconds, or about 0.605 per iteration. Native selected
30 iterations; its profile observed 4.02 CPU-seconds, or about 0.134 per
iteration. The roughly 4.5x normalized CPU gap agrees directionally with the
release wall-time result.

Selected DD sample attribution:

| Stack/path | Sampled CPU | Interpretation |
| --- | ---: | --- |
| Timely stacks, exclusive bucket | 55.6% | Progress, scheduling, and dataflow runtime are the largest measured family |
| Differential Dataflow stacks, exclusive bucket | 14.4% | Arrangements/operators beyond the Timely frames |
| `FusedDdJoin::step` / `drive_to`, inclusive | 67.0% / 66.3% | Most time occurs while advancing the persistent dataflow |
| `propagate_pointstamps`, inclusive | 39.2% | Frontier/progress tracking is a major real-workload cost |
| Timely `Tracker::propagate_all`, inclusive | 28.9% | Same conclusion at a lower frame |
| `FusedDdJoin::build`, inclusive | 3.3% | Rebuilding the worker is not the main pointer cost |
| host `HashMap::eq`, inclusive | 4.5% | Full-state comparison is visible but not dominant here |

Inclusive rows overlap and must not be added. The important distinction is that
the actual pointer workload spends most CPU inside the join-driving phase, but
the largest named work there is Timely progress/frontier machinery around the
operators, not construction of the join plan. Native's top self-cost was its
`Database::merge_all` path and it has no corresponding Timely progress layer.

## Additional costs around the join

These are source-confirmed and plausibly important across workloads even where
pointer's profile did not rank each one first:

1. **Fixed-width dataflow state.** Every relation/binding row and key flowing
   through the DD dataflow is a zero-padded `[u32; 48]`, or 192 bytes. An
   arranged `(key, row)` starts around 384 bytes before trace overhead,
   regardless of logical arity. The authoritative host mirror is
   variable-width.
2. **Per-ruleset duplication.** Each exact rule-id set retains its own worker,
   input integral, arrangements, and fed snapshot. Term/proof maintenance
   rulesets do not share one global indexed database as native does.
3. **Full-state synchronization.** Before a ruleset runs, DD compares current
   and prior version maps. A changed map causes full old/current scans and a
   clone of the complete current map; even unchanged input pays whole-map
   equality. The incremental dataflow therefore has a non-delta-proportional
   host feed (`egglog-experimental/dd/src/interpret.rs:292-340`).
4. **Eager host materialization.** DD captures output deltas into a host hash
   map, materializes every positive binding as a hash-map environment, then
   interprets primitives and heads (`dd_native.rs:650-667`,
   `interpret.rs:365-445`). Guards cannot reduce an intermediate inside the DD
   join if they execute only after it.
5. **Missing persistent host indexes.** A first write or RHS lookup can rebuild
   a complete key map, and replacing a key scans the relation. Native keeps
   persistent primary-key and index objects, although a secondary index can
   itself require a full refresh after a major generation change
   (`egglog-experimental/dd/src/lib.rs:503-581`, `:967-985`;
   `egglog-experimental/dd/src/interpret.rs:584-618`;
   `egglog/core-relations/src/table/mod.rs:537-550`;
   `egglog/core-relations/src/hash_index/mod.rs:43-89`).
6. **Retraction churn.** Rebuild freshness can be represented as a removal epoch
   followed by an insertion epoch. DD propagates negative join results even
   though negative bindings do not fire host heads.

The one-peer Timely allocator is in-process; it does not spawn an OS worker for
each ruleset and does not serialize messages on the controlled one-thread path.
Final EGraph destruction is excluded from CLI timing. Those mechanisms do not
explain the measured gap.

## Hypothesis ledger

| Hypothesis | Result | Evidence |
| --- | --- | --- |
| DD's join algorithm is weaker | Confirmed mechanism; real-workload share unresolved | Source-order left-deep plan plus the 2.61x time / 36.8x RSS atom-order effect |
| Runtime work around the join matters | Observed candidate bottleneck | 55.6% exclusive Timely samples and 39.2% inclusive pointstamp propagation on pointer; `drive_to` also encloses all dataflow work |
| Worker construction is the dominant real-pointer cost | Rejected | `FusedDdJoin::build` was only 3.3% inclusive |
| Full-state host synchronization is the dominant pointer cost | Narrowed | Present, but `HashMap::eq` was 4.5% inclusive; it may rank higher on other rule/state shapes |
| DD recomputes every seminaive join from scratch | Rejected with caveat | Input arrangements persist and advance with signed deltas, but DD does not honor explicitly naive `RuleSpec.seminaive` mode |
| Proof generation causes the base gap | Rejected | DD term alone is 3.5--3.7x slower on pointer and 6.2--8.3x on Herbie |
| Native's parallelism explains the comparison | Rejected for these runs | Both runner paths used `-j 1` |
| Startup/debug/teardown explains the long cases | Rejected | Release builds; seconds-to-120s gaps; teardown excluded. Startup only confounds tiny canaries |

## Priorities suggested by the evidence

1. Add DD phase counters/timing to separate snapshot diff, `drive_to`, progress,
   capture/consolidation, environment construction, and host merge per ruleset.
   DD currently does not expose native-style phase timings.
2. Fix physical planning: choose a connected/selective atom order, push
   constants/repeated-variable constraints into arrangements, and evaluate
   whether DD should receive the native tree decomposition or a multiway join.
3. After adding counters, investigate semantics-preserving ways to reduce
   Timely progress traffic and duplicated per-ruleset state. The current
   removal/insertion epoch split carries freshness semantics, so fewer epochs
   cannot be assumed safe.
4. Replace `[u32; 48]` rows/keys with arity-sized representations or specialized
   layouts before scaling memory-heavy workloads.
5. Feed rulesets from an explicit mutation log and retain host key indexes so a
   one-row change does not scan and clone whole relations.
6. Add a DD CI canary on pointer analysis plus an atom-order regression. Keep
   math and Luminal outside a blocking smoke test until their resource use is
   bounded, and represent container-action cases as unsupported rather than
   performance timeouts.

## Reproduction artifacts

Benchmark reports:

- `/tmp/dd-default-30s-ce6a69fa.{jsonl,md}`
- `/tmp/dd-math-standard-120s-ce6a69fa.{jsonl,md}`
- `/tmp/dd-eggcc-standard-120s-ce6a69fa.{jsonl,md}`
- `/tmp/dd-luminal-standard-120s-ce6a69fa.{jsonl,md}`
- `/tmp/dd-pointer-main-dd-6r-ce6a69fa.{jsonl,md}`
- `/tmp/dd-herbie-main-dd-6r-ce6a69fa.{jsonl,md}`
- `/tmp/dd-join-order-500-ce6a69fa.{jsonl,md}`
- `/tmp/dd-join-order-500-reversed-6r-ce6a69fa.{jsonl,md}`
- `/tmp/dd-join-order-1500-ce6a69fa.{jsonl,md}`
- `/tmp/dd-small-main-ce6a69fa.{jsonl,md}`

Temporary controlled inputs:

- `/tmp/dd-join-order-{bad,good}.egg`
- `/tmp/dd-join-order-facts`
- `/tmp/dd-join-order-facts-1500`

Profiles:

- `/tmp/dd-pointer-profile-term-ce6a69fa.md`
- `/tmp/main-pointer-profile-term-ce6a69fa.md`
- `/tmp/dd-profiles-ce6a69fa/v2/`

Core commands:

```bash
./bench.py --backend dd --treatments term,proofs --rounds 1 \
  --timeout-sec 30 --force-run \
  --report /tmp/dd-default-30s-ce6a69fa.jsonl --format markdown

./bench.py --backend main,dd --treatments term,proofs --rounds 6 \
  --timeout-sec 30 --force-run \
  --report /tmp/dd-pointer-main-dd-6r-ce6a69fa.jsonl --format markdown \
  --fact-directory benchmarks/data/pointer-analysis-small \
  benchmarks/pointer-analysis-small.egg

./bench.py --backend main,dd --treatments term,proofs --rounds 6 \
  --timeout-sec 30 --force-run \
  --report /tmp/dd-herbie-main-dd-6r-ce6a69fa.jsonl --format markdown \
  egglog/tests/web-demo/herbie.egg

./bench.py profile benchmarks/pointer-analysis-small.egg \
  --fact-directory benchmarks/data/pointer-analysis-small \
  --backend dd --treatment term --profile-seconds 10 \
  --profiles-dir /tmp/dd-profiles-ce6a69fa --top 30 \
  --format markdown --force-run
```

No production code was changed during this investigation.
