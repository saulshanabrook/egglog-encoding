# Injectivity and disequality reference for the EggCC study

This file is the compact reference for the mathematical rules, host contract,
treatments, implemented cases, and evidence identities. Read the
[explanation](report.md) for the connected argument and [reproduction guide](reproduce.md)
for commands.

## Terms and relations

| Name | Meaning |
| --- | --- |
| equality sort | An e-graph sort whose values can be unioned and canonicalized. |
| primitive | A native immutable value such as `i64`, `bool`, or `String`; primitives are compared directly and are not unioned. |
| marked constructor | A constructor declared `:injective`; for existing applications of that same constructor, equal outputs imply equal corresponding equality-sort inputs and equal primitive fields. |
| committed application | An application row present in the current canonical graph, eligible for read-only reasoning. |
| `disequal(a,b)` | An action that asserts a symmetric constraint between values of the same unionable equality sort. |
| NEE | The not-equal-relation representation used by the EggCC integrations. It stores one ordered canonical pair per assertion; reads probe both orientations. |
| EE | An alternative equality embedding that represents disequality by equating a private equality term with a private false value. |
| `known-disequal?(a,b)` | A partial read-only query over committed/canonical state. It returns `Unit` for a finite witness and is undefined for unknown; it creates no terms or stored derived answer. |
| private graph | A fresh query graph for one exact EggCC source context; branch assumptions are discarded after the target query. |
| bridge | Host code that exports only an exact proved contextual predicate or consumer relation to EggCC's main graph. |

## Logical rules

Let `F` be marked injective and let `G` be any constructor whose relevant
applications are committed.

| Rule | Premises | Conclusion | Restrictions |
| --- | --- | --- | --- |
| cancellation | `F(a1,...,an) = F(b1,...,bn)` | `ai = bi` for each equality-sort child | Primitive child pairs must be equal; unsupported/container fields reject the declaration or query. |
| primitive conflict | Equal marked applications have primitive fields `pi` and `qi` | continue if `pi=qi`; execute `panic` if `pi!=qi` when `injectivity` runs | No primitive disequality fact is stored. This is distinct from the encoded self-disequality contradiction check. |
| marked forward disequality | `ai != bi` | `F(a1,...,ai,...,an) != F(b1,...,bi,...,bn)` | Requires a sound injectivity law for the complete constructor input. |
| sibling-guarded reverse disequality | `G(a1,...,ai,...,an) != G(b1,...,bi,...,bn)` and every `aj=bj` for `j!=i` | `ai != bi` | `G` need not be marked. Exactly one child pair may remain unresolved. |
| canonical transport | `a=a'`, `b=b'`, and `a!=b` | `a'!=b'` | Uses canonical representatives. |
| self-conflict | `a!=a` | contradiction | Used to distinguish inconsistent assumptions from an unknown query. |

For a binary constructor, parent disequality alone means
`a!=c OR b!=d`. Neither child fact may be added until the other child pair is
known equal. Different constructors do not participate in reverse reasoning.

## Execution and storage

Marking a declaration installs generated cancellation and primitive-panic rules
in the shared `injectivity` ruleset; declaration alone does not run them. The
tested propagation sequence is:

1. materialize constructor applications, equalities, and any explicit
   `(disequal a b)` assertions;
2. run `(run-schedule (saturate injectivity))` when equal-output cancellation is
   needed;
3. commit the resulting graph state; and
4. call `known-disequal?` from a `:naive` query rule.

`known-disequal?` performs its marked-forward and sibling-guarded reverse search
on demand, without saturation. Its queue, visited set, and parent index are
temporary; it creates no constructor applications, unions, or persistent
derived-pair cache. A native primitive mismatch can terminate a marked-forward
witness path without creating a primitive disequality relation.

`check-contradiction` is separate. It saturates the private disequality
normalization rules and succeeds when a contradiction is present; it does not
run `injectivity` or turn an unknown structural query into a stored fact.

## Supported boundary

- Equality-sort children may be unioned and may be operands of explicit stored
  `disequal` assertions.
- Primitive children are compared immediately when a rule needs them.
- Containers and unsupported native/custom fields are outside the encoding.
- Query operands and constructor applications must already exist; an undefined
  query result means “not established.”
- Marking is a semantic promise. The host must justify totality, types, scope,
  effects, wrapping behavior, lifetimes, and mutation assumptions.
- The EggCC studies use private NEE graphs. EE is used only for the stated
  differential diagnostics.

## EggCC host contract

An eligible query must establish all of the following before export:

1. exact typed source expressions and source-context identity;
2. the actual reached branch assumptions for that context;
3. exact input/Get transport, including checked loop-slot invariance where used;
4. total sound representation laws for the constructors introduced in the
   private graph;
5. a positive final witness from the generic query; and
6. a single exact target predicate or consumer relation to export into the main
   graph. QR7 exports a `Qr7MustAlias` relation, consumed by a bounded added
   store-forward bridge; its private pointer equality is not unioned globally.

Unsupported translation, missing evidence, ambiguity, graph inconsistency, or
an undefined query suppresses export. Private intermediate equalities and
disequalities never become global EggCC facts.

## Treatment definitions

| Treatment | Behavior |
| --- | --- |
| U0 | Untouched pinned EggCC baseline. |
| B1 / Off | Same retargeted host and dependencies as the candidate, with scoped reasoning disabled. |
| SeedOnly | Builds the same finite terms, identities, annotations, and source seeds but runs no closure or export. |
| PrimitiveOnly | Preserves the same graph/seeds and checks only corresponding primitive fields; performs no equality-sort inference. |
| Manual | Independent finite least-fixed-point implementation of the same generic closure over the same terms and seeds. |
| Encoding | Generic injectivity/disequality rules and read-only query. |
| knockout | Removes one inference edge, query, bridge, or application while preserving the fixed input and other stages. |
| rescue | Supplies exactly the missing intermediate fact to test the downstream path. |

Manual equivalence is expected and prevents a claim of unique logical power.
PrimitiveOnly distinguishes these examples from a direct primitive conflict.
QR7 uses generated injectivity cancellation and equality witness queries only;
its treatment names do not imply a disequality contribution. Its Manual arm
uses a finite equality closure; Encoding also runs that closure for audit, and
Manual materializes the engine graph. Those arms do not isolate compiler cost.

## Implemented cases

| Case | Marked constructors | Unmarked reverse constructor | Essential dynamic facts | Consumer | Status |
| --- | --- | --- | --- | --- | --- |
| QR7 | lossless `K7(Word)` | none | equal quotient and remainder; representation identities; cancelled word equality; same-base address congruence | exact `Qr7MustAlias(Expr,Expr)` relation and added bounded store-forward bridge | strongest substantive-consumer injectivity-only runtime result |
| Same-mask | fixed `Shift7(Word)` | `Mask(Word,Word)` | unequal mask applications with common dynamic mask; `x!=y`; unequal shifts | exact contextual integer `Eq=false` | qualifying constructed runtime speedup |
| Parts32 | `Parts32(Word)` | `Pair(Word,Word)` | `x!=y`; representation equalities; equal low halves; unequal high halves | exact contextual high-part `Eq=false` | primary qualifying combined-mechanism runtime speedup |
| Affine | invertible `Affine(Word,Word)` and odd `OddMul(Word,i64)` | wrapping `Add(Word,Word)` | two key-child equalities; one equal Add sibling; isolated and propagated disequality | exact contextual `Eq=false` | supporting; unmeasured; validation/lint defects |
| Route | tagged `Route(Bool,Word,Word)` and odd `OddMul` | wrapping `Add` | common dynamic selector; payload cancellation; reverse then forward disequality | exact contextual `Eq=false` | supporting; unmeasured |
| Sort | `OrderKey(Word,Word)` containing min, max, orientation, plus odd `OddMul` | wrapping `Add` | full key equality; input cancellation; reverse then forward disequality | exact contextual `Eq=false` | supporting; unmeasured |

`Mask`, `Pair`, and `Add` are intentionally unmarked. Their use of reverse
disequality is justified by congruence plus equal siblings, not by injectivity.

## Bounded negative probes

| Lead | Intended chain and consumer | Actual result | Disposition |
| --- | --- | --- | --- |
| Pack32 | cancel a bounded two-child packing, use an equal sibling to isolate disequality, propagate through a fixed shift, then apply contextual `Eq=false` | 14 positive treatments, 11 outputs each; zero accepted queries or exports; identical emitted Bril and native process-main instructions | fail-closed actual probe; no endpoint or timing result. Its generic law/consumer portfolio is covered by Route and Parts32, without refuting the Pack32 theorem or importer feasibility. |
| same-region A1 | prove a bounded live-cell `NoAlias`, transport it through invariant loop inputs, then feed the existing commute/forward memory behavior | after one functional revision, auxiliary `TupleRemoveAt`/hoist rows remain conservatively rejected; 31 interpreter pairs and 233 native checks agree with zero exports and identical code | attempt budget exhausted; no bug or speedup. The scoped law remains plausible and a different implementation is not ruled out. |

The Pack32 authority is the [actual-probe report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-integration/report.md).
The A1 authority is its [actual-attempt report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-integration/actual-r0/report.md),
with machine-readable `summary.json`, `acceptance.json`, and `inspection.json`
beside it. Neither negative probe supplies evidence for the qualifying speedup.

## Sound constructor laws used

| Constructor | Law |
| --- | --- |
| `K7(x)` | `(trunc(x/7), x-7*trunc(x/7))` reconstructs every signed i64 exactly; only the complete pair is injective. |
| `ShiftK(x)` | `x -> x+K mod 2^64` is a bijection for fixed `K`. |
| `Parts32(x)` | `(x & 0xffffffff, (x-(x&0xffffffff))/2^32)` reconstructs every signed i64 exactly. |
| `Affine(a,b)` | The chosen 2x2 matrix has determinant one and an inverse modulo `2^64`. |
| `OddMulK(x)` | Multiplication by odd `K` is a bijection modulo `2^64`. |
| `Route(p,a,b)` | `(p, select(p,a,b), select(p,b,a))` reconstructs `p,a,b`. |
| `OrderKey(a,b)` | `(smin(a,b), smax(a,b), select(a<b,1,0))` reconstructs the ordered input pair, including ties. |

Raw `Bitand`, `Add`, `Select`, `Smin`, `Smax`, `Expr`, and effect/state terms are
not marked injective.

## QR7 authorities and records

All QR7 paths in this section are relative to
`benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/`.

| Authority | SHA-256 |
| --- | --- |
| [Corrected source identities](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/source-identities-r1.json) | `22c37674b4f8617b90cceadddb2daa0992b501b9f627029ebc48dbda6515723c` |
| `corrected-source-r1.tar` | `17d40620cb9c621ff493cb4edfd5099a487ce0f68ee054184b75381386a7e30e` |
| `eggcc-candidate-r1.patch` | `3242cf2bd7925912fa7902b9fdeee2a98889fe6e1dba5f5d0d93cea31691295f` |
| `bin-r1/eggcc` | `ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251` |
| `fixtures/source.bril` | `408955db7a868d6a539512bdb2cc09a01fbb06ef39aa54b445d589293dc942c2` |
| [Causal inspection](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/final-r1/inspection.json) | `54801698936cd372e2aa8b4d1d76a32c9bf3e706e295b939018cceb9cb533ae0` |
| [Actual-binary inspection](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/actual-binary-inspection-r1.json) | `7cfc70703384fa1b4e5f2c563c01b640b2115035600fcf6163e8b93298297ed4` |
| [Frozen timing design](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/prospective-timing-design-r1.json) | `490ca1cea524edfd8e0bc6d2652a87bc1dcddf2989b38be12d54feff7d88b601` |
| [Independent timing verification](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json) | `d23cda45901736c2c02721f7c456bf591526fc72e262f84de1a0c27c68276b56` |
| [r2 cleanup patch](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/nits-r2.patch) | `b0802da11e40e6d7fba3eefc8a3639a81153bee445cd90a71000e967d4211e00` |
| [r2 direct-check summary](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/validation-summary.json) | `830dafc1de2e46df0159564ed303632f9ea94bf1232e8c232189946ce875e49c` |
| [Fresh U0 nits comparison](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/u0-nits/comparison.json) | `92a5f5a568bed5d6ee6db381a8de576cf6b473bc7a713d364bde80a9a21dd374` |
| [r1/r2 matrix comparison](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/matrix-r2/r1-r2-comparison.json) | `0b29b24ccfe9b5b7de9d2b5a1a2cd82f095810384fa542aeb935d042dee125f4` |
| [r2 actual-binary inspection](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/matrix-r2/actual-binary-inspection-r2.json) | `1c92c4b9b4407a6cc4a521d7a5f94cbb816edcbd262b0ab8b3426d0d0f57fdf4` |
| [r2 host comparison](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/host-tests/comparison.json) | `12bf6cbaef77011ba8f029537559eb1cf51c4898ea016355cb8e4aeb3cf2edab` |
| [r2 final validation summary](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/final-summary.json) | `051e8a3951265779bba1ddd3b5b0eee79fc8c73dc06c7657d9d4db20f1214d9a` |
| [Final repository `make check`](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/root-make-check-r4/receipt.json) | `4e419fe4e240069a782f8ea3a01dd1fc0e3a396c8f5f6934cb1c203dfec574f2` |

`source-identities-r1.json` has `schema_version: 1`, status
`corrected-source-frozen-and-release-target-revalidated`, and
`binary_identity_equal: true`. It binds the overlay archive's members, base
archives, host/engine/harness files, patch, frozen compiler, and release-recheck
receipt. The archive is an overlay, not a complete standalone checkout. Its
`timing_samples_taken: false` records the pre-timing freeze.

The r1 compiler, SHA-256
`ab1185cd3e24d1ed1698bc004ed3cc70f16c89202e3cc36a910b8308221df251`,
is the immutable timing authority. The four-hunk r2 validation cleanup rebuilds
to compiler SHA-256
`046efff7fcc7ea3a1e31ff8e35ccad32001967b75f97e4f2c1efaef0413b6333`.
Across all 37 matrix cases, r2 preserves semantic rows, queries, e-graph
evidence, optimized Bril, 1,739 disassembled function bodies, every loadable
Mach-O section, and all 177 native outputs. Complete regenerated Mach-O hashes
differ only in UUID, temporary-object symbol/string metadata, and the derived
ad-hoc signature. That establishes execution-content equivalence; it does not
convert the retained r1 samples into direct measurements of regenerated r2
files, and no r2 timing claim is made.

| Record | Relevant exact fields |
| --- | --- |
| `final-r1/inspection.json` | `functions[mode][main or _main]` holds LLVM function hashes, `load_i64`, `store_i64`, and `cyclic_basic_block_components`; `causal[mode]` holds `queries`, `relation_rows`, and `events`. All five causal/code `gates` are true; `timing_collected` and `performance_acceptance` are false because this inspection precedes timing. |
| Query receipt in `causal[mode].queries` | `pair_equal`, `key_equal`, `word_equal`, `address_equal`, `export`, `injectivity_saturated`, `engine_witness_queries_run`, and `manual_receipts` distinguish each inference and export boundary. |
| `actual-binary-inspection-r1.json` | `schema_version: 1`, `status: passed`; `modes[mode].functions.process_main` binds actual Mach-O instruction hashes/counts and `internal_backward_branches`; `groups` defines instruction-identical arms. |
| `prospective-timing-design-r1.json` | `schema_version: 1`, `revision: 1`; `arms` binds binaries/emitted Bril/assembly; `sessions[].cycle_order` freezes the schedule; `workloads` binds arguments and exact stdout; `primary_hot_comparisons` and `same_code_groups` define gates. `timed_samples_taken: false` is the precollection freeze state. |
| `timing-r1/independent-verification.json` | `schema_version: 1`, `status: passed`; `sessions[session].workloads[workload].comparisons[label]` holds `point_estimate` and `bootstrap95`; `gates.overall_speedup_acceptance` and every other gate are true. |
| `validation-r2/final-summary.json` | Binds the four-hunk source cleanup, fresh U0 nits control, complete matrix parity, host-root comparison, absent memory guard, filtered heavy raytrace, and the r1-timing/r2-validation boundary. |

| Native group | Arms | Actual process-entry instructions / backward branches |
| --- | --- | ---: |
| baseline | U0, Off, SeedOnly, PrimitiveOnly, cancellation-off, identity-off, query-off, transport-off, bridge-off, consumer-off | 91 / 2 |
| winning | Encoding, Manual, x-rescue, key-rescue | 55 / 0 |

The baseline executed LLVM entry already has `load_i64: 0`. The code change is
a phase-ordering/loop-elimination result. The baseline process-entry instruction
hash is `66d827e619ee132afed2d8ea3878a084cd184fee24b0b912a93519cdee24bcf0`;
the winning hash is
`8118a0fa625e0f98210d68a42f26122abe209a0a1ddf09425b0c26b006f17360`.
Whole native executable hashes differ. `transport-off` withholds export at the
bridge gate while transport computation still runs: it is an export-gate
placebo, not a direct computation ablation. `consumer-off` retains one exact
relation row and no `QR7 must-alias store forward` event.

The executed correctness matrix is 14 positive cases with 154 native checks,
18 premise/divisor-negative cases with 18 checks, four changed-pointer cases
with four checks, and one no-context case with one check: 37 compiler cases and
177 native checks total, plus emitted/source interpreter parity. This covers
less than the integration plan's aspirational type/context/lifetime/mutation
matrix; it must not be presented as every proposed rejection test.

| Runtime workload | Arguments | Exact stdout | Role |
| --- | --- | --- | --- |
| hot-equal-key | `12 12 10000000` | `49999995000000\n` | primary payoff |
| neutral-zero-trip | `12 12 0` | `0\n` | reported control; no speedup gate |

There are 14 arms, one warmup per arm/workload/session, and ten serial fresh
processes per measured row. The screen has one 14-cycle block and 392 measured
rows; the independent confirmation has eight blocks, 112 cycles, and 3,136
measured rows. The Williams design balances position and directed immediate
predecessors within complete blocks. Bootstrap intervals resample complete
14-cycle blocks with 10,000 draws and seed `7019`.

| Primary hot confirmation comparison | Point estimate | Bootstrap 95% |
| --- | ---: | ---: |
| Encoding/U0 | 0.55054942 | [0.54710116, 0.55750217] |
| Encoding/Off | 0.55028237 | [0.54417290, 0.55228263] |
| Encoding/SeedOnly | 0.55210042 | [0.54940045, 0.55441964] |
| Encoding/PrimitiveOnly | 0.55337667 | [0.54957634, 0.55707113] |
| Manual/U0 | 0.55741057 | [0.55376977, 0.55986024] |

Every screen primary point estimate is below `0.99`, every confirmation primary
upper 95% bound is below `0.99`, and every confirmation hot point ratio within
each instruction-identical group is in `[0.98,1.02]`. Neutral Encoding/U0 is
`0.98925850`, interval `[0.98367291,1.00032756]`. All outputs are exact and all
completed rows are retained. Process and memory snapshots are descriptive and
never reject or discard samples. The supported endpoint is fresh-process
generated-program runtime for this fixed QR7 workload; compiler/lowering time,
proof support, disequality contribution, raytracing, and general-workload
conclusions are excluded.

## Parts32 performance authority

Frozen design:
`benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/prospective-timing-design-frozen.json`,
SHA-256 `c646d77e41334fd252a4e951245068f771afbbb41e44cd828e30edd58b0f6367`.

| Workload | Session | Encoding/U0 | Complete-block bootstrap 95% |
| --- | ---: | ---: | ---: |
| equal-low-positive | 1 | 0.92426 | [0.92354, 0.92549] |
| signed-min-boundary | 1 | 0.92431 | [0.92220, 0.92466] |
| signed-max-crossing | 1 | 0.92504 | [0.92404, 0.92843] |
| equal-low-positive | 2 | 0.91952 | [0.91526, 0.92272] |
| signed-min-boundary | 2 | 0.91492 | [0.91242, 0.91724] |
| signed-max-crossing | 2 | 0.91398 | [0.91143, 0.91670] |

Each session contains 90 prospectively balanced cycles, three workloads, five
arms, 1,350 measured rows, 45 warmups, and eight passing process checks. Every
observation runs 32 fresh native processes with one million loop iterations per
process. The speed gate requires upper 95% below `0.99` for Encoding/U0,
Manual/U0, and Encoding/B1 in every workload and session; all 18 comparisons
pass. B1/U0, SeedOnly/B1, and Encoding/Manual pass the prospectively defined
placebo-validity check. Workloads and sessions are never pooled.

Independent verification:
`benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/timing/independent-verification.json`,
SHA-256 `9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959`.

The separate ten-cycle, five-arm compiler-time diagnostic is descriptive only.
Its Encoding/Manual paired median ratio is `0.99919`, with interval
`[0.99370, 1.00697]`. Retarget differences make comparisons against U0
unsuitable for a compiler-speed claim. Summary:
`benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/compile-diagnostic-final/results/summary.json`,
SHA-256 `283a6af7bb6a9d69d87510fab681042170f47ff70efa7a95719e37a8d36ad12e`.

## Same-mask performance authority

Frozen design: `benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/confirmation-design.json`,
SHA-256 `a8eca05eaf0455536d737ea9064adff54573022e26ea68a1073323f3848c6a0e`.

| Comparison | Point estimate | Bootstrap 95% |
| --- | ---: | ---: |
| Encoding/U0 | 0.98083849 | [0.98041942, 0.98164075] |
| Manual/U0 | 0.98087323 | [0.98004442, 0.98230442] |
| B1/U0 | 1.00034293 | [0.99859575, 1.00183362] |
| Encoding/Manual | 0.99964 | [0.99847, 1.00088] |

There are 32 balanced cycles, three warmups per arm, 200 million loop
iterations per observation, and exact output `1200000000\n` for every measured
run. The acceptance condition is upper 95% Encoding/U0 below `0.99`.

## Source identities and validation boundaries

- EggCC U0: `a0bbec127f83249074a46af3fd6f6126c90fe0fb`.
- Selected encoding base: `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`
  plus the retained generic n-ary reverse-disequality delta.
- Parts32 evaluated compiler SHA-256:
  `d712e8347bf6eea231de829174a9436f411a3cedfd210daf8e7c4614c2371d2f`.
- Parts32 immutable compiler/source archive SHA-256:
  `ba2f65df7091573a594b7c51ec68a8b3665b5c85f279fe4415ca0f6e08565873`.
- Reconstructed U0 Git archive SHA-256:
  `7a886debd758e78d0e859a05bbac75084e7da9c4f4bd0d73321dcf6f5ad25c2a`.

The final repository-root `make check` passes: 1,979 Python tests and 1,502 Rust
tests/doctests pass, with two Python snapshots and six ignored Rust tests. The
isolated QR7 engine check also passes: 233 Python tests and 1,804 Rust
tests/doctests pass, with two Python snapshots and six ignored Rust tests. The
cleaned r2 EggCC DAG suite passes all 70 tests, including six QR7 tests.

The first direct checks found QR7-local formatting and two strict DAG Clippy
diagnostics. The four-hunk r2 cleanup changes only `scoped_qr7.rs`; root and DAG
formatting now pass, and QR7-specific strict-Clippy diagnostics are zero. The
remaining root Clippy diagnostic (`unnecessary_unwrap`) and two DAG diagnostics
(`unnecessary_unwrap` and `cloned_ref_to_slice_refs`) reproduce at the same sites
in byte-identical pinned-U0 source. The host nits gate remains failed and is not
described as green.

The cleaned r2 host test command passes 31 unit and 2,420 file-test bodies, then
rejects the same 13 unaccepted snapshots as r1. Every pending snapshot matches
the dependency-retarget-only control byte-for-byte, and every checked-in
snapshot remains equal to U0. No snapshot was accepted. Affine has 17
candidate-specific sidecar diagnostics and remains supporting only; same-mask
retains its documented limits. Exact receipts, streams, source manifests, and
attribution are in the [r2 final validation summary](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r2/final-summary.json).
The memory guard is absent from every reviewed receipt. Only the heavy
`raytracewithscreen` host test was filtered; `raytrace-test-benchmark` ran and
passed.

The final search boundary is recorded by the read-only
[cycle-06 Codex audit](../eggcc-nontrivial-encoding-payoff/cycles/06-codex-audit.md),
[Claude Fable audit](../eggcc-nontrivial-encoding-payoff/cycles/06-fable-audit.md),
and [independent source validation](../eggcc-nontrivial-encoding-payoff/cycles/06-fable-validation.md).
They found no additional bounded eligible lead. This is a finite-search result,
not an exhaustive source or backend theorem. The validation rejects specific
LLVM-pass attribution, an exhaustive equality-consumer census, and treating
`ContextOf` as a lifetime proof.

The earlier `ObservedBool` Add/Sub bugs are excluded from this reference's
qualifying result. They reduce to a direct primitive Boolean mismatch and do not
use stored disequality.
