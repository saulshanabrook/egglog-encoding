# Independent review of the frozen compiler prototype

**Result: no blocking source, configuration or correctness-evidence finding for
the frozen three-case study.** The prototype is suitable to enter the planned
timing and broad-validation gates with the limitations below. This is a bounded
source/receipt review, not a proof of the entire compiler or alias analysis.

The reviewer ran no compiler, build, fixture or test commands and edited no
source. Existing command receipts, logs, emitted Bril, e-graph snapshots and
hashes were read and independently checked. Machine-readable evidence is in
[prototype-final-receipt-review.json](prototype-final-receipt-review.json).

## Exact reviewed boundary

Eggcc worktree: `/Users/saul/p/wt/eggcc/encoding-study-retarget`, base HEAD
`15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. The authoritative frozen artifact
is `../retarget/prototype/final/`, not the earlier development checkpoint.
All 14 current source files and their archived copies matched the checkpoint's
source hashes. The full patch includes the new, otherwise-untracked rules,
tests, README and Bril fixtures; the feature patch separates them from the
already-reviewed engine-only retarget.

| Artifact | SHA-256 |
| --- | --- |
| full.patch | `7ab6605cedbdb7e6e44fe7b4a6f1768033b1cb83bb7c4f3ad5aee391f64cb08c` |
| feature.patch | `243298fbf886be35e9919d54a73bfa4a973e8da62c7a1361fcf455cc8b913183` |
| final compiler | `d44a89c2f752aff60b2691d9e055f23e54215fc9dfa74a0db8e956afc713162e` |
| native Tiger | `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a` |
| exact_local_addresses.egg | `541df505987408d94d0ce3be1857a191df4b77b1c87d4e65b7a7ecb3a1b7e2ee` |
| dag_in_context/src/lib.rs | `f6b3f45d0bb2a7028c691d709b8bb4b4f76aa2fb31f6918640c61c355fe8ec0a` |
| src/main.rs | `8eae87472ebd3db93b87f322730b98f7ae861bdeed63155d6fd7e378cc62088f` |
| final correctness.json | `6fdb8746afb878cc84603e01dc11125e47369cf81f992e37dccdfbe6e14e90fb` |

The JSON review receipt retains every reviewed source hash and per-case
serialized-node diagnostics. Earlier evidence under `prototype/` used compiler
`f07b2586...`; it was independently inspected first, but is not silently
substituted for final-source validation. Its separate inspection record remains
`prototype-receipt-review.json`.

## Findings resolved before freeze

The first reviewed implementation appended the exact-address closure after
ordinary ablation processing. An enabled mode combined with `--ablate
mem-simple` could therefore reference a removed ruleset. The frozen source now
rejects all enabled-mode/ablation combinations deliberately, rather than
pretending to support a different inference contract.

The CLI rejects that combination before loading the input (`src/main.rs:113`).
The API validates both graph construction and optimize's zero-pass path
(`dag_in_context/src/lib.rs:498` and the optimize entry). Context erasure is
also rejected. API tests exercise graph construction and zero-pass rejection;
an integration test invokes the CLI and checks exit 2, the intended diagnostic,
and empty stdout. The final external capture independently records all six
enabled-mode/context-or-ablation rejection combinations. No unresolved
configuration blocker remains for the supported unablated, context-aware modes.

One review correction matters: `Run::new` uses `EggccConfig::default()`
(`src/util.rs:367-380`), whose `non_weakly_linear` is true. The false override is
used by `test_benchmark_config`/`all_configurations_for`, not this constructor.
The reviewer's earlier message suggesting the original 12 native round trips
used false was mistaken. The frozen native test additionally sets true
explicitly, and the final CLI capture uses production true.

## Source assessment

Default behavior remains off. Off adds neither the new prologue declarations
nor the appended closure; the existing flags retain their prior plumbing.
Passing the whole config into `build_program` carries the new mode through
actual optimization and emitted-egglog paths. The combined source rulesets
still depend on the same existing hacker-rule flag. The source pass-list
implementation and native Tiger/extraction implementation are unchanged.

The production rules strengthen the replay's domain: a declared function must
have the sole `StateT` input, allocations must be positive constant-sized
`PointerT(IntT)` allocations, and stores carry constant integers. Calls,
frees, branches, loops and unknown effects have no transfer rule, although
existing source equalities/inlining can expose an eligible expression.
Descriptors contain only immutable function/rank/offset data; no `Expr`,
contextual `Const` or mutable points-to record is marked injective.

The query consumer joins both exact pointers' allocation origins through
`LiveAllocation` at the **same pre-store state and function**. Its nonalias
premise is a structural inequality witness for those descriptors, not different
current `Expr` class IDs. The manual variant derives its state-scoped pair
relation from the same liveness/key premises and primitive rank/offset
inequalities. Neither variant exports a new global `NoAlias` fact. Both use the
existing write/load commute consequence and existing forwarding.

The valid-offset induction remains sound: `delta >= -offset` and
`delta < size-offset` establish an in-bounds representable sum before adding.
Positive sizes and in-bounds offsets also keep both guard subtractions
representable. This does not promise that arbitrary huge allocations succeed;
the law is conditional on defined executions and actual fresh live regions.

The guard schedule has the required ordering. Each exact-address propagation
round is followed by injectivity and the direct audit inside its saturation.
The consumer runs only after that audited closure. Audits run again after the
consumer and after existing memory/type/indexing closure, and a final audit and
absence checks precede returning from program execution. A fresh e-graph is
built for each original pass, so old rank facts are not carried across native
extraction into a later pass. Serialization follows successful completion of
the whole program; errors/panics prevent it.

This fixes the earlier concern about a cyclic corrupted state generating ranks
until saturation without reaching a final check. The seeded cyclic-state test
now rejects promptly inside the propagation loop. Tests also reject a seeded
pointer merge, unequal rank counts, and a merged descriptor with incompatible
primitive fields. They check the intended diagnostic and that the serialization
sentinel was not reached, rather than treating arbitrary failure as success.

There are no `disequal` assertions in this prototype's new rules. Consequently,
the prior review's suggested explicit assertion-contradiction check is not an
unimplemented assertion-validation obligation here. Injectivity and both
analysis consistency audits run. If asserted disequalities are added later,
their contradiction check and corresponding controls must be added explicitly.

## Independently checked final evidence

The final capture uses archived input files, frozen binaries, contexts,
ordinary execution, all three default parallel passes, native Tiger greedy,
production `non_weakly_linear=true`, and one Rayon thread. It is diagnostic
correctness evidence with interpretation/logging/e-graph dumps, not performance
evidence.

The review independently checked:

- 18 successful interpreted CLI receipts and 18 successful emitted-Bril
  receipts across A, B and final prototype off/keys/query/manual on three cases;
  current binary, input, run-data, Bril and all 54 e-graph hashes match.
- Both non-null interpreter fields equal the expected `17\n` on
  fresh-allocations and `99\n` on same-pointer and zero-offset.
- Logs show passes 0, 1 and 2; each interpreted run retained three actual
  serialized e-graphs without conflict markers.
- Only fresh-allocation query/manual runs have consumer witnesses and remove
  the load. A/B/off/keys emitted output is byte-identical for every case;
  query/manual output is byte-identical to each other.
- Six invalid CLI combinations reject with exit 2, expected diagnostics and
  empty stdout. Final focused receipts show 2 selected guard/API tests and
  2 selected native/CLI integration tests passed, with no failures/timeouts.

The emitted fresh-allocation feature output still contains both allocations,
stores, print and frees; the loaded value is replaced by the earlier 17. The
same-pointer/zero-offset controls retain the correct later value and show no
exact-consumer witness. This is a real full-compiler optimization observation,
not merely an encoding replay. No real compiler bug is established.

## Scope limits and remaining gates

- Off-to-keys includes the new audited key analysis **and** an additional
  memory/type fixed-point closure after each original pass. It is not a pure
  annotation/query-cost contrast. Query and manual share that closure.
- Manual still uses the common query-based consistency audit. It is not a
  query-free algorithm comparison. The current structural-witness workload has
  no asserted disequalities, so it does not isolate NEE/EE assertion-storage
  performance.
- The native correctness cases are three small closed straight-line programs.
  Replay controls separately cover unknowns, bounds and contexts; these native
  runs do not establish general call/loop/inlining or mixed-type behavior.
  Conflict absence remains a rejection check, not a proof that every possible
  source equality preserves universal co-liveness/ranks.
- The existing optional memory analysis already supports this operation
  sequence. The demonstrated increment is over the active default analysis;
  do not claim that all prior eggcc analyses miss it.
- No runtime, memory saving, generated-program speedup, or scaling claim
  follows from these correctness diagnostics. Timing must use fresh repeated
  non-interpreted/non-diagnostic invocations with the frozen configuration and
  defined wait4-RSS scope.
- Complete encoding and eggcc Make gates remain root/owner work after this
  review. Their absence here is a pending delivery gate, not a failed or passed
  test result.

Within these boundaries, the resolved configuration issue and the available
positive/negative/guard evidence leave no additional concrete blocker to the
planned bounded measurement. Broader semantic or performance claims need their
own evidence rather than an inference from these three programs.
