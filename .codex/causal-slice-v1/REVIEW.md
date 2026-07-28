# Check-directed slice replay: review handoff

## Status

The production review candidate is
`8ff038bfdf18b373db051fa98a999dda8e871f51`. It closes the last known replay
failure by retaining the pre-event denotation read by every selected structural
equality carrier. The correction is consumer-side: it uses existing trace
history and changes neither capture schema nor replay syntax. The five frozen
artifacts remain byte-identical.

The implementation is ready for architectural and correctness review under a
deliberately bounded contract:

- Supported programs either produce an artifact that passes strict replay in
  a fresh proof-testing graph, or fail closed without publishing one.
- There are no known capture panics or replay-failure classifications. Eqsolve
  now publishes and strictly replays all seven check roots.
- Compatibility expansion and further performance tuning are deferred. On the
  current binary, sliced proofs are materially faster and use less memory than
  full proofs on every benchmark in the accepted five-file cohort.

## User-visible contract

`--slice-output FILE` requests a validated replay artifact without enabling
ordinary proof output:

```text
egglog --slice-output slice-replay.egg input.egg
```

`--proofs` is independent. `--slice --proofs` remains useful when proof output
is wanted; bare `--slice` is rejected because it requests no observable output.

Capture is serial-only and currently limited to one input file, the main
backend, ordinary seminaive execution, and successful `check` roots. Unsupported
backends, schedulers, command shapes, mutation shapes, proof-testing modes, and
multi-thread activation fail closed with a specific diagnostic. There is no
fallback to the unsliced input.

Before publication, egglog renders the owned artifact, reparses those exact
bytes in a fresh proof-testing graph, executes the program, and reruns its
checks. A temporary file is synced and atomically persisted only after that
validation succeeds.

Retained source rewrites preserve their surface form. Two selected directions
of a `birewrite` render as one `birewrite`; a single selected direction renders
as a deterministically named, correctly oriented `rewrite`. Generated replay
names use the `__slice_replay` namespace. User variables colliding with the
deterministic hidden rewrite root are handled by suffixing the hidden root.

## What changed in the review-readiness pass

### Review structure and vocabulary

- The former 9,266-line receipt kernel is now `core-relations/src/provenance`,
  split into capture, model, term, view, and cold explanation modules.
- Backward selection and artifact construction are now separate
  `egglog/src/slicing/backward.rs` and `egglog/src/slicing/replay.rs` modules.
- Internal and public names consistently describe an execution trace and a
  replay slice instead of exposing the old receipt terminology.
- CLI flags and generated identifiers were renamed before external review, so
  reviewers do not need to translate a compatibility vocabulary.

The file moves are isolated from the semantic rename so `git log --follow`
remains useful:

- `53f2397`: conceptual move-only module boundary.
- `e37e3b2`: capture/model/view/explanation split.
- `f4d3c1c`: mechanical vocabulary and CLI rename.

### Bounded code and hot-path cleanup

- Removed unreachable parallel trace table insertion (`2fd90b8`). Ordinary
  parallel insertion remains available and its four-thread large-insert canary
  passes.
- Removed parallel-only cause drafts (`8b93e56`). Live serial deferred-merge
  causes still retain their exact predecessor fact.
- Removed production-only test accounting, dead replay catalog state, and
  unused exports/counters.
- Input SHA-256 is computed only when trace capture needs it (`2a64887`).
- Surface command ASTs are cloned only while trace capture is active
  (`aa7c11a`).
- The remaining shared setup cost identified by source review is the
  deterministic rewrite-root variable scan; it is per command, not per row.

### Backend and publication boundaries

- The DD backend rejects trace metadata before registering or mutating a rule.
- Fresh sliced benchmark collection checks CLI capabilities before doing work.
- A requested slice must have either a file output or proof output.
- Publication is validation-gated and uses temporary-file persistence.

## Suggested reading order

1. This synopsis and `egglog/README.md` for the contract.
2. `53f2397`, `e37e3b2`, and `f4d3c1c` for the mechanical review refactor.
3. `egglog/src/cli.rs` for activation, strict replay validation, and
   publication.
4. `egglog/core-relations/src/provenance/{model,capture,view,explain,terms}.rs`
   for the trace representation and capture boundaries.
5. `egglog/egglog-backend-trait` and `egglog/egglog-bridge` for integration and
   fail-closed capability transport.
6. `egglog/src/slicing/backward.rs` for causal closure.
7. `egglog/src/slicing/replay.rs` for owned artifact construction and naming.
8. `egglog/core-relations/src/table` and `free_join` for mutation/rekey capture
   and the serial/parallel boundary.
9. `test-support/causal_corpus.rs`, `egglog/tests/slice_cli.rs`, and the proof
   snapshots for the executable contract.
10. `benchmarking/` and `EXPERIMENTS.md` for performance and rejected designs.

## Correctness evidence

### Executable corpus

The high-level corpus is green across 187 programs: 151 core and 36
experimental/workload cases.

- `KnownCapturePanic`: 0.
- `KnownReplayFailure`: 0; the variant and its final registry entry are gone.
- Runtime `Unsupported`: 48 explicit contract boundaries.
- Static proof-incompatible exclusions: 52.
- Extract-only root exclusions: 4.

Every runtime rejection expects exit 1 and an absent fresh artifact. The
allowlist is centralized and checked for sortedness, duplicates, stale paths,
and stale dispositions.

`CS-REPLAY-EQSOLVE` was reduced before fixing it, so the correction follows a
named model error rather than the surface failure. Backward closure followed
native applied equality edges, while replay re-executed their structural source
or rule actions. An action endpoint can already be canonicalized when the
native edge is applied, so replaying that action without the earlier endpoint
denotation equality applies a different edge. In the reduced Eqsolve trace,
equality 954 proposes `328 = 4082` but actually applies `4082 -> 327`; equality
724 is what made 328 denote 327. A three-node `A = B; B = C` counterexample
reproduced the failure without proofs, grounded schedules, congruence, or
rebuild. Three of six allocation orders exposed it.

The fix gives every replay-visible equality one strict pre-event denotation
query. It explains each structural proposal endpoint at `id - 1` and
`position - 1`, verifies those representatives against the recorded native
parent/child edge, and queues the prerequisite equalities, facts, causes, and
rekeys through ordinary backward closure. An event cannot justify itself. The
trace already contained every required field, so no recording or artifact
schema changed.

Carrier-owned targets do not retain a redundant producer, but a historical
container anchor remains an input. A direct rule-union/Vec regression proves
that distinction: the old mode loses the source anchor; the accepted mode
retains it. A fixed-seed property additionally covers source and rule unions,
source and rule sets, deletion/recreation, shuffled allocation order, and
unrelated prefix noise in native and term replay. The six-order counterexample
is unignored and green.

One bounded simplification succeeded: the general denotation law replaced the
old optional check-root cross-endpoint seeding. Two tempting special-case
deletions were rejected on evidence: congruence-child support remains necessary
for Knapsack, and firing-term availability remains necessary for Combinators.
Eqsolve is now `ChecksOnly` because its seven checks are supported while
extracts are not replay roots—not because any replay failure remains.

### Five-workload artifact oracle

The current candidate generated all five artifacts twice; both generations
matched each other and the frozen `df8aeab` oracle byte-for-byte. The refactor
intentionally renamed generated
identifiers and preserved rewrite syntax, so these are a new frozen byte
oracle rather than a claim of identity to the pre-rename files.

| Workload | SHA-256 | Lines | Bytes |
| --- | --- | ---: | ---: |
| Math | `417b80f7a08d29000ab7c8288df22c0c457be3b607ae0bb8a70177b5d8663a6b` | 64 | 6,606 |
| Eggcc | `15cc5a6f4cbb5c40d3c06c55fe5361cb399bc435d704d1b900aa36f273f975bb` | 3,422 | 160,753 |
| Pointer | `86046da30e97b0d73349d5e63b4e02a2efba5a8a49b38fd2e2b7c115b0e496a1` | 34 | 1,998 |
| Hardboiled | `fb5f701069049b8f86df546fd7303daaa6a3823350631ed9d71b8398779ffff0` | 294 | 26,141 |
| Luminal | `49c83a9764bc67e12a554fab66a9244c0fa4b2c73f4a2d14f9345bccfb39a811` | 49 | 6,493 |

Independent inspection replayed all five artifacts under the experimental
entrypoint and the four main-binary-compatible artifacts under the main
entrypoint. Eggcc intentionally requires the experimental
`pair-min-by-second-i64` primitive, so vanilla egglog rejects that artifact at
declaration time rather than constituting a replay failure. Each artifact
contains exactly one source-equivalent check; all 28 `run-rule` forms are
list-form; schedules precede checks; selected rewrite directions are correct;
and no old `__causal` identifier remains.

## Performance evidence

The final public-harness comparison used the same release binary for all
treatments
(`sha256:874d47768da4466f19426c18b6a27c0e9cd0c0bed3324586f2b7909e3277ca77`),
a 120-second timeout, and the normal append-only cache. It progressed from one
to three to six rounds without forcing rows. All observations succeeded. The
harness marked the checkout dirty only because the two pre-existing untracked
files were present; the benchmarked tracked sources are exactly `8ff038b`.

| Workload | Sliced proofs / proofs wall, 95% CI | Peak RSS, 95% CI |
| --- | ---: | ---: |
| Math | 0.217-0.220x | 0.387-0.391x |
| Eggcc | 0.397-0.399x | 0.594-0.603x |
| Pointer | 0.0932-0.0962x | 0.191-0.194x |
| Hardboiled | 0.545-0.557x | 0.475-0.482x |
| Luminal | 0.0338-0.0352x | 0.0904-0.0925x |

Suite-total wall is **0.138-0.141x**. Every per-file upper bound is below 1,
and every workload also uses less peak RSS than full proofs. The report is
the normal append-only `.reports.jsonl`, SHA-256
`5ea7b06e013177ea3f1805e741b694862a0c816b08125509aacb9e1b73d13b15`.

The same final binary measured sliced proofs versus normal/off at **2.20-2.23x**
suite wall:

| Workload | Sliced proofs / off wall, 95% CI | Peak RSS, 95% CI |
| --- | ---: | ---: |
| Math | 3.47-3.73x | 5.11-5.17x |
| Eggcc | 1.83-1.84x | 3.51-3.60x |
| Pointer | 4.08-4.28x | 2.28-2.30x |
| Hardboiled | 2.34-2.38x | 2.32-2.34x |
| Luminal | 1.66-1.69x | 1.34-1.35x |

The separate whole-feature
base-versus-current ordinary comparison was inconclusive on wall time: suite
0.601-1.03x and every per-file interval included 1. Peak RSS was higher for
four of five workloads. Two plausible causes remain disclosed: binary-layout
sensitivity, observed twice on this branch at 5-8%, and real shared-path work
from the earlier correctness consolidation's 571 production lines. This pass
removed two known ordinary-path costs (input hashing and command cloning) but
did not add an instructions-retired profiler or repeat the base comparison
after layout-changing review refactors.

## Size accounting

The calibrated rustfmt-normalized production metric is:

| Base | Net production LoC |
| --- | ---: |
| Whole-feature `4940be37` | **+22,609** |
| Logical-v1 `0d7ffbb` | **+11,002** |
| Pre-refactor `8598ad4` | **+347** |
| Reduction start `74eb9218` | **-623** |

The endpoint-denotation commit is +305 production lines; the publication-test
seam after `df8aeab` is +15. Together they are +425/-105 production lines
relative to that checkpoint. The fix's 415 net test/harness lines receive no
size credit. The whole reduction campaign remains 623 production lines smaller
than its clean start. The last calibrated token inventory was at `df8aeab`: 465,679
nontrivia Rust syntax tokens, 4,891 fewer than `74eb9218`; it was not rerun for
this correctness patch.

The accounting formats each Rust source with rustfmt 1.8.0, excludes dedicated
tests/snapshots/docs/ledgers and complete outer `#[cfg(test)]` items, then uses
the Myers line diff without rename credit. It reproduces the prior
`8598ad4`/`4940be37` oracle exactly.

Tests, snapshots, documentation, and this ledger receive no production-LoC
reduction credit. No new direct dependency was introduced versus `8598ad4` or
`74eb9218`; atomic publication uses only the standard library.

## Validation

Focused gates already passed during implementation:

- Full `egglog` library suite: 141 unit tests.
- Causal corpus: 151 core plus 36 experimental/workload programs.
- Proof snapshot regeneration: 349 core plus 44 experimental/workload cases.
- `make python-check` (Ruff, mypy, 173 pytest cases, 2 snapshots).
- `make benchmark-smoke` (2 successful isolated observations).
- DD checks, focused pre-mutation guards, the four-thread ordinary insert
  canary, CLI rewrite/collision replay canaries, formatting, and diff checks.

Final required gate on the current candidate:

`make proof-tests` passed 349 core and 44 experimental/workload cases. Without
rerunning that subset, `make check` then passed lockfile validation, formatting,
Ruff, mypy, both Clippy configurations, 173 Python tests, the full Rust
workspace and doctest suite, and the DD timing-summary integration test. The
rebuilt release binaries are
`c7abdfab3dabf8ae5358b0a5e90cd55b2016c365a4eda2976fbb660894871b4f`
(main) and
`874d47768da4466f19426c18b6a27c0e9cd0c0bed3324586f2b7909e3277ca77`
(experimental). The candidate reproduced all five frozen artifact hashes.

## Explicitly deferred

- The 48 runtime and 56 static/extract fail-closed compatibility boundaries.
- Parallel trace capture; both public multi-thread activation errors remain.
- Annotation-only provenance and slice-time premise re-derivation. That is a
  future contract/architecture decision, not a packaging refactor.
- Further performance and binary-layout stabilization. The current acceptance
  requirement is that every sliced-proof workload remain faster than proofs.
- Sub-threshold LoC ideas that would move complexity or reintroduce layouts
  already rejected by measured experiments.

## Commit map after the mechanical refactor

- `d4dabcb`: preserve source rewrite and birewrite syntax.
- `2fd90b8`: remove unreachable parallel trace table insertion.
- `adef905`: remove production-only slice test accounting.
- `2a64887`: skip input hashing outside trace capture.
- `eba52a3`: validate fresh sliced benchmark capabilities.
- `a37e42e`: reject trace metadata in the DD backend.
- `ce30d50`: remove dead replay catalog state.
- `eaea1d7`: require an explicit slicing output.
- `125f61a`: document the public contract.
- `8b93e56`: remove parallel-only trace cause drafts.
- `aa7c11a`: avoid cloning commands outside trace capture.
- `896a905`: cover rewrite-root collisions end to end.
- `1a97d0e`: refresh deterministic rewrite proof snapshots and delete one
  unreachable snapshot.
- `df8aeab`: publish atomically without adding a dependency.
- `eb312ec`: decouple the publication-safety oracle from a known replay defect.
- `4bd0264`: reduce Eqsolve to the structural-endpoint denotation error.
- `8ff038b`: close structural-carrier denotation dependencies and delete the
  final replay-failure classification.
