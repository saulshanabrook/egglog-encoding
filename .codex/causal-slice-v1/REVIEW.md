# Check-directed slice replay: review handoff

## Status

The production checkpoint reviewed and benchmarked here is
`df8aeab6313cdd086d899778e5b750a2b7948d47`. The only change after that
checkpoint is this review-only documentation; it does not change the binary.

The implementation is ready for architectural and correctness review under a
deliberately bounded contract:

- Supported programs either produce an artifact that passes strict replay in
  a fresh proof-testing graph, or fail closed without publishing one.
- `core/web-demo/eqsolve.egg` is the one named, known slicing defect. Strict
  replay catches it and prevents publication; it is not presented as an
  intentional `Unsupported` boundary.
- Compatibility expansion and further performance tuning are deferred. The
  current implementation is materially faster and uses less memory than full
  proofs on every benchmark in the accepted five-file cohort.

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
- `KnownReplayFailure`: 1 (`CS-REPLAY-EQSOLVE`, below).
- Runtime `Unsupported`: 48 explicit contract boundaries.
- Static proof-incompatible exclusions: 52.
- Extract-only root exclusions: 4.

Every runtime rejection expects exit 1 and an absent fresh artifact. The
allowlist is centralized and checked for sortedness, duplicates, stale paths,
and stale dispositions.

`CS-REPLAY-EQSOLVE` is retained as an honest defect classification. Its first
observed strict-replay boundary is the final equality check, where the replay
cannot match `@ExistsConstructor2`. Two bounded consumer-side attempts did not
establish a sound correction. The validation gate reports the replay error and
leaves the artifact absent; no broad predictive predicate or recording-schema
expansion was introduced to relabel it as supported or `Unsupported`.

### Five-workload artifact oracle

The final artifacts were generated twice and were byte-identical between
repetitions. The refactor intentionally renamed generated identifiers and
preserved rewrite syntax, so these are a new frozen byte oracle rather than a
claim of identity to the pre-rename files.

| Workload | SHA-256 | Lines | Bytes |
| --- | --- | ---: | ---: |
| Math | `417b80f7a08d29000ab7c8288df22c0c457be3b607ae0bb8a70177b5d8663a6b` | 64 | 6,606 |
| Eggcc | `15cc5a6f4cbb5c40d3c06c55fe5361cb399bc435d704d1b900aa36f273f975bb` | 3,422 | 160,753 |
| Pointer | `86046da30e97b0d73349d5e63b4e02a2efba5a8a49b38fd2e2b7c115b0e496a1` | 34 | 1,998 |
| Hardboiled | `fb5f701069049b8f86df546fd7303daaa6a3823350631ed9d71b8398779ffff0` | 294 | 26,141 |
| Luminal | `49c83a9764bc67e12a554fab66a9244c0fa4b2c73f4a2d14f9345bccfb39a811` | 49 | 6,493 |

Independent inspection replayed all five artifacts under both the main and
experimental entrypoints. Each contains exactly one source-equivalent check;
all 28 `run-rule` forms are list-form; schedules precede checks; selected
rewrite directions are correct; and no old `__causal` identifier remains.

## Performance evidence

The final public-harness comparison used the same clean release binary for both
treatments (`sha256:5a7e77e2b4480d7da6904e6ba79272d468e804ee2632eb1f615e31ca5bc17d32`),
a 120-second timeout, and the normal append-only cache. It progressed from one
to three to six rounds without forcing rows. All 60 observations succeeded.

| Workload | Sliced proofs / proofs wall, 95% CI | Peak RSS, 95% CI |
| --- | ---: | ---: |
| Math | 0.235-0.257x | 0.388-0.392x |
| Eggcc | 0.391-0.408x | 0.589-0.611x |
| Pointer | 0.0924-0.0941x | 0.190-0.193x |
| Hardboiled | 0.552-0.560x | 0.473-0.487x |
| Luminal | 0.0371-0.0381x | 0.0908-0.0959x |

Suite-total wall is **0.149-0.155x**. Every per-file upper bound is below 1,
and every workload also uses less peak RSS than full proofs. The report is
`/private/tmp/egglog-sliced-review-depless.jh27Wx/results.jsonl`, SHA-256
`c6f51f454f3792e4e1fcf395caa4a521994004c443f9f5a95efb7d4ef5737a7c`.

The earlier same-binary measurement at the pre-refactor checkpoint put capture
plus slicing at 2.00-2.12x normal/off suite wall. The separate whole-feature
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

| Base | Additions | Deletions | Net production LoC |
| --- | ---: | ---: | ---: |
| Whole-feature `4940be37` | 24,167 | 1,878 | **+22,289** |
| Logical-v1 `0d7ffbb` | 19,276 | 8,594 | **+10,682** |
| Pre-refactor `8598ad4` | 13,062 | 13,035 | **+27** |
| Reduction start `74eb9218` | 13,676 | 14,619 | **-943** |

The review-readiness work is therefore approximately LoC-neutral (+27) after
the rewrite-preservation feature and dependency-free atomic publication. The
whole reduction campaign remains 943 production lines smaller than its clean
start. Current production contains 465,679 nontrivia Rust syntax tokens, 4,891
fewer than `74eb9218`, and 121 `unsafe` keywords, one fewer than that base.

The accounting formats each Rust source with rustfmt 1.8.0, excludes dedicated
tests/snapshots/docs/ledgers and complete outer `#[cfg(test)]` items, then uses
the Myers line diff without rename credit. It reproduces the prior
`8598ad4`/`4940be37` oracle exactly.

Tests, snapshots, documentation, and this ledger receive no production-LoC
reduction credit. No new direct dependency was introduced versus `8598ad4` or
`74eb9218`; atomic publication uses only the standard library.

## Validation

Focused gates already passed during implementation:

- Full core suite: 125 unit tests and 2 doctests.
- Causal corpus: 151 core plus 36 experimental/workload programs.
- Proof snapshot regeneration: 349 core plus 44 experimental/workload cases.
- `make python-check` (Ruff, mypy, 173 pytest cases, 2 snapshots).
- `make benchmark-smoke` (2 successful isolated observations).
- DD checks, focused pre-mutation guards, the four-thread ordinary insert
  canary, CLI rewrite/collision replay canaries, formatting, and diff checks.

Final required gate:

`make proof-tests` passed 349 core and 44 experimental/workload cases. Without
rerunning that subset, `make check` then passed lockfile validation, formatting,
Ruff, mypy, both Clippy configurations, 173 Python tests, the full Rust
workspace and doctest suite, and the DD timing-summary integration test.

## Explicitly deferred

- Root-cause and correct `CS-REPLAY-EQSOLVE` without expanding recording merely
  to hide the defect.
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
