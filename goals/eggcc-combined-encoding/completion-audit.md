# Completion audit

Complete: functional/source checks, independent semantic and document reviews, official compiler gate execution, fresh failure attribution and final preservation comparison are recorded. The [accepted facts](facts.md) and [approved plan](plan.md) remain unchanged. Official test/lint gates remain failed on limitations reproduced in the fresh pre-integration control; they are not relabeled as passes.

The result is a **richer joint integration** in an existing compiler check. It is not a new bug, optimization, speedup or scoped negative. Untested candidate directions remain open.

| Accepted fact | Evidence and disposition |
| --- | --- |
| `joint-case` | Same Function/Arg → ExpectType/HasType obligation; 50 intermediate query observations and ten fixed-input consumer outcomes show both annotation and selected-query contributions. |
| `richer-reasoning` | Pointer and multi-argument list structure propagate an equality-sort leaf distinction through the nested tuple to the diagnostic. No primitive payload panic, cancellation or reverse inference is required. |
| `impact` | Validated integration qualifies under the accepted outcome boundary. No new baseline bug, optimization or speedup is claimed. |
| `comparison` | Existing, equivalent manual and combined checks report the same nested mismatch. Annotation removal loses the composite query witness; tag-only query use retains the diagnostic but lacks its nested premise. |
| `soundness` | [Finite type contract](findings/type-contract.md) and [independent semantic review](findings/type-review.md) justify four injective free constructors and separate tag laws. Helpers stay unmarked; unsupported/missing/unknown coverage and collapsed tags fail explicitly. |
| `implementation` | Nine authored compiler-delta files relative to the reconstructed baseline; default-off modes and bounded existing type metadata. No engine extension, proof support, Lean work, paper edits, commits or pushes. |
| `correctness` | 18 engine tests, nine focused DAG tests, 54 independent Rust Type comparisons, one five-mode native host test, one CLI-parser test and ten primary CLI optimize/emit runs pass. Full candidate DAG passes 83 tests. Both root suites pass 2,421 integration tests; the official test/lint failures are freshly matched as described below. |
| `claims` | Machine checkpoint flags explicitly reject new-bug, optimization, speedup, unrestricted-solver and required-cancellation claims. Internal malformed IR and diagnostic normalized reparses are labeled separately from valid-source execution. |
| `preservation` | Isolated candidate/control checkouts, exact reconstructed source/dependency maps, retained source archives/patches and fresh machine-readable results. Final comparison: all 30,609 protected old files unchanged; candidate/control source and accepted goldens unchanged. |
| `explanation` | [Explanation](report.md), [reference](reference.md) and [reproduction guide](reproduction.md) show one connected inference, actual before/after rules, old/manual outcomes and limits. [Independent document review](findings/document-review.md) found no blocker; optional representation-name clarification applied. |
| `negative-result` | Conditional negative-result branch was not taken. [Candidate discovery](planning/consumers.md) remains a set of unexhausted leads, not evidence of universal impossibility. |
| `prior-example` | Earlier Boolean-observer study preserved as a separate fallback. This result uses equality-sort structural propagation in the same type diagnostic and does not count repetition of the old example. |

## Functional evidence binding

The [final functional checkpoint](../../benchmarks/local/eggcc-combined-encoding/consumer/oracle-final/checkpoint.json), SHA `227599b8ac493ecb60b012191d8d56b7ae90e602ad721992f8c00c8ec2a6b985`, binds source manifest `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`. Source archives, full patches, commands, environment, return codes, stdout/stderr, binaries and machine-readable outcomes are retained under ignored `benchmarks/local/eggcc-combined-encoding/`.

[functional-verification.json](functional-verification.json) records the coordinator's separate hash/outcome checks: all 794 current source files match, 50 query observations and ten consumer outcomes match the stated controls, all 54 oracle rows match independently computed expectations, and all ten primary CLI calls exit successfully through passes 0/1/2. Interpreted source/result strings are both `7\n`; emit-only rows are not counted as interpreted correctness. The final oracle test-only delta preserves the production closure used for the earlier native/CLI receipts; that reuse is explicit.

The initial test-before-fix failure in the experimental tag-consistency guard, missing Tiger executable and unmodified printed-output reparse failure remain retained. Five comment-normalized reparses are diagnostic only. None is relabeled as a baseline bug caught by the encoding.

## Official gate disposition and completion decision

The [final gate summary](../../benchmarks/local/eggcc-combined-encoding/final-gates/summary.json), SHA `b116e66101b0cd69c25ea53e7725e4b356c3fca3074999ef42c046c1192f1b69`, binds 47 terminal command receipts:

- Candidate/control official `make test` and `make nits` each return 2. Thirteen pending snapshot bodies match exactly, with 26 fresh exact-selected trials confirming one test per invocation. All three strict root/DAG Clippy source-site diagnostics match the control. No snapshot acceptance, lint allowance or unmatched new failure is reported.
- Candidate root: 37 library, one CLI and 2,421 integration tests pass; control: 36 library and 2,421 integration tests pass. Both have two ignored documentation tests. Remaining full DAG suites pass 83/74 tests. Prettier and all four root/DAG formatting checks pass.
- Default-Off public prologues are exactly 185,221 bytes, SHA `d5aacd0b84d58c0674b18188c43e25f30488c1920ae54142391508dfec9c76b7`. Existing five root and ten DAG observer canaries are covered by the full suites without redundant subset reruns.
- Candidate 794 files, control 788 files, encoding 969 files and accepted snapshots remain unchanged. All 30,609 protected old files remain unchanged. Only the 13 retained generated `.snap.new` files per new role were added. All owned command processes are terminal.

The accepted positive completion path is satisfied: a richer joint encoding reaches a real existing compiler diagnostic, has an equivalent manual comparison, independent finite oracle and feature-contribution controls, and preserves valid-source native behavior. The failed official gates remain a disclosed inherited integration limitation. No speedup campaign, new baseline bug, exhaustive candidate search or paper edit is part of this completion.
