# Find an impactful EggCC encoding case

Continue beyond the completed local-address example until there is an additional reproducible compiler/analysis speedup, generated-program speedup, or genuine baseline compiler bug, or an evidence-backed review supports a scoped negative conclusion. Improvements to the encoding are also in scope. The accepted [facts](facts.md) define the outcome; an encoding improvement, fewer rows, or a removed operation alone does not establish the impact objective.

This is an execution plan. Setup discovery has been read-only; the experiments below have not run.

## Starting evidence and approach

The preceding [study report](../eggcc-encoding-case-study/report.md) validates a small load-elimination case but claims no stable compiler-time/RSS benefit or genuine bug. It did not measure generated-program runtime. Preserve that result rather than retiming it under a new name.

The dirty primary encoding checkout does not contain the injectivity feature; select a verified feature source in a new worktree rather than rebuilding it in that primary checkout. The encoding [source review](planning/encoding.md) confirms a separate reasoning gap at feature revision `392b6d6b`: reverse search only handles marked unary constructors. The proposed extension is ordinary congruence:

```text
f(a₀, …, aₙ₋₁) ≠ f(b₀, …, bₙ₋₁)
  and aⱼ = bⱼ for every j ≠ i
  imply aᵢ ≠ bᵢ.
```

For example, `f(a,b) ≠ f(c,d)` and `a = c` imply `b ≠ d`. Without sibling equalities, parent disequality gives only a disjunction. This reverse rule does not require injectivity. Equal-parent cancellation and child-difference-to-parent-difference remain restricted to marked injective constructors.

Use two parallel discovery tracks after freezing source: improve this bounded query fragment and investigate real EggCC consumers. Integrate only after the semantic mechanism and a discriminating test are clear. Keep one owner per implementation surface and one owner for shared builds/timing; review the combined proposal before each substantial new experiment.

## Ordered work

1. **Freeze current baselines and isolate the follow-on.** Refresh the selected EggCC and encoding revisions, dependency pins and feature-branch state when execution starts. Preserve dirty primary checkouts and the preceding study's frozen evidence. Create new worktrees under `/Users/saul/p/wt/eggcc/` and `/Users/saul/p/wt/egglog-encoding/`, reconstructing previous uncommitted prototype changes only from its verified source patch/archive when needed. Keep new raw artifacts under ignored `benchmarks/local/eggcc-encoding-impact/`, outside Cargo `target/`. Reuse compatible build caches and native/runtime setup without altering frozen binaries.

   Record both Cargo manifests/lockfiles, toolchain, native Tiger identity, feature options, contexts, passes, extraction, source patches and binary/input hashes. Historical original-engine and engine-only controls remain useful references; new feature contrasts require fresh, matched observations and must not pool the previous noisy cohorts.

   **Verify:** pre/post hashes and status/HEAD/branch comparisons for preserved source; hashes of reused previous evidence; `git rev-parse HEAD`, binary-safe source patches and both resolved Cargo dependency graphs. Allow only explicitly owned new goal/artifact paths in preservation comparisons. Begin with the previously validated Rust 1.91.0/tool setup, recording any necessary change.

2. **Implement the remaining-child query fragment first.** Work in `egglog-experimental/src/disequality.rs`, its existing `tests/injectivity_disequality.rs`, and the executable example `tests/injectivity/injectivity-disequality.egg`. Add the missing unmarked cross-sort binary case before changing implementation. Generalize one mechanism to n-ary reverse congruence; preserve marked-only forward inference. Update module/reference explanations and the mathematical example deliberately, including old negative tests that encoded the unary-only limit.

   Start with constructor tables whose outputs and focused child are unionable equality sorts, and whose siblings are primitives or unionable equality sorts. Primitive siblings use native equality. Unknown query results remain undefined; different current class IDs do not establish disequality. Retain ordinary-mode-only rejection in term/proof modes. Direct primitive disequality assertions/queries, container reasoning and arbitrary function tables remain outside this first slice. Find unmarked input sorts as well as marked ones; do not accidentally depend on EE's internal representation tables.

   Preserve the read-only contract: no derived parent/child pair relation, missing applications, unions, persistent query cache or new graph rows. A transient per-query index or scan is allowed; measure its cost before adding persistent indexes or core APIs. Keep cycles finite with visited typed-pair search.

   **Verify:** run meaningful positive and negative cases for unary/binary/ternary positions, two unresolved children, unequal siblings, unmarked forward inference, mixed integer/bool/string siblings, late unions, scheduled injectivity, subsumed rows, pop/redeclaration, cycles, contradictions and no graph/table growth. Run both NEE/EE and core/extended scheduling. Compare supported pair queries against an independent iterative least-fixed-point oracle over a finite fixed application graph. This supports a precisely stated fragment, not unrestricted completeness.

   **Schedule contract:** queries inspect the committed graph and do not perform injectivity unions. Consumers must rerun after hidden parent witnesses or sibling equalities change, using the required `:naive` context. `check-contradiction` closes private disequality normalization only; it is not a joint fixed point with injectivity and consumers. Test the actual bounded pipeline order. Add a public closure/materialization facility only if a concrete consumer needs it, as a separate reviewed slice with update/convergence tests. Preserve fail-fast audits inside any generative saturation.

3. **Build and test an expanded candidate map.** Use the [consumer discovery](planning/consumers.md) and [measurement discovery](planning/measurement.md) as starting evidence, not as established wins or an exhaustive list. For each lead record the source consumer, mathematical invariant, active/default versus optional status, existing equivalent reasoning, expected observable effect, workload coverage, smallest falsifying experiment and current disposition.

   Begin with these concrete leads, expanding the map when evidence suggests others:

   | Lead and source surface | First experiment and boundary |
   | --- | --- |
   | Signed endpoints and interval overflow: `dag_in_context/src/utility/canonicalize.egg`, `interval_analysis.egg`, `interpreter.rs` | Test valid wrapping-i64 endpoint comparisons and multiplication sign cases on unmodified baseline with small-value controls. These are untested suspicions; the existing Const guard may already detect the fault. |
   | NoAlias production versus demand: `dag_in_context/src/optimizations/mem_simple.egg` | Measure untimed produced pairs versus actual write/load demands in existing inputs. If a sound same-anchor offset domain is reached, compare query, materialized manual pairs **and direct primitive demand guards**. Different anchors alone prove nothing; do not inject generic Add. |
   | Call-site fresh regions and loop memory: `mat-mul.bril`, `csrmv.bril`, memory consumers | Inspect actual inlined passes for blocked hot loads/stores. Only then add validated fresh-return/effect/lifetime certificates and a justified loop consumer. Current keys do not cover these dynamic call/loop forms. |
   | Conditional fixed-split tuple cancellation: `schema.egg`, `utility/util.egg`, `optimizations/{passthrough,loop_invariant}.egg` | Find real same-result/equal-prefix-length pairs and projection costs. Compare a guarded rule or fixed-split representation with existing projection closure; arbitrary Concat stays unmarked. |
   | Scoped false-Eq information: `interval_analysis.egg` | After the query slice, test a bottom-aware context-local bridge. Impossible branches must not panic globally or leak facts; parent Expr disequality alone is not pointwise runtime inequality. |
   | Immutable type/Term metadata: `schema.egg`, `type_analysis.egg`, `utility/terms.egg` | Find a missed sound check or removable material cost; close as redundant if existing normalization already supplies it. Mutable interval/points-to records remain excluded. |

   Full workload paths and line evidence are in the two discovery notes. `csrmv` adjacent rowptr reads may produce irrelevant NoAlias pairs, but contain no intervening write needing commute; the matrix hot loop crosses array roots. Neither is an established hit. Do not use the current `vsmul` as a scaled vector-loop result: its source lacks the backedge.

   Investigate sound constructor/constant checks, active alias/memory consumers, scoped branch/equality facts and other promising immutable analyses. Reuse rejected cases only when a new restriction changes the semantic argument. Arbitrary Concat/Bop/Top injectivity, globally contextual Const cancellation, mutable points-to-record injectivity and structural key disequality as universal runtime nonaliasing remain invalid shortcuts.

   Cheap suspected baseline bugs should be tested before expensive integration. For each one, establish defined input semantics and a minimized baseline failure; distinguish a wrong output from a compiler panic, timeout or already-existing guard. Explain whether the encoding contributes to detection/localization or whether the finding is ancillary to the encoding case study. Source inspection alone establishes no bug.

   **Verify:** retain executable positive/negative or counterexample checks and exact diagnostics. A real bug requires a baseline reproducer and sound violated invariant; seeded faults and invalid annotations never count. Existing or scaled workloads must actually reach the proposed consumer; missing coverage is a recorded rejection/extension decision, not a performance result.

4. **Integrate the strongest sound consumer and keep searching.** Choose the next prototype by expected impact and evidence cost. Write down the hypothesis, target transformation or analysis delta, owned files, expected correctness signal and early rejection gate before implementation. Broader compiler/runtime changes are allowed when tied to that case. Keep the existing full optimizer, native extraction and reconstruction unless a comparison explicitly documents a justified change.

   Memory cases must distinguish committed equality, witnessed disequality and semantic nonaliasing. Carry context, effect/liveness, valid bounds and overflow conditions into the consumer. New cross-call/loop reasoning requires its own semantics; the previous static allocation rank is not a global runtime identity. Do not export state-scoped witnesses to a global NoAlias relation.

   For every contrast use an engine-only/feature-off control on the same chosen engine, the feature treatment, and an equivalent manual analysis when replacing one. Separate encoding-query changes, added analyses/closure and consumer rewrites with ablations. Keep source options, passes, thread counts and backend settings fixed. Use NEE/EE subarms only when asserted-disequality representation is relevant.

   **Verify:** complete actual EggCC optimization/extraction/reconstruction, retain transformation or analysis receipts, run source/optimized output comparisons across all arms and input variants, require non-null matching interpreter fields and nonzero selected tests. Preserve negative cases where inference or a rewrite must remain absent. A standalone replay is diagnostic evidence only. Review correctness before timing.

5. **Measure promising effects with matched controls.** Reuse or narrowly extend the case-study collector and its tests in the new source worktree. Keep hash-validated manifests, raw observations, statuses and receipts under the new raw-artifact root. Select the compatible process runner deliberately and preserve current memory-guard/timeout behavior; do not overwrite it with the older study copy. Add a separate small native adapter only if a promising case needs it. Use release binaries with correctness interpretation and diagnostic instrumentation outside timed compiler runs. Run no overlapping builds, tests or other collectors on the measurement host during measured blocks, and record observed unrelated host load rather than attributing its effects to the feature. Use one warmup and a balanced/interleaved pilot, initially ten observations per endpoint for two arms or twelve for four-arm rotations. Use pilot variability to predeclare a separate confirmation cohort and uncertainty method, then reproduce a promising result independently; do not repeatedly extend one cohort in pursuit of significance.

   Report compiler/analysis wall time, defined compiler memory and generated-program runtime separately, per workload, with variability and all neutral/regressive results. The previous wait4 child RSS is not a simultaneous process-group peak. Define any phase-only timing explicitly and retain total compilation cost. For standalone `.egg` costs use public `./bench.py`, an explicit ordinary `off` treatment and a new explicit report path.

   Before native runtime sampling, screen the same-backend optimized IR/final code: LLVM may erase a Bril-level difference. Compile both emitted programs with identical backend/runtime flags and validate successful exits and outputs first. Predeclare the primary optimized backend (`O3_O3`); inspect final code as well as saved IR because saved `O3_O0` IR alone does not describe the final `O3_O3` compilation. Use `O0_O0` only as a separately labeled backend control. Exclude compilation, argument parsing and unrelated setup from a kernel claim; if reporting end-to-end execution, say exactly what it includes. Use scalable inputs only when their connection to a real consumer is clear. Operation counts alone do not establish runtime speedup. If using built-in instrumentation, check its terminal-print restriction and interval; on arm64 label `cntvct_el0` values elapsed counter ticks, not CPU cycles. Keep instrumented and uninstrumented artifacts and metrics distinct.

   **Verify:** collector rejection checks cover mismatched outputs/provenance, missing observations, failed runs and zero selected tests. Verify compiler and generated-program evidence separately; regenerate tables/standalone SVG/PDF figures from raw rows without an overall aggregate. Retain complete blocks without post hoc outlier deletion; stop or classify interrupted blocks rather than dropping unfavorable samples. Do not accept a timing claim from a median shift within the observed variability or from one favorable cohort.

6. **Continue until impact or an evidence-backed exhaustion review.** Keep the candidate map current with concrete dispositions: semantically rejected, redundant/already supported, not reached, implemented, neutral/regressive, positive, or blocked on a specific requirement. Pursue remaining plausible high-value leads rather than stopping after another neutral example or a fixed number of prototypes. After two no-progress cycles in one domain, reassess its mechanism and evidence rather than repeating the same implementation; this is not a limit on the whole search.

   A positive endpoint is an additional reproducible compiler/analysis or generated-program speedup, or a genuine baseline compiler bug, with its attribution and paper relevance stated. A negative endpoint requires independent review of the map and substantial targeted experiments: explain why each remaining plausible high-value lead failed or cannot presently be established. An untested promising lead prevents an exhaustion conclusion; a concrete external blocker must remain explicit. State the investigated scope, never that no possible use case exists. Useful encoding improvements and neutral examples still belong in the dossier.

   **Verify:** a reviewer checks the evidence behind candidate dispositions and challenges the proposed stopping decision. Resolve concrete objections by more experiments or a narrower supported conclusion. Record the final reasoning, without introducing an arbitrary time/token/prototype cap or additional user-approval gates during ordinary authorized research.

7. **Deliver and audit the complete dossier.** Write this goal's `report.md`, candidate map, rerun instructions and completion audit. Include laws, cases and origins, source checkpoints, measured effects or scoped negative findings, per-workload costs, encoding limitations, precise execution/proof boundaries and recommendations for the paper. Do not edit the paper itself or add new proof/Lean support.

   **Verify:** run the affected repositories' required checks after final changes, classify any failure against a matched unchanged control, and record precise limitations rather than claiming green gates. Reproduce a representative result into a fresh artifact directory and regenerate figures/tables; audit every accepted fact and recheck preservation. Existing historical snapshot/lint/runtime limitations must be revalidated if encountered, not silently ignored or repaired as unrelated work.

## Concrete validation entrypoints

Run these from the eventual isolated encoding workspace root after source changes, not during setup:

```bash
cargo +1.91.0 test -p egglog-experimental --test injectivity_disequality --test injectivity --test disequality
cargo +1.91.0 test -p egglog-experimental --test files injectivity
make check
```

Run focused EggCC consumers/canaries while iterating, then the required root/DAG gates after the final source change:

```bash
RUSTUP_TOOLCHAIN=1.91.0 make test
RUSTUP_TOOLCHAIN=1.91.0 make nits
```

CLI correctness uses the selected built binary with explicit options, `--run-mode optimize --with-context --interp --run-data-out RECEIPT.json INPUT.bril`. Assert `original_interpreted` and `result_interpreted` are both non-null and equal. Fixture input variants use `# ARGS:`; do not assume trailing CLI arguments are forwarded. Omit interpretation and diagnostic dumps for compiler timing. Record the CLI/harness default differences rather than treating them as identical endpoints.

After carrying the verified collector into the new encoding worktree, use explicit fresh manifest/result paths:

```bash
uv run --no-project --python 3.13 python scripts/eggcc_encoding_case_study.py collect STUDY.json RESULTS.json
uv run --no-project --python 3.13 python scripts/eggcc_encoding_case_study.py verify STUDY.json RESULTS.json
uv run --no-project --python 3.13 --with matplotlib==3.10.7 python scripts/eggcc_encoding_case_study.py figures STUDY.json RESULTS.json FIGURES_DIR
uv run --no-project --python 3.13 --with pytest==8.4.2 --with matplotlib==3.10.7 python -m pytest -q tests/test_eggcc_encoding_case_study.py
```

The collector and source-verified native preparation commands are detailed in [measurement discovery](planning/measurement.md). Any new runtime collector command must be documented and smoke-tested once implemented; it does not exist merely because this plan proposes it. New benchmark-runner changes also require root `make benchmark-smoke` with a temporary machine-readable report. Do not redundantly rerun `make proof-tests` after successful full `make check` without a new proof concern.

## Accepted automated-verification map

| Fact ID | Required automated evidence |
| --- | --- |
| `preservation` | New source/configuration manifest, frozen-input hashes, both dependency graphs and pre/post author-work preservation checks. |
| `encoding-gaps` | Requested red/green query case, finite-fragment oracle, NEE/EE and scheduler/lifecycle/primitive negative matrix; blockers explicit if a proposed extension is not implemented. |
| `correctness` | Actual compiler transformation receipts, nonzero focused test counts and source/optimized output equality across claimed arms/inputs. |
| `bugs` | Minimal sound baseline failure for each genuine-bug claim; seeded controls separate; explicit N/A if no bug is claimed. |
| `speedup` | Additional repeated attributable speedup evidence or a genuine-bug receipt; if neither is claimed, explicit N/A plus the manually reviewed exhaustion evidence. |
| `comparison` | Matched baseline/feature/ablation identities and equivalent manual analysis when applicable, with validated output contracts. |
| `measurement` | Complete per-workload raw rows, timing/memory boundaries, variability, independent confirmation and retained negative results. |
| `reproduction` | Hash/receipt verification, exact commands/inputs, fresh-directory rerun and regenerated tables/figures. |

Semantic justifications, workload relevance, candidate ranking, scope and exhaustion remain reviewed judgments. Automated checks support those judgments and do not prove compiler semantics or unrestricted logical completeness.

## Risks to keep visible

- More reverse-query edges can increase scans and transient memory despite adding no persistent pair rows.
- Consumer premises may be contextual or effect-dependent; an algebraically valid query rule cannot validate an unsound asserted parent disequality.
- Existing workload calls and dynamic indices may fall outside a narrow exact-address domain. Extending that domain requires a new semantic argument.
- LLVM may already remove a newly eliminated Bril operation, and host timing noise can exceed a plausible benefit.
- The prior retarget had independently reproduced snapshot changes and baseline lint failures. Those limit broad compatibility claims even when a focused experiment passes.
