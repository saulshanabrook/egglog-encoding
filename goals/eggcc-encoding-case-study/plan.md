# Eggcc case study for injectivity and disequality

Produce evidence for a later paper section by testing whether the encodings find a real compiler bug, enable a useful optimization, or replace manual analysis. Begin with semantic eligibility and a controlled retarget; expand compiler/runtime work when a concrete promising case needs it. A documented negative result with a measured illustrative fallback satisfies the goal. Do not draft the paper.

The accepted [facts](facts.md) define the outcomes. The [source map](source-map.md) records setup observations and exact entrypoints; none of the proposed compiler experiments has run yet.

## Ordered work

1. **Freeze reproducible baselines and isolate experiments.** Refresh the current eggcc checkout, PR #119, relevant upstream history, and existing local changes; record the actual chosen revisions rather than assuming setup SHAs remain current. Create or reuse matching worktrees under `/Users/saul/p/wt/eggcc/` and `/Users/saul/p/wt/egglog-encoding/`. Preserve both primary checkouts and other goals' artifacts. Record both eggcc manifests/lockfiles, tool versions, build flags, binary hashes, and source diffs in a study manifest. Initially use the provided eggcc branch; qualify branch-specific findings unless reproduced upstream.

   **Verify:** compare pre/post status and file hashes for preserved checkouts; inspect `git rev-parse HEAD`, `git diff --binary`, and both resolved Cargo metadata outputs. Record a common Rust toolchain for each performance contrast, trying 1.91.0 first; if the original pin cannot use it, retain that limitation and rely on the same-engine contrasts below for feature attribution.

2. **Audit the two main leads before adding axioms.** Inspect `schema.egg`, `utility/{canonicalize,util}.egg`, `type_analysis.egg`, `interval_analysis.egg`, `optimizations/{mem_simple,memory}.egg`, and `schedule.rs`. Record each candidate's mathematical law, context, expected benefit, existing equivalent reasoning, and counterexamples. Reject blanket injectivity of `Concat`, `Bop`, and `Top`; justify any narrower operator-specific law separately. Check `Single` and literal wrappers separately from context-sensitive `Const`. Preserve the existing top-level constant guard unless a stronger rule is justified.

   For aliasing, distinguish three notions: raw equality-sort `!=` tests distinct current e-class IDs; `known-disequal?` finds an asserted or derived disequality witness under the chosen axioms; nonalias requires addresses to differ on every applicable defined execution. The first does not establish the second, and the second alone does not establish the third. Investigate exact address keys or sound possible-address sets only with explicit conditions; unequal intervals can overlap, so inequality alone does not imply disjointness. Include repeated allocation sites, unknown/call-derived pointers, branch assumptions, lifetime and offset arithmetic where relevant. The optional loop-analysis record comparison is a secondary lead, not a reason to enable the entire optional analysis automatically.

   **Verify:** retain executable counterexamples and positive/negative semantic checks for every implemented assumption. Include unreachable contexts, zero/symbolically-zero offsets, same-pointer and overlapping-address controls. Explicitly check that unsupported disequality/nonalias witnesses and forbidden rewrites remain absent; unknown query controls must remain undefined. Use distinguishable stored values so bad memory reasoning cannot pass accidentally. A violation caused by an invalid new axiom is a rejected candidate, not an eggcc bug. If the audit leaves no justified lead needing integration, record that scoped result and proceed directly to the fallback in step 5.

3. **Establish an engine-only retarget.** First use a small dependency-only Rust probe to exercise the host APIs actually used by eggcc: program execution, evaluation/extraction, serialization and function-to-DAG conversion. Add separate feature capability checks in ordinary mode under NEE and EE. Then point both eggcc `Cargo.toml` files at the same isolated `egglog-experimental` path and regenerate both lockfiles. Keep analysis/optimization behavior unchanged. Adapt real incompatibilities narrowly; validate serialization through Tiger and reconstruction into a fresh graph, not just successful parsing.

   **Verify:** run both `cargo +1.91.0 check --locked --tests` and the equivalent command with `--manifest-path dag_in_context/Cargo.toml`. Inspect both resolved dependency graphs for the intended engine/core versions. Run the arithmetic, constant and memory canaries below. Preserve the native extractor and all passes; a selected-pass `.egg` replay is diagnostic evidence only. Broader compatibility work is allowed when it advances a justified case; record the reason and checkpoint instead of silently changing the workload.

4. **Build controlled prototypes and search for incremental value.** Reproduce current constant checks and active `NoAlias` successes before claiming additional coverage. Use small Bril controls first, then extend only promising candidates. A bug search must use sound invariants and reproduce the baseline fault. An optimization/relation replacement must show the actual transformation or analysis effect and correct full compiler output. Existing forwarding, missed-load snapshots, two-allocation tests and loop cases are starting points, not established wins. Keep optional-analysis activation separate from the default analysis.

   | Arm | Engine and behavior | What the contrast establishes |
   | --- | --- | --- |
   | A | Original pinned engine and unmodified compiler | Historical/compiler baseline. |
   | B | Retargeted engine with compatibility changes only; no new encoding behavior | A to B includes the engine upgrade and adaptation. |
   | C | Same engine/configuration as B, with justified annotations/assertions/query checks | B to C isolates encoding/detection costs and coverage. |
   | D, when applicable | Same engine as C, with the proposed optimization or analysis replacement | C to D isolates its incremental effect. |

   Use NEE/EE subarms when assertion representation is relevant. For an equivalent manual-analysis comparison, preserve the same inference/output contract; report intentional differences in logical strength. Fix contexts, schedules, pass counts, extraction, thread counts and rule options across each contrast. Undefined query results mean unknown. Use `:naive` for query rule bodies and explicitly schedule equality injectivity; do not claim missing constructor-disjointness or multiargument reverse support.

   **Verify:** require nonzero focused test counts, expected transformation evidence, and source/optimized interpreter agreement for every input variant, plus explicit absence of unsupported inferences. The default interpreted file trial performs the output comparison; sequential/no-context trials do not, so obtain explicit interpreter receipts for every configuration used in claims. CLI JSON needs an assertion that both interpreter fields are non-null and equal. Retain `# ARGS:` variants for multiple inputs. Seeded faults are useful controls but must be labeled separately from genuine bugs.

5. **Decide whether an eggcc case is convincing; take the fallback if necessary.** Maintain a candidate assessment with evidence-backed statuses: rejected on semantics, already supported, prototyped, useful, neutral/regressive, or blocked on a concrete integration requirement. There is no two-prototype cap. Pursue broader compiler/runtime changes when a candidate's law, intended transformation and expected evidence justify them. If the investigated leads produce no defensible case, state that scoped negative conclusion and why; do not claim impossibility. Build a small standalone example using the actual encodings, clearly labeled illustrative rather than production-derived, with meaningful positive/negative checks and an interpretable cost comparison.

   **Verify:** every final claim links to supporting artifacts or an explicit limitation. Run the fallback checks with the appropriate encodings if that path is used; otherwise record it as not applicable.

6. **Collect costs after correctness is established.** Add a small case-specific collector under `scripts/eggcc_encoding_case_study.py` and fixtures/configuration under `benchmarks/eggcc-encoding/`; reuse existing process measurement support rather than adding a generic benchmark framework. Keep durable raw evidence under ignored `benchmarks/local/eggcc-encoding-case-study/`, outside `target/`, without changing other studies' caches. The collector records complete commands/configuration, input/binary hashes, correctness receipts, exit/timeout status, wall time and defined peak-RSS scope. Time release binaries without interpretation or diagnostic instrumentation. Start with one warmup and ten alternating/interleaved observations per endpoint and case; retain raw rows and variability. Increase sampling only if uncertainty warrants it.

   Report optimizer time and memory per workload. Generated-program performance requires separate validated execution and separate labeling. Use `./bench.py` for standalone `.egg` comparisons, explicitly selecting ordinary `off` treatment so its proof default cannot change the workload. NEE/EE comparisons require a meaningful assertion workload; engine-only replays cannot substitute for full compiler measurements. Retain failures and negative/neutral results.

   **Verify:** the collector's `verify` command checks manifest hashes, nonempty observations, conditional claim evidence and correctness receipts. Its `figures` command regenerates tables and standalone SVG/PDF figures from raw rows, without an overall aggregate. Test meaningful failure modes: mismatched interpreter outputs, zero selected tests, incomplete compiler runs, missing rows and mismatched provenance. New collector commands are to be implemented here; they do not exist at setup time.

7. **Deliver the evidence dossier and complete validation.** Write `report.md` alongside this goal with the encoding laws, candidate assessments, successful cases or scoped negative result, per-case costs, limitations, and a recommendation for the later paper section. Link portable rerun instructions, source patches, raw observations and figure sources. Preserve author-facing detail outside the paper and do not edit `/Users/saul/p/extended-egglog-paper`. Run the affected repositories' full checks after final implementation changes, then verify a fresh artifact directory can reproduce a representative result and regenerate figures.

   **Verify:** use eggcc `RUSTUP_TOOLCHAIN=1.91.0 make test` and `RUSTUP_TOOLCHAIN=1.91.0 make nits`, adjusting the explicit override if a different common toolchain was selected; these cover root and standalone DAG contexts. Run the encoding root `make check` for changes there, plus meaningful collector tests. Existing proof tests may run as regressions, but new query proof support and Lean work are outside scope. Record unavailable checks and their precise impact; unsupported measurements cannot become paper claims.

## Concrete verification entrypoints

From an eventual isolated eggcc root after lockfile updates; commands are source-checked, not executed during setup. The root fixture filters below use substring matching to include configuration variants. Exact small-fixture names require the `_snapshot` suffix; always check the executed count. Only interpreted trials provide semantic output comparisons.

```bash
cargo +1.91.0 test --locked --release --manifest-path dag_in_context/Cargo.toml --lib convert_to_egglog_simple_arithmetic
cargo +1.91.0 test --locked --release --manifest-path dag_in_context/Cargo.toml --lib -- optimizations::memory::load_after_write_without_alias --exact
cargo +1.91.0 test --locked --release --manifest-path dag_in_context/Cargo.toml --lib -- interval_analysis::test_if_constant_fold --exact
cargo +1.91.0 test --locked --release --no-default-features --test files -- constant_fold_simple-optimize
cargo +1.91.0 test --locked --release --no-default-features --test files -- mem_simple_store_forwarding-optimize
cargo +1.91.0 test --locked --release --no-default-features --test files -- mem_simple_redundant_load-optimize
cargo +1.91.0 test --locked --release --no-default-features --test files -- mem_loop_store_forwarding-optimize
```

For CLI correctness, run a built binary with `--with-context --run-mode optimize --interp --run-data-out CASE.json INPUT.bril`, retain its actual configuration, then assert `original_interpreted is not None`, `result_interpreted is not None`, and equality of those fields. Omit `--interp` for timing. The harness and CLI have different `non_weakly_linear` defaults; do not compare them as the same treatment.

The proposed collector exposes `collect`, `verify`, and `figures`, taking an explicit study manifest/result path. A clean rerun must be documented using its final actual CLI. For standalone encoding checks, reuse `cargo test -p egglog-experimental --test injectivity --test injectivity_disequality` and the injectivity file-harness filter; run `make check` after encoding changes rather than redundantly rerunning its proof subset.

## Accepted automated-verification map

| Fact ID | Required evidence |
| --- | --- |
| `isolated-baselines` | Version/configuration manifest, both Cargo dependency graphs, source/binary hashes and preserved-checkout pre/post comparison. |
| `case-correctness` | Positive/negative regressions, nonzero harness counts and checked non-null interpreter-output equality across arms/inputs. |
| `bug-claims` | Baseline reproducer and violated invariant for each real-bug claim; separately labeled seeded tests; explicit N/A if no bug is claimed. |
| `optimization-claims` | Complete optimizer/extractor/reconstruction result, transformation evidence and correctness receipt; explicit N/A for replay-only or no-optimization outcomes. |
| `performance-evidence` | Repeated per-case raw time/RSS rows, statuses, fixed treatment boundaries, variability and separate program-performance labeling. |
| `reproducible-artifacts` | Collector verification, hash/path consistency, fresh-directory rerun, regenerated figures/tables and source commands. |
| `fallback-example` | If used, executable semantic checks and ordinary-mode cost measurements; otherwise explicit N/A. |

Semantic validity, scope assessment, negative conclusions, proof boundaries and paper relevance require manual review; automated checks support rather than prove those judgments.

## Remaining uncertainties

- Visible API compatibility does not establish that the current schema, schedules, serializer and native extraction round trip work on the new engine.
- Sound useful annotations may be narrow or redundant. Contextual equalities and pointer semantics are the main semantic obstacles.
- A real case may cost more than existing manual rules or offer no new optimization. The report must retain that result rather than selecting only favorable cases.
