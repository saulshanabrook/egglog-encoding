# Benchmark reproduction audit

## Current status — 25 September 2026

The reproduction effort was **active and incomplete** on this date. It covers complete source optimization and faithful
standalone `.egg` replay for Eggcc, HardBoiled, MISAAL, Churchroad, DialEgg, and
SpEQ. Target-device execution, Math/Luminal changes, performance collection, and
chart work are outside this goal. Ordinary reproduction does not establish
strict proof compatibility, extraction optimality, or paper execution timings.

The [live coverage report](local/reproduction/REPORT.md) is authoritative for
current per-case outcomes. The [corpus manifest](local/reproduction/corpus/manifest.json)
lists admitted files and every source/session alias; only its listed files belong
to the current corpus. Admission requires complete source optimization and actual
output checks, followed by successful ordinary replay at recorded identities.
HardBoiled instead uses exact author-published inputs and their original extraction
outputs. MISAAL now requires complete Egglog processing without downstream LLVM
lowering. Incomplete Egglog prefixes, historical successes at changed identities,
and unlisted older files remain diagnostic evidence.

| Family | Verified complete source and ordinary replay evidence | Remaining requirement |
|---|---|---|
| Eggcc | 97 runnable configurations; 582 replays and 2,928 native-output checks at the current optimized compiler/shared-adapter identity. | 94 configurations require the genuine Gurobi CLI and usable license access; see the [access investigation](reproduction/eggcc-gurobi.md). |
| HardBoiled | The user-selected author-published suite has 42 exact files and 2,074 original extraction outputs, all passing ordinary replay. Earlier 34 native parents remain historical evidence. | The public command passes all 42 files and 2,074 outputs; a repeated call reuses all 84 capture/validation receipts. Omitted GPU/AMX configurations remain coverage context. |
| MISAAL | In progress; consult the live report for current outcomes across 93 required generator/target pairs and 99 paper aliases. | Complete-source outcomes and ordinary validation remain in progress. Prepared generators and isolated canaries do not establish family coverage; nine extras remain separate. |
| Churchroad | Both required parents and both persistent-session replays pass, including actual synthesis feedback and 19 native-output checks. | The 27 later evaluation designs remain inventoried extras, not additional required WOSET cases. |
| DialEgg | All 24 required parents; 73 replayed sessions, 51 output-bearing aliases and 26 distinct files. [Final receipt audit](local/reproduction/diagnostics/final-family-sweep-0001/dialegg-final-audit.json). | Retain NMM160 as an extra and preserve alias/session distinctions. |
| SpEQ | All eight available-source applications pass complete optimization and ordinary replay, including original-C GEMM. [Final family summary](local/reproduction/diagnostics/final-family-sweep-0001/speq-summary.json). | Exact TPAL and TSVC2 inputs/setup remain missing after complete-archive and Docker dependency recovery; the [missing-input investigation](reproduction/speq-missing-inputs.md) states the exact requirements. |

The [optimized Eggcc/Churchroad refresh audit](local/reproduction/diagnostics/eggcc-churchroad-optimized-refresh-0002/audit-0001.md)
binds their current counts, settings and retained failures. The
[four-family clean-recipe map](local/reproduction/diagnostics/final-family-sweep-0001/four-family-clean-recipe-map.md)
links fresh preparation, complete canaries and ordinary receipts for DialEgg,
HardBoiled, Churchroad and SpEQ; its formerly pending Churchroad refresh is now
complete. It also records successful paired GPU/AMX observation controls.
[Eggcc preparation](reproduction/eggcc-preparation.md) documents the optimized
build recipe and preserved assertions. The external blockers above have concrete
recovery histories; none counts as a successful reproduction.

The [author-published HardBoiled collection](reproduction/hardboiled-published-suite.md)
is now the user-selected source: all 42 files pass ordinary replay with all 2,074
original extraction outputs restored from the exact parent revision. They map
to 26 paper GPU configurations plus 16 extra Conv1D sizes. The collection omits
`conv_layer-16`, `conv_layer-32`, `attention`, and AMX; retain the existing source
captures and mapping investigation as historical coverage evidence. These 42
published files are not 42 new native parents or a claim of complete paper
coverage. The coordinator selects these published files directly without Halide
regeneration. One strict-proof
canary passed; the other 41 files have no strict-proof validation claim.

### Locations and public commands

The [pipeline instructions](reproduction/README.md) describe pinned preparation,
family/case selection, guards and immutable retries. Durable
[settings](local/reproduction/settings.json), [stage receipts](local/reproduction/stages/),
the report and corpus live under ignored `benchmarks/local/reproduction/`, outside
Cargo's disposable build cache. Source parents, replay sessions, aliases and
distinct files are separate accounting units.

Run from the repository root:

```sh
# Resume all six families with the recorded preparation settings.
make reproduce-benchmarks

# Resume selected families through preparation, capture and ordinary validation.
uv run --locked python scripts/suite_acquisition.py reproduce --family eggcc --family churchroad

# Refresh the report without starting source optimization or replay.
uv run --locked python scripts/suite_acquisition.py reproduce --stage report

# Validate retained captures with the current ordinary engine.
uv run --locked python scripts/suite_acquisition.py reproduce --stage validate
```

Unresolved required cases keep full collection nonzero; historical AMX mappings
do not gate the selected published HardBoiled suite. The
report distinguishes those blockers from unsuccessful source runs. The
[pipeline documentation](reproduction/README.md) describes remaining reproduction
work and verification boundaries.
This corpus remains separate from the production benchmark catalog and
performance cache.

## Historical audit — 24 September 2026

The remainder preserves the initial audit against papers, published artifacts,
upstream source and then-retained local records. Its counts, failures, “current”
references and proposed next steps describe that date; the current section and
live report above supersede them. In particular, the historical AMX environment
suggestions and MISAAL capture boundaries do not alter the accepted goal's
exclusion of target-device execution.

**We have substantial Egglog input coverage, but have not reproduced every paper workload.** The old catalog counts describe our acquisition scope, not completeness against each paper. Some entries contain a complete independent Egglog call from a parent compiler run that later failed; others deliberately cover only one compiler phase.

This audit did not run generators or benchmarks, change the catalog or selections, or contact authors. It distinguishes source coverage from proof compatibility, resource admission, and reproduction of native application performance.

The recommendations about failed parents follow the later request to avoid including partial programs that error. They concern a **completed-parent benchmark population**. A complete independent call from such a parent can still be retained as an explicitly qualified per-call workload; it is not evidence of parent success. Completion of a declared capture/Egglog phase is also narrower than full native compilation and execution. In particular, MISAAL acquisition deliberately stopped before native legalization and execution.

## Files and measurements at the initial audit

- The catalog has **362 cases/configurations**: 226 marked captured, 47 blocked, and 89 intentionally deferred Math cutoffs.
- Its selected inputs resolve to **275 distinct workload/fact identities**, with **no missing selected files**. These are not 275 independently completed source applications.
- Five incomplete HardBoiled AMX parents and five incomplete MISAAL parents still contribute selected files. Their successful individual calls do not establish successful parent reproduction. The catalog needs an admission correction before claiming a completed-parent population.
- The latest engine, including the dedicated DAG implementation of `prove-extract`, changes the executable identity. Source extractions have also been restored in several families. The fresh coverage snapshot has **no currently admitted cases or matching measurements for its exact current identities and 300-second policy**. Historical measurements and validation remain evidence for their old identities; they cannot validate changed programs or binaries.
- The production cache remains intact: **9,081 observations**, SHA-256 `c3483925bbf359996e88152ea5dcbfd059c11eb2bfaf9bcb8fdf1d532021c4c6`. This audit appended none.

The current Egglog executable SHA-256 is `7eb04703af3707fb60c1ebe8cef66a86f72de1dc55081c636b8ea38fe06229b2`. The inspected catalog SHA-256 is `2a59f9b20a1d859662c2bc6be69688ee497571a5e7ca561432449c333ac8ab59`.

Evidence: [catalog snapshot](local/reproduction-audit-20260924/catalog-snapshot.json), [all 362 catalog cases](local/reproduction-audit-20260924/cases.csv), [current coverage](local/reproduction-audit-20260924/current-coverage.md). Each family report below includes source links, exact boundaries, and retained diagnostics.

## Paper-to-input summary

| Family | Paper/artifact population | What we have | What is still missing or qualified |
|---|---|---|---|
| Math | One combined seven-seed graph, 100 iteration endpoints | Proof workloads 1–11; separate no-proof reproduction 1–13 | 12–100 intentionally deferred; our schedules differ from the paper; non-incremental Egglog curve absent |
| Eggcc | 96 source programs; several compiler passes and extractor experiments | All 96 first-pass exports | Later passes with their actual host-extracted inputs; native effect-safe extraction; other paper configurations |
| Luminal | Seven preserved model exports; no evaluation-paper denominator identified | All seven files and schedules | Complete original export provenance; broader current model zoo is a possible extension, not a proven missing paper population |
| HardBoiled | 29 identified GPU graph configurations; seven supported AMX schedule/layout cells | All 29 GPU configurations plus one extra; files from five AMX executables | All five AMX parents abort; mapping five executables to seven supported cells remains unresolved |
| MISAAL | 33 workloads × three targets = 99 cells, mapping to 93 generator/target pairs | 52 original-backend Egglog phases complete; one qualified historical add capture | Six partial phases, 34 absent exports among paper-related pairs; artifact settings differ from the paper |
| Churchroad | WOSET paper's worked mapping example plus solver experiment; later evaluation has 27 designs | Two integration-circuit mapping prefixes | External synthesis, returned graph updates, final extraction; later 27-design population not cataloged |
| DialEgg | Five runtime applications; nine named timing kernels | All nine kernels represented, plus extra 160MM; 13 distinct selected calls | Complete parent pipelines and canonicalization treatments; exact timing wrappers differ |
| SpEQ | Ten applications | Eight have complete application Egglog bytes; seven successful translation replays | PolyBench GEMM does not derive the intended result; TPAL and TSVC2 inputs/setup missing |

Paper cells, source programs, fresh egraph calls, and regionalized extraction problems are different units. Runtime sizes that leave the compiler graph unchanged and non-Egglog baselines do not imply additional missing `.egg` files.

## Math / PLDI 2023 Egglog

The paper's §5.3/Figure 7 uses the combined seven seeds and 24 analysis-free rules at 100 cutoffs, comparing Egg, Egglog, and non-incremental Egglog. The artifact uses backoff scheduling and seven repetitions. The Math generator explicitly overrides its generic simple scheduler; Egglog's match limit is 1,000. [Paper](https://ztatlock.net/pubs/2023-pldi-egglog/2023-pldi-egglog.pdf), [pinned generator](https://github.com/pldi23-eqlog-ae/micro-benchmarks/blob/5360490242ec846d3323f3a8e83e3df78cb81f2f/src/math.rs).

All inputs/rules are available. Our 1–11 proof workloads use simple/seminaive scheduling and a frozen equality first established at each endpoint. Cutoffs 12–100 need no missing source acquisition; execution cost and proof-witness validation were intentionally deferred. The separate upstream 1–13 no-proof/no-check experiment is another scheduling treatment. Neither is a reproduction of the original three-curve figure.

Herbie and pointer analysis remain explicitly excluded by the earlier scope decision. Analysis-dependent Math and Lambda examples with semantic discrepancies also remain documented exclusions. They must not disappear into a claim that we reproduced the entire Egglog paper.

**Next:** retain the agreed 1–11 scope, or separately reproduce the paper's original schedule and third engine if full Figure 7 replication is wanted. [Detailed Math audit](local/reproduction-audit-20260924/math.md).

## Eggcc

The paper reports **96 programs**: 64 Bril, 30 PolyBench, Fenwick, and raytracer. Its **9,610 regionalized graphs** are extractor inputs, not 9,610 standalone Egglog executions. All 96 source programs and first-pass exports exist locally. [Paper, §§7–8](https://ztatlock.net/pubs/2026-oopsla-eggcc/2026-oopsla-eggcc.pdf).

Our capture requests `--run-mode egglog --stop-after-n-passes 1`. The pinned default parallel optimization schedule has three passes. Each creates a fresh egraph, executes rules, runs the host extractor, and uses that selected program as the next pass's input. Consequently we are missing later pass inputs and their actual extraction feedback. Repeating pass-one text cannot reproduce them. Built-in extraction is not a substitute for the effect-safe Statewalk DP/ILP extractor. [Schedule](https://github.com/egraphs-good/eggcc/blob/16be0063133ef0b8ba21cd75ee377002dc3ecbed/dag_in_context/src/schedule.rs#L161).

The current replay checks an inferred function/body type; it does not extract and prove equivalence of the native optimizer's final program. It can be labeled a first-pass analysis workload, but not a full optimization reproduction. The official artifact also distinguishes its small default region sample from its paper-scale experiment; the VM's source revision was not verified against our pin. [Artifact README](https://zenodo.org/api/records/21479729/files/README.md/content).

**Next:** capture later fresh-egraph passes using genuine preceding host-extraction results, preserve their output contract, and reconcile the exact artifact revision/configuration. The original effect-safe extraction experiments require their own harness. [Detailed Eggcc audit](local/reproduction-audit-20260924/eggcc.md).

## Luminal

All seven pinned exports are present and hash-verified: Gemma, Gemma4 MoE, Llama, paged Llama, Qwen, Qwen3 MoE, and Whisper. Their schedules are retained. They come from a compiler-regression reproduction, not an identified evaluation-paper suite. The replay's derived lowering check is not full inference correctness or selection of a runtime GPU kernel. [Pinned collection](https://github.com/saulshanabrook/egglog_repro/blob/7fb0194812b5b11e41a286d8b55e48e3b0bfcd66/README.md).

Neither that collection nor the inspected current official README supplied an evaluation-paper population. We therefore cannot claim paper-wide completeness. Original compiler revision, checkpoints, dtypes, shapes, backend, and export recipe are not fully mapped by the retained file pin. Current upstream includes Flux2, Llama3.1 FP8, and YOLOv11 modules without counterparts among the seven named dumps; these are optional new acquisition targets. [Current model manifest](https://github.com/luminal-ai/luminal/blob/3432aeeaba8650e7ea5031dbcad94dd7af355906/crates/model_zoo/src/lib.rs).

**Next:** establish original export provenance before describing broader coverage; define a separately pinned model-zoo campaign if expanding beyond the seven dumps. [Detailed Luminal audit](local/reproduction-audit-20260924/luminal.md).

## HardBoiled

The paper's GPU graph-changing configurations reconcile to **29**: 16 Conv1D sizes, six convolution/resampling cells, four ML shapes, resize-down, recursive filtering, and Tensor Core denoising. All are captured; resize-up is an additional artifact variant. Table II's four resize output sizes are runtime parameters to the same compiled library. CUDA/vendor baselines do not invoke the accelerator Egglog optimization and are not missing `.egg` programs. [Paper, §§IV–V](https://arxiv.org/html/2512.02371v2).

AMX is incomplete. Table I has ten schedule/layout cells, seven supported and three unsupported. The artifact exposes five executables without a verified mapping to all seven supported cells. All five emitted complete individual Egglog files, then their parent runs aborted. They may have missed later invocations. The retained attributable logs report `amx synthesized`, then missing `fopen64` during Linux-target execution on macOS. Three VNNI programs overwrote one log, so that particular error cannot be assigned independently to all three. [Artifact instructions](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/README.md#support-for-schedules-in-amx).

This is strong platform-mismatch evidence, not evidence of a proof-encoding problem or proof that ARM is the sole cause. The intended control is Linux/x86 with the specified LLVM and Intel SDE, plus separate per-run logs. An amd64 container on this Mac is not established to support the full SDE/JIT workflow.

**Next:** quarantine the five AMX parents from completed-parent admission, reproduce them in the intended environment, and obtain the seven-cell configuration mapping. Keep all failed captures as diagnostics. Current selection still includes them; this audit did not change it. [Detailed HardBoiled audit](local/reproduction-audit-20260924/hardboiled.md).

## MISAAL

Table 4 has **33 workloads × three targets = 99 cells**. The three batched-matmul rows share a batch-dynamic generator, leaving **31 generators per target, 93 paper-related pairs**. The catalog's 102 entries add nine extra tensor recipes. Runtime batch choices do not automatically require separate `.egg` exports. [Paper, §5 and Table 4](https://hydride.cs.illinois.edu/files/2025/04/MISAAL-PLDI-Camera-Ready-3.pdf).

| Paper-related pairs | Completed original Egglog phase | Partial phase | No export | Qualified historical capture |
|---|---:|---:|---:|---:|
| ARM, 31 | 28 | 3 | 0 | 0 |
| x86, 31 | 24 | 3 | 3 | 1 |
| HVX, 31 | 0 | 0 | 31 | 0 |
| Total, 93 | 52 | 6 | 34 | 1 |

The historical x86-add file is tied to a genuine published generated Python program, but was run with our newer backend and was not regenerated from its named C++ source. It is not a 53rd original-source/original-backend completion. The current 104 adapted files comprise 86 from completed original phases, 17 additional files exclusive to partial parents, and that one qualified add file. Raw-input deduplication differs slightly because the old add component also occurs in average pooling.

The exact unresolved boundaries are:

- **All 39 HVX configurations** (31 paper-related plus eight extras): missing pattern imports/products in the pin stop execution before a genuine Egglog invocation. Current upstream [PR #19](https://github.com/RafaeNoor/MISAAL/pull/19) addresses the identified prerequisite gaps. Recovery has not been executed; it is a concrete next step, not 39 recovered cases.
- **x86 mul/softmax:** original frontend vector-distribution assertions. Target-feature changes alone did not resolve preserved probes; changing lookahead emitted Python but has not established a complete canonical run.
- **x86 l2norm:** no expected generated program after abstraction, followed by linkage expecting its absent LLVM output.
- **x86 conv_nn and extra tensor_shr:** original backend division by zero on their first call, no successful selected prefix. **x86 fully_connected and depthwise_conv** fail later, leaving selected successful calls.
- **ARM blur7x7, conv_nn, fully_connected:** repeated recursive re-lowering without progress. Individual successful calls do not complete the parent.

The five partial parents with selected files should not remain in a completed-parent benchmark population. Shared files with independent complete-parent provenance should remain available through those complete aliases.

There is also a configuration gap: the paper describes abstracted Halide rules and five-iteration bursts; pinned ARM/x86 recipes disable generated frontend patterns, and HVX uses three iterations. Full native legalization, linking, and hardware/simulator execution were intentionally not run. Artifact-default Egglog phase completion does not reproduce Table 4/Figure 12 or offline rule-synthesis experiments.

**Next:** try current-upstream HVX prerequisites in a separately pinned experiment; obtain the exact paper flags/dependencies; isolate the frontend, zero-width rule, and recursive non-progress failures. A faithful x86-host control is useful, but the paper also used Apple M2 and the available evidence does not establish ARM as the general cause. [Detailed MISAAL audit and all 33 rows by target](local/reproduction-audit-20260924/misaal.md).

## Churchroad

The WOSET paper explains a 16×32 multiplication mapping and a separate multi-solver bitwidth experiment. It does not define a two-program evaluation suite. Our two programs are the pinned integration tests, `simple_mul` and `wide_mul`. Five ordered fragments are retained per circuit; each replay combines the four active components from one persistent egraph, omitting inactive module-enumeration declarations and adding a proposal check after the mapping schedule. [Paper](https://woset-workshop.github.io/PDFs/2024/7_Scaling_Program_Synthesis_Ba.pdf).

The native driver continues through external Lakeroad synthesis, reinserts synthesized results, and performs specialized final extraction. Those phases and their output contract are absent from our captures. Module enumeration also needs the custom `debruijnify` operation. Replacing the final extraction with arbitrary built-in extraction would change the application.

A separate, later public evaluation repository contains **27 manifest designs**: 18 multiply, five multiply-add, and four multiply-accumulate. All referenced HDL files exist, but their exact source entries are absent from our catalog. Some may overlap semantically with the two integration examples; do not call all 27 distinct additional workloads without comparing. The repository describes a later environment, not automatically the WOSET paper's population. [Pinned evaluation manifest](https://github.com/gussmith23/churchroad-evaluation/blob/af615fa460667a08228a7e8f7e3d345b310e39ac/manifest.yml).

**Next:** capture complete persistent-egraph sessions through synthesis reinsertion/final extraction, and reconcile the later evaluation designs. Six Egglog feature tests and three named Rust-driven cases remain deferred test coverage, not automatically missing paper benchmarks. [Detailed Churchroad audit](local/reproduction-audit-20260924/churchroad.md).

## DialEgg

The paper has five runtime applications and nine timing kernels: image conversion, vector normalization, polynomial evaluation, 2MM, 3MM, and NMM sizes 10, 20, 40, 80. All nine kernel bodies/rule configurations are represented by our captures. NMM160 is an additional artifact case. The ten chosen inputs produced 25 retained independent calls; 14 selected aliases deduplicate to **13 workloads**. [Paper, §8, Tables 1–2 and Appendix A](https://azizzayed.com/publications/dialegg/zayedcgo24.pdf).

Eleven excluded helper/wrapper calls are retained, not missing source. They lack seeds matching the optimization rules; adding artificial work would misrepresent their purpose. Four selected matrix helper aliases perform actual shape/type inference. These should be labeled analysis workloads, distinct from matrix reassociation. Original extraction roots are now restored for the ten selected kernel calls.

The paper's timing script uses `test/`; capture uses `bench/`. Detailed source comparison found identical core kernels/rules, apart from return spelling or whitespace in two cases. The wrappers differ: vector normalization uses one million versus 100 million vectors. Capture also returns before Egglog execution and MLIR reconstruction, so it does not demonstrate a complete native pipeline. Canonicalization-before-equality-saturation treatments may change the seeded graph and have not separately been captured. [Artifact procedures](https://github.com/AzizZayed/dialegg-cgo-artifact/blob/4d0d522e98c15becdc5e7d711348cb0891ff0d44/README.md).

**Next:** preserve the complete named-kernel coverage claim, but capture the exact timer parents and preprocessing treatments if reproducing those experiments. Validate the restored extraction files at their current identities. [Detailed DialEgg audit](local/reproduction-audit-20260924/dialegg.md).

## SpEQ

The paper's Table 2 enumerates ten applications. **Seven successful translation replays** exist: TACO, CSparse, Scimark4, NPB CG, Netlib C, NPB IS, and Parboil. Four use preserved FIR; three were recovered by running original C through the pinned frontend. The recorder produces actual `.egg` commands; no replacement workload or expected equality was inferred by hand. Local tool versions differ from the original container, so this is not full environment reproduction. [Paper, §6.1.6 and Tables 2–4](https://www.paramathic.com/wp-content/uploads/2024/04/REV_PLDI_rev2.pdf).

- **PolyBench GEMM:** a complete application `.egg` export exists, including original scheduling/extraction. The intended GEMM translation does not appear. Fixed-size rank-two application accesses differ from the flattened symbolic reference; regenerating from C did not fix it. Two other recorded chunks contain setup only and must not count as application workloads. The old driver selects `gemm_ref`, not `polybench_gemm`, so its archived timing row is not proof of PolyBench success.
- **TPAL and TSVC2:** no named application source/LLVM inputs appear in the verified full 73,109-member archive. TSVC2 also needs its exact reduction reference/driver setup. Arbitrary current TPAL/TSVC programs are not justified replacements. [Artifact](https://zenodo.org/records/10963236).

Thus **eight cases have complete application Egglog bytes, seven have successful intended translations, and two lack inputs**. These are three distinct counts. Exact original-container behavior remains unverified. The archive includes a Dockerfile whose contents were not retained/read in this audit; no assertion is made that it fetches the missing inputs. A faithful Linux/x86 toolchain is a useful GEMM control, while source/reference/version differences remain plausible explanations. ARM is not established as the cause.

**Next:** obtain TPAL/TSVC2 inputs and setup from the authors, and resolve PolyBench with their intended reference/toolchain. Keep its failed full kernel as diagnostic evidence. [Detailed SpEQ audit](local/reproduction-audit-20260924/speq.md).

## Consequences for collection and figures

`make figures-expanded` operates on the current catalog. It does not discover paper populations, acquire later Eggcc passes, complete Churchroad's driver, or repair artifact failures. Its current pipeline collects baseline observations, compares both proof-recording and proof-extraction treatments, handles the Math comparison separately, then renders. It should not be taken as a paper-reproduction completeness check.

Before the next large collection:

1. For a completed-parent population, correct admission for the five partial HardBoiled parents and five partial MISAAL parents, retaining their files, failures, and complete-source aliases. Keep any separately admitted complete calls labeled as per-call workloads. Decide explicitly whether phase-only Eggcc/Churchroad workloads fit the intended claim.
2. Prioritize uncaptured available work: Eggcc later passes, current-upstream MISAAL HVX recovery, and Churchroad's later evaluation inventory/full sessions. These need genuine generation, not invented inputs.
3. Resolve author/environment questions: HardBoiled's AMX cell mapping and Linux/x86 run; MISAAL's exact evaluation flags and remaining original-compiler failures; SpEQ's two missing inputs and GEMM reference mismatch.
4. Revalidate exact restored programs with the current binary, then collect through the existing append-only cache. Apply the separately chosen normal-mode timing window only after source completeness has been recorded. Too-fast/too-slow exclusion is not an acquisition failure.

Existing encoding issues describe another stage: [#87](https://github.com/saulshanabrook/egglog-encoding/issues/87) covers Eggcc proof-mode execution failures, [#85](https://github.com/saulshanabrook/egglog-encoding/issues/85) a MISAAL strict-proof substitution failure, and [#86](https://github.com/saulshanabrook/egglog-encoding/issues/86) excessive proof overhead. Their files exist; these issues do not explain absent paper inputs. [#88](https://github.com/saulshanabrook/egglog-encoding/issues/88) concerns the eleven DialEgg helper calls, not eleven missing applications. All remain open at this audit; changed extraction identities require fresh evidence before asserting whether earlier failures persist.

The per-family reports and machine-readable receipts are in [the audit archive](local/reproduction-audit-20260924/). No author messages, upstream issues, benchmark observations, or acquisition changes were made in this review.
