# SpEQ recovery investigation

Inspected 2026-09-24 (local date), including the root agent's subsequent guarded flag-lane runs and MemorySSA diagnostic. This report separates successful capture/replay from correctness of the source compiler. No builds, native generators, device execution, or author messages were performed by this investigation. Only the explicitly authorized opt-in flag interface and focused synthetic tests were edited.

The [2026-09-25 missing-input follow-up](speq-missing-inputs.md) records the newly
checksum-verified Dockerfile and its dependency-source audit. It updates the
Dockerfile recovery status below while retaining the exact TPAL/TSVC2 input and
setup requirements.

## Current evidence and boundaries

The paper selects ten applications (§6.1.6, p.17; Table 2, p.18). Its environment is LLVM 17.0.0 with an Intel Xeon W-2145 and NVIDIA RTX 3080 Ti (§6.1.1–4, p.17). The present lane instead uses native macOS LLVM 17.0.6, the pinned REV source, and the existing Egglog Python 13.2.0 API port. This is a documented compatibility reproduction, not the paper's container. [Paper](https://www.paramathic.com/wp-content/uploads/2024/04/REV_PLDI_rev2.pdf), [DOI](https://doi.org/10.1145/3656445).

The original-C baseline completed six intended translations and their standalone output comparisons. The explicit `-D_FORTIFY_SOURCE=0 -DPOLYBENCH_USE_C99_PROTO` lane completes seven: TACO-Gen, CSparse, Scimark4, NPB CG, Netlib C, NPB IS, and Parboil. Polybench still fails its translation assertion; TPAL and TSVC2 remain missing exact SpEQ inputs/setup. These counts come from the ten entries in [the current index][index], not old preserved-FIR replay counts. Parboil's seventh capture has a **confirmed source-to-FIR branch-polarity defect inherited from the author source**. It establishes native/replay agreement, not C equivalence.

| Case / lane | Emitted application work | Parent's expected translation | Ordinary standalone result | Proof validation |
|---|---|---|---|---|
| Parboil, baseline | One FIR region, parser fails; zero application extracts | Failed | Not admitted | Not run |
| Parboil, explicit flags | One FIR region, one extraction, native cost 80 | Succeeds, with source correctness defect below | Exact native output agrees | Not run |
| Polybench, baseline | All three regions accounted; region 2 parsed/extracted, cost 327 | GEMM absent | Not admitted | Not run |
| Polybench, C99 flags | All three regions accounted; region 2 parsed/extracted, cost 291 | GEMM absent | Not admitted | Not run |
| TPAL / TSVC2 | No exact SpEQ application capture | Missing source/setup | Not run | Not run |

All runs retain the original reference rules, **5 transform / 1 expand / 3 transform** schedule, costs, extraction request, and ordered skipped-region outcomes. Bytes emitted for setup or an unsuccessful translation are not successful workloads. Proof validation would certify only the supplied Egglog reasoning; it would not repair an incorrect LLVM-to-FIR translation.

## Parboil: a repaired platform parse failure, then a confirmed historical translation defect

### 1. Why the native baseline never reached EqSat

The original application C hash is `7d1e8d746ca40c4579377867e79674caad15b81592ce8037e96c474c44e41172`. Its baseline FIR contains a malformed memory-state assignment:

```text
%call4.3 = %call9 = call ptr @__memset_chk(ptr noundef ... ) #7
```

The application therefore has `skipped-parse`, not a failed histogram derivation. [Baseline receipt][parboil-before]. macOS SDK `secure/_common.h:29–38` enables `_USE_FORTIFY_LEVEL` from `_FORTIFY_SOURCE`; `secure/_string.h:135–137,242–244` redirects `memset` to a checked builtin. REV's `Lambda::translateLoopBody` prefixes every memory-writing instruction with the memory-state assignment and then prints the entire instruction, including the call's own result. This creates the duplicated assignment for a return-valued checked call. The parser also cannot model arbitrary such calls: `Call.toEgg` supports only `@llvm.memset.p0.*`. [REV source, lines1978–1981](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L1978), [local parser, lines459–462][parser].

The explicitly recorded flag disables this SDK fortification in the acquisition lane while keeping the C bytes intact. Root's real guarded run now emits the expected `llvm.memset`, reaches histogram extraction, finishes the original analysis, and passes standalone output comparison. The C99 flag has no Polybench-macro use in this Parboil source. Fresh FIR hash: `8affd14608ba01199fe09c9a1a574efe045b5971a1ed5d60d35edeeb4c94e29d`; standalone hash: `7731266bc31b95bde2461179d02167b6783701213400915230075b3aac678d53`. [Flag-lane receipt][parboil-after]. This resolves the observed parser obstruction; it does not establish arbitrary fortified-call support.

### 2. Exact MemorySSA evidence for the polarity error

Root ran the bounded diagnostic against the **fresh flag-lane** `analysis.ll`; exit 0, 0.0602 seconds. [Diagnostic command/receipt][polarity-receipt], [complete MemorySSA output][memoryssa].

```llvm
; in for.body13:
%cmp17.not = icmp eq i8 %1, -1
br i1 %cmp17.not, label %for.inc, label %if.then

if.then:
  %inc = add i8 %1, 1
; 4 = MemoryDef(6)
  store i8 %inc, ptr %arrayidx15, align 1
  br label %for.inc

for.inc:
; 5 = MemoryPhi({for.body13,6},{if.then,4})
```

For condition true, the edge comes directly from `for.body13` and selects unchanged memory **6**. For false, it comes from `if.then` and selects updated memory **4**. FIR instead emits `if %cmp17.not then %call4.4 else %call4`, selecting **4 on true**. The outer test is reversed too: `%cmp111.not = (%mul == 0)` goes directly to the outer merge and should select memset state **3**, whereas FIR selects the inner-loop state **5**. Its MemoryPhi is `7 = MemoryPhi({for.body,3},{for.inc22.loopexit,5})`.

The cause is the pinned [`Lambda::getPhiBr`, lines1818–1830](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L1818): it tests whether the true successor dominates incoming predecessor 0; otherwise it assumes predecessor 1 is true. When the true successor is the merge itself, it dominates neither predecessor. The result becomes dependent on incoming order. `translatePhi` uses that choice directly. `IfThenElse.toZ3` is ordinary `z3.If(cond, then, else)`, so an inverted FIR convention does not explain this. [Parser lines470–478][parser].

The author's preserved [`REVTest.cpp`, lines341–370](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/unittests/Transforms/REV/REVTest.cpp#L341) contains both reversed choices. Thus this is not evidence of ARM changing arithmetic, nor a new adapter inversion. The complete historical Linux environment has not been rerun; the public snapshot is the available historical behavior evidence.

**Smallest proposed REV repair (not implemented here):** classify the direct branch-to-merge edge by its incoming predecessor being the conditional branch's own block. For non-direct paths, classify incoming predecessors by dominance of `getSuccessor(0)` or `getSuccessor(1)`. Require exactly one true and one false classification; explicitly reject unsupported/nonconditional/more-than-two-input shapes instead of guessing or dereferencing a null branch. Retain all original application code and Egglog rules. This is a source compiler correction, recorded separately from the historical lane.

**Tiny proposed regression:** compile the following through the exact recorded passes; inspect MemorySSA and emitted FIR for the selected update, without executing target code:

```c
void saturating_increment(unsigned char *a, int n) {
  for (int i = 0; i < n; ++i)
    if (a[i] != 255) ++a[i];
}
```

Check both values 254 and 255 against the FIR conditional's branch table: 254 selects the update; 255 selects unchanged memory. Test an equivalent negated condition, both incoming predecessor orders in a tiny LLVM fixture, a two-sided diamond, and a scalar PHI in addition to a MemoryPhi. For the real Parboil source, separately check `%mul==0` chooses memset rather than inner-loop state. Only then recapture the real application and compare its changed native output with the standalone replay. A successful old output comparison is not a substitute for these tests.

## Polybench: the first flag was insufficient; the remaining mismatch is visible before EqSat

Original application hash: `e0fc07f40f59e83fc57f1d4e1e99f1718ffce106dcdc44c3e30ed88848228aea`. Baseline defaults use fixed matrix extents 1100/1200 in the GEPs but symbolic `nj`/`nk` loop bounds. The reference `gemm_ref.c` uses `nj`/`nk` for both strides and bounds. The parser explicitly flattens a fixed array GEP as `i*leading+j`, so the mismatch is not just a cosmetic type spelling. [Polybench header lines39–55][polybench-header], [GEMM reference][gemm-ref], [parser lines901–908][parser], [baseline receipt][polybench-before].

The published `POLYBENCH_USE_C99_PROTO` header switch correctly changes parameter extents to the symbolic dimensions, but the genuine run **still fails**. All three regions are accounted: an empty/setup region is skipped, initialization is skipped on unsupported `srem`, and the kernel is extracted but contains no GEMM. New kernel FIR hash `88ea197d575dfd8cf55a189ff2e6d067f40b3f1369da4f95129605c716ee334f`; standalone diagnostic hash `4531fc93732ae31c6b63ed53a3629d09c5fa498989fe4f3378ccfb67e063acc4`. [C99 receipt][polybench-after].

The fresh LLVM `polybench_gemm` entry defines `%0 = zext i32 %nj to i64` and `%1 = zext i32 %nk to i64`. The emitted loop-only FIR omits these definitions, yet uses `%0/%1` as strides. It also retains chained GEPs: `gep(C,i*%0)` followed by `gep(previous,j)`. The resulting extracted expression visibly has nested `select1(select1(C,i*%0),j)`, not the reference's flat `select1(C,i*nj+j)`. Finally, `arrayType` falls back to untyped `ptr %C`, producing `_int(%C)` for the loop's memory state rather than its expected typed array. These are separate frontend representation losses. Increasing the same EqSat schedule cannot justify inventing the missing `nj=%0` fact or pointer typing. [Fresh FIR][polybench-fir], [fresh LLVM][polybench-llvm], [REV arrayType lines1803–1815](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L1803).

**Prior proposed experiment (now completed with an earlier frontend rejection; see follow-up below):** retain `-D_FORTIFY_SOURCE=0`, replace C99_PROTO with the other published switch `-DPOLYBENCH_USE_SCALAR_LB`; do not combine them. This keeps fixed array typing while making loop bounds use matching NI/NJ/NK constants. It preserves source bytes and reference rules, and records a distinct supported Polybench configuration. Prediction: fixed strides/bounds match without missing entry stride definitions or chained VLA GEPs. Possible falsifier: LLVM removes positive-bound guards which the symbolic reference still expects, or another structural mismatch remains. Require a real GEMM result and ordinary agreement; do not assume success.

If that lane fails, the justified compiler repair is to preserve relevant pure dominating SSA definitions at the FIR boundary, carry correct memory element types, and lower same-element-type pointer offsets to one address before creating a load/store expression. Test GEP composition with unequal symbolic strides and nonzero offsets; do not add a blanket `select(select(A,i),j)=select(A,i+j)` rule, because ordinary nested array selection does not have pointer-offset semantics. A general frontend repair is more substantial than a flag change and needs independent regressions before another complete capture.

The artifact's active driver selects `gemm_ref` and comments out `polybench_gemm`; the table renderer infers success from eight timing rows. Neither establishes a successful application translation. [Driver lines13–22][driver], [table renderer lines57–65][table3]. Keep this distinction when comparing the paper's GEMM detection claim (§6.2, p.18) with the artifact.

## SCALAR_LB and no-GVN follow-up: earlier rejection, then incomplete FIR

The subsequent complete `-D_FORTIFY_SOURCE=0 -DPOLYBENCH_USE_SCALAR_LB` run is **not another unmatched GEMM extraction**. It emits only two FIR regions (blank, then `init_array` rejected for `srem`), hence zero application extracts. Its LLVM still contains `polybench_gemm`. [Complete capture](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/4e89ad7ea7a0f8316f7bbf89d6e8815cd74278638d04922dd250575c45b54a89/attempt-0001/capture-result.json), [frontend manifest](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/4e89ad7ea7a0f8316f7bbf89d6e8815cd74278638d04922dd250575c45b54a89/attempt-0001/capture/speq/speq-polybench_gemm/source/frontend/manifest.json), [LLVM](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/4e89ad7ea7a0f8316f7bbf89d6e8815cd74278638d04922dd250575c45b54a89/attempt-0001/capture/speq/speq-polybench_gemm/source/frontend/analysis.ll:183).

GVN shares `%idxprom = zext i32 %i.04 to i64` between the C-scaling loop and the later multiply loop. LCSSA introduces `%idxprom.lcssa` in the first loop's exit while that loop also stores C. `findLiveOut` sets `Legal = (NumPhis == 1) != (StoreInsts.size() == 1)`, so one scalar liveout plus one store rejects the entire function before FIR rendering. This is a supported frontend limitation, not an Egglog rule-search failure. [REV source lines2432–2465](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L2432), [rejection return lines2495–2513](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L2495).

Root then ran a guarded 30-second diagnostic on that exact retained `input.ll`, omitting GVN. It succeeded in 0.062 seconds and emitted **three** REV regions; the final region includes the GEMM arithmetic. This confirms the predicted earlier rejection mechanism. The command and identities are retained in [receipt](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/speq-scalar-no-gvn/receipt.json); [FIR output](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/speq-scalar-no-gvn/probe.stderr.log) and [LLVM](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/speq-scalar-no-gvn/analysis.ll:185) are diagnostic evidence only. The original source, standard pipeline, and complete-capture status were not changed.

```text
/opt/homebrew/Cellar/llvm@17/17.0.6/bin/opt
-load-pass-plugin=PLUGIN
-S
-passes=mem2reg,loop-rotate,instcombine,simplifycfg,loop-simplify,lcssa,print<revpass>
/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/4e89ad7ea7a0f8316f7bbf89d6e8815cd74278638d04922dd250575c45b54a89/attempt-0001/capture/speq/speq-polybench_gemm/source/frontend/input.ll
-o /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/speq-scalar-no-gvn/analysis.ll
```

`PLUGIN` is the exact retained `rev-plugin.so` path in that receipt, SHA-256 `0bbbb659d80589b3661b5461914e70d7b0e6eb97051419dadf8fddb7c1bf98ff`; input SHA-256 is `33ef44fe6a4046d4285b2488ff362f12c821f155411d7486f740e71facfe4a87`. Root's actual diagnostic also omitted `-enable-load-in-loop-pre=false`; that GVN-specific option is immaterial when GVN is absent, but the receipt above is authoritative.

Two remaining FIR defects prevent promoting that diagnostic:

* The parent k/i folds return `()` even though their child loop stores C. `translateLoopBody` skips all blocks belonging to child loops and collects `MemDefs` only in the retained direct blocks. Without the dynamic-bound guards/merge MemoryPhis, no child final memory state reaches the parent output. [REV lines1939–1962](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L1939), [output generation lines2058–2064](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L2058).
* The emitted ranges end at 1099/1199/999 for loops executing 1100/1200/1000 iterations. LLVM now tests the *current* IV (`j < 1099`) after executing the body, whereas the symbolic form tests its increment. `translateLoop` prints `getFinalIVValue()` directly without accounting for the comparison/step form. [REV lines2082–2086](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/lib/Analysis/REVPass.cpp#L2082). Do not add 1 indiscriminately: the previous symbolic increment-tested form already prints the exclusive bound.

**Next discriminating test, proposed and unrun:** take the exact no-GVN command from its receipt and remove only `instcombine` from the pass list, writing a new directory. Prediction: bounds become 1100/1200/1000 while empty outer outputs remain. This separates bound normalization from nested memory-state propagation; it is not a complete source-reproduction configuration or an expected GEMM success. If the prediction fails, inspect the loop-rotate/SimplifyCFG comparison form before modifying REV.

A source-preserving REV repair needs focused regressions for nested loops whose only memory effect is in a child (plus intervening direct stores/conditional paths), and equivalent loop tests on current IV versus next IV, including zero/one/two iterations and symbolic guards. It must thread the actual child exit memory state and compute the correct fold range; dropping scalar/memory outputs or manufacturing an Egglog witness is not acceptable. C99_PROTO's free stride SSA values / pointer typing / GEP composition remain a separate failed lane, recorded above.

## Missing TPAL and TSVC2: real upstream candidates, exact SpEQ mapping still absent

The pinned archive's verified full **73,109-member** index has hash `23acf74505c56b2e08479b8cfb82a52b4670ef5f95bd3fce36192649615ab136`. A fresh member-name scan still finds no `tpal` or `tsvc` entry. The artifact's table script contains the expected labels `tpal_spmv` and `tsvc`, but both selections are commented out. This establishes a packaging gap, not absence of the benchmark projects on the Internet. [Archive receipt][archive-index], [member list][archive-members], [table script][table3].

### TPAL

The original project's public [repository](https://github.com/mikerainey/tpal) remains available. Current `master` is `96d7297390e8e401d87ebfaf9f699f9c14595502` (2021-06-08). Its actual [`runtime/bench/spmv_orig.hpp`](https://github.com/mikerainey/tpal/blob/96d7297390e8e401d87ebfaf9f699f9c14595502/runtime/bench/spmv_orig.hpp#L14) contains `spmv_serial`, a CSR loop over `uint64_t` indices and double values, plus separate interrupt variants. Header SHA-256 is `dcd9af575a233ba7e5e4282d3068089f2de4f7540520ad88adab49a10f79ab41`. [`spmv.cpp`](https://github.com/mikerainey/tpal/blob/96d7297390e8e401d87ebfaf9f699f9c14595502/runtime/bench/spmv.cpp) dispatches several matrix input shapes, so the project name does not uniquely identify a driver/input configuration.

This is a genuine source candidate, not a reference kernel invented for SpEQ. A future explicitly labeled upstream-source lane could compile the unchanged header as C++ and account for all its functions/regions, without building the TPAL runtime or executing its benchmarks. **It cannot yet be called the exact paper input:** no evidence links `spmv_serial` byte-for-byte to SpEQ's missing `tpal_spmv.c`, or records any author edits, selected function, frontend options, or parameter mapping. Required recovery evidence is that mapping or the missing original file plus checksum/configuration. Do not rename a different SpMV and count it as recovered TPAL.

### TSVC2

The public [TSVC2 repository](https://github.com/UoB-HPC/TSVC_2) has `master` `badf9adb2974867ac0937718d85a44dec6dec95a` (2015-10-02). The [README](https://github.com/UoB-HPC/TSVC_2/blob/badf9adb2974867ac0937718d85a44dec6dec95a/README.md) links its older C source to the paper's cited Maleki suite and distinguishes relaxed/default/precise math configurations. Its genuine [`src/tsvc.c`](https://github.com/UoB-HPC/TSVC_2/blob/badf9adb2974867ac0937718d85a44dec6dec95a/src/tsvc.c) has SHA-256 `456dd573b84b30e6f32c943bb559d80374eec67177de48223e95124a8c3fc627` and multiple different reductions: `s311` sum, `s312` product, `s313` dot product, `s314` max, `s317` repeated product, `s319` coupled sums, and `vsumr` another sum. The SpEQ paper says only “TSVC2 / Reduction”; that does not identify the function.

There is a second missing input: the artifact registers only GEMM/GEMV/Histogram. Its README describes adding a `reduction_ref.c` constant-add example, but does not activate a Reduction reference or identify a TSVC case. [Artifact reference registration lines154–169][run-benchmark], [README reduction instructions][readme]. The exact selected function, headers/constants, precision/fast-math flags, reference source, parameter mapping, and driver registration are required. Compiling all of TSVC or adding a guessed reduction rule would create new work, not recover the claimed exact case.

## Current public recovery search and remaining environment gap

Live read-only GitHub API inspection found 15 `avery-laird/lleq` branches: `artifact` is still the pinned `00bd6254b3832d94558b7c38a394ea03d01a2763` (2024-03-25); every other branch tip is older. Default `main` is a 2022 LLVM merge. Four public PR records concern earlier CSR/CSC/dense work; no later published repair or fork was found. [Branches](https://api.github.com/repos/avery-laird/lleq/branches?per_page=100), [artifact commit](https://api.github.com/repos/avery-laird/lleq/commits/artifact), [issues/PR metadata](https://api.github.com/repos/avery-laird/lleq/issues?state=all&per_page=100). This search does not establish that private/unpublished fixes do not exist.

Zenodo's current version list still ends at [10963236](https://zenodo.org/records/10963236); the three earlier records also contain about 6.26-GB archives. [Version metadata](https://zenodo.org/api/records/10963236/versions?size=10). No newer artifact publication was found. The full index records a 1,893-byte root Dockerfile, but its contents were not retained by the earlier extraction and were not recovered in this small-text-only investigation. A plain gzip archive cannot yield a late tar member from its filename index alone. Therefore dependency fetches from that Dockerfile remain unknown; Docker must not be claimed to supply the missing inputs without inspecting it. A later approved acquisition should retain that file before rebuilding a large image.

## Implemented interface, validation, and next gates

The minimal authorized patch changes only `scripts/paper_benchmarks/record_speq.py`, `scripts/dialegg_speq_complete.py`, and `tests/test_dialegg_speq_complete.py`. `capture_complete_speq` / `complete_capture` accept `Namespace.speq_frontend_flag`, a list defaulting to empty when absent. Each value is passed as a literal argument `--frontend-flag=VALUE` to the recorder; the recorder requires `--complete`. Flags affect original application C compilation only. Case, source, and frontend receipts retain their ordered values and original hashes. Root integrated the patch and supplied corresponding immutable settings in its coordinator.

Focused synthetic tests: **26 passed**; Ruff checks/format and Mypy passed. They verify baseline and explicit flags, all ordered regions, unchanged opt pass list, durable receipt flags, and non-success on parent failure. These tests do not establish reproduction. The real flag-lane and MemorySSA results above were executed by root and independently read here.

Ordered next gates:

1. Preserve the seven actual native/replay successes and both baseline failures; label Parboil's source-correctness issue separately.
2. Preserve the failed SCALAR_LB capture and successful no-GVN diagnostic separately. The next diagnostic removes InstCombine too; neither is a GEMM reproduction. Validate nested memory propagation and loop-bound normalization before a frontend repair capture.
3. Implement and test edge-aware PHI polarity mapping on an isolated frontend copy; recapture Parboil with the corrected frontend and compare real output. Do not repair its Egglog result by adding a witness.
4. If Polybench still fails, test pure-SSA closure, GEP address composition, and memory typing as frontend correctness work before another capture.
5. Recover the artifact Dockerfile and exact TPAL/TSVC mapping/setup. Public upstream candidates may support a separately labeled reproduction lane, but do not silently substitute for missing paper inputs.

No target-device execution or performance campaign is required for these gates. No claim of strict proof validity or original C equivalence follows from a successful process or standalone replay alone.

[index]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/index.json
[parboil-before]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-parboil_hist/complete/d90ff784069879715905bb9aea1c0908e518c9cacf340ab58e43677e615571c5/attempt-0001/capture/speq/speq-parboil_hist/manifest.json
[parboil-after]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-parboil_hist/complete/dcd7e644c2d175a9ae9265672c97356efe7368c346b1dcb8076675ec4372b92f/attempt-0001/capture/speq/speq-parboil_hist/manifest.json
[polarity-receipt]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/speq-polarity-diagnostic/receipt.json
[memoryssa]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/speq-polarity-diagnostic/memoryssa.stderr.log
[polybench-before]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/0ee5fc49bf9591a8725848ad7365505c7a8b9d7860ff492933cd6ac45d1c2961/attempt-0001/capture/speq/speq-polybench_gemm/manifest.json
[polybench-after]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/1e928d93389854f3e329445f738e671a77f968eaf6a4b5c3e749af9555701e52/attempt-0001/capture/speq/speq-polybench_gemm/manifest.json
[polybench-fir]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/1e928d93389854f3e329445f738e671a77f968eaf6a4b5c3e749af9555701e52/attempt-0001/capture/speq/speq-polybench_gemm/source/frontend/application-002.fir
[polybench-llvm]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/1e928d93389854f3e329445f738e671a77f968eaf6a4b5c3e749af9555701e52/attempt-0001/capture/speq/speq-polybench_gemm/source/frontend/analysis.ll
[parser]: /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact/parseIR.py:459
[polybench-header]: /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact/benchmarks/polybench.h:39
[gemm-ref]: /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact/benchmarks/gemm_ref.c
[driver]: /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact/driver.py:13
[table3]: /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact/figures/table3/draw_table3.py
[run-benchmark]: /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact/run_benchmark.py:154
[readme]: /Users/saul/p/egglog-encoding/benchmarks/local/sources/speq/artifact/README.md:52
[archive-index]: /Users/saul/p/egglog-encoding/benchmarks/local/evidence/speq-artifact-index.json
[archive-members]: /Users/saul/p/egglog-encoding/benchmarks/local/evidence/speq-artifact-members.jsonl
