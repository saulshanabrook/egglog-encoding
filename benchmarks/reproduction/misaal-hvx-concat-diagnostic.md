# LLVM12 HVX concat diagnostic handoff

Four new owned files are retained in `HVX-CONCAT-DIAGNOSTIC.patch`. No existing capture or preparation module changes. Two imported production dependencies were refreshed byte-for-byte from live in this mirror for testing and are excluded from the patch.

The runner injects the exact current `concat_lowering_cpp()` and the exact pinned common `Legalizer::getBitvectorOfRequiredType` function into the support harness. It compiles one host LLVM12 analysis executable, creates and verifies real LLVM IR, then evaluates its emitted instruction DAG with LLVM constant folding over every 16-bit and 8-bit value. Direct, mapped scalar, and mapped vector paths each exercise the whole domain; original and mapped inputs deliberately differ. Fixed output type and every repeated lane are checked. This is 197,376 value cases, two unrelated-call preservation cases, and 36 separately guarded negative shape/arity/annotation/mapping cases. Actual target-device or source-parent programs never run.

Malformed cases must invoke the exact fragment fatal-error reason and return86 through an installed LLVM fatal handler. Crashes, LLVM assertion failures, accepting invalid inputs, wrong reasons, partial test counts, and resource stops cannot pass. Every child runs sequentially with5GiB process cap,10GiB disk reserve, required memory guard, authorized warning-pressure policy, and immutable request/result logs. Tool/compiler/sharedLLVM/fragment/accessor/source/harness/binary hashes and all artifacts are retained. The CLI owns the existing heavy-job lock; the in-process API requires the caller to own it.

Light validation:13 mocked-process tests pass; Ruff check/format and mypy pass; CLI help renders. No native compilation or harness execution has occurred. These tests establish protocol behavior only. The LLVM12 C++ harness still requires the real gate below.

From the live repository after root integration and heavy-slot ownership:

```sh
uv run --locked python -m scripts.reproduction_misaal_hvx_diagnostic \
  --common-source benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/sources/MISAAL/Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/common/Legalizer.cpp \
  --llvm /opt/homebrew/opt/llvm@12 \
  --output benchmarks/local/reproduction/misaal-hvx-concat-diagnostic-0001 \
  --timeout-sec 60
```

The expected overall result is `status=success`, `exhaustive_value_cases=197376`, `rejected_shapes=36`, with `corpus_admission=false`, `source_parent_execution=false`, and `device_execution=false`. Retain failures and halt after the first safety stop. Success would validate only these concat lowering cases and mapping behavior, not other HVX instructions, native parent completion, original-C equivalence, or ordinary/proof corpus admission.

## Actual native result, 2026-09-25

The first attempt reached compilation and exposed the LLVM12 fatal-handler callback signature (`const std::string &`, rather than `const char *`). The harness was corrected without changing the production fragment. The second immutable attempt passed all 197,376 exhaustive value cases and 36 exact rejection cases against LLVM12. Evidence: `benchmarks/local/reproduction/misaal-hvx-concat-diagnostic-0002/diagnostic.json`. No target program or complete source parent ran in this diagnostic.
