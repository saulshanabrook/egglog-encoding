# EggCC injectivity and disequality study

Start with the [explanation](report.md). It follows two optimizations from
source branch conditions through the encoding, the exported EggCC fact, the
rewritten Bril, and the measured native-program runtime:

- **QR7:** quotient/remainder-key cancellation derives address equality and
  enables early store forwarding. The resulting native entry has no loop;
  elapsed time falls by about 44.9% on the constructed hot workload.
- **Parts32:** injectivity and equal-sibling disequality reasoning establish
  that two high halves differ. Removing the redundant comparison enables a
  vectorized loop; elapsed time falls by 7.5%–8.6% on three constructed
  workloads in two independent sessions.

Both use ordinary compilation-time inference. The measurements concern the
generated programs on one Apple Silicon machine. The explanation gives the
scope, manual comparisons, and causal controls for each result.

## Read the implementation and evidence

| Material | Entry point |
| --- | --- |
| Connected explanation | [report.md](report.md) |
| Mathematics, treatment definitions, exact results, and source identities | [reference.md](reference.md) |
| Generic injectivity lowering | [injectivity.rs](../../egglog-experimental/src/injectivity.rs) |
| Generic disequality query and equal-sibling reverse search | [disequality.rs](../../egglog-experimental/src/disequality.rs) |
| Small mathematical examples | [injectivity-disequality.egg](../../egglog-experimental/tests/injectivity/injectivity-disequality.egg) |
| QR7 source recognizer and store-forwarding bridge | [scoped_qr7.rs](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/scoped_qr7.rs), [compiler patch](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/eggcc-candidate-r1.patch) |
| Parts32 source recognizer and target-predicate export | [compiler patch](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/eggcc-final.patch), [engine patch](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/encoding-final.patch) |
| QR7 accepted raw measurements | [confirmation samples](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/confirmation/samples.jsonl.gz), [independent verification](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json) |
| Parts32 accepted raw measurements | [session 1](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/timing/session-01/samples.jsonl), [session 2](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/timing/session-02/samples.jsonl), [independent verification](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/timing/independent-verification.json) |
| Retained experimental replay procedures | [reproduce.md](reproduce.md) |
| Publication inventory and original hashes | [sharing-manifest.json](sharing-manifest.json) |

The branch contains the final explanation, earlier research notes and audits,
source fixtures and patches, accepted timing rows, causal summaries, and
representative emitted Bril, LLVM, and assembly. The earlier goal directories
record how the search progressed; the explanation above is the current account.

## Branch and artifact boundaries

The branch starts from `faf1905150cedafa54753c7deb8038af66c74e01`, the archived
experimental encoding snapshot based on `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`.
This preserves the implementation used by the experiments. EggCC itself is a
separate repository; its source overlays and patches are included with the
evidence, relative to EggCC revision
`a0bbec127f83249074a46af3fd6f6126c90fe0fb`.

Selected artifacts are committed under `benchmarks/local/` so the report's
relative links resolve after cloning. That directory remains ignored for new
local runs. Large captures and source archives use lossless `.gz` compression.
The inventory records both the published-file hash and the original hash; the
frozen source identities and absolute paths inside historical records retain
their original meaning. A few links in historical notes refer to the original
machine or partial source overlays; those are listed in the inventory.

Compiled executables, build caches, duplicated per-invocation graph dumps, and
unreferenced intermediate captures remain local. The retained replay guide
describes the original machine's paths and immutable binaries. Reading the
report, inspecting its published evidence, and verifying file integrity work
from this checkout; the historical native replay commands require reconstructing
their source and binary prerequisites. Rebuilding does not reproduce the exact
Mach-O identities or the original measurements automatically.

## Verify the published files

This needs only Python's standard library and does not run a compiler or a
benchmark:

```bash
python3 goals/eggcc-encoding-payoff/verify_artifacts.py
```

To inspect a compressed capture:

```bash
gzip -dc benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/confirmation/samples.jsonl.gz | head -n 1
```

The root suite checks the encoding and its ordinary test harness:

```bash
UV_PYTHON=3.12 make check
```

Published historical experiment scripts are excluded from routine Python
formatting and type checks so their frozen contents stay intact. The current
encoding, benchmark library, and tests keep their normal checks.
