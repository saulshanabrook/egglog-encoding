# Root-owned selector gate (prepared, not executed)

Copy this whole package into a fresh ignored diagnostic directory in the main
workspace after integrating the reviewed patch. Its source tree is copied again
under a fresh run output; old preparation sources, libraries, captures and
requests are read-only inputs. No target-device code executes.

```sh
.venv/bin/python \
  benchmarks/local/reproduction/diagnostics/misaal-x86-selector-gate-0001/run.py \
  --root /Users/saul/p/egglog-encoding \
  --output /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/diagnostics/misaal-x86-selector-gate-0001/attempt-0001
```

The driver takes the existing cross-process heavy-job lock. All subprocesses use
the existing guarded `Preparation` runner (5 GiB aggregate group RSS,10 GiB disk
reserve,warning pressure permitted). Builds are serial; LLVM probes get 60s.
A resource stop ends the sequence and its original status remains visible in
`result.json`. It retains requests/logs/output hashes and never publishes a
capture request or settings.

Before configure, the materializer must confirm all three original source pins,
2,025 cases/24,536 guards, and 1,951 changed binary guards in 1,349 cases. The driver
retains the complete patched source inventory before the compiler runs and
checks it again after compilation and at finalization. Sealed source members
must match exactly; extra C++ files and symlinks are refused.

Expected twelve gates:

* Old plugin: all five reduced inputs retain the one Hydride call, including
  all three valid 128/256/512 SRAV32 inputs. LLVM verification still succeeds.
* New plugin: three positive inputs contain the specific original wrapper call
  and pass the unchanged lowering audit. Wrong Boolean and wrong width-selector
  controls retain the original Hydride call and therefore fail that audit.
  Their LLVM must still verify; syntax failures do not count as negatives.
* New plugin: the exact retained full tensor_shr and conv_nn linked inputs pass
  the unchanged audit for all 1/68 original requested functions and LLVM verify.

The 512 reduced input preserves the exact raw tensor LLVM plus verbatim source
wrapper definitions/declarations/attribute groups. The 256/128 variants scale
vector width and width parameters, retaining the same actual selected operation.
The negative fixtures alter exactly one selector value. `manifest.json` records
the original raw/wrapper hashes and all fixture/tool/helper/source identities.
The full original capture gates ensure the synthetic width fixtures alone cannot
be mistaken for successful source lowering.

No native gate has run while preparing this package. Two data-only driver tests
cover added/changed native sources and symlink refusal. These tests and the
production helper's 55 focused tests are not native success evidence. If any gate
fails, retain its fresh output and diagnose it; do not reinterpret failure as an
expected rejection or automatically retry. A full fresh preparation and complete
source-parent plus standalone replay remain necessary for corpus admission.
