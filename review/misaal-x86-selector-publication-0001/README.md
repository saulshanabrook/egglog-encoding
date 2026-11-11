# Immutable publication after the native selector gate

Prepared recipe only: **do not run before the twelve native selector gates
succeed**. No native process or real request publication ran during authoring.
Copy this separate package into a new ignored diagnostic directory; do not edit
the sealed `misaal-x86-selector-gate-0001` package.

The driver is data-only and holds the existing heavy-job lock while it verifies
and writes evidence. It requires the exact sealed native manifest, all twelve
positive/negative gates, all 28 guarded process results, LLVM verification,
unchanged compiled source membership/bytes, plugin hash, and full guard
derivation. A missing, partial, resource-stopped, changed or failed gate refuses
publication. It never fabricates a successful parent/corpus outcome.

It verifies the exact 102 original request bytes selected when this recipe was
prepared, using the existing source/product verifier. It verifies compile
dependencies, deduplication source constants, retained identity paths and the
sealed Racket environment. Expensive runtime-tree checks are cached only when
all verifier-consumed request inputs match (benchmark label is not consumed).
All sources/products remain in their original locations. Existing requests and
the selected base settings are copied into `before/` and never modified.

New requests preserve every original field except the explicitly recorded
publication changes:

* All 102 receive `pattern_deduplication: exact-render-last-v1` and new evidence
  references. Original literal-width guards, lookahead policy, source timeouts,
  cache transitions, runtime, generators, backend and source hashes remain.
* Only the 32 x86 requests replace `legalizer`, its hash and `LEGALIZERS_DIR`.
  Their compiled-source repair metadata points to the fresh native build and
  exact patch derivation. It does not claim the retained runtime checkout's old
  generated C++ was edited or used to compile this new plugin.
* The historical requests omit three deduplication prerequisite hashes. Those
  unchanged files are verified against the helper's constants, then bound in
  publication evidence and identity paths. Original source-hash dictionaries
  remain intact; conflicting existing pins are rejected.

The output `settings-canaries.json` contains all six families. The five other
families' values are copied exactly. For MISAAL, only the new requests directory
and added identity paths change. Existing configuration blockers are preserved;
none is added for the other 100 unattempted cases. They remain pending. Naming
this overlay for canaries is an execution-order reminder, not an admission.

First, after root confirms the gate's `attempt-0001/result.json` is successful:

```sh
.venv/bin/python \
  benchmarks/local/reproduction/diagnostics/misaal-x86-selector-publication-0001/publish.py \
  --root /Users/saul/p/egglog-encoding \
  --settings /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/settings.json \
  --settings-sha256 f77c32677ebf57950ae04e2a5c28149cee4161e3126f81b896df1e0aa6eb583d \
  --gate /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/diagnostics/misaal-x86-selector-gate-0001 \
  --gate-result /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/diagnostics/misaal-x86-selector-gate-0001/attempt-0001/result.json \
  --output /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/diagnostics/misaal-x86-selector-publication-0001/attempt-0001
```

The settings hash above is the review-time snapshot. If other-family settings
change legitimately before publication, root must explicitly supply the newly
verified current settings hash; the MISAAL request directory and every original
request must still match the sealed recipe. A changed MISAAL request needs a
new reviewed recipe, not a silent manifest update. Use a fresh output directory
after any failed attempt.

Then root runs **only these two** complete source-parent and ordinary canaries:

```sh
.venv/bin/python -m scripts.suite_reproduction \
  --family misaal --stage all \
  --case misaal-x86-tensor_shr --case misaal-x86-conv_nn \
  --settings benchmarks/local/reproduction/diagnostics/misaal-x86-selector-publication-0001/attempt-0001/settings-canaries.json
```

Only after both native completion and separate ordinary validation succeed may
root deliberately use this same reviewed full-population overlay for broader
collection. This driver never updates canonical settings, stage indexes,
catalogs, prior outcomes or the corpus. Eight synthetic tests cover the gate
contract, source/plugin tampering, all-102 preservation, policy conflicts,
runtime-cache boundaries and historical missing prerequisite pins. They are
not substitute evidence for running the real native gate or these canaries.
