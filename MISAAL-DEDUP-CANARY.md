# Immutable HVX deduplication canary request

The preview at `misaal-hvx-dedup-canary-preview/` contains the verified original
request/settings bytes, one derived request, provenance, settings and an artifact
hash receipt. Only `pattern_deduplication: exact-render-last-v1` is added to the
request. All source/tool bindings and the original cold-cache contract remain.
The settings retain all existing MISAAL fields and identities, change the request
directory to the one-case subset, and add the immutable provenance identity.
Original inputs were rechecked unchanged after creation.

New tracked code/test patch: `MISAAL-DEDUP-CANARY.patch`. No shared-file changes.
Five focused tests, Ruff, formatting and Mypy passed. Actual prerequisite file
verification succeeded while producing the preview; no compiler or native job
ran. The receipt status is `request-prepared`, not source-complete or reproduced.

After applying the patch, run from `/Users/saul/p/egglog-encoding` to create the
durable root artifact (this writes JSON only and refuses an existing directory):

```sh
.venv/bin/python -m scripts.reproduction_prepare_misaal_pattern_canary \
  --settings benchmarks/local/reproduction/prerequisites/misaal-all-targets-attempt-0001/settings.json \
  --output benchmarks/local/reproduction/prerequisites/misaal-hvx-dedup-attempt-0001
```

After acquiring the next heavy slot, the exact coordinator invocation is:

```sh
.venv/bin/python -m scripts.suite_reproduction \
  --family misaal --case misaal-hexagon-blur3x3 --stage all \
  --settings benchmarks/local/reproduction/prerequisites/misaal-hvx-dedup-attempt-0001/settings.json
```

The flag produces a new capture identity; no `--retry` is required. This uses
the existing source timeout and ordinary validation settings. It creates no
warm cache and does not alter original requests. The coordinator owns the heavy
lock and completion/validation gates. The output settings deliberately contain
only the MISAAL family and only one available request; use them for this case.

Original request SHA-256:
`c12cbc31dc47110c6479ade3cbc10a33a7472d99e1def518b0baa19ca6dfe6fd`.
Derived request SHA-256 (identical at either artifact destination):
`1033fc33c38f5ac99f9d557f709a35451910e329a10dafbf16bed9c3ed314eb6`.
