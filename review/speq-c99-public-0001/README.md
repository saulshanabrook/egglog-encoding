# SpEQ C99 public integration handoff

`implementation.patch` is review-ready; no native command was run for this integration.
The baseline and changed-file hashes are in `handoff.json`. The patch applies cleanly
to the live root baseline. Only the one SpEQ keyword in
`scripts/reproduction_preparation.py` overlaps the sibling's file ownership;
its MISAAL width policy is a separate hunk.

The tracked gate helper owns 30 guarded operations: a paired PHI/candidate build
and exact harness, 16 domain fixtures, 8 disabled reference analyses, 4 function
selection controls, and a fresh original-C comparison of all three regions.
Preparation readiness does not admit a workload. A complete selected capture
rebuilds its own pair, checks the fresh baseline against the selected candidate,
and retains the existing all-region parser, original reference rules, 5/1/3
schedule, native recognition/output contract and separate ordinary validation.

Validation: 260 focused tests passed in 1.37 seconds; Ruff check/format and mypy
passed for all 14 changed Python source/test files. These are mocked or data-only
checks. Gate helper was authored by misaal_racket_recipe and independently read by
the integration owner. Parent review is still required for the core integration;
the backend review is queued, not represented as complete.

## Proposed root-owned native gate

Use a fresh output directory. This example reuses already verified immutable
artifact/LLVM sources through the public preparer's existing receipt validation;
it does not consume ignored experimental gate products. The root may instead use
the newly retained full-stream acquisition receipt, or `--acquire-archive` for a
clean acquisition. The CLI owns the shared lock; each native C99 step retains the
5 GiB process cap, 10 GiB disk reserve and existing pressure guard.

```sh
.venv/bin/python -m scripts.reproduction_prepare_speq \
  --output benchmarks/local/reproduction/preparation/speq-c99-public-attempt-0001 \
  --artifact-source benchmarks/local/reproduction/preparation/speq-attempt-0002/sources/artifact \
  --artifact-receipt benchmarks/local/reproduction/preparation/speq-attempt-0002/evidence/artifact-receipt.json \
  --lleq-source benchmarks/local/reproduction/preparation/speq-attempt-0002/sources/lleq \
  --c99-frontend-repair polybench-gemm-address-v1
```

After actual preparation succeeds, root can use the fresh settings in a deliberate
all-family overlay and run only `--family speq --case speq-polybench_gemm --stage all`
through `scripts.suite_reproduction`. A standalone one-family canary is also
possible with the fresh settings path directly, but root controls report refresh
and overlay publication. No command here has been executed and no corpus case is
admitted by the implementation or prerequisite result alone.
