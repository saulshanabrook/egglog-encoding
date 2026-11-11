# Published HardBoiled Egglog inputs

The author's [egglog-benchmarks collection](https://github.com/yihozhang/egglog-benchmarks/tree/a85aa6e2f5195d850fba57700efcf97dc1b507a6/benchmarks/hardboiled)
is the selected HardBoiled suite: 42 standalone GPU optimization workloads. These inputs
can be used without rebuilding Halide or running generated device code.

There are 32 Conv1D sizes (8 through 256, step 8), six convolution/resampling
cases, and `matmul`, `denoise`, `rec_filter`, and `resize`. They correspond to
26 of the 29 GPU configurations in our paper inventory, plus 16 additional
Conv1D sizes. The published resize input matches resize-down. The collection
does not provide `conv_layer-16`, `conv_layer-32`, `attention`, or AMX inputs;
record those omissions as coverage context, without making them prerequisites
for reproducing this author-published suite. Earlier native captures remain
available as historical evidence.

## Reproduce the published inputs

```bash
uv run --locked python scripts/suite_acquisition.py reproduce --family hardboiled --stage all
uv run --locked python scripts/suite_acquisition.py reproduce --family hardboiled --stage report
```

The reproduction-owned inventory in `benchmarks/reproduction/population.json`
pins all 42 source files by Git blob, SHA-256, size, and original extraction
count. Preparation downloads those exact files into a fresh evidence directory;
it does not prepare Halide. Capture omits only the statically verified unused
higher-order rules described below, retaining the exact source separately.
Each adapted file then follows the existing guarded ordinary-validation and
corpus-publication stages. Published provenance
is recorded separately from native parent completion, with proof validation
left unrun. `benchmarks/catalog.json` and the performance cache are unchanged.

The previous 34 native source parents, 38 captured sessions, and AMX paper-cell
accounting remain under `hardboiled.native_history`. Their old stage receipts
remain available; they do not contribute extra cases or block this published
population. Existing native HardBoiled settings are replaced by source-only
settings when this selected population is prepared.

## Extraction and compatibility

Commit `a85aa6e2f5195d850fba57700efcf97dc1b507a6` comments out every final
extraction, and additionally prints table sizes in `conv1d_104.egg`. For an
extraction-inclusive workload, use the exact files from its parent,
[`da432767a04c1803dc7edb5a9f653d90c0fbe623`](https://github.com/yihozhang/egglog-benchmarks/tree/da432767a04c1803dc7edb5a9f653d90c0fbe623/benchmarks/hardboiled).
This restores 2,074 original extraction queries; it does not infer new ones.
All 42 restored files were verified against that revision's Git blob hashes.

These files already use current constructor and no-merge syntax. Ordinary
execution requires no modernization. Proof mode rejects `unstable-app` and
`unstable-fn` even in an unscheduled rule. All 42 files contain four such rules
in `canonicalize`, while their sole schedule runs only `typechecking`, the
default ruleset, and `amx`.

Capture now applies `omit_unexecuted_higher_order_rules` from
`scripts/hardboiled_replay.py` automatically. Its guard requires the exact closed
schedule and rejects active uses; every scheduled rule and original extraction
query is preserved. Verification recomputes the adaptation from the pinned
source and rejects other changes. All treatments use the same adapted file;
its new hash requires new observations. Raw sources and old observations remain
unchanged.

## Verification on this checkout

Evidence is retained in ignored
`benchmarks/local/reproduction/diagnostics/hardboiled-published-suite-0001/`:

- `acquisition.json` pins the source revision, URLs, Git blobs, and SHA-256 hashes.
- `original-extractions/` contains the exact parent-revision inputs.
- `ordinary-replay-0001/` records successful ordinary execution of all 42 files
  on engine SHA-256 `7eb04703af3707fb60c1ebe8cef66a86f72de1dc55081c636b8ea38fe06229b2`.
  `output-audit.json` verifies all 2,074 requested results were emitted.
- `proof-compatible/` preserves those same schedules and queries, omitting only
  the statically checked unused rule definitions. `proof-canary-0002/` records
  successful strict proof validation of `conv1d_8.egg`. The initial unmodified
  proof-mode rejection remains in `proof-canary-0001/`.
- `coverage-review.json` records the independent paper/configuration mapping.

All executions used the shared lock and memory/disk guards. These are diagnostic
replay results, not timed benchmark samples; `.reports.jsonl` was not modified.
Those historical runs did not validate the other 41 inputs in strict proof mode.
Published replay coverage establishes this author-published suite, not full
native source regeneration or every paper experiment. The public reproduction
command selects this published source kind automatically.

The integrated public command also passes all 42 files and all 2,074 outputs.
`diagnostics/hardboiled-published-public-sweep-0001/audit.json` records the exact
bytes, ordinary outputs, and protected hashes. Repeating the full command leaves
all 84 capture/validation receipts unchanged and launches no new replay stages.

## Integrated proof-compatible selection

The earlier published-input path bypassed the manual compatibility copies above,
so timed proof runs still selected the unsupported definitions. The capture path
now applies the guarded omission, and the catalog selects the 42 adapted files
in `benchmarks/local/reproduction/hardboiled-proof-compat-20260929/corpus/`.
Original captures, source hashes, and historical observations are retained.

Current diagnostic evidence is in
`benchmarks/local/hardboiled-published-proof-compat-20260929/`:

- All 42 adapted files pass ordinary execution and proof recording, retaining
  all 2,074 original extractions.
- The reported `upsample_32` failure passes proof extraction and strict proof
  testing. Its 381 ordinary extraction outputs are identical before and after
  removing the four unused definitions.
- `publication.json` binds the validated corpus receipt; exactly 42 workload
  identities changed, with all other cases and existing blockers unchanged.

These correctness diagnostics are separate from timed benchmark observations.
`make figures-expanded` automatically collects the adapted files under their
new hashes and reuses compatible observations for other families. Strict proof
testing of all 42 files is not claimed by this repair.
