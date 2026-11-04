# Real-collector protocol smoke preparation

Prepared only: no build, compiler invocation, collection, test, helper import or measurement ran. The compiler owner still holds the diagnostic slot. The new raw preparation directory is `compiler/observations/collector-protocol-smoke/` under the impact raw root. It contains an unchanged input copy, explicit reference/source packages, `bindings.json`, `defaults.json`, `field-contract.json`, `commands.template.json` and a deliberately **non-runnable** `study.template.json` wrapper. No `run-01/study.json` or results file has been created. Final helper2 source/patch/check paths and hashes must exist and be bound before a runnable manifest is frozen and root authorizes launch.

## Minimal real integration check

Use frozen **debug** compiler `fresh-evidence-debug/bin/eggcc`, SHA-256 `221d6477ed5f54faba9bd0bc4b33f5489df9914f5529ffee97b3c15c3957a762`, and its exact sibling Tiger `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. Their actual files were hashed during preparation. Use the unchanged collector SHA-256 `79c4147dbe5b74d1d9138e170643a7c09205f55a6d49d355f1fc201c3a811380` from the final E1/harness worktree, and pinned `harness-prep/.venv/bin/python` (Python 3.13.11).

One case `x1` copies `mul-minimal-one.bril` unchanged, input SHA-256 `b8bc31ef18ebefd6f25057439e277569a931b2ec769295cbf590aef14550bf9c`. Keep its `# ARGS: 1`; expected source/result are independently **`false\n`** in every arm. The reference follows wrapping i64 `1*2=2`, signed `2<0=false`, and cites the existing frozen source-oracle receipt and x=1 CLI matrix. No new source-oracle execution is implied.

Arms are Off/Manual/Injective, with one binary and compiler cwd `/Users/saul/p/wt/eggcc/encoding-impact` throughout. Actual recognized arm arguments are:

```text
--with-context --run-mode optimize --observations off
--with-context --run-mode optimize --observations manual --observation-evidence-dir ABS_RUN_DIR/evidence/manual
--with-context --run-mode optimize --observations injective --observation-evidence-dir ABS_RUN_DIR/evidence/injective
```

The collector owns input, `--interp` and unique `--run-data-out` paths. Do not add those to arm arguments. No query probe, profiling, instrumentation, debug/egraph dump or ILP timing flag is enabled. Retain the frozen CLI defaults: Parallel schedule, all three default passes, production `non_weakly_linear=true`, context enabled explicitly, greedy Tiger, no ablation/function subset, and `RAYON_NUM_THREADS=1`. These values come from the SHA-bound main/config source and existing frozen x=1 captures, not a new CLI call. ILP defaults are inactive. `defaults.json` records the remaining settings.

Set `warmups: 1`, `observations: 1`, `timeout_sec: 300`: **nine calls**, ordered three correctness, three warmups and three measurement-phase protocol calls, each phase Off/Manual/Injective. Three correctness outputs must all equal the independent reference. Six later outputs must be null because those calls omit interpretation. Manual and Injective must each create three distinct persistent children under separate fresh roots; Off has no observer tree/locator. A single round is deliberately not a balanced cost cohort. Retain raw timing fields as diagnostic protocol data, but discard them from study analysis: no cost table/figure, aggregate, variability or speedup inference.

## Concrete verified artifact IDs

Use `--reference-artifact expected-x1-reference` and `--source-artifact smoke-source-package` for the proposed helper2 collector post-step. Case key is exactly `x1`.

`reference.json` SHA-256 is `3c294f2f86642baffbedfe3402f8d53a95c661c461406432e6a92a0967c576e5`, with the required shape:

```json
{"cases":{"x1":{"input_sha256":"b8bc31ef18ebefd6f25057439e277569a931b2ec769295cbf590aef14550bf9c","expected_output":"false\n"}}}
```

Additional origin/contract fields retain its basis. The frozen endpoint manifest's actual keys are `binary_sha256`, `source_manifest_sha256`, and **`source`** for its source-manifest pathname. Rather than rewrite it, `source-package.json` normalizes that pathname to `source_manifest`. Package SHA-256 is `3ade7dff4ba80b5dd523950a7ff30dc94691334c7c9891b13b8d9ccc210106f0`; it binds binary `221d6477…`, source-manifest `25d0615af2ff87c97d4bad79f4bb0f9829d026cbe8255dfd6ec08875d8ecf297`, the unchanged endpoint manifest, source patch and Tiger. Its helper2 provenance is deliberately separate from the compiler build authority: changing Python post-capture tools does not claim those tools were compiled into this binary.

The template also individually lists `frozen-debug-endpoint`, `frozen-debug-source`, `frozen-debug-patch`, `frozen-tiger`, `encoding-final-authority`, final harness checkpoint/patch/gates, pinned Python environment/lock, source-oracle command/receipt and existing matrix. `bindings.json` records actual paths and hashes. No mutable output root is an immutable pre-run artifact. The placeholder IDs `helper2-source`, `helper2-patch`, `helper2-checks` must be replaced with actual frozen paths/hashes and reviewed outcomes; do not create hand-written fake test counts to satisfy the collector's optional tests-artifact protocol.

## Named verified-cohort post-step

The owner proposes a `collector` subcommand taking `--study`, `--results`, `--collector`, `--source-artifact` and `--reference-artifact`. Its implementation/entrypoint/output flags are not yet frozen. `field-contract.json` is the concrete association contract; it supplies no invented `verified: true`, independent PID or full-stderr field.

The step must hash-pin and import the frozen collector and call its actual `verify(study, results)` with normal completeness checks. Hash the immutable study/results bytes, select the exact row index and `(phase,repetition,case,arm)` from that verified result, then recheck the results hash before archival. Bind actual row command/cwd/engine/configuration, explicit and effective environment hashes, status/exit/signal/error and normal compiler receipt. Binary/input/source/reference hashes come from the verified `results.provenance` entries, selected by kind/id, not a newly fabricated row. This collector uses plain 64-hex SHA-256 values without the public benchmark cache's `sha256:` prefix.

Copy each normal compiler JSON to a fresh per-row path, require its original/copy hashes to equal `row.receipt_sha256` and parsed content to equal `row.receipt`, and retain the copy association without changing historical argv. Validate the source artifact's binary hash against that arm's binary provenance; match the source manifest path/hash to the individually verified `frozen-debug-source` artifact. Match the reference's `cases.x1.input_sha256` to the case input provenance. The reference's exact output is independent of the row's own interpretation fields.

For each arm, the correctness anchor is **the same case/arm, `phase=correctness`, `repetition=0`**, with strings `false\n`/`false\n`, matching source/binary/configuration/cwd/mode/root/environment identity. Warmup/measurement rows require both interpreter fields present and null, and retain that correctness row index/identity/receipt hash plus the reference artifact hash. Do not accept a cross-arm correctness substitute, reinterpret nulls, or turn on `--interp` during timing. Off binds these normal provenance/receipt/reference fields and requires an absent/None observer locator; it does not manufacture an evidence tree.

Enabled rows take the successful locator from the copied compiler receipt. Validate mode/root, all required complete pass artifacts/stages, no conflicts, full-tree containment and hashes, and cohort-wide child uniqueness across **all three phases**, not just the final three rows. Successful collector rows contain **no independent Popen PID or full stderr**; index PID remains compiler-declared. Do not route these rows through the full-stderr diagnostic archive API. Existing greedy x=1 normal receipts have `extract_region_timings=[]` in all three modes, so its length must not be used as a three-pass counter. Enabled completion markers and source-bound full CLI evidence provide that boundary; Off has no new observer index or per-row log/native dump attestation.

The actual row order and all field names are written in `field-contract.json`. Expected final counts are nine copied receipts, three reference-checked correctness anchors, six null/null later receipts, three Off no-tree bindings and six unique enabled trees. Failed/missing rows, changed provenance/results, wrong phase/linkage, swapped/duplicate children or malformed evidence stop this smoke and retain the failure; they do not justify weakening verification.

## Future commands, not executed

Cwd: `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding`. The exact known collect/verify argv and common outer environment are machine-readable in `commands.template.json`. Once helper2 is frozen, the manifest is bound, fresh output roots are confirmed and root releases the diagnostic slot, the intended invocations are:

```sh
EGGLOG_BENCH_MEMORY_GUARD=1 RAYON_NUM_THREADS=1 RUST_LOG=error \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/harness-prep/.venv/bin/python \
  /Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/scripts/eggcc_encoding_case_study.py collect \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/collector-protocol-smoke/run-01/study.json \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/collector-protocol-smoke/run-01/results.json
EGGLOG_BENCH_MEMORY_GUARD=1 RAYON_NUM_THREADS=1 RUST_LOG=error \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/harness-prep/.venv/bin/python \
  /Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/scripts/eggcc_encoding_case_study.py verify \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/collector-protocol-smoke/run-01/study.json \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/compiler/observations/collector-protocol-smoke/run-01/results.json
```

The guard setting must be in this common **outer** environment. An arm-only setting does not activate parent monitoring. Keep its invocation/policy receipt separately; source failures/resource stops are retained honestly. Future helper2 execution must use the frozen actual entrypoint with source/reference IDs above; its proposed command remains a placeholder until owner supplies it. No cost window, study collection, alternative wrapper/native adapter or collector/model/Rust source change is authorized by this preparation.
