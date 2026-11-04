# Full-eggcc case-study evidence

This small driver never builds a compiler or changes a configuration. Supply
built release binaries and a fixed study JSON. Keep study evidence under
`benchmarks/local/eggcc-encoding-case-study/`, outside Cargo's `target/`.
Paths in the study resolve relative to the study JSON; CLI paths resolve from
the invocation directory. Use fresh result paths: collection refuses to replace
existing results or a receipt directory.

```sh
uv run --no-project --python 3.13 python scripts/eggcc_encoding_case_study.py collect STUDY.json RESULTS.json
uv run --no-project --python 3.13 python scripts/eggcc_encoding_case_study.py verify STUDY.json RESULTS.json
uv run --no-project --python 3.13 --with matplotlib==3.10.7 python scripts/eggcc_encoding_case_study.py figures STUDY.json RESULTS.json FIGURES_DIR
```

Python 3.12 or newer is required; these commands explicitly select Python 3.13.
Only `figures` needs Matplotlib. The pinned invocation uses an isolated uv
environment and does not add a project dependency. `collect` and `verify` use
the standard library and the existing `benchmarking.processes.run_command`.
Operational messages go to stderr; command failure returns a nonzero exit.

The following is a schema example, **not a measured case or runnable study**:

```json
{
  "schema_version": 1,
  "study_id": "chosen-eggcc-case",
  "warmups": 1,
  "observations": 10,
  "timeout_sec": 300,
  "cases": [
    {
      "id": "positive",
      "label": "Positive control",
      "input": "fixtures/positive.bril",
      "origin": "eggcc REV:path, or precise derivation and local patch"
    }
  ],
  "arms": [
    {
      "id": "B",
      "binary": "/absolute/path/to/release/eggcc",
      "cwd": "/absolute/path/to/eggcc-worktree",
      "engine": "egglog-experimental REV, ordinary NEE",
      "configuration": "engine-only compatibility arm; common Rust VERSION",
      "args": ["--with-context", "--run-mode", "optimize"],
      "env": {"RAYON_NUM_THREADS": "1"}
    }
  ],
  "artifacts": [
    {
      "id": "source-manifest",
      "path": "provenance/compiler-and-dependencies.json",
      "origin": "revision, toolchain, build flags, resolved dependency graphs and dirty diff inventory"
    },
    {
      "id": "focused-tests",
      "kind": "tests",
      "path": "correctness/focused-tests.json",
      "origin": "exact canary commands and retained stdout/stderr"
    }
  ],
  "claims": {"real_bug": null, "optimization": null}
}
```

Cases, arms and artifacts need unique filename-safe `id` values. Input and
artifact origins are required. Arms require explicit engine/configuration
labels and `--run-mode optimize`. List every configuration file, manifest,
lockfile, source diff and evidence file that needs byte-level verification in
`artifacts`; hashing an inventory JSON does not recursively hash its referenced
files. Binaries and input files are always hashed separately. The driver does
not establish source/build equivalence or semantically justify new axioms.

Represent interpreter input variants as separate `.bril` fixtures with retained
`# ARGS:` lines and origins. Eggcc's CLI currently ignores its trailing
positional arguments when constructing interpreter input. The collector passes
only each fixture path, and does not expose an interpreter-arguments setting.
Fix all optimizer flags, schedules, pass counts, extraction settings and thread
counts through the arm configuration; unspecified flags retain that binary's
defaults. Keep engine-only and feature contrasts separate.

A `kind: "tests"` artifact is JSON with `"status": "success"` and a positive
integer `"selected_tests"`; collection checks this before launching any process.
Retain command and log evidence alongside those
fields; the collector checks the receipt/count, not the truth of a hand-written
count. Claims default to explicit nulls. A real-bug claim requires
`description`, `violated_invariant`, and `baseline_reproducer` naming a retained
artifact ID. An optimization claim requires `description` and `transformation`
naming an artifact ID. These byte-level checks support manual review of the
actual baseline fault, invariant, transformation and representative coverage;
they cannot establish those claims by themselves. Label seeded faults in the
case origins and evidence.

Collection first runs every case/arm with `--interp --run-data-out RECEIPT`.
It explicitly requires both interpreter-output fields to be non-null and equal;
eggcc's CLI alone does not compare them. Correctness timings are discarded.
Only then does it run warmups and observations with the same optimizer flags,
omitting `--interp`. Every repetition visits cases in manifest order and rotates
the starting arm, giving A/B, B/A order for two arms. Warmups and interpreted
checks never enter figures. Diagnostic/profiling flags are rejected.

Compiler wall time includes launching the CLI, optimizing, extracting,
reconstructing, and writing its JSON receipt. It excludes interpretation and
does not measure generated-program execution performance. RSS is the existing
runner's platform-normalized `wait4` child `rusage.ru_maxrss`, **not simultaneous
process-group peak, host memory use, or combined eggcc+Tiger live RSS**. The
OS's child-resource accounting limits apply. Rows and figure labels retain that
scope. Use independent measurements for any stronger memory claim.

Results include exact commands, working directories, explicit environment
overrides, engine/configuration labels, hashes, full compiler JSON receipts,
exit/signal/timeout status, and raw time/RSS observations. All inherited
environment values are hashed per key; selected non-sensitive execution keys
are also retained as text. Explicit `env` values are retained as text, so do not
put credentials in the study. Other inherited values are not disclosed and
must be supplied separately if necessary for reproduction. `RUST_LOG` defaults
to `error`, matching the shared process runner. Result JSON checkpoints after
every invocation and retains incomplete/failing rows; the first failure stops
collection. Partial runs are never accepted by verification or figure export.

`verify` checks the study, current binaries/inputs/artifacts and compiler receipt
hashes, exact scheduled row count/order, invocation/configuration provenance,
successful exits, non-null equal correctness output, and positive finite timing
and RSS observations. Preserve referenced files at their recorded paths for
verification; relocating or rebuilding requires a fresh study/result capture.
No cached measurement is silently reused.

`figures` verifies first and writes `figure-data.json`, `table.md`, and one
standalone SVG/PDF pair per case. Figures show every observation, the median,
and min/max; the table includes sample standard deviation. These express
observational variability, not confidence intervals. `n=1` explicitly leaves
standard deviation unavailable. There is no overall aggregate. The figure data
retains raw values and source result/study hashes for inspection. Regenerate
into a fresh directory with the same command to check the artifact path.

Focused protocol tests use clearly labeled pytest compiler stand-ins. Their
rows are **test fixtures, not eggcc study measurements**:

```sh
uv run --no-project --python 3.13 --with pytest==8.4.2 --with matplotlib==3.10.7 python -m pytest -q tests/test_eggcc_encoding_case_study.py
```
