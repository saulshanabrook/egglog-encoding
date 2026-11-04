# Reproduction and evidence navigation

Start with `report.md`, `summary.json`, `acceptance.json` and `positive-rejection.json`. `commands/*/receipt.json` retains exact argv, cwd, environment, executable/input hashes, stdout/stderr hashes, exits and timeout bounds. The stdout/stderr siblings preserve the full output, including all failed attempts. Diagnostic elapsed values are not performance samples.

`initial-installed-scoped_alias.rs` is the actually tested initial implementation; `inputs/scoped_alias.rs` is the earlier formatted source template. These were already distinct before this task. `revision-1.patch` is against the installed initial module. `revision-1-scoped_alias.rs` is the tested revised module. `final-source-r1.tar` contains both complete source roots; `source-identities.json` binds each member. Preserve the fixed root paths if rebuilding because both Cargo manifests use an absolute encoding path.

To rerun the expected failing focused suite in the retained copied roots, set the same environment as `run.py`, choose a fresh command-capture directory, and execute:

```sh
cargo test --locked --manifest-path /private/tmp/eggcc-alias-actual/dag_in_context/Cargo.toml a1_ -- --nocapture
```

The expected result is three passing and three failing tests. The complete host library command is the same without `a1_ -- --nocapture` and with `--lib`; expected result is 67 passing and three failing tests. Full gate output is under `commands/full-host-lib/`.

For the actual endpoint, inspect `positive-results.json`, `negative-results.json`, and `matrix/*/*/result.json`. Each arm retains its emitted `optimized.bril`, interpreter/compile run data, egraphs, evidence receipt, native `program`, complete LLVM, disassembly and selected compact functions. Replaying a native binary with the retained `outputs[].args` must reproduce `expected_stdout`; this needs no compiler or benchmark-cache writes. `inspect-binaries.py` contains the exact extraction and assertions for actual native code, and should be run only on a disposable copy of this evidence directory because it writes derived inspection files.

`matrix.py` specifies the exact fixture mutations, argument rows and independent arithmetic oracle. It is a diagnostic/correctness driver and contains no timing collector. For a fresh full replay, copy the scripts into a new evidence directory, point its frozen compiler/U0/input paths at these hash-verified artifacts, and let `run.py` create new labels and receipts. The supplied scripts refuse command-directory collisions; do not rerun them into frozen captures.

Setup failures remain explicit: a diagnostic logging format error, the initial/revised certificate failures, one relative-path CLI launch failure followed by a successful absolute-path retry, and a historical installation-hash assertion failure. `freeze-first-failure.json` explains the latter and the corrected script-name shadowing issue. No such repair changed compiler semantics after functional revision one.
