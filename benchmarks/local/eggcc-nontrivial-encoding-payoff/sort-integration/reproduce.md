# Reproduce the scoped-sort probe

This is a correctness and code-generation experiment. It contains no timing campaign. Run from `/Users/saul/p/egglog-encoding`.

First inspect the frozen result:

```bash
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/inspect.py
```

The inspector reads source, binary, command-stream, output-oracle, causal-control, primitive-null, and validation identities. It does not build, collect new rows, accept snapshots, or change the retained result.

To rerun the emitted/native and interpreted matrix with the frozen binaries, choose a new empty output directory. The two source trees must remain at their recorded `/private/tmp` paths because compiler runtime discovery and Cargo path dependencies are fixed there. The public compiler calls, argv, environment, input/binary hashes, outputs, and errors are retained under `commands/`.

```bash
export SORT_OUTPUT_ROOT=/private/tmp/scoped-sort-replay-unique
mkdir "$SORT_OUTPUT_ROOT"
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/matrix.py positive
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/matrix.py negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/matrix.py context-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/invalid_folds.py
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/verify.py
unset SORT_OUTPUT_ROOT
```

`matrix.py` uses the admitted U0 executable for native lowering in every role, with the same LLVM 18 `O3_O3` settings. It captures source, U0, B1 (`off`), SeedOnly, PrimitiveOnly, Manual, Encoding, seven causal knockouts, and two true intermediate rescues. The positive source/header is immutable; the interpreter uses separate copies with the exact row's `# ARGS` header, because pinned U0 interpretation ignores positional CLI arguments.

`primitive_null.py` is a separate executed null over the retained compiler graph, not dynamic reasoning in Rust PrimitiveOnly. Its retained `primitive-null.json` and command receipt enumerate every constructor schema, application, and corresponding primitive-field comparison. Its zero-mismatch conclusion is independently audited in `independent-audit.md`. Running this script in this retained directory replaces that derived JSON deterministically; inspection is sufficient for a read-only audit.

The complete host and selected engine sources are archived in `host-source.tar` and `engine-source.tar`, with individual hashes in `source-files.json`. `candidate.patch` includes both integration files and path/lockfile changes relative to verified U0. Rebuilding uses Rust 1.91.0 and the environment in `commands/build-release/receipt.json`. Required checks are captured in `validation.json`; `host-make-test` is the actual `make test` invocation, and `dag-release-tests` separately runs the DAG release suite when the host Make target stops before reaching it. No snapshot should be accepted to make this experiment appear green.

If the two isolated source directories have been removed, restore the archives into their recorded locations before using the replay commands. These `mkdir` calls intentionally require absent paths:

```bash
export SORT_EVIDENCE=/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration
mkdir /private/tmp/eggcc-sort-candidate /private/tmp/encoding-sort-candidate
tar -xf "$SORT_EVIDENCE/host-source.tar" --strip-components 1 -C /private/tmp/eggcc-sort-candidate
tar -xf "$SORT_EVIDENCE/engine-source.tar" --strip-components 1 -C /private/tmp/encoding-sort-candidate
```

The archives include runtime objects and complete dependency source; the frozen compiler binary lives in `bin/eggcc`. For a source rebuild, use `commands/build-release/receipt.json`'s exact argv/environment with the restored source trees. The Rust registry and pinned Git dependencies must be available locally for its `--offline --locked` build. Retain the admitted U0 tree and binaries as well: every native role deliberately uses that compiler's unchanged LLVM lowering.
