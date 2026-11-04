# Reproduce the Parts32 integration gate

Use `source-admission.json`, the two admitted Git archives, `final-source.tar`, `eggcc-final.patch`, `encoding-final.patch` and `final-source-identities.json` to reconstruct the exact evaluated source. The selected E1 files and upstream source hashes are embedded in the admission record. `write-candidate.py` records the initial implementation; `failure-ledger.json` explains the one transport revision. Do not rerun admission scripts over existing candidate paths or capture commands over an existing label: they deliberately refuse overwrite.

The exact compiler and native commands, cwd, environment, bounds, input/executable hashes, streams, exit codes and diagnostic elapsed times are in `final-reviewed/commands/*/receipt.json` (native replay) and `commands/*/receipt.json` (builds and validation). Those elapsed times are not performance samples. Every compiler command is bounded at 180 seconds; native checks at 30 seconds. Cargo checks use a longer finite bound. Memory-pressure blocking is disabled.

From the root workspace, the captured public driver invocations were:

```
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py positive
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py loop-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/matrix.py context-negative
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/inspect.py
```

Run matrix phases only into a new evidence root. Existing phases already contain immutable command labels, compiled outputs and native captures. `inspect-final.py` can be rerun against the final retained captures; it neither compiles nor executes native binaries.

The focused registered commands are retained as `focused-reviewed-final` (five tests) and `engine-tests` (18 tests). The isolated engine root's required validation entrypoint is `make check`; local-cache and Python interpreter details are in its receipt. The private empty Git metadata exists only so Python root-discovery tests operate on an actual repository; no commits were created.

The available source-boundary modes are `off`, `seed-only`, `primitive-only`, `forward-off`, `reverse-off`, `identity-off`, `high-rescue`, `query-off`, `manual`, `encoding`, `bridge-off`, `consumer-off`, and `if-consumer-off`, selected by `EGGCC_SCOPED_MODE`. `EGGCC_SCOPED_EVIDENCE` points to a new directory for boundary receipts. The extra `known-disequal-forward-only?` read primitive disables all generic reverse edges while preserving graph rows and seeds; ordinary `known-disequal?` is unchanged.

The accepted generated-runtime campaign is bound by
`prospective-timing-design-frozen.json` and `timing-preflight.json`. Its two
complete session directories contain 1,350 raw rows, 45 warmups, eight process
checks, and one summary each. Recompute the accepted result without executing
native programs:

```
python3 -B benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/verify-timing.py
```

That verifier uses exclusive creation and therefore refuses to overwrite the
retained `timing/independent-verification.json`. To rerun it, copy the complete
experiment directory to a new location and remove only the copied verification
file. Never mix rows from `timing-aborted-process-admission-01` or
`timing-aborted-process-admission-02` with an accepted session. The accepted
verification SHA-256 is
`9b26a8c4a1176979d555ff0c054ee0c985c8a3faa0e7c4313f225a4cbaaae959`.

The compiler-time diagnostic is separate and descriptive. Its validated
frozen result is under `compile-diagnostic-final/results/`; its summary SHA-256
is `283a6af7bb6a9d69d87510fab681042170f47ff70efa7a95719e37a8d36ad12e`.
Running it again requires a copied result root and the exact reconstructed
working directories recorded in `compile-diagnostic-final/reconstruction.json`.

For a fresh replay with the final immutable compiler, set `PARTS32_BINARY` to the absolute path of `bin-reviewed-final/eggcc` and `PARTS32_OUTPUT_ROOT` to a new empty evidence directory before invoking `matrix.py`. The retained final replay lives under `final-reviewed/`; never overwrite it. Run `python3 .../parts32-integration/inspect-final.py` to recheck that complete capture without executing any compiler/native binary.

`seed-only` retains the exact graph, representation identities and dynamic seeds and performs no saturation, contradiction probe, witness query, manual closure or export. `primitive-only` retains the same graph/seeds and finds no marked primitive fields; it also performs no equality-sort inference. The final capture asserts these graph and seed identities. The first rejected null and all earlier captures remain preserved outside `final-reviewed/`.

`final-reviewed/compile-command-map.json` contains exact observed optimize commands plus templates requiring fresh run-data/evidence paths for every separate compiler-time diagnostic. It binds source, executable and emitted hashes. Such a diagnostic cannot serve as generated-runtime speed evidence.
