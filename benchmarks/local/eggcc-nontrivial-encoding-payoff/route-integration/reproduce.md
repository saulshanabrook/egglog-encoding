# Inspect and reproduce the Route probe

The evidence is immutable after `identities.json` is frozen. The probe sources are at `/private/tmp/eggcc-route-candidate` and `/private/tmp/encoding-route-candidate`; exact copies are in `candidate-source.tar` and `engine-source.tar`. The candidate Cargo manifests use the latter absolute engine path. Preserve existing source/evidence directories.

For an existing-artifact audit, from this directory run:

```bash
python3 inspect.py
```

The inspector checks source and artifact hashes, command-output hashes, U0/B1 parity, Manual/Encoding parity, all knockouts, both intermediate rescues, the actual primitive-column scan, semantic negatives and exact outputs. It does not collect rows, rebuild binaries, accept snapshots or time workloads.

For a fresh command matrix, use a new evidence directory at the same depth beside `route-integration`, copy `run.py`, `matrix.py`, `verify.py`, `positive-oracle.json`, `fixtures/` and `bin/` there, and run the following there. The drivers refuse to overwrite a command receipt. They require the admitted sibling `admission/bin/eggcc`, LLVM 18 tools and the recorded runtime under the exact candidate source root.

```bash
python3 matrix.py positive
python3 matrix.py negative
python3 matrix.py context-negative
python3 matrix.py source-native
python3 verify.py
```

`run.py` records exact argv, cwd, environment, file-input hashes, stdout/stderr hashes, exit code and finite timeout. It disables the benchmark memory guard. Operational elapsed values serve only timeout diagnosis. Native lowering is the same U0 `--run-mode llvm --optimize-egglog false --optimize-bril-llvm O3_O3` pipeline for every emitted/source role. Interpreter checks write separate exact-`# ARGS` files.

For a fresh candidate build and checks, use distinct receipt labels in the new evidence directory:

```bash
python3 run.py release cargo build --offline --locked --release --bin eggcc
python3 run.py focused cargo test --offline --locked --manifest-path /private/tmp/eggcc-route-candidate/dag_in_context/Cargo.toml scoped_reasoning -- --nocapture
python3 run.py dag-lib cargo test --offline --locked --manifest-path /private/tmp/eggcc-route-candidate/dag_in_context/Cargo.toml --lib -- --nocapture
python3 run.py engine cargo test --offline --locked --manifest-path /private/tmp/encoding-route-candidate/Cargo.toml -p egglog-experimental --test injectivity_disequality -- --nocapture
python3 run.py fmt cargo fmt --all -- --check
python3 run.py dag-fmt cargo fmt --manifest-path /private/tmp/eggcc-route-candidate/dag_in_context/Cargo.toml -- --check
python3 run.py clippy cargo clippy --offline --locked --tests -- -D warnings
python3 run.py dag-clippy cargo clippy --offline --locked --manifest-path /private/tmp/eggcc-route-candidate/dag_in_context/Cargo.toml --tests -- -D warnings
python3 run.py host make test
```

A fresh build must be copied into the new evidence `bin/eggcc` before running its matrix; retain its hash. `cargo insta` failures and `.snap.new` files remain failures. Do not accept them. The retained final validation records the candidate's full check outcome and verifies the selected engine bytes before reusing its earlier complete engine check.
