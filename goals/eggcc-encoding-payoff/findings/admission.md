# Foundation admission

U0 is admitted as an untouched-main release compiler/current-main Tiger pair with the declared git dependencies and an existing passing interpreter/native canary. Frozen E1 passed its 18 integration tests and one ordinary-file trial. This is infrastructure admission, not a new bug, optimization, speedup, full-suite result, or prospective endpoint result.

The terminal index is [admission-summary.json](../../../benchmarks/local/eggcc-encoding-payoff/admission/admission-summary.json), SHA-256 `cd3808c67369c0c57dbb3516e2dda00c7ce431c157387982ef5df19296422450`. It binds 75 shell-free command receipts with exact argv/cwd, per-value effective-environment hashes, explicit environment, timeout, PID, terminal exit, and full stdout/stderr hashes. All commands are terminal; all owned build/canary/test PIDs are absent. Expected nonzero statuses are absent-branch checks and the final absent-process check, not failed builds/tests.

## Isolated sources and handoff

Revalidated origin main/PR handles before reconstruction:

| Role | New worktree | Base / authority |
|---|---|---|
| U0 | `/Users/saul/p/wt/eggcc/encoding-payoff-upstream-control` | `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, branch `codex/eggcc-encoding-payoff-upstream-control` |
| B1 | `/Users/saul/p/wt/eggcc/encoding-payoff` | same main, branch `codex/eggcc-encoding-payoff` |
| E1 | `/Users/saul/p/wt/egglog-encoding/eggcc-encoding-payoff` | `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`, branch `codex/eggcc-encoding-payoff` |

Compiler origin main was `a0bbec127f83249074a46af3fd6f6126c90fe0fb`; encoding origin main was `03e533714524c1b21be77edff46fb694120b8b81`, PR119 head `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`. These are captured live handles, not a claim that historical `15ee` is current main. Applicable root/new-E1 AGENTS were read before edits; no compiler AGENTS file was present.

`admission/main-source.tar` is the exact main git archive; `main-source.json` SHA `28218c37633a31839936dfa2bce7675f092b26dc1cbf557bc9baad92836c2c3e` maps 771 source files. U0 stayed byte-identical throughout and has clean final git status.

E1 applied only the frozen combined-goal reconstruction patch SHA `0d7a25f64b68b21bef48a56f6df36c3fa6071feed0ed5597bea481897083e687` on392b. All969 source hashes match the old authority and remain unchanged after tests. `admission/E1-source.json` SHA `97618f533dfb36f038432cab4517cff78a855eb23caf1ea100f3e27e35f44fe2` binds the source map, patch and authority. No new encoding implementation was added. Generated `.pyc` files are outside all three source maps; admission adapters disable bytecode writing.

B1's dependency-only handoff changed exactly `Cargo.toml`, `Cargo.lock`, `dag_in_context/Cargo.toml`, and `dag_in_context/Cargo.lock`, retargeting both experimental-engine dependencies to new E1. Intentional lock regeneration was followed by equal locked root/DAG metadata: B1 resolved295/190 packages; U0's unchanged locked metadata resolved291/185. Full graphs and sources are retained, so these counts are not the only dependency evidence. The immutable handoff authorities are:

- `admission/B1-handoff-source.json` SHA `bb1bd4c546fae2413f2f5a51dd634b3b7b303ae3f6069af84d87939364315f1c`.
- `admission/B1-handoff.patch` SHA `b92c8f39273702f466da4217fad80904b91350d352857cfd5a3cf9cd013b8747`.

Root transferred B1 source/build ownership to the compiler worker before U0 completion. This agent performed no B1 observer/API port or code generation and did not inspect or touch live B1 after handoff. Future B1 identities belong to that worker's checkpoints.

## Effective environment and U0 pair

Recorded tools: Rust/Cargo1.91.0 (`aarch64-apple-darwin`), Homebrew LLVM/clang18.1.8, `/usr/bin/g++`. Commands used role-private `CARGO_TARGET_DIR`, `CARGO_BUILD_JOBS=4`, `RUST_TEST_THREADS=4`, `RAYON_NUM_THREADS=1`, `LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18`, `LIBRARY_PATH=/opt/homebrew/lib`, `PYTHONDONTWRITEBYTECODE=1`. `RUST_LOG=error` except the passing U0 diagnostic used `info` to retain pass markers. Memory guard was UNSET in every receipt. Compiler wrappers, Rust flags, snapshot acceptance and Make overrides were removed; no storage or memory-pressure admission block was introduced.

U0 retained its declared experimental revision `08771f9f69de51cc8cdc58e3760b7f00a03e40d8` and underlying egglog revision `ebba7bb902bdc1b0f377b6bb22c06ac305912674`. Both dependency checkouts were tracked-clean at start/end. Exact command, cwd U0:

```sh
cargo build --locked --release --bin eggcc
```

It exited0 without timeout (1,800-second bound). Compatible old control cache was cloned privately; copied historical top-level eggcc/Tiger binaries were quarantined outside lookup paths. The actual main build supplied Tiger without a buildscript workaround. The frozen pair and final admission authority are:

- `admission/U0-release/manifest.json`, SHA `6f1b81ec383a88a15abff05152a66d6e826db24817d6f021b9670ed3889296fa`.
- `admission/U0-release/bin/eggcc`, SHA `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0`.
- `admission/U0-release/bin/tiger`, SHA `130eaba8bb575e196b8e18898826356269efe6e28a56b9d3690ef42647d3b201`.

The old `bd53…` Tiger was not admitted for main. The manifest binds main Tiger/build-script source hashes, actual C++ executable/flags and artifact hash. Reused runtime `rt.bc`/`rt.o` have SHA `c24564b983852848320eed8cd19cc02678ad781a821e6dff133489994c644f91` / `07123ecfab57014f9f227953c277fa53edca38c7c1e362ebf02ee5a44be62b84`; all six runtime source inputs match the retained compatibility authority. This is explicit compatible artifact reuse, not a fresh runtime-build claim.

## Existing passing canary

Six bounded calls used the frozen pair from cwd U0 and a copied, hashed `tests/passing/small/add.bril` (`1+2`, expected independently `3\n`):

1. `--with-context --run-mode parse --interp --run-data-out SOURCE_JSON INPUT`.
2. `--with-context --run-mode optimize --interp --run-data-out CORRECTNESS_JSON INPUT`.
3. `--with-context --run-mode llvm --optimize-egglog false --optimize-bril-llvm O3_O3 -o REFERENCE --llvm-output-dir REFERENCE_LL --run-data-out REFERENCE_JSON INPUT`.
4. Execute `REFERENCE` directly.
5. Same LLVM command with `--optimize-egglog true` and fresh optimized output paths.
6. Execute optimized binary directly.

All six exited0 without timeout. Parse/optimize original and result interpreter fields were non-null and exactly `3\n`; both actual native binaries exited0 and printed exactly `3\n`. Native-lowering interpreter fields were null and were not treated as correctness evidence. Optimize and optimized-lowering full logs each show actual passes0,1,2. Complete concrete paths/argv/JSON/LLVM/binary hashes are in the manifest and command receipts. No `--add-timing`, new-case endpoint, emitted-Bril reparse, or empty-ARGS printer fix was involved.

## Frozen E1 focused validation

Cwd E1, private E1 target cloned from compatible old frozen E1 cache:

```sh
cargo test --locked -p egglog-experimental --test injectivity_disequality
cargo test --locked -p egglog-experimental --test files injectivity_disequality -- --exact --nocapture
```

Both exited0 without timeout (1,800-second bound each). The first ran18/18 passing tests, no ignored/filtered tests. The second selected exactly1 ordinary-file trial and passed1/1. `tests/files.rs` uses sanitized filename stems: the old proposed path-shaped filter would have selected0, so it was corrected from source before execution; that wrong filter was never run. `admission/E1-tests-result.json` SHA `73f4017d333cf0b6e2ff2955365120ab783a1877dbf0ec287f93d680f81f6e07` binds counts and source identity. Command receipt hashes are `7afd1f1bd6d338dd4b99e7795409a676fb6655a2fc131b99b41848007b001cd2` and `4ca769b5d482c6382c436f5251c99998c979acba5736cda9140101cde61fba92`.

## Preservation and remaining admission

The prospectively frozen34,654-entry protected inventory included old source and case-study/impact/combined evidence. Final comparison found **0 changed,0 missing** bytes/modes/symlink targets, without restoration. `admission/protected-final-comparison.json` SHA `374872fef043a786b547d1e2b065ca9e9ecf9eea2cbe5bbe0ef137d70af65ff8` binds the original inventory SHA `a814ed99f3ce69966e3ca6838bfc735ec62510ec28aa3e859797f52d2c737db6`. New payoff coordination/evidence was excluded prospectively. Final U0/E1 source maps and exact terminal process check are indexed.

No full Make gate, proof subset, performance cohort, new-case optimized endpoint, source/snapshot acceptance, commit or push occurred. Official current-main gates still require fresh attribution; historical snapshot/lint failures confer no waiver. B1 port/controls and first encoding detector receipt remain root-coordinated before independent prospective U0 endpoints. This admitted foundation alone does not satisfy the payoff goal.

## Subsequent final U0 gates

The paragraph above describes the original foundation checkpoint; its complete report bytes are retained as `admission/final-gates/u0/findings-before.md` with original SHA `deda97283fa4f00c994530164654b17baa4bc2de0e6223dfb0e97811a8aaf46c`. After the independent U0 endpoint slice, root authorized this separate final gate slice with sole broad-command ownership. B1/E1 full gates did not overlap it.

**Fresh U0 `make test` passed. Official `make nits` failed and remains failed.** The full summary is [final-gates/u0/summary.json](../../../benchmarks/local/eggcc-encoding-payoff/admission/final-gates/u0/summary.json), SHA `20ecfd32e9e7dd1290ec7df3c6ff626723bb8d433968d06e72830cfe19423d25`. Exact command/env/stdout/stderr and before/after source receipts are under its `commands/` directory.

Commands ran sequentially, with shell-free argv and a 3,600-second process-group timeout each; none timed out. They used Rust 1.91, 4 build jobs, 4 test threads, Rayon 1, LLVM 18, explicit Python 3.13, U0-only target/runtime root, memory guard UNSET, and cleared wrappers/Rust flags/Insta update/force-pass/Make flags. No `fixnits`, source edit, snapshot acceptance, lint allowance, or selective rerun occurred.

| Command | Cwd | Exit | Actual coverage |
|---|---|---|---|
| `make test` | U0 |0| 31 root library and 2,421 integration tests passed; 2 root doc tests ignored; 64 DAG tests passed; 0 pending/unreferenced snapshots |
| `make nits` | U0 |2| Prettier passed; installed pinned Clippy/rustfmt components available; root strict Clippy failed at one site; root fmt and all DAG nits unreached |
| `cargo fmt --check` | U0 |0| Unreached root format check passed |
| `cargo clippy --tests -- -D warnings` | U0/dag_in_context |101| Unreached strict DAG lint check failed at two sites |
| `cargo fmt --check` | U0/dag_in_context |0| Unreached DAG format check passed |

Official test receipt SHA is `a34951f3594067bb488897df1036660bf4f214c6eba409bbb2b5ebfe535b0d97`; official nits receipt SHA is `5ff3b6aac95d3a78ccdc428254911e5f7596ec9b9cb1c1d181e15adab90ed040`. The official test target reached the complete DAG suite, so no DAG test rerun was needed. Only skipped nits components were supplemented. The successful test total is 2,516, with 2 doc tests explicitly ignored; zero-selected binary/doc targets are not counted as successful case coverage.

The three strict lint failures are established afresh on untouched `a0bb…` U0 under Rust 1.91:

- `src/rvsdg/optimize_direct_jumps.rs:236`, `clippy::unnecessary_unwrap`, source SHA `d15406ee7ef7e72f04a0185648c0d1ce5ea83d6c609c9da36ab8bc26acd936c7`.
- `dag_in_context/src/extractiongymfastergreedydag.rs:134`, `clippy::unnecessary_unwrap`, source SHA `2f8406cd070d52f054ff74e2863270510a68e1296560ebe64b818cf4feb9c365`.
- `dag_in_context/src/fastercbcextractor.rs:991`, `clippy::cloned_ref_to_slice_refs`, source SHA `cb0c10f5ce03e6b7ac42c70a978a40a9184cd219ca9d54f051f7b9b27ca15052`.

Exact numbered source excerpts and full diagnostics are retained/bound in `summary.json`. This is current U0 attribution, not an inherited 15ee waiver. Historical 13 snapshot failures did not recur here: all current U0 tests/snapshots passed without accepting a snapshot. Candidate/B1 failures still require their own exact source/diagnostic matching.

Before/after every command, all 771 source/accepted-golden/manifest/lock hashes matched the main source authority; the admitted compiler/Tiger/runtime and actual target compiler/Tiger hashes stayed unchanged. Final git status is clean. The final protected audit rechecked all 34,654 prior entries with **0 changed, 0 missing**, no restoration: `protection.json` SHA `915dddcc93d9b428dc69d6a39beb68b712debb6a6b5c0b7ce5d8ea571c7f10b9`.

The initial read-only summary attempt was denied permission to launch `/bin/ps` by the new sandbox after its source/protection checks passed; its stdout/stderr and protection receipt remain as `summarize-attempt1.*` / `protection-attempt1.json`. A bounded read-only audit escalation had already been launched before root said that process inspection was optional; it completed with exit 0 and confirmed all five gate PIDs/process groups absent. No gate/build/test was repeated for that bookkeeping check. All command sessions are terminal and the broad-command slot is released. No prospective case or performance evidence was collected in this gate slice.
