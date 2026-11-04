# Restricted exact local address prototype

Status: working prototype with focused correctness, independent parent review and broad test execution completed. The strict Make gates retain the engine-only snapshot and baseline Clippy limitations below. Frozen source and native artifacts are unchanged; all compiler/build processes are stopped for parent timing. No performance samples, commits or pushes were made by this worker.

The complete patch against eggcc 15ee7cba is `full.patch`; `feature.patch` excludes the already accepted engine-only dependency retarget. Both include new files. `source/` archives every changed/new file, and `checkpoint.json` pins source, patch, executable, Tiger and correctness hashes. `full.patch` passes `git apply --check` against the clean baseline. The original `retarget/engine-only.patch`, checkpoint and frozen A/B binaries are unchanged.

## Behavior and safety boundary

The CLI adds `--exact-local-addresses off|keys|query|manual`, default `off`. Enabled modes require contexts and reject ablation at CLI and Rust boundaries, including optimize's zero-pass return. Off omits the feature declarations and schedule. All measured correctness arms preserve the default parallel schedule, all three native passes, production non_weakly_linear=true and greedy Tiger with fresh-graph reconstruction.

The feature seed requires matching FunctionHasType state-only input and top-level InFunc context. Address witnesses cover positive constant-sized integer allocations, checked in-bounds constant offsets, live allocation origins, and constant-integer stores. There is no annotation on Expr, Const or runtime data and no export to global NoAlias. Static allocation ids do not justify freshness. Unsupported effects have no propagation rule; source equalities or third-pass AST inlining may expose eligible forms.

The complete original source pass runs first. Its feature postlude saturates one propagation step, injectivity and direct nongenerative audits together, so an ordinal-producing cycle cannot run unchecked. It audits before/after consumers, runs existing memory forwarding and type/indexing closure, then audits again before serialization/native extraction. Seeded pointer/count/cyclic and primitive-key conflicts are rejected before a serialization sentinel in every enabled mode.

Off-to-keys includes added memory/type fixed-point closure and query-based consistency auditing, so that contrast is not pure annotation cost. Query/manual share those costs and inference domain. Manual materializes state-scoped ManualNoAlias pairs; query consumes structural disequality witnesses on demand. Manual still uses the shared query-based audit. The prototype has no asserted-disequality workload and does not isolate NEE/EE assertion-storage costs.

## Focused correctness evidence

- `prototype-final-guards.*`: 2 passing selected tests. They execute 12 seeded conflict combinations (pointer, unequal ordinal, actual cyclic state merge, primitive-key union × keys/query/manual), each with a 2-second rejection gate and serialization sentinel, plus context/ablation rejection at graph and zero-pass optimize boundaries. These deliberately invalid equalities are seeded controls, not compiler bugs.
- `prototype-final-native-tests.*`: 2 passing selected tests, including 12 full native optimizer/interpreter round trips and actual CLI ablation rejection. The test sets non_weakly_linear=true explicitly. Fresh allocations retain the load under off/keys and remove it under query/manual; all source/optimized fields equal 17. Same-pointer and zero-offset controls equal the later 99 in all modes.
- `prototype-final-capture.*`: 18 successful frozen CLI correctness invocations and 18 separate emitted-Bril invocations. These compare A and B historical/engine-only controls with final prototype off/keys/query/manual on all three cases. Every correctness row has non-null equal expected interpreter fields, exactly pass indices 0/1/2, three native input snapshots and pinned compiler/Tiger/input hashes. A/B/off/keys emitted Bril is byte-identical per case; query/manual emitted Bril is byte-identical per case. `correctness.json` retains all rows and artifacts.
- `validation.json`: all six final frozen CLI invalid-context/ablation combinations exit 2 before producing output.
- `prototype-final-patch-check.*` and `prototype-final-diff-check.*`: patch application and whitespace checks pass.

Instrumented correctness times include logging, interpretation and graph dumps and are not optimizer performance observations. The parent will run any timing separately.

## Broad gates and retained limitations

`gates.json` pins all broad-gate argv, working directories, timeouts, exit codes and raw-log hashes. Compiler checks used Rust 1.91.0, the existing shared compiler target, four Cargo jobs, four test threads and one Rayon thread. `post-gates-integrity.json` verifies all 14 source files against the frozen copies, both patches, final compiler/Tiger and original frozen A/B artifacts. No compiler source, lockfile, accepted snapshot or frozen executable changed during the gates.

The first `make test` attempt exited 2 with 757 missing-runtime backend/benchmark trial failures (1664 passed). The documented `make runtime` prerequisite used its pinned nightly-2024-05-01 with CARGO_TARGET_DIR unset, preserving compiler caches. It emitted LLVM18 bitcode before failing the no_main executable link on macOS. LLVM18 `opt -passes=verify` accepted that bitcode; copying the emitted bitcode and compiling the existing runtime C file completed the documented outputs without source changes. `runtime-artifacts.json` and `runtime-bitcode-copy.json` pin exact artifacts and setup receipts. The first failures remain recorded as setup failures.

The resolved `make test` rerun executed 31 library tests, one CLI test, two feature-native tests and 2421 file trials with zero execution failures; two documentation tests are ignored. Its official exit remains 2 because cargo-insta retained 13 changed golden snapshots for review. It did not reach the second Makefile command. Running that exact standalone DAG command separately, `cargo insta test --release --unreferenced=reject`, passed all 66 tests with no pending or unreferenced snapshots. This is not a claim that the strict whole Make gate passed.

All 13 pending snapshot bodies reproduce byte-identically in an isolated reconstruction of the preserved engine-only B source and final prototype Off. The 26 exact-trial runs each selected one test with default features and the existing file harness non_weakly_linear=false; each expected snapshot assertion failure matches its full-gate candidate. Interpreter-result checks precede snapshot comparison. This locates the golden changes in the engine retarget, before the feature. `snapshot-controls.json`, `engine-control-source.json` and `gate-snapshots/` retain every receipt and expected/new candidate. No snapshot was accepted.

Official `make nits` exits 2 at Rust 1.91 Clippy's unnecessary_unwrap in unchanged `src/rvsdg/optimize_direct_jumps.rs:236`; the untouched original A source reproduces that diagnostic. Prettier passes. Separate root and DAG rustfmt checks pass. Strict standalone DAG Clippy reports unnecessary_unwrap in `extractiongymfastergreedydag.rs:134` and cloned_ref_to_slice_refs in `fastercbcextractor.rs:991`; both entire source files are byte-identical to A (`baseline-lint-source-identity.json`). Diagnostic root/DAG Clippy runs pass when allowing only those respective known lints. Those altered commands are retained separately and do not turn the official nits result green. No unrelated lint fix was made.

## Diagnostic row counts

`diagnostic-row-counts.{json,md}` derives 54 per-case/arm/mode/pass rows from the retained, hashed serialized egraphs, after each closure and before Tiger. These are serialized rows/nodes, not peak RSS, peak graph size or derivation counts. Counts include serialized subsumed rows.

On fresh-allocations pass 0, query and manual both have 2 ExactLocalAddress, 7 LiveAllocation and 5 FreshState rows. Query has 0 ManualNoAlias rows; manual has 6. Both record one DidExactOptimization witness. Their total serialized node counts are 544 and 550 respectively. Keys has the same 2/7/5 shared analysis rows, no pair rows or consumer witness, and 524 total nodes. This substantiates the avoided explicit pair materialization for this case, with no speedup claim.

## Reproduction and development history

The fixed `capture-correctness.py` uses archived input copies and frozen sibling executable/Tiger artifacts, then asserts interpreter results, all three passes, optimized-source identities, load removal, consumer witnesses and absent conflicts. Its exact child argv/cwd/environment and exit/timeout results are retained as `retarget/prototype-final-cli-*` receipts. It is a correctness capture, not the study's timing collector.

The final frozen compiler is `bin/eggcc`, SHA256 d44a89c2f752aff60b2691d9e055f23e54215fc9dfa74a0db8e956afc713162e. Sibling native Tiger is unchanged, SHA256 bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a. Current-executable sibling lookup selects that frozen artifact.

The earlier `prototype/bin`, `prototype/correctness.json` and `prototype-cli-*` receipts are a development checkpoint predating the ablation guard. They are retained and must not be used as the final source/binary pairing. Review identified that enabled mode plus ablation could reference a removed ruleset; final CLI/API rejection fixes that configuration gap without changing unablated analysis. No failing full native semantic experiment occurred in this slice.
