# Final compiler gates: terminal with matched inherited failures

**No new unmatched compiler/source failure was found. Official `make test` and `make nits` remain failed in both candidate and fresh control.** This is bounded attribution, not an overall green validation claim. The build slot is released; every owned command PID is absent after completion. No source, golden, lock, encoding, old evidence, proof or paper edit was made by gate execution.

The exact final candidate authority is `consumer/oracle-final/source.json`, SHA `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`, checkpoint SHA `227599b8ac493ecb60b012191d8d56b7ae90e602ad721992f8c00c8ec2a6b985`. Its794 files differ from the prior production-final package only by the reviewed test-only independent oracle addition. The fresh control retains all788 pre-integration source bytes, authority SHA `1ba7cec15488284f396d57473b28a9d455bf490c5ec475580540dce0898d811e`. All969 E1 source identities remain unchanged. Fresh locked root/DAG metadata resolve295/190 packages and are exactly equal between roles after compiler-root relocation only.

| Exact gate, sequential per role | Candidate | Fresh pre-integration control |
| --- | --- | --- |
| root `make test` | rc2;37 lib +1 CLI +2421 integration passed;2 docs ignored;13 pending snapshots | rc2;36 lib +0 CLI +2421 integration passed;2 docs ignored;13 pending snapshots |
| root `make nits` | rc2;Prettier passes;root strict Clippy stops at line236 | same |
| DAG `cargo insta test --release --unreferenced=reject` | rc0;83/83 tests;no pending/unreferenced DAG snapshots | rc0;74/74;no pending/unreferenced DAG snapshots |
| root and DAG `cargo fmt --check` | both rc0 | both rc0 |
| DAG `cargo clippy --tests -- -D warnings` | rc101;two unchanged sites | rc101;same two sites |

The DAG sub-gates and root format checks ran because official Make stopped before reaching them. The candidate's full suites include the5 existing root observer tests,10 DAG observer tests,9 structural DAG tests (including the54-row independent Rust Type-equality oracle), one valid source/native host control over5 modes and one CLI parser test. Control full suites include the same existing observer5+10. **No filtered canary subset was rerun** after that coverage. CLI production defaults/native results remain separately bound by the owner's ten actual optimize/emit receipts; cfg(test) integration uses `non_weakly_linear=false`, while default CLI is true. These full suites do not replace that distinction.

The13 exact pending snapshot names in the official runs agree, and all complete actual `.snap.new` files are byte-identical across the fresh roles. Then26 fresh selected invocations—13 per role, `cargo test --locked --release --test files TRIAL -- --exact --nocapture --test-threads 1`—each selected exactly1, failed only that snapshot and exited101 without timeout. Every actual file equals its own official capture and the other role's entire file. Each pair binds the same input, `tests/files.rs`, `src/util.rs`, accepted golden, flags, shared E1 and dependency graph; accepted snapshots were never changed. Selected attribution results SHA `66e858edb0480e898f17b0cb3cab982ff01e8a6f8050195acb163401a509777d` records all pairs. This reproduces the limitation under the current matched E1/harness; it does not establish the cause of every old golden difference or claim upstream/pre-E1 correctness.

All three strict Clippy diagnostic blocks and their full source file bytes match in the fresh control: root `src/rvsdg/optimize_direct_jumps.rs:236:28` (`unnecessary_unwrap`); DAG `src/extractiongymfastergreedydag.rs:134:33` (`unnecessary_unwrap`) and `src/fastercbcextractor.rs:991:37` (`cloned_ref_to_slice_refs`). No diagnostic in newly owned structural source appeared. `attribution/lint-results.json`, SHA `b619e1afadc1a1ad4714244dfe21d058edb9add89e8574ffb1cfeb564a302cc0`, retains exact blocks/context/source hashes. No allowances or fixes were used; strict Clippy failure is still a limitation.

A raw-only standalone Rust1.91 caller exported public `dag_in_context::prologue()` from each role's actual root-gate-built rlib. Source maps, Cargo compile logs, freshly role-relocated depinfo, actual rlib/link-search artifact hashes and toolchain are bound; cache filenames alone are not the source proof. Both default outputs are **185221 identical bytes**, SHA `d5aacd0b84d58c0674b18188c43e25f30488c1920ae54142391508dfec9c76b7`. Actual Debug defaults differ only by candidate `structural_types: Off`; both retain `observations: None` and `non_weakly_linear: true`. `prologue-export/results.json` SHA `3388b94e847c3d3b17adf1342af86e4f370a9b63ffa098d016552746486d46ae` is the direct default-Off byte comparison. No worktree test/source file was added for it.

Each command records shell-free argv/cwd, full effective-env per-value hashes, stdout/stderr, terminal status,1800s timeout and compiler/E1/accepted-snapshot/runtime/Tiger identities before and after. Rust1.91/jobs4/testthreads4/Rayon1/LLVM18 match preparation. `EGGLOG_BENCH_MEMORY_GUARD` is **unset** throughout; no memory-pressure gate was reintroduced. No command timed out. Actual release Tiger remains executable and `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`; pinned runtime BC/O remain unchanged. Candidate release EggCC remains `95c8d944cdc4fb816d3f65ea653feba07fffaae2fb4043507a1c47160f2b9082`. No new performance claim or measurements were made.

All794 candidate/788 control source bytes and accepted snapshots are unchanged at terminal. Visible additions outside either source map are exactly the13 retained pending snapshot files per role; target/runtime outputs are classified separately as generated. `source-after.json` SHA `4d2f039d1260f1dbbbdb4da70a9cfa7727f7b1008a55dd6cd2b4e343e0b770b2` binds the complete maps. The final protected comparison checked **30609 prior files/modes/symlinks,0 changes**, receipt `protected-after.json` SHA `a51068e16ba908492b244ca4e4c62bda957244597b765763d8288e806021ad94`. No restoration was used.

Raw tooling failures remain visible: the selected-case checker initially used an incorrect capitalized Insta-message substring, then a malformed string edit was caught by AST parse before another command. Both checker versions/errors are retained; the already-valid first selected receipt was validated and reused without rerunning that test. The standalone export's initial link failed because direct rustc lacked Cargo's OpenBLAS search directory; the retry passes the actual retained Cargo build-output `rustc-link-search` directives and succeeds. None was repaired in compiler/encoding source, and no official gate was relabeled because of these repairs.

The terminal index is `benchmarks/local/eggcc-combined-encoding/final-gates/summary.json`, SHA **`b116e66101b0cd69c25ea53e7725e4b356c3fca3074999ef42c046c1192f1b69`**, binding47 actual command receipts (including the retained direct-link failure), all artifact comparisons and owned-PID termination. Root may use this as bounded final-gate/attribution evidence with the explicit failed official targets; release/goal claim scope remains root-owned. No further build/test is scheduled by this worker.

---

# Historical preparation record

**Preparation complete; no gate build/test has run.** The compiler worker retains the shared slot. Candidate source is untouched by this worker; its final checkpoint and root slot allocation are still required before executing the prepared gates. No new encoding full check is scheduled: the exact unchanged engine source has its completed18-test focused regression, and all969 source hashes were rechecked again here.

Created only the absent detached worktree `/Users/saul/p/wt/eggcc/combined-encoding-control` at `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. Applied the immutable pre-integration retargeted patch from `provenance/baseline-source.json` (SHA `d4ebbe674bda0ba3fda19f7c8e8fdfd4f8974c056839651b9bea1ffe90bfebb1`); apply-check and apply exited0. All788 control source files match that package **byte for byte**, before and after metadata. Regenerating the complete control patch reproduces the exact input patch SHA `73e93343ede42fde1b2a0f48e56060b5afbf6791e3f54fd1e142a3066d3f8c40`. Both Cargo manifests already point to the same new E1 source `/Users/saul/p/wt/egglog-encoding/eggcc-combined-encoding/egglog-experimental`; no candidate-source read/copy was used to derive the control.

Locked root/DAG metadata commands both exited0 and match the complete pre-integration graphs exactly after relocating only the compiler root to the control path (295/190 packages; same shared new E1 paths/features/dependencies). All969 encoding source hashes match the completed regression map. The two historical `.pyc` entries are retained/generated package bytes, not new authored tests or loaded Python. Complete source/metadata identities are frozen in `final-gates/preparation/control-source.json`, SHA `1ba7cec15488284f396d57473b28a9d455bf490c5ec475580540dce0898d811e`.

Prepared compatible native runtime assets without rebuilding: six runtime source inputs match the frozen compatibility authority; copied `rt.bc` (`c24564b983852848320eed8cd19cc02678ad781a821e6dff133489994c644f91`) and `rt.o` (`07123ecfab57014f9f227953c277fa53edca38c7c1e362ebf02ee5a44be62b84`) from the preserved prior runtime to the control's runtime directory. They are separate generated artifacts, not modifications of the788 authored/package source entries. Prior LLVM18 verification and nightly runtime provenance remain identified; no new runtime/compiler/tool/test invocation is claimed. `runtime/install.sh`/`cargo clean` were not run. Artifact/source binding is in `runtime-artifacts.json`, SHA `1c988abab61a4d531811245540a41c5cce017db012983cef420d8b3d61bc930f`.

## Commands ready for root allocation

`final-gates/preparation/gate-plan.json` is deliberately **PREPARATION_ONLY** with candidate source package null. It retains exact commands, role cwd/output prefixes, conditions,1800-second bounds and environment, and cannot be read as completed results. Root must bind the reviewed final candidate source/patch/configuration, verify fresh candidate/control dependency graphs agree under relocation, and reserve the slot first. Candidate and control run sequentially with fresh result prefixes.

For **each** source root (`combined-encoding` and `combined-encoding-control`):

```sh
make test
make nits
```

The official Makefile runs root then DAG `cargo insta test --release --unreferenced=reject`; nits runs Prettier, strict root/DAG Clippy and fmt. Preserve each official result, including nonzero status and full logs. If an aggregate exits before completing its DAG sub-gate, complete the remaining strict commands with cwd `ROLE_ROOT/dag_in_context`:

```sh
cargo insta test --release --unreferenced=reject
cargo clippy --tests -- -D warnings
cargo fmt --check
```

If root Clippy stopped nits before root formatting, additionally run `cargo fmt --check` from the role root. Do not repeat a successful full sub-suite automatically. Old observer canaries are recorded as optional existing5-root/10-DAG filters, only when full suites did not reach them or a new failure warrants focus; candidate-specific structural tests must use their actual registered names/counts and are not fabricated in the control.

Use `RUSTUP_TOOLCHAIN=1.91.0`, jobs4, test threads4, Rayon1, `RUST_LOG=error`, LLVM18 prefix `/opt/homebrew/opt/llvm@18`, `/opt/homebrew/lib`, and role-local `CARGO_TARGET_DIR=ROLE_ROOT/target`. Clear inherited wrappers/flags, encoded flags, incremental override, Insta update/force-pass and Make flags. The memory guard remains **unset**, never value0; no pressure gate/preflight is reintroduced. Record full effective env hashes plus explicit settings per command, source/lock/metadata/runtime/Tiger identities before/after, and actual selected counts. `dag_in_context/build.rs` emits Tiger under the role source root's target/PROFILE, so role-local targets preserve lookup. Cache cloning is deferred: only clone a compatible quiescent target into the private control target after owner terminal/slot allocation, never copy the worker's live target.

## Fresh failure attribution contract

The historical13 snapshot and3 lint sites are not waived. Archive the first official logs and pending actual snapshot files immediately, before any selected rerun can overwrite them; accepted snapshots remain untouched. For every recurring snapshot failure, use a freshly retained exact-name candidate/control trial, e.g. the explicit template `cargo test --locked --release --test files EXACT_TRIAL -- --exact --nocapture --test-threads 1`, and require exactly1 selected test. Bind the common input, harness, accepted golden, effective configuration/toolchain and both source/engine/dependency packages. Compare **complete actual snapshot bodies**, not only names/counts or presumed old status. Candidate/control root relocation is disclosed; no ad hoc content normalization creates equality. New or unmatched bodies remain unresolved failures.

For lint attribution, compare the fresh **strict** candidate/control root and DAG diagnostics at the actual lint/site with matching relevant source context. A warning category elsewhere in the baseline does not excuse newly added code. No lint allowance or automatic fix is planned/authorized. Official failed Make targets remain failed even if independent attribution later supports an inherited limitation. No snapshot acceptance, `test-clean`, `fixnits`, source/golden rewrite or unrelated repair is performed by this preparation. New failure-driven source edits require owner/root review and a new checkpoint.

The protected30,609-file before snapshot remains preserved at `provenance/protected-before.json`, SHA `6970a58f777afaf8ef1e18fc5e8b128c5b60b93818cf6fdde1c19578f02acd6f`, with its read-only final comparison tool. Control setup wrote only the new control tree and ignored new preparation files. There are no compiler gate outcomes, structural consumer results or performance numbers in this preparation.

## Preparation receipts

All paths below are relative to `benchmarks/local/eggcc-combined-encoding/final-gates/preparation/`; stdout/stderr and full per-command environment/terminal receipts are retained alongside the journal:

- `prepare-control.py`: `fdfaee12b354ddc0db902cfe2d1aea5a8d224b8e5a04a0cc9d85d4dbb1b6a189`
- `commands.json`: `d6ace99339baff87cfdd35fc299bb311fefda99bde04fe2e5293197dfd506d36`
- `control-source.json`: `1ba7cec15488284f396d57473b28a9d455bf490c5ec475580540dce0898d811e`
- `control-source.patch`: `73e93343ede42fde1b2a0f48e56060b5afbf6791e3f54fd1e142a3066d3f8c40`
- `metadata-root.stdout`: `48dc7d30dcef147984c6f320ae880b501232e0ab3e84474230884fd406577233`
- `metadata-dag.stdout`: `7501fa78f46a101925ad48167864699c3381350b98700865f0388b2bab41ff86`
- `runtime-artifacts.json`: `1c988abab61a4d531811245540a41c5cce017db012983cef420d8b3d61bc930f`
- `gate-plan.json`: `f96f368d91f9ed428221e793fe1c3f5d1fcf9edd03866b8080ac5c41235d023e`

Closed preparation UTC: 2026-10-18T05:12:49.950545+00:00. Waiting for root slot; no builds/tests/workloads, commits/pushes, proof/paper changes or shared STATUS edits.

## Tiger side-effect admission supplement

The compiler owner has now observed a real tooling-only failure: `target/release/tiger` was absent despite cached Cargo buildscript output. Before native final gates, **verify the actual executable exists at the selected lookup path and bind its bytes**; Cargo cache freshness/stdout is insufficient for an output emitted outside Cargo's tracked artifact set. Root's owner is repairing this with the actual retained buildscript and explicit manifestdir/PROFILE, without a source workaround; that failure/retry stays retained.

This preparation does not run that buildscript or copy its live output. After worker terminal and root slot allocation, either invoke the actual known buildscript in the control with captured environment/source/tool/flags or copy a compatible frozen terminal Tiger artifact. Require matching build.rs plus every Tiger C++/header input, actual binary hash/executable mode and role-local destination, alongside the already bound six runtime source inputs and rt.bc/rt.o. Check release for full `make test` and any other profile only if a later native canary uses it. This is an artifact-readiness requirement, not a new compiler-semantic claim or advance waiver of an official failure.

## Generated artifacts ready; official gates held for oracle checkpoint

At 2026-10-18T05:23:09.268266+00:00, the candidate target was terminal/quiescent and APFS-cloned into the private control target (`/bin/cp -cR candidate/target/. control/target`, exit0,2.726s). Both actual release Tiger executables are executable and match SHA `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`; build.rs and all Tiger source inputs match the exact pre-integration control. The six runtime inputs match, and the two pinned generated runtime artifacts were copied from prepared control into the previously absent candidate paths. Candidate794 and control788 source bytes are unchanged before/after, bound to oracle-final/source.json SHA `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`. Receipt: `generated-artifact-preparation/receipt.json`, SHA `083207dc38ce5a2f0f4ca58d8563e4f668281ffcf1685f85dd5b1f6a0fdb7409`.

No build/test/workload was run for this preparation. Root is routing the newly added independent Type-oracle test through its focused target; official gates remain held until terminal result and final checkpoint authorization. `final-gates/run-gate.py` is prepared only: shell-free per-command process-group timeout/captured stdout/stderr/env/source/artifact/snapshot receipts, with no source or snapshot writes. Its invocation itself is not a test/gate result.
