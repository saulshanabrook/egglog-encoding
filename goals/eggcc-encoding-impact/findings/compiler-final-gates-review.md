# Final compiler gate and attribution review

**Consent for the bounded release/source-gate admission, with the documented official-gate exceptions; no blocker found.** Official `make test` and `make nits` remain failed. The exact terminal final-release matrix, ten repeats and source identity now support root binding the two prospective successful-cost studies while preserving those failures. Final manifest admission and an exclusive host window remain root-owned; this review launches no costs and does not make the full compiler gates green.

No project/helper import, build, test, compiler workload or timing ran in this review. I read source/receipts/logs and independently recomputed hashes, snapshot equality, source maps and counts using standard-library scripts. The one additional Git operation was read-only `git archive --format=tar 15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`, cwd `/Users/saul/p/wt/eggcc/encoding-impact`, held in memory for identity comparison. Only this findings file was written.

## Exact source boundary

All paths below are relative to raw `compiler/observations/corrected-control-1/`. First source/hash audit: **2026-10-17T22:48:32.996418+00:00**; final: **2026-10-17T22:55:49.712614+00:00**. All 788 declared live compiler files and five E1 source files matched at both checks. The unchanged seven-file harness and seven import/build boundary identities from `harness-final-gate/checkpoint-2.json` also matched at the final check.

- Pre-repair uncorrected inventory: `uncorrected-source.json`, `dd0b011fe3524b31de2789f931c521fe1abea9b63001d05aab7b7c8c3e0ea496`.
- New full inventory: `final-lint-source.json`, **`9ded5939ed0e0bbf5b5be4a69d9d5e8c094eb46259efce0d9cb93841621862f3`**; full patch **`db5eec0373d8a77a06356d3d064a17b449e83208baed3f416e463ea0970b66e6`**.
- Exactly one map entry changed: `dag_in_context/src/observations/tests.rs`, `271c694e1cd1999d9ab960f405b64b0fdec5a9b636e0ed577fd3378343d78874` → **`67074cfe369419fba1b9853c76130566a7305d90e7848aaa0b5ecfcd14fa16e1`**. The small `test-lint-fix-1/test-only.patch` hashes to `44faafb128b64250395e79b0bac8546342b92c477d1e68480686dbf69d70f8d2`.

The entire repair is `&[input.clone()]` → `std::slice::from_ref(&input)` at test line457. It retains the same borrowed one-element input value and all assertions. `observations.rs:856–857` includes that module only under `#[cfg(test)]`. There is no production Rust/egg, observer lifecycle/semantics, CLI/helper, input, expected snapshot, lock or E1 change. The original interval is restored at `ff363e2c10c57c2f3f79005d1f883f98091b3a32d023f43265b2ccbb89ce2647`. Four live Python helper hashes remain those consented by the final Python2 authority `91ba80ab…`.

## What the official targets establish

The actual `make test` receipt exits2, without timeout. Its root execution reports **36 unit tests and 2421 integration trials passed**, with two ignored doc tests. Cargo-insta then reports **13 snapshots to review** and returns failure before Make reaches the standalone DAG line. The passing Rust trial summaries do not mean those thirteen golden expectations matched. Generated `.snap.new` bytes were retained in `gate-snapshots/`; the 788 tracked/source identities, including stored expected snapshots, are unchanged. No snapshot was accepted.

The separately executed remaining DAG release suite passed **74/74, zero filtered**, both before and after the approved test-only repair. Post-repair focused observation tests passed **10/10** (64 filtered in that focused command). The prior root-focused test selected/passed five; it and the full root outcome were not unnecessarily rerun for a DAG-only cfg(test) borrow repair, as authorized. This distinction remains explicit rather than calling a new complete target green.

Official `make nits`, both before and after repair, exits2 on the unchanged root `unnecessary_unwrap` at `src/rvsdg/optimize_direct_jumps.rs:236`; it passes Prettier before stopping. Separate strict DAG Clippy exits101. Before repair it also identified the owned test clone warning. After repair, only the two unchanged DAG sites remain: `extractiongymfastergreedydag.rs:134` (`unnecessary_unwrap`) and `fastercbcextractor.rs:991` (`cloned_ref_to_slice_refs`).

Diagnostic root Clippy succeeds only with `-A clippy::unnecessary_unwrap`; diagnostic post-repair DAG Clippy succeeds only with the two explicitly named baseline categories allowed, while retaining `-D warnings`. Strict runs remain failed, and these altered commands are not official nits passes. The final strict DAG log has no owned observation-test clone warning, and the successful diagnostic pass covers compilation beyond the baseline blockers. Root format and post-repair DAG format checks exit0. No unrelated lint fix or snapshot update was introduced.

## Independent matched snapshot/lint controls

I audited `fresh-engine-control/attempt-2/results.json`, **`241c479424a8e12d948b3b2b599df7c2fd3cec5325887ea385b1a30ee745d7d9`**, its actual controller `cd6e3df0701a7722be3021db67196cfd045a00db150cffd9f0a5b8bd3e3f4cd0`, every selected command receipt/stdout/stderr and both candidate bytes, rather than trusting `status=matched`.

The base Git archive hashes to `f0dbec7788aef03c1dbe587aa3b835c6029e89b4307799baef760b02f2e95c90`; all 762 base entries exactly match the declared base map. All 762 prepared control files match their recorded hashes. Its only source changes from base are the four Cargo manifest/lock files. Both locks are byte-identical to the primary current E1 graphs; manifests are byte-identical to the primary plus only explicit root/DAG `[workspace]` boundaries required by the raw directory's enclosing workspace. Both root and standalone DAG resolve the same absolute E1 `egglog-experimental` path. The control has no observer source/rule edits, and input, `tests/files.rs` and expected snapshots are identical to the primary for each trial.

All thirteen actual commands are `cargo test --locked --release --test files -- --exact TRIAL`, each under Rust1.91/Rayon1, with **exactly one selected, one failed snapshot, exit101 and no timeout**. Each retained log identifies its trial and newly written candidate. The exact official pending set, retained snapshot index and thirteen control rows agree. I recomputed all full candidate hashes and bodies: **all thirteen control `.snap.new` files equal the primary retained files byte-for-byte, including their bodies**.

| Workload | Matched exact snapshot variants |
| --- | --- |
| `branch_duplicate_work` | optimize, sequential |
| `branch_hoisting` | no-context |
| `if_invariant_do_pull_out` | optimize, sequential |
| `if_invariant_dont_pull_out` | sequential |
| `loop_strength_reduction` | optimize |
| `loop_with_mul_by_inv` | optimize |
| `pull_out_small` | optimize, sequential |
| `strong_loop` | optimize, no-context, sequential |

I checked retained actual test binary `8594a3b5f96fc038742b0eeb208a0b8a8402382ad86ae9f27d16e27f45cca795` and Tiger `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`; the native lookup boundary uses the control manifest-root Tiger after checking no sibling Tiger exists at the primary test-binary location. The reused runtime bytes match the documented source-compatible rt.bc/rt.o authority; reuse is not relabeled as a newly successful `make runtime`.

Fresh strict root and DAG lint controls also exit101 at the same three sites, with byte-identical source files and the same two lint categories. This is fresh matched current-E1 evidence, not reliance on the historical pre-E1 engine. The earlier failed control attempt remains retained (`FileNotFoundError`); it is not treated as a successful comparison.

These comparisons justify attributing the pending snapshots/lints outside the observer delta **under this matched harness configuration**. They do not establish why every golden differs, prove either optimizer correct, isolate an E1 contribution, or show pre-E1/upstream-main passes. The integration harness explicitly uses `non_weakly_linear=false` (`tests/files.rs:61`, `Run::test_eggcc_config`); production CLI/defaulttrue requires its own actual final endpoint matrix. No cfg(test) suite is being substituted for that matrix.

## Frozen endpoint identity and remaining admission

The now-terminal restored release build (`cargo build --locked --release --bin eggcc`) and freeze receipts exit0. I independently hashed final/earlier original and corrected binaries, Tigers, source manifests and patches. `final-release/manifest.json` hashes to **`ff017790bf298fd56213f56759b8372cd6d74bb12457a747f088c03670f9fef2`**; its source manifest is **`5cddb863fa1a242fd028051400fb9a58c54ff33c876fe74a678e29fee020c6a3`**, with the same 788 map as the reviewed final-lint inventory. Final original compiler **`5d980389feec6270146db9a2cfe4e1775974102ab6c50cdf7bad029471907af1`** and Tiger `bd53d371…` are byte-identical to the accepted pre-repair original endpoint. Its sole source difference is the cfg(test) borrow line.

The frozen corrected compiler **`f44edb3cb9c4b9660524335a29bea536571fe2ddbd1bcc68ba589decbd9bcc15`**, source manifest `8748805409bdc89ae7d529521140aacadb85483ffb421b957d82b3a8de0fbc22` and pre-repair test inventory remain immutable. Corrected versus pre-repair original maps differ only in the interval file; corrected versus final original maps differ in that interval plus the explicit test-only borrow line. Do not retroactively claim the corrected endpoint used the new test source or passed the deliberately incompatible ordinary bug-witness full suite.

Twenty-four initially inspected source-check wrappers' command-receipt hashes matched; their before/after restoration records, the current full map and the final build agree. The later terminal index and final diagnostics below also match. Source/package bytes are stable at this review boundary. Official target failures and their exact matched attribution must travel with bounded acceptance. Root may now bind final endpoint/control/gate artifacts in the prospective studies; final manifests and host admission remain separate. No performance result, production fix or all-input correctness claim follows from this review.

## Terminal endpoint and diagnostic admission audit

The subsequently supplied **`final-summary.json` SHA256 `a9a32c2d100c406fcb148ea9226c726b2d9d37e180f207f1f8ecdc85c76fa5ce`** closes the previously pending endpoint boundary. I verified all 33 artifact-index hashes. `final-command-index.json`, SHA256 **`2dd04ee19c7b2e431435ceeeac4399ef63906b83aec104884defea1f758634a2`**, contains 132 distinct command receipts: all 132 actual JSON hashes, argv/cwd/status/timeout fields and 264 retained stdout/stderr hashes match. Expected original-red oracle exits, official failures and the failed first fresh-control setup remain present; no generic nonzero exit is counted as a successful detector.

The final **37-row matrix**, `final-release/results.json` SHA256 **`6002863600cf5295fc34285b9fe5e017826859f0acb8dac9659670459bd41bcd`**, has exactly seven parse/source oracles, 28 ordinary four-mode cases and two separately flagged pre-pass probes. Independent receipt checks give seven source-oracle successes, 24 complete native round trips, three exact observer rejections and three before-seeding unsupported-domain rejections. Actual binary, input hashes, flags, modes, interpretation fields, logs and native artifact counts agree. All successful optimized cases have pass order 0/1/2 and three Tiger egraphs; each rejection has first-pass logs only, no Tiger egraph or normal receipt. I checked enabled original/archived full-tree hashes, actual captured PID/full-stderr locator agreement, mandatory replay files, complete-pass stages and exact pre-serialization rejection/no-serialization boundaries.

MAX Off/CommonSeed still have non-null source `true\n` and result `false\n`. CommonSeed's first committed receipt contains the known conflict while its no-audit configuration accepts and proceeds: that preserves the intentional bad-merge control, not a conflict-free success. Manual/Injective reject the exact `(ObservationConflict 5 2 1 true false)` before serialization/Tiger. The final x=1 Off/Manual/Injective receipts are all `false\n`/`false\n`; both checker arms complete all three native passes. Across CommonSeed/Manual/Injective, each x=1 pass has two identical point records, six identical logical seed records, two supported Bool observations and the same skipped unselected region with zero observations. Only `mode` and the declared `literal_injective` metadata differ (false/false/true). This is nonzero matched coverage while retaining the intended representation difference.

The final **ten repeats**, `final-release-repeated/results.json` SHA256 **`aa6c916fb7e8b0918950706fa8c1742bea3521a1ac641c83c0d937554f0a09c8`**, contain five independently checked identical-argv pairs and ten unique persistent children. Six x=1 captures succeed with exact false/false; four MAX Manual/Injective captures retain the named rejection. Original and archived tree/normal-copy hashes agree, and each first capture's immutable locator/tree/normal-copy binding equals its revalidated binding after the second shared normal-receipt overwrite. Driver/helper hashes are the final consented Python2 bytes. These are interpreted diagnostic invocations, not a measured cost cohort.

For the separately frozen corrected package I also read the four original-red and four corrected-green actual command/normal/native receipts: unchanged driver/helper/MAX input, original Off/CommonSeed true→false with three passes and named checker rejection; corrected **all four modes exit0 with true/true and three native egraphs/passes**. Its 24 nearby-control receipts contain 21 full native non-null output matches and three explicit unsupported-before-seeding rejections. These checks support the proposed corrected-MAX successful-control case without asserting a general arithmetic fix or rewriting its pre-repair cfg(test) inventory.

`final-quiescence.json`, SHA256 **`9e6a115f67ab593baa4f0a5eb04fdf96fed29c75351f9fbcf9df5ac6e1225e83`**, retains the owner's check at **2026-10-17T22:50:10.322959+00:00**: no active owned/external compiler-native process, all known sessions terminal, restored 788-file audit and no performance collection. The earlier unrelated Cargo observation is explicitly retained in `final-report-attempt-1.json`; it ended before the final report. I read these receipts rather than claiming a new process survey or reserved cost window. Root must still recheck and reserve the host before sampling.

## Reviewed command receipt identities

All command cwd values are the new compiler worktree; common recorded environment is Rust1.91, the same compiler `CARGO_TARGET_DIR`, jobs4/testthreads4/Rayon1 and LLVM18. No timeout occurred in these rows. Exact argv/env/logs remain adjacent to each receipt. The table records actual exit status, including failures.

| Receipt basename | Exit | SHA-256 |
| --- | ---: | --- |
| `official-make-test` | 2 | `86017f2b6f5ff7ef90ceceb82ea57a928c2ef083b85ba62e5c5a2e667afc99de` |
| `official-make-nits` | 2 | `003ed359c1818d63374d165fd71be1fbf70cae726439c528ba0dc30f41e34962` |
| `post-fix-official-make-nits` | 2 | `c9d28e888d3418f05c5055c00c7aaa6f67538240c35d706d3371c4637b0bf242` |
| `post-fix-dag-observations` | 0 | `d661631437495583ee05b34925e204d77b33c445589f5cf98008da40d5131f9b` |
| `post-fix-full-dag-release-suite` | 0 | `8d4e12c19e20b03e95e0dfc2c9044d519e265ad54944de9ea2747c4883a8e7f9` |
| `post-fix-strict-dag-clippy` | 101 | `030d01640d32bcd0281d19b94d68ca62ad496e816f1ce127b0231cb8a1d6b75b` |
| `post-fix-diagnostic-dag-clippy-baseline-only-allows` | 0 | `8c954b253c4a41ac381cdcb98d7c7eaf9cde47c8984521d9218f209be9800755` |
| `diagnostic-root-clippy-known-lint-allow` | 0 | `2194f4acb461e09c2291df8de1ab176e66da44843a864c191d907119b4c117b0` |
| `remaining-root-format` | 0 | `9358be04811212ddb54363d01cc0cdbea55fe97821c1d7a4436eca69ad1319f8` |
| `post-fix-dag-format` | 0 | `cdb87df13e1266b2a118e3d1a1d637ef1f240148c63b2cf125de88ba469774be` |
| `focused-root-observations` | 0 | `4569d683e32f00823ddc8345faf57cde4366ffa9a63a3ce835bfbc042cf59be7` |
| `final-restored-release-build` | 0 | `6a8e894a86467f13bb2e65ebff35b55a619bc0c85998febc160b276bb3e0e17c` |
