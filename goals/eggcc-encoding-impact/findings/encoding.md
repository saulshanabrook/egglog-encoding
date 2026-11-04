# Remaining-child reverse congruence: review checkpoint 1

The requested missing case is implemented in the isolated worktree `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding`, branch `codex/eggcc-impact-encoding`, based on `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`. Focused correctness evidence is green, independent review found no blockers, and full `make check` passed on the unchanged reviewed source in the second attempt below. This closes a defined encoding gap; it establishes neither an EggCC speedup nor a baseline compiler bug.

## Hypothesis and result

Hypothesis recorded before implementation: the existing query omits unmarked n-ary reverse congruence. A reverse implication guarded by equal siblings should recover the missing witness while preserving the marked-only forward rule and read-only storage contract.

The smallest test introduces different `Input` and `Output` sorts and an **unmarked** binary constructor `F`. From `disequal(F(A,B), F(A,C))`, it asks `known-disequal?(B,C)`. The pre-change source compiled and failed that check (one failed Rust test, exit 101). The helper encounters NEE first and stopped there; this red receipt does not independently establish an EE red. After the change the same test passes in both NEE and EE (one passed Rust test, exit 0).

The broader tests and independent finite oracle accept the proposed delta: newly supported reverse witnesses are observable, the negative cases stay unknown, and queries preserve rows/tables. One first-pass negative fixture used a nonexistent `(sort Opaque :no-union)` parser spelling. That attempt is retained as `focused-1`; the corrected fixture obtains an actual non-unionable equality sort from a relation declaration. Its successful checks are in `focused-2`. No parser failure is counted as a semantic negative control.

## Law and supported fragment

For a constructor `f` and a chosen position `i`:

```text
f(a0, ..., an-1) != f(b0, ..., bn-1)
and for every j != i, aj = bj
implies ai != bi.
```

If the focused arguments were also equal, ordinary congruence would equate the results, contradicting the parent disequality. This rule does **not** need injectivity. Unary reverse has no sibling premises. Forward inference from one unequal argument to unequal results, and cancellation from equal results to equal arguments, continue to require `:injective`.

The implemented reverse fragment includes constructor tables with a unionable equality-sort output and focused input. Every sibling must be a primitive or unionable equality sort. Existing canonical scalar values establish sibling equality. Custom function tables, containers and non-unionable siblings are excluded. User `:internal-hidden` constructors participate; private `@disequality-*` representation constructors do not, keeping this fragment independent of NEE/EE layout. Direct primitive query operands remain rejected and use native `!=` instead. Existing declaration restrictions and term/proof query rejection remain unchanged.

Unknown stays undefined. There is no constructor disjointness, inference from absent equality, or choice between two unresolved positions. In particular, the implementation does not simplify repeated disequality disjuncts: unequal `T(a,k,a)` and `T(b,k,b)` do not make this query infer `a != b` without another witness. Thus neither the implementation nor this evidence claims unrestricted congruence/disequality completeness.

## Source changes and storage/schedule contract

Five source files change:

- `egglog-experimental/src/disequality.rs`: reflect current eligible schemas; retain the marked-constructor set for forward inference; build a transient index of existing parent rows by typed child and position; enqueue a parent-result goal only for the same constructor/position with all sibling columns equal. The existing typed unordered visited-pair search terminates cycles. Existing assertion probes and contradiction normalization are unchanged.
- `egglog-experimental/tests/injectivity_disequality.rs`: add the minimal red/green case and scalar, excluded-fragment, scheduler, lifecycle and cyclic controls; update the prior unary-only expectation.
- `egglog-experimental/tests/injectivity_disequality/oracle.rs`: independent finite iterative closure model and all-pair comparisons.
- `egglog-experimental/README.md` and `egglog-experimental/tests/injectivity/injectivity-disequality.egg`: explain and demonstrate unmarked remaining-child inference and its limits.

No core API, persistent index, graph rows, parent applications, unions, materialized derived pair relation, or joint-closure facility is added. Subsumed rows are read. Query tests instantiate operands before taking storage counts, then check that row counts and function names stay unchanged. The implementation relies on existing committed-row/canonical-ID read APIs; it does not mutate the e-graph to complete a witness.

Queries inspect the committed graph. They do not run `injectivity`; consumers must be `:naive` and rerun after hidden parent assertions or sibling equalities change. The tested bounded protocol, for both NEE/EE and both core/extended schedulers, is:

1. A parent disequality with two unresolved positions leaves the focused child unknown; saturating the consumer does not produce its result.
2. Equal marked `Wrap` results do not make their children equal until `injectivity` runs. `check-contradiction` alone supplies neither that union nor the missing child witness.
3. A direct committed sibling union immediately enables a query.
4. `(run-schedule (saturate injectivity consume))` exposes the scheduled sibling equality and produces the consumer result.
5. A later parent assertion becomes visible after rerunning `consume`.
6. A final forbidden child union is detected by `check-contradiction`.

This is an executable pipeline order, not a general public joint-fixed-point guarantee.

## Verification

All commands ran from `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding` with:

```bash
export RUSTUP_TOOLCHAIN=1.91.0
export CARGO_BUILD_JOBS=4
export CARGO_TARGET_DIR=/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/target
```

The new target began as a clone-on-write copy of compatible build output from the injectivity worktree; compilation and tests subsequently wrote only the new target. Build/check elapsed times in receipts are diagnostics, not performance observations.

| Exact command | Result |
| --- | --- |
| `cargo test -p egglog-experimental --test injectivity_disequality unmarked_binary_reverse_congruence_is_cross_sort -- --exact --nocapture` before fix | 0 passed, 1 failed, exit 101, intended NEE check failure |
| Same command after fix | 1 passed, 0 failed, exit 0, NEE and EE inside test |
| `cargo test -p egglog-experimental --test injectivity_disequality --test injectivity --test disequality -- --nocapture` | 33 passed: query 18, injectivity 9, disequality 6; exit 0 |
| `cargo test -p egglog-experimental --test files injectivity` | 7 passed, 0 failed, 69 filtered; exit 0, including three proof-compatible injectivity fixtures |
| `target/debug/egglog-experimental --disequality-encoding nee egglog-experimental/tests/injectivity/injectivity-disequality.egg` | exit 0 |
| Same CLI command with `ee` | exit 0 |
| `rustfmt --edition 2024 egglog-experimental/src/disequality.rs egglog-experimental/tests/injectivity_disequality.rs egglog-experimental/tests/injectivity_disequality/oracle.rs` | exit 0 |
| `git diff --check` | exit 0 |

The 18 query tests include both assertion encodings; the scheduler test additionally runs both core and extended modes. The matrix covers unmarked unary/binary and each ternary position, mixed integer/bool/string siblings, unequal siblings, two unresolved children, differing constructor names, absent unmarked forward/cancellation, hidden constructors, excluded container/custom/non-unionable siblings, late unions and parent facts, scheduled injectivity, contradictions, subsumed/canonical rows, pop/redeclaration and failed declarations, unsupported direct query types and term/proof modes, witness-free cycles and cycles with finite witnesses, and no query storage growth.

The oracle fixes 22 named classes and 17 applications spanning unmarked binary/ternary/unary/mixed constructors and marked equality/native constructors. It uses two committed equality partitions (acyclic and cyclic), 16 seed subsets and two encodings: **64 graphs and 16,192 unordered pair queries including self-pairs**, of which 412 succeed and 15,780 remain undefined. It repeatedly applies the two supported laws to all application pairs until no facts change. It has no goal queue or parent index, and does not call the implementation to compute expected results. It holds equality fixed and does not model scheduled cancellation; the separate scheduler tests cover that boundary. All pair results agree and leave storage unchanged. This tests the stated finite fragment rather than proving a general theorem.

## Checkpoint, provenance and next review

Raw evidence is under `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/encoding/`:

- `initial.json`, `red-test.patch`, `red.{json,stdout,stderr}`: hypothesis, baseline hashes and failing minimal test.
- `green-minimal.*`, `focused-1.*`, `focused-2.*`, `files.*`, `cli-nee.*`, `cli-ee.*`: exact commands/environment, exits and outputs, including the corrected fixture attempt.
- `reviewable-1.patch`: full five-file checkpoint, including the new oracle; SHA-256 `b21d12ce1fd58453275d001609d12583439a295c8899d4ed058bd1ba070c1ee0`.
- `reviewable-1.json`: base/branch, all changed source hashes, patch hash, tested CLI hash and result counts.
- `bin/known-disequal-debug`: independent frozen bytes for the tested CLI, SHA-256 `c5d2b867415eb5d68cb0e84898bd596c68f255238a05b433fdc4d339b0bb1d4a`.

The five-file patch was submitted for independent correctness/scope review before further changes; review and coordinated gate results follow. This slice adds a full scan of eligible constructor rows and transient index allocation to every structural query that misses the assertion fast path; high-degree matching parents can also form large row cross-products. There is no cost or speedup claim. Measure actual consumers before changing this design or considering persistent indexes/API expansion. Previous frozen study artifacts and original source worktrees were not modified.

## Coordinated full gate, first attempt

Independent review found no blockers and confirmed all five checkpoint hashes. The first complete `make check` attempt used the same source/worktree/target and explicit environment above, plus `UV_PYTHON=/Users/saul/.local/share/uv/python/cpython-3.13-macos-aarch64-none/bin/python3.13`. Recorded versions are Rust/Cargo 1.91.0, uv 0.13.0 and CPython 3.13.11.

This attempt is **resource-failed, not green**. Lock/format/lint/mypy, Rust format, Clippy `--workspace --all-targets -- -D warnings`, and private workspace rustdoc link checks passed. Python passed 233 tests and two snapshots. Completed Rust result summaries account for 1,222 passes; the workspace run stopped while listing `egglog-bridge --lib` tests with `Os { code: 28, kind: StorageFull, message: "No space left on device" }`, followed by `make: *** [rust-test] Error 101`. An earlier LLVM output-stream StorageFull error is also retained. The volume was actually full (about 120 MiB available); no new-code semantic/lint fix or snapshot acceptance followed.

Raw `full-check/attempt-1.{stdout,stderr}` retain the complete emitted logs. The wrapper waited for make, then also hit Errno 28 when persisting its final receipt. Consequently make's exact child exit code was not retained: `attempt-1.json` records it as null, the wrapper exit as 1, the exact error evidence, and a recovered terminal resource-failure status. `attempt-1-counts.json` records completed-stage counts without treating the partial Rust run as a pass.

Once all build/test processes had exited, only this task's generated `target/doc` directory (80 MiB) was removed, using exact-path, non-symlink and generated-index preconditions, to recover enough room to write the terminal evidence. The initial force-style shell cleanup was automatically rejected; the path-checked Python cleanup succeeded. Original source/build trees and frozen evidence were untouched. All five source hashes still matched `reviewable-1.json`; the patch remained the reviewed checkpoint. The partial first run is not a successful final gate; retry results follow.

## Coordinated full gate, successful retry

The coordinator subsequently observed 9.2 GiB available. The cause of that broader capacity recovery is **not established** and is not attributed to the known 80-MiB generated-doc removal. No broad cleanup ran, compatible target output was retained, and an unrelated goal's active build was preserved. On this basis the exact `make check` command was retried in the same cwd with the same explicit Rust 1.91.0 / jobs4 / target / Python 3.13.11 selection. No source changed between attempts.

**Attempt 2 completed with make exit 0.** All nine emitted gate commands passed: uv lock, Python format/lint/mypy, Rust format, workspace/all-targets Clippy with denied warnings, private workspace rustdoc with denied warnings, Python tests and complete workspace Rust tests. Independently parsed result summaries record **233 Python tests and two snapshots passed; 1,804 Rust tests passed, zero failed, six ignored**, across 60 Rust result summaries including doc tests. There was no filtered Rust selection. The full run includes the E1 query/oracle tests and proof-compatible fixtures; no separate proof subset was rerun.

The retry stderr includes the earlier LLVM StorageFull text, but it is a replayed saved Cargo diagnostic rather than evidence of a new failing system call: the exact 65 bytes reside in `target/debug/.fingerprint/egg-math-benchmark-ed107198bb9d1c47/output-test-bin-egg-math-benchmark`, with an mtime during attempt 1. Cargo completed cached test compilation in 0.13 seconds without a Compiling line; a contemporaneous check showed 9.1 GiB available. The saved diagnostic copy, SHA-256, mtime and filesystem observation are retained as `full-check/attempt-2-replayed-diagnostic.txt` and `attempt-2-diagnostic.json`. No fresh StorageFull test/listing failure occurred, and every gate command plus make returned successfully. The first resource failure remains preserved and is not relabeled.

`full-check/attempt-2.{json,stdout,stderr}` retain exact command, environment, tool versions, before/after source hashes, explicit successful make return and full logs. `attempt-2-counts.json` contains every Rust result summary; `final-summary.json` records the independent counts, all gate statuses, log/build-input hashes and build-relevant environment. Elapsed times are diagnostic only and are not performance observations. All five final source hashes equal the independently reviewed `reviewable-1.json`; no code fix, snapshot acceptance, new patch delta, commit or push was needed. The stable patch remains SHA-256 `b21d12ce1fd58453275d001609d12583439a295c8899d4ed058bd1ba070c1ee0`.
