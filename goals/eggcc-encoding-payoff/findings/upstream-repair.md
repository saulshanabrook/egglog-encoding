# Original-dependency compiler repair

The final compiler-fix candidate uses current main `a0bbec127f83249074a46af3fd6f6126c90fe0fb` and its original declared dependencies. Only two source paths differ: `dag_in_context/src/interval_analysis.egg` contains the reviewed guarded Add/Sub transfer repair, and `dag_in_context/src/interval_analysis.rs` adds its direct interval tests. No observer, E1 path, manifest/lock change or new fixture is part of this compiler source.

The isolated source is `/private/tmp/eggcc-payoff-upstream-repair`. Durable source and patch authority is under `benchmarks/local/eggcc-encoding-payoff/compiler/final-gates/upstream-repair/`:

- `source.json`: 771-file manifest SHA `d8361035101161e02b8ec30b2c7e4b02d483b6af2169c0d492e326250e87df93`, with complete `source.tar` and original source authority.
- `guarded-interval-repair.patch`: exact reviewed arithmetic patch SHA `819ece07070d55edef942c1d8e14af02770d3a29ad98a5f72ca0d6ff4b838e74`; repaired `.egg` SHA remains `ba4180adf9c460c061d4207124ed808810f4dcb91cc0dcccd021c46d2ab1c3a7`.
- `interval-test-only.patch`: SHA `ca2937b46267b14f0d1f7f5578a0b533772c161334f23c3c3c5727beda0fe714`. The new tests preserve eight safe bounded transfers and decline fifteen missing, wrapping, empty, Dead, BoolB or unresolved mixed-kind cases without producing result bounds or panicking.
- `final.patch`: complete two-file diff SHA `ff79254209de544a05f80171b2c1ef84e22c5cb3ae550c7d4071139d1361a6be`.

Both operand intervals must have all four numeric endpoints and be nonempty. Globally defined clamped threshold comparisons prove the entire Add/Sub rectangle does not wrap before either output endpoint is set. Both bounds come from that same eligible tuple. Unknown opposite endpoints conservatively decline. The repair changes no later interval rule, including the previously known Mul rules; it makes no general compiler-soundness or performance claim.

## Interpreter and native validation

Focused interval tests pass 15/15 with nonzero discovery, including all new direct boundary rows. The release build succeeds. Frozen compiler SHA is `7f25894ad0e5f1aa9987326dda52fc4275bde0374f448d0e422768c7c4fd8349`; Tiger SHA is `130eaba8bb575e196b8e18898826356269efe6e28a56b9d3690ef42647d3b201`. Runtime artifacts remain the admitted `c24564b9…` and `07123ecf…` bytes. The build receipt binds these to the original-dependency two-file source.

The exact twelve-case independent oracle SHA remains `0bd80e89973c34b067cf014501dd2b0efb7397bdeafce4bfa609ce09710b5a6f`. All 96 matrix commands exit0 without timeout. Source and optimized interpretation agree with the oracle; each exact emitted program is separately reinterpreted, lowered without another EggCC optimization using the matched O3_O3 backend/runtime, and directly executed with the declared argument. All twelve source-native and twelve exact-emitted-native outputs match, including four explicit empty outputs. All 24 full optimizer invocations record passes0/1/2. Both endpoint cases now produce true; all ten nearby/skipped controls retain their expected behavior.

Matrix authority is `matrix-results.json` SHA `6bfccbe483405a8e27bc50a7a242d4a6eaff401c17099c32808d1dc9f40b9bc3`. This independently validates the repair with original dependencies; it does not depend on E1's retargeted optimization behavior.

## Official gates

Official `make test` exits0: 31 root unit tests, 2,421 integration cases and 66 DAG tests pass, for 2,518 registered passes and no failures. Two doc tests are ignored. There are zero pending and zero unreferenced snapshots; no snapshot is accepted. This is two more passing tests than fresh original U0, corresponding to the new interval test functions.

Official `make nits` remains failed, exit2, at the same root Clippy site as fresh U0. Only unreached strict components are run separately: root formatting passes, strict DAG Clippy exits101 at U0's same two sites, and DAG formatting passes. Prettier passes. All three source hashes match fresh U0 exactly:

| Fresh baseline diagnostic | Source |
| --- | --- |
| `unnecessary_unwrap` | `src/rvsdg/optimize_direct_jumps.rs:236` |
| `unnecessary_unwrap` | `dag_in_context/src/extractiongymfastergreedydag.rs:134` |
| `cloned_ref_to_slice_refs` | `dag_in_context/src/fastercbcextractor.rs:991` |

No baseline site is changed or waived. No candidate-only diagnostic or snapshot change appears. Exact terminal receipt hashes are:

| Command | Exit | Receipt SHA-256 |
| --- | --- | --- |
| Focused interval tests | 0 | `c036c4d5b0290222434d46c34a6ce57d356cdc2503b2108d1ca82a0d487635ab` |
| Release build | 0 | `2ffdc19d16103031ccc650189b1356c35bbe255f1f14a8bbfc7df6f6482dc05c` |
| `make test` | 0 | `24c85de8de569309249a9b10ee085119e0df1a567983e95ce22884938dfea15f` |
| `make nits` | 2 | `b5bc930d496f1d6338db6a859743d1a0d81affe779cebcfe45fa640b3968145f` |
| Root `cargo fmt --check` | 0 | `0a4984fcd5069248893c0491accba28430e9d180f84051e552f7c3c4005f3920` |
| DAG strict Clippy | 101 | `7ba6d87e9c0aff863fbd5fcc4e12aa5068b3c898dddeabd8d345785e313c3ffd` |
| DAG `cargo fmt --check` | 0 | `6d2deb1a6a7ea0e3f1c90ee302d80e5bae20fff7ab7a790c66f5dbc7e15a1c92` |

## Terminal protection and limits

All 103 captured commands are terminal: 101 exit0 and exactly two fail strict checks at fresh U0's unchanged lint sites. The memory guard is unset; inherited wrappers, Rust flags, Insta acceptance/force settings and Make overrides are cleared. Rust1.91, jobs4, test threads4, Rayon1, LLVM18 and the private target are recorded in every receipt. No source or expected snapshot changes during validation.

The final audit rechecks the exact two-file source, all original manifests/locks, frozen compiler/Tiger/runtime bytes, original U0's admitted pair/runtime, B1's unchanged 790 source files and thirteen pending outputs, E1's unchanged 969 source files, and all 1,467 previously frozen corrected experiment artifacts. All 103 captured child PIDs and process groups are absent. The initial sandbox denied the read-only `ps` audit; its approved escalation then verified absence. That audit limitation affects no compiler/test command. Workspace-wide protection of older studies remains owned by root/harness.

Final `summary.json` SHA is `c8ab2b8ea67e41ebce45a244521e48883cf090a8fb81fb8508056a88e5f847fe`; `source-protection-after.json` SHA is `ee9779a229bacc753b33960173e98b72d4190e1fcbd5893021a464e4db5878d1`. Final `checkpoint.json` SHA `6e165adb98453da8cb84f271bf641ddc65046bc7fb2fcbd992c0784d14516d04` freezes 797 files. The broad-command slot is released.

The earlier E1-retargeted B1 full-test gate and its thirteen pending snapshots remain preserved, with an explicitly missing initial Make child-exit receipt. Fresh handoff-only trials attribute all thirteen differences to E1/lock state, and [the branch-hoisting finding](branch-retarget.md) records an actual separate wrong-output regression. None is accepted or counted as a qualifying original-dependency Add/Sub discovery. This clean final repair route contains no E1 or observer integration. No commit, push, proof, paper or timing claim is made.
