# Ackermann Statewalk capture audit

Read-only audit of the saved successful `eggcc-ackermann--statewalk` attempt on 2026-09-25. No native compiler, extractor, replay engine, or device was run during this audit. No capture implementation or live evidence was changed. The accompanying `ACKERMANN-CAPTURE-AUDIT.json` records the independently recomputed hashes and session summary.

**Conclusion:** no incomplete-parent or manufactured-output admission found in this case. The saved evidence represents the entire selected source optimization: three native optimization passes, each followed by Tiger extraction and a fresh Egglog reconstruction graph, with both `main` and `ack` present throughout. Six standalone workloads are independently validated; this is one source program, not six benchmark programs.

## Retained parent and boundaries

The index entry points to complete identity `6e330cb5a227ae3c7342813ced57ad2beaa15dda2351c714b7859df0cbbcbdbd` and validation identity `7bf72847e5d1f3a50a9d6a705b85ad6d65fccf8fdb84a224b4bc0bdb9965b102`. The capture is under `benchmarks/local/reproduction/stages/eggcc-ackermann--statewalk/complete/<identity>/attempt-0001/capture/eggcc-ackermann--statewalk/`; the coordinator validation has its own immutable stage.

The native command invokes the prepared Eggcc binary on the original `benchmarks/passing/bril/core/ackermann.bril` with only `--run-mode optimize`. There is no pass cutoff, function restriction, interpreter, or target execution. Native completion returned exit 0 in 3.589 seconds. The terminal `parent-complete` event retains actual optimized Bril; `native-output-000.txt` equals `native.stdout.log` except the stdout trailing newline. Its SHA-256 is `babc50d9d6aa715af48f72331f06ac951947c6ccb5c8783847396ce8ef1d6c1b`.

The 16 ordered native events comprise three complete five-event groups, then parent completion. Every optimization start records expected passes = cutoff = 3; every pass completion records successful native typechecking. Materialization records expected = actual = 6 and terminal complete = true.

| Pass | Optimization events | Reconstruction events | Tiger selected nodes, main / ack |
|---|---|---|---|
| 0 | 0, 1, 4 | 1, 2, 3 | 20 / 104 |
| 1 | 5, 6, 9 | 6, 7, 8 | 20 / 104 |
| 2 | 10, 11, 14 | 11, 12, 13 | 195 / 276 |

The instrumented prepared source confirms these are actual native graph boundaries: `dag_in_context/src/lib.rs:941` iterates the full schedule, `:972` builds the next invocation from `res`, `:986` creates a fresh optimization graph, `:1017` invokes the real extractor, and `:1030` assigns its typechecked result back to `res`. `:772` captures actual Tiger output, `:777` creates the separate reconstruction graph, and `:784` performs normal reconstruction and argument-type repair. The hook logs reconstructed terms before argument-type repair; the next pass captures the actual resulting source program. It does not substitute a replay-generated result into this native feedback path. `src/main.rs:177` records parent completion only after `run.run()` returns; native `src/util.rs:725` implements optimize through final Bril reconstruction.

Tiger arguments are `--ilp-solver gurobi` in all three events, without `--ilp-mode`: this is the default Statewalk path, not evidence that licensed Gurobi extraction ran. The pinned compiler revision is `16be0063133ef0b8ba21cd75ee377002dc3ecbed`; exact source/binary/engine hashes are in the JSON.

## Roots and standalone checks

I regenerated all six session descriptions, standalone file bytes, and output contracts directly from the retained events and current adapter. All matched byte-for-byte. I also verified all 64 artifact hashes in the saved capture and validation stages, plus the live native source, native executable and replay engine hashes.

Each optimization session contains the entire native optimization program and two appended `check` commands. The checks bind original seed Function roots to actual selected original graph nodes. Every retained Tiger child is checked against its original eclass; omitted type/context fields are recovered from that selected original node. Request multiplicity is preserved, and the actual graph's two Function requests match the two retained selections in all three passes (`scripts/eggcc_churchroad_complete.py:471`). The adapter only applies its declared compatibility conversion: removes an unreferenced ExprSet helper block and changes six deterministic no-merge helpers to merge-old; schedules remain in place (`scripts/suite_capture_eggcc_churchroad.py:282`).

Each reconstruction replay is the actual Tiger-produced fresh-graph initialization followed by two query-only checks of the actual host-returned Function terms. The Tiger initialization legitimately creates a new graph because the native compiler does the same. It is not inserted into the preceding optimization graph as an assumed equality. The six added suffixes contain only `check` commands; none contains a generated `let`, `union`, `set`, or insertion action. No replay has an `extract`, `prove`, or `prove-extract` request. Optimization checks are at command positions 998 and 999; reconstruction checks at 30 and 31. Exact tokens, ordering and preceding-state hashes are retained and rechecked by `native_check_contract` (`scripts/hardboiled_replay.py:48`).

All six coordinator executions succeeded on the retained engine (`7eb04703af3707fb60c1ebe8cef66a86f72de1dc55081c636b8ea38fe06229b2`), with empty output as expected for query-only workloads. They establish that the recorded native selections are represented and equal to their source roots in the replayed graph. They do **not** independently prove Tiger's optimality, linearity constraints, source-language equivalence, argument-type-repair semantics, or device behavior. Each contract explicitly records `claims_optimality: false`; `proof_validation` remains `not-run`.

## Duplicate ordinary validation

The current adapter first executes every replay using `--mode no-messages -j 1` (`scripts/suite_capture_eggcc_churchroad.py:755`), then coordinator `validate_capture` executes the same bytes again with `-j 1` (`scripts/reproduction_validation.py:230`). `NoMessages` only suppresses returned messages (`egglog/src/cli.rs:336`); it does not skip schedules or checks. Ackermann therefore incurred 12 replay processes for six sessions: adapter 1.122 seconds, coordinator 1.105 seconds, excluding orchestration overhead.

The coordinator layer additionally verifies terminal source/materialization status, session byte identity, exact ordered check/prefix contracts, and response counts. Those checks should remain. A narrow implementation is authorized separately: give the adapter a default-on `validate_ordinary` option, have the coordinator dispatcher opt out, retain completed materialization as `ordinary-validation-pending` with no admitted workloads, and let the stronger coordinator validator perform the sole execution. Direct adapter CLI behavior stays unchanged. No receipt reuse or weaker admission gate is needed.
