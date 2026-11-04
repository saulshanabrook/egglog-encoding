# Separate E1 retarget regression

This is excluded from the qualifying original-dependency Add/Sub finding. No snapshot is accepted, and byte-identical engine-only attribution is not a semantic approval.

The exact-current handoff-only compiler contains a0bb's original 771 source files with only the admitted four Cargo manifest/lock changes. It has neither observer plumbing nor the guarded interval repair. Its source manifest is `compiler/final-gates/handoff-control/source.json` SHA `b44148750755ecf1fd9bd43975496b333ca222c005a753afbd209525805c72af`; its fresh compiler SHA is `acc574c0d4bbe92a3e0651a91b9196fd1346e9ca8be777ea1a55c98344e6d60b`, with the admitted current-main Tiger SHA `130eaba8…` and original runtime artifacts.

All thirteen exact snapshot trials selected one test, exited101 on their snapshot assertion and reproduced the live candidate's pending bytes exactly. `compiler/final-gates/handoff-control/results.json` SHA `40c4a7ec6b2bf5c12e3774e6cef5efd6d62fe8ab30d24dc7dedc8fed0c183de5` binds those child exits and actual emitted bytes. This establishes that the E1/lock retarget package alone is sufficient for all thirteen deltas; the observer and arithmetic repair are unnecessary for them.

The `branch_hoisting` pending body is wrong for valid input n=1. The unchanged source loops y over 0 through 499 and last sets x to 2*y for n=0 or 3*y otherwise, so expected output is 998 or 1497. The original fixture SHA is `13e36dcdd09b50220448fe5dfd546e82413fbe2214bb56122f947f6290091493`; the independent n=1 fixture changes only its ARGS comment and has SHA `b1c42f534f47b90853bd8d3c5d5aa2eaa44c1221363897960086d30981affcd5`.

| Argument | Source interpretation | No-context optimized interpretation | Source O3_O3 native | Exact emitted O3_O3 native |
| --- | --- | --- | --- | --- |
| 0 | 998 | 998 | 998 | 998 |
| 1 | 1497 | 998 | 1497 | 998 |

All twelve commands exit0 without timeout. Each full optimization records passes0/1/2; the exact n=1 emission is byte-identical to the pending snapshot body except for its ARGS comment. Both source and emitted artifact are lowered without another EggCC optimization using the same O3_O3 backend/runtime, then directly executed with both arguments. Native executable hashes are `403a5be6a8c96ad0f2a3735ecc95efc8626732d1d6ca251094887918df0dc90e` (source) and `9f463a5d2001ca9d2f8b67233337563a92f6f93e65dd70fa73fe3f26eb8ce796` (emitted). Exact receipt/output authority is `compiler/final-gates/branch-hoisting/results.json` SHA `3287f42a9947db73b9f1be97c9e294913450706bd262b7bbfb4c49af603e582d`.

The current-main API does not authorize specialization to the ARGS comment. In the handoff-only source, `src/util.rs:303,318` parses ARGS into `ProgWithArguments.args`. `Run::optimize_bril` at431 accepts only a Program and configuration; `RunMode::Optimize` at725 passes those values, then separately carries the original arguments into its visualization. Interpretation uses the argument vector. `src/main.rs:96-99` documents no-context mode as disabling contextual matches, replacing body contexts with a dummy and skipping fundamentally contextual rules; it does not describe input specialization. The no-context datatest variant at `src/util.rs:534-537` inherits `Run::new`'s `InterpMode::None` at367-371. Therefore that particular snapshot trial never checks an interpreted result, including its declared n=0 input. The all-input failure is an actual separate regression, not a waived snapshot difference.

The E1 package cause has not been narrowed to a specific engine change. U0's full gates pass against their original snapshots; no new U0 branch-hoisting runtime result is claimed here. The separate [original-dependency repair-only validation](upstream-repair.md) is complete and preserves frozen U0 and B1 source, binaries and pending snapshots; this retarget regression is excluded from that repair and from the qualifying Add/Sub claim.
