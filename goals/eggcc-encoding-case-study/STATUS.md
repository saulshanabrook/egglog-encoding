# EggCC encoding study status

Execution complete; root completion audit and final goal status are authoritative.

The study validates a small compiler-integrated load-elimination case using
immutable address keys and on-demand structural disequality. Query/manual give
the same checked program; query avoids six explicit pair rows. No new compiler
bug, production-workload improvement or stable timing/RSS advantage is claimed.

The [report](report.md) contains laws, rejected candidates, actual compiler
transformations, per-case observations and limits. [rerun.md](rerun.md) records
source patches, build/configuration boundaries and regeneration commands.
[completion-audit.json](completion-audit.json) maps every accepted fact.

## Final scoreboard

- Original semantic checkpoint: 16/16 expected NEE/EE outcomes; fail-fast extension: 14/14.
- Frozen compiler: 18 interpreted +18 emitted-program runs; all three passes,
  native Tiger and reconstruction; four focused tests and six CLI rejection checks.
- Fresh reproduction:four new emitted programs match previous bytes and retain
  correct load presence/absence; fresh interpreter receipts all return 17.
- Engine control: 48 complete invocations,40 measured rows.
- Feature controls: 144 complete invocations,120 measured rows.
- Fresh representative: 48 complete invocations,40 measured rows; wider timing
  variation retained separately. All three collectors' final verify commands pass.
- All figures/tables independently regenerate byte-identically; PDFs inspected.
- Encoding full make check passes (256 Python +1,797 Rust tests; optional plot
  test covered by separate pinned 24-test suite).
- EggCC root executions 31+1+2+2421 and standalone DAG 66 pass after runtime setup.
  Official make test retains 13 engine-only snapshot changes; official make nits
  retains baseline Rust 1.91 Clippy lints. No snapshots accepted or unrelated fixes.
- Preservation: 8,365 pre-existing file states and unrelated statuses/HEADs/branches
  unchanged;46 study source files match archived source checkpoints.

## Ownership and retained work

All three workers completed naturally and have no active compiler/build process.
Root owns synthesis/provenance. study_retarget owned the compiler, engine-only
control and native/runtime checks; study_semantics owned semantic fixtures and
scope review; study_harness owned the collector, independent review and figure QA.
No further task is pending in these domains.

Primary checkouts and original injectivity worktree remain preserved. Study source
is isolated in /Users/saul/p/wt/eggcc/encoding-study-retarget and
/Users/saul/p/wt/egglog-encoding/eggcc-study. The latter's 32 new files are staged as
a reviewed checkpoint; no study commit/push was made. Complete source patches,
frozen compiler/Tiger bytes, raw observations and receipts live under
/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/.

No paper edits, new proof support or Lean work were performed. A separate
standalone fallback was unnecessary because the actual compiler case succeeded.
