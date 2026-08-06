# Review: "Merge-First Standalone DuckDB SQL Compiler" plan

Reviewed: 2026-08-05. Subject: the `<proposed_plan>` posted 2026-08-05 01:17 in
codex thread `019f85eb…` (saved copy of the plan text was reviewed verbatim).
Verification: two read-only agents (repo premises, engine claims) plus direct
workload inspection; empirical probes on DuckDB v1.5.5 CLI; GitHub issue and
release checks.

## Verdict

**No blocker. The plan is sound to move forward** once four amendments are
folded in. Every load-bearing premise checked out; the amendments are
implementation-contract fixes, not architecture changes.

## Premises verified (all green)

- `origin/main` = `6ef88f1` (2026-08-04 17:33, "Remove containers from Eggcc");
  merge-base `853fbfd` correct; divergence 129 commits vs 15.
- Overlap between `37fc161` and origin/main is **exactly the twelve files** the
  plan names; `git merge-tree` is conflict-free — but only *textually*:
  `RuleBodyCall` gained the `IndexTable` variant on main while the branch edits
  `backend_impl.rs`, `dd/src/{lib,interpret}.rs`, `egglog/src/lib.rs` — files
  that must exhaustively match on that enum. Compile breakage is guaranteed,
  which validates the plan's merge+IndexTable-as-one-slice decision.
- IndexTable IR confirmed (`egglog-backend-trait/src/lib.rs:157`,
  `{id, any_of, read}`; probe-not-scan semantics; `TypeError::IndexValueUnbound`
  guard). Generated rebuild shape matches the review's claim exactly:
  `Table(All) + IndexTable(All) + != + Lets + Delete → Set` via
  `:internal-include-subsumed` (`proof_encoding.md:248-285`,
  `proof_encoding_rebuild.rs`). `index_any.egg`/`index_probe.egg` + snapshots exist.
- Current-main `eggcc-2mm-pass1.egg` (4,518 lines): **zero containers** (all five
  sorts are ordinary datatypes now), four constructor-valued merges
  (`Smaller`, `bound-max`/`bound-min`, `IVTMin`), six `unstable-fresh!` uses,
  ~25 `panic` rules. Plan's characterization exact.
- Rustdoc gate real: `rust-doc-links` (`cargo doc --workspace
  --document-private-items` with `-D warnings`) wired into `rust-nits`;
  Makefile is also the most-restructured overlapping file (`nightly-*` split).
- All corpus files exist on origin/main, including Pointer's fact directory
  and `egglog/tests/web-demo/eqsat-basic.egg`.
- CLI incantation `duckdb -safe -no-init -batch -bail -json :memory: -f prog.sql`
  works **verbatim** on 1.5.5: all flags exist (it is exactly `-no-init`); `-f`
  is exempt from safe-mode file restrictions while SQL-level `read_csv`/`COPY`
  correctly fail; `error()` + `-bail` → exit 1, later statements never run, and
  stdout retains the complete well-formed JSON arrays of every prior statement
  (clean prefix-comparison for oracles).
- Official v1.5.4 CLI binaries exist (`duckdb_cli-osx-arm64.zip` on the GitHub
  release) — exact-1.5.4 acceptance is procurable.
- UNION type cap is **exactly 256 members** (bind error at 257) — the plan's
  census-and-nest requirement is correctly calibrated.
- Issue #13974 (multiple working-table references in a recursive branch):
  real, **closed as not-planned**, and reproduces on 1.5.5 — silently drops
  rows, exit 0. Issue #23677 (`top_n_window_elimination` dropping NULL-keyed
  rows under ROW_NUMBER + top-N): real, **still live on 1.5.5**, reproduced.

## Required amendments (would break as written)

1. **Large-N `Repeat` must not unroll textually.** Pointer's schedule is
   `(run 100000)` (`pointer-analysis-small.egg:204`). "Repeat N emits the
   source-specified number of guarded attempts" is fine for eggcc's
   `repeat 3`/`repeat 5` but produces a gigabyte artifact for Pointer. Large-N
   Repeat must lower like `Saturate` — a recursive controller with a loop-frame
   counter in state, exiting early on `can_stop` — which the plan's own
   schedule-CFG state machine (PC + nested loop frames + counters) already
   supports. Add an explicit unroll-vs-loop threshold.
2. **`print-size`/`print-stats` must be named in-scope.** Math ends with
   `(print-size Add)`, `(print-size)`, `(print-stats)`; Pointer has two
   `print-size` calls. A literal "reject extraction/output at preflight" fails
   two of the four blocking workloads. Lower `print-size` as `SELECT count(*)`
   rows in the JSON output (and `print-stats` as a stats row), or explicitly
   strip them under the benchmark treatment. Related correction: the plan says
   Math "has no source check" — it has one
   (`(check (= (Pow (Var "x") (Const 2)) (Mul (Var "x") (Var "x"))))`, line 68),
   which is favorable (one more oracle) but the census should be fixed.
3. **`-safe` locks *all* `SET` configuration — add two structural compiler
   obligations.** Under `-safe`, every `SET` fails ("configuration has been
   locked"). This is consistent with the plan's "no SET statements", but it
   removes the only workaround for #23677 and makes `max_expression_depth`
   unraisable. Therefore the compiler must guarantee, and lint for:
   (a) **no nullable ORDER BY key** in any ROW_NUMBER/QUALIFY/top-N pattern
   (coalesce to a total-order sentinel) — the optimizer bug otherwise silently
   drops rows; (b) **operator nesting stays well under ~990** (default depth
   limit 1000 minus internal overhead; parsing is superlinear past ~1200 even
   unlocked — deep nesting is not an escape hatch). Flatten generated merge
   expression trees via CTE chains.
4. **The one-working-table-reference-per-branch rule must be compiler-enforced.**
   #13974 violations produce *silently wrong results with exit 0* and DuckDB has
   closed the issue as not-planned — the engine will never diagnose it. The
   plan states the rule; it must be an emitted-SQL lint, not a convention.

## Accepted risks (no action needed, monitor at the stated gates)

- Merge slice is guaranteed to open with compile errors (non-exhaustive
  matches) and a never-run rustdoc lane — the plan's gate-both-parents,
  one-slice, abort-on-double-failure discipline covers it.
- eqsat-basic's 110s hard gate: strongly favorable evidence (1.0s standalone
  replay of the 5,795-statement trace; 0.19s recursive-CTE prototype).
- Luminal's outermost `saturate` tower spans nearly the whole program → its
  recursive region will be very large (~1ms/branch planning, full-branch
  evaluation per iteration). Under the plan's own rules a timeout is
  `timeout_censored` after static lowering + reduced canary pass, so this
  risks coverage, not completion.
- `:memory:` + `-bail` means no post-mortem DB. The verified well-formed JSON
  prefix on stdout is the observable for "earlier committed commands retained";
  acceptance tests should compare that prefix.
- "No compiler-invented fuel limit" is a clean policy; a missed no-op guard
  means an in-statement infinite loop caught only by the external 110s
  watchdog. The capability canaries (unchanged-replacement recursion) are the
  real defense — keep them blocking.
