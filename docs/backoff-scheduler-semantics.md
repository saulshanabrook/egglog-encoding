# Backoff Scheduler Semantics

This report records the scheduler behavior needed to compare current `egglog`
with the PLDI 2023 Eqlog artifact and with `egg::BackoffScheduler`. It replaces
an earlier diagnosis of the experimental scheduler's stale-match backlog. That
diagnosis remains useful historical evidence, but the backlog is no longer the
implementation on this branch.

## Result

The current implementation now provides the paper-compatible seminaive policy:

- an eligible rule searches only rows fresh since its last **accepted** batch;
- the scheduler may cap a search at `match_limit + 1` matches;
- a batch over the limit is rejected in full and is not retained;
- rejecting a batch does not advance the rule's seminaive cursor;
- a later eligible attempt searches the current live database again;
- ground-rule matches count as matches even when they bind no variables;
- scheduler deferral is distinct from database progress; and
- `saturate` stops on `RunReport.can_stop`, not merely on an iteration with no
  database update.

These semantics target the archived Eqlog Math table totals through 100
scheduled steps and the archived pointer-analysis output sizes. The standalone
paper harness carries exact ordered output oracles for timed off, term, and
proofs runs, followed by a strict proof-testing checker pass. Committed focused
proof tests cover Math checkpoints 0 and 10 plus pointer analysis;
`paper_bench.py run artifact-full math` is the explicit broad execution gate for
every Math checkpoint.

This is not a claim that current `egglog` implements `egg`'s scheduler in every
respect. The target is the paper's seminaive Eqlog behavior while retaining
`egglog`'s table and deletion semantics.

## Interface Contract

The scheduler boundary is explicit in
[`egglog/src/scheduler.rs`](../egglog/src/scheduler.rs):

```rust
pub enum SearchPlan {
    Skip,
    Search { max_matches: Option<usize> },
}

pub enum SearchResult<'a> {
    Complete(&'a Matches),
    LimitExceeded { at_least: usize },
}

pub enum BatchDecision {
    ApplyAll,
    Reject,
}
```

The backend owns seminaive freshness and bounded query execution. The
scheduler owns only policy:

1. `plan_search` says whether to search and optionally supplies a cap.
2. The backend searches the current live state from the last accepted cursor.
3. `finish_search` receives either the complete batch or evidence that the cap
   was exceeded.
4. `ApplyAll` applies the complete batch and commits the fresh cursor.
5. `Reject` discards the batch and leaves the cursor unchanged.

This division avoids a scheduler-owned host backlog. It also lets a backend
stop a large search once it has enough evidence to ban the rule.

The experimental backoff policy is implemented in
[`egglog-experimental/src/scheduling.rs`](../egglog-experimental/src/scheduling.rs).
It doubles a rejected rule's threshold, bans it for the configured number of
scheduler iterations, and preserves other rules' statistics when fast-forwarding
over a period in which every rule is banned.

## Historical Failure

The previous interface queried first and then let a scheduler filter a fully
materialized `Vec<Value>`. Rejected matches were retained as a backlog. That
created four observable problems:

1. A later attempt saw old matches instead of the current live database.
2. Deleted rows could be replayed from the backlog.
3. Match limits could not bound query materialization.
4. Ground rules divided a flattened value count by zero bound variables.

The minimal witness used three `R` rows and `R(x) -> S(x)`, with match limit 2
and ban length 2. After the first rejection, one or two `R` rows were added.

| Case | `egg` fresh second search | Historical backlog result |
| --- | --- | --- |
| Add one row | Four matches fit the raised threshold; `S=4` | Three retained matches were applied; `S=3` |
| Add two rows | Five matches exceed the raised threshold; `S=0` | Three retained matches were applied; `S=3` |

The `egg` witness was run against commit
`f94c346748ea1fb76493cb1127a0b40dcec3efd6`. Its relevant implementation is
[`egg/src/run.rs`](https://github.com/egraphs-good/egg/blob/f94c346748ea1fb76493cb1127a0b40dcec3efd6/src/run.rs#L925-L964):
an eligible rewrite calls `search_with_limit(egraph, threshold + 1)` and drops
the rejected result.

The old `egglog` outputs were:

```text
add-one: R=4 S=3
add-two: R=5 S=3
```

The equivalent `egg` outputs were:

```text
add-one: R=4 S=4
add-two: R=5 S=0
```

Those finite-state differences established the stale-work bug. They did not
establish that every fair monotone run must end in a different saturated state.

## Current Regression Evidence

Focused tests in
[`egglog-experimental/tests/integration_test.rs`](../egglog-experimental/tests/integration_test.rs)
cover the scheduler lifecycle directly:

- `test_top_level_let_scheduler_persists_on_the_egraph`
- `test_backoff_rejects_grown_delta_again`
- `test_backoff_does_not_replay_deleted_rejected_match`
- `test_backoff_delta_starts_after_last_accepted_batch`
- `test_backoff_counts_ground_rule_matches`
- `test_backoff_run_schedule_should_not_report_progress_without_egraph_updates`
- `test_saturate_continues_until_scheduler_can_stop_after_no_progress_ban`
- `run_with_is_preserved_in_term_and_proof_modes`
- `scheduler_driven_saturate_is_preserved_in_term_and_proof_modes`

Lower-level canaries in
[`egglog/src/scheduler.rs`](../egglog/src/scheduler.rs) cover capped search,
all-or-nothing rejection, subsumed rows, and separation of scheduler progress
from database progress.

Run the focused integration checks with:

```shell
cargo test -p egglog-experimental --test integration_test backoff
cargo test -p egglog-experimental --test integration_test \
  scheduler_driven_saturate_is_preserved_in_term_and_proof_modes
```

## Math Artifact Oracle

The source in
[`benchmarks/math-microbenchmark/base.egg`](../benchmarks/math-microbenchmark/base.egg)
is ported from `micro-benchmarks/src/eqlog/math_full.egg` in the PLDI artifact:

- DOI: <https://doi.org/10.5281/zenodo.7709794>
- Archive SHA-256:
  `2f061f4f59fd3404638db0d9ad9d130e008d4c41fdeb58ade30684d8e424607a`

Generated checkpoints execute an explicit sequence of exactly N scheduled
steps. They do not use `repeat`, because the experimental schedule language's
`repeat` is exact while core `Repeat` may stop when its child can stop.

The sum of the 13 printed source tables is:

| Steps | Rows | Steps | Rows |
| ---: | ---: | ---: | ---: |
| 0 | 35 | 60 | 515,678 |
| 10 | 21,052 | 70 | 518,802 |
| 20 | 38,292 | 80 | 1,002,003 |
| 30 | 81,131 | 90 | 1,376,385 |
| 40 | 163,480 | 100 | 2,080,931 |
| 50 | 288,119 | | |

At checkpoint 10, the exact per-table output in off, term, proofs, and strict
proof-testing modes is:

```text
1857
3771
6893
1838
6676
3
2
1
1
1
1
5
3
```

The standalone paper harness also stages a read-only copy of the historical
Rust driver and validates the selected Eqlog row against the same total.

## Pointer Artifact Oracle

[`benchmarks/pointer-analysis-initdb.egg`](../benchmarks/pointer-analysis-initdb.egg)
uses the artifact's default match limit and ban length and now runs:

```lisp
(run-schedule (saturate (run-with paper-backoff)))
```

Scheduler-driven saturation is required here. A fixed `repeat 100000` obscures
the stop contract and has different early-stop behavior in the experimental
and proof-instrumented execution paths.

The historical Eqlog lane and all current treatment lanes produce:

```text
expr_points_to: 5832
ptr_points_to: 342
```

The current fixture additionally checks the known `strlen` allocation fact.
Input provenance and hashes are recorded in
[`benchmarks/data/pointer-analysis-initdb.PROVENANCE.md`](../benchmarks/data/pointer-analysis-initdb.PROVENANCE.md).

## Remaining Differences And Limits

- `egg` searches a rebuilt e-graph from scratch when a rewrite becomes
  eligible. The paper-compatible `egglog` path uses seminaive rows since the
  last accepted batch. The reproduced artifact totals validate this policy for
  the target workloads; they do not make it identical to `egg` on every graph.
- `egglog` supports table deletion, subsumption, merge actions, and other state
  not modeled by classic `egg` rewrite scheduling. The accepted-cursor rule is
  what prevents rejected or deleted work from being replayed.
- Scheduler state is attached to named rules. Combining independently authored
  rulesets with colliding explicit rule names needs a separate identity design
  before it can be treated as a generic composition guarantee.
- Top-level scheduler declarations and initialized scheduler state survive
  e-graph cloning. Push/pop and concurrent execution of schema-identical clones
  are explicitly tested, including independent collector and backend
  notification state. Defining divergent table schemas after cloning remains a
  separate bridge lifecycle concern rather than a paper benchmark requirement.
- The experimental extended schedule language and core schedule AST are not a
  general language-parity promise. The paper fixtures use explicit sequences
  for fixed iteration counts and `saturate` for fixpoint execution.
- The DD backend explicitly rejects custom scheduler execution. DD parity was
  not a requirement for this work.

These limits should be kept separate from the resolved stale-row contract and
from the validated artifact compatibility claims.
