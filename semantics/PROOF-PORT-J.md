# Task J: recursive expression matching

## Status

Complete. `lake build EgglogSemantics EgglogPaper` succeeds (1104 jobs),
including all six scoped test modules and all 25 unchanged paper
`assert_no_sorry` checks. No failing module remains.

Reproduce from this worktree's `semantics/` directory:

```bash
source /tmp/proof-port-env.sh
lake build EgglogSemantics EgglogPaper
```

Successful build log: `/tmp/proof-port-j-build-4.log`. Validation used local
`lake build` only, with no Makefile or network checks. The initial Lake
launcher configuration error was resolved by the supplied environment shim.

Changed 15 scoped Lean files plus this note. Original Lean sources are saved
in `/tmp/proof-port-j-original`; initial file hashes are in
`/tmp/proof-port-j-initial-hashes.json`, and the task-local diff is
`/tmp/proof-port-j.diff`. Comparing the hashes confirms no out-of-scope source
was changed, including either root file or `Proofs/Congruence/`. Existing
worktree changes are preserved.

The statement audit in `/tmp/proof-port-j-statement-audit.json` confirms all
existing theorem names survive and exactly the 22 statements below changed.
Added-line proof-construct, whitespace, and line-length scans pass. No `sorry`,
`axiom`, `native_decide`, or heartbeat increase was introduced. No removed
`Expr.rows` / `Expr.rowsList` reference remains in the scoped sources.

## Statement changes

All existing theorem names are retained. These are all 22 theorem statement
changes and the one predicate definition change. Evaluation equalities remain
wherever a statement names the result:

- `Lookup.eval`, `Lookup.exists_cong`, `Lookup.of_eval`, `Lookup.of_agreeOn`,
  `Lookup.mono_live`, and `Lookup.transport`: replace live `e.rows σ` evidence
  with `Expr.Matches db σ e`.
- `LookupList.eval`, `LookupList.of_eval`, `LookupList.of_agreeOn`,
  `LookupList.mono_live`, and `LookupList.transport`: the corresponding
  replacement by `Expr.MatchesList db σ es`.
- `Expr.rows_agreeOn` and `Expr.rowsList_agreeOn`: retain the historical names;
  conclude equivalence of matching under the agreeing environments, replacing
  equality of the removed row lists.
- `Matches.storedCases`: each branch retains its evaluation and stored
  witnesses, replaces live rows with expression matching, and reconstructs
  the new `Matches` constructors.
- `Lookup.lookupWith`, `LookupList.lookupListWith`, `lookupWith_lookup`,
  `lookupListWith_lookup`, and `lookupWith_iff`: replace semantic live rows
  with recursive matching and executable row-list tests with `exprHoldsWith`
  / `exprsHoldWith` at `d.closureF`.
- `patternHolds_entry_of_mem_rows` and definition `EntryRead`: replace the
  argument-list live-row premise by `Expr.MatchesList`, retaining evaluation.
- `Egglog.Tests.SemanticCong.min_eval_does_not_imply_lookup`: replace live rows
  in the negated conjunction by expression matching.
- `Egglog.Tests.SemanticCong.relational_literal_subsume_agrees`: retain the
  evaluation equality and agreement conclusion, expressed with
  `Relational.exprHolds` and `exprHoldsWith` instead of row-list tests.

New helpers `Expr.Matches.eval_exists` and `Expr.MatchesList.eval_exists`
establish defined evaluation. `exprHoldsWith_iff` and `exprsHoldWith_iff`
relate the executable recursive tests to the specification. No separate
lookup judgement or row traversal is reintroduced.

## Semantic issues

No new semantic issue was found. The supplied `Relational.liveRow` ignores
literal marks, resolving the Task I disagreement; the agreement regression
now passes with `decide +kernel` and keeps its agreement conclusion. The
existing counterexamples for unrepresented variable bindings and `min`'s
discarded operand still pass. The G/H semantic boundaries remain unchanged.

No premises were added or conclusions weakened outside the documented
replacement of removed row traversals with recursive matching. No root import
or paper assertion change is required. Both root files built as supplied.
