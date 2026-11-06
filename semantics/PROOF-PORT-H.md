# Task H: subsume names a row by its symbol and children

## Status and validation

Complete. `lake build EgglogSemantics EgglogPaper` succeeds (1104 jobs),
including all six requested test modules and all 25 unchanged paper
`assert_no_sorry` checks. No scoped failure remains.

Reproduce from this worktree's `semantics/` directory:

```bash
source /tmp/proof-port-env.sh
lake build EgglogSemantics EgglogPaper
```

Successful build log: `/tmp/proof-port-h-build-3.log`. The initial launcher
configuration error was resolved by the supplied environment shim. No Makefile
or network checks were run.

Changed 15 scoped Lean files plus this note. Existing worktree changes were
preserved; original scoped files and source hashes are saved under
`/tmp/proof-port-h-original`, with the task-local diff at
`/tmp/proof-port-h.diff`. Comparing the source hashes found no out-of-scope
changes, including no edits to either root file or `Proofs/Congruence/`.
Scoped `git diff --check` and the trailing-whitespace/proof-construct scans
pass. No `sorry`, `axiom`, `native_decide`, or heartbeat increase was added.

The proofs now carry evaluated child lists to the application named by the
subsumption symbol. Evaluation agreement, writes/marks, scope progress,
preservation, finiteness, source properties, provenance, and interpreter
refinement use that application consistently.

## Statement changes

Every theorem name is retained. These are the only four theorem statement
changes, together with the one public predicate definition change:

- `evalAction_eq_some`: the subsumption alternative now quantifies `f`, `es`,
  and `ts`, uses `a = .subsume f es` and `Expr.evalList es σ = some ts`, and
  inserts and marks `.app f ts`.
- `execAction_eq_some`: the subsumption alternative likewise quantifies `f`,
  `es`, and `ts`, evaluates the child list, and returns `d.subsume (.app f ts)`.
- `Action.mem_marks`: returns `f`, `es`, and `ts` with `.subsume f es` in the
  head, successful child-list evaluation, and `t = .app f ts`.
- Definition `Action.EvalTerms`: the `.subsume f es` branch checks evaluation
  of `Expr.app f es`; all theorems consuming this predicate keep their types.
- `Egglog.Tests.SemanticCong.writes_subsumes_commute`: both action sequences now use
  `.subsume "f" [a.toExpr]` in place of `.subsume (f a).toExpr`.

## Fixture updates

- Provenance counterexample `replacement`: subsumes `"T"` with its literal child.
- Source-proof rejection guard: subsumes `"F"` with `a.toExpr` as its child.
- Semantic-congruence programs `replaceRows`, `sameRound`, and `stuckHead`:
  spell the same application targets using the new symbol/children constructor.

## Semantic issues and root imports

No new semantic issue was found. Subsumption still inserts the named row,
retains its children, and marks it; the general invariants and semantic
boundaries documented in `PROOF-PORT-G.md` remain intact. No premise was added
or conclusion weakened to complete this port.

No root import or paper assertion change is needed. Both root files were
validated as supplied, without edits or temporary replacements.
