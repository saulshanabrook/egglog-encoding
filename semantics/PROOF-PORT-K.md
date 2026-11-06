# Task K: actions add to the e-graph directly

## Status and validation

Complete. `lake build EgglogSemantics EgglogPaper` succeeds (1104 jobs),
including all six scoped tests and all 25 unchanged paper `assert_no_sorry`
checks. No failing module remains in the requested build.

Reproduce from this worktree's `semantics/` directory:

```bash
source /tmp/proof-port-env.sh
lake build EgglogSemantics EgglogPaper
```

Successful full-build log: `/tmp/proof-port-k-build-3.log`. The initial Lake
launcher configuration failure was resolved with the supplied environment
shim. Validation used local Lake builds only; no Makefile or network checks.
Existing unrelated linter warnings remain.

Changed nine proof modules, `Tests/Examples.lean`, and this note. Original
proof/test/root files are backed up in `/tmp/proof-port-k-original`, with
initial source hashes in `/tmp/proof-port-k-initial-hashes.json`. The task-local
diff is `/tmp/proof-port-k.diff`; the statement/scope audit is
`/tmp/proof-port-k-statement-audit.json`. No out-of-scope source changed,
including either root file or `Proofs/Congruence/`. Preexisting worktree
changes are preserved. Scoped `git diff --check` and added-line scans pass.
No proof placeholder, new axiom, `native_decide`, or heartbeat increase was
introduced.

## Proof changes

- `Writes`: `RunRules.eq_pair` now follows from direct action application and
  the existing writes/marks correspondence. `RunRules.eq_sUnion` uses
  `mem_ruleResults_iff_queryMatches`, preserving the equivalence between the
  two substitution representations. `RunRules.eq_addEqs` follows from
  `eq_pair` and empty marks for subsume-free rules.
- `Step`: `RunRules.wf` follows from well-formedness of individual rule results
  and componentwise database union.
- `Finite`, `DiagonalPreservation`, `StatePreservation`, `Subsume`,
  `InterpRound`, and `InterpSubsume`: replace dependence on the former
  definitional equality by explicit rewrites with `RunRules.eq_pair`.
- `LiveTables`: empty-round identity simplifies the direct union definition.
- `Tests/Examples`: the round-membership proof rewrites with `eq_pair` before
  constructing its write witness.

The three former `Spec.Sequential` imports already pointed at `Spec.Facts` in
the supplied checkout; no additional import edits were needed.

## Statement changes

None. All existing theorem names and statements are preserved,
including the pair, union, and subsume-free presentations of `RunRules`.
The example statement and all proof-library definitions are unchanged too.

## Semantic issues and root imports

No new semantic issue was found. The proved pair presentation shows that the
new direct-action round has exactly the same equations and marks as the
previous set-valued reading, including subsumption and stuck heads.

No root import or paper assertion change is required. Both root files build
as supplied, without edits or temporary replacements. The semantic boundaries
documented in the previous ports remain unchanged.
