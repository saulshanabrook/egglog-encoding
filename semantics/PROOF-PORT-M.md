# Task M: string literals and unions between applications

## Status and validation

Complete. `lake build EgglogSemantics EgglogPaper` succeeds (1104 jobs),
including all six scoped test modules and all 25 unchanged paper
`assert_no_sorry` checks. No failing module remains in the requested build.

Reproduce from this worktree's `semantics/` directory:

```bash
source /tmp/proof-port-env.sh
lake build EgglogSemantics EgglogPaper
```

Successful full-build log: `/tmp/proof-port-m-build-3.log`. The supplied
environment shim resolved the initial Lake launcher configuration error.
Validation used local Lake builds only, without Makefile or network checks.
Existing unrelated linter warnings remain; the changed ordering proofs have
no warnings.

Changed two proof modules, `Tests/SourceProof.lean`, and this note. Existing
worktree changes are preserved. Starting Lean sources and notes are backed
up in `/tmp/proof-port-m-original`, including a hash inventory. The task-local
diff is `/tmp/proof-port-m.diff`; the statement/scope audit is
`/tmp/proof-port-m-statement-audit.json`. The source hashes confirm no
out-of-scope source edits, including either root file or `Proofs/Congruence/`.
Scoped `git diff --check` and added-line proof-construct, whitespace, and
line-length scans pass. No `sorry`, `axiom`, `native_decide`, or heartbeat
increase was introduced.

## Proof changes

- `Proofs/Order.lean`: handle integer, string, and mixed literal comparisons
  in asymmetry, totality, and transitivity using the underlying linear orders.
- `Proofs/OrderFinite.lean`: supply `strings` and `numbersFirst` in
  `Term.blt_admissible`. The finite-vocabulary argument already enumerates an
  arbitrary finite set of `Lit` values and needs no constructor-specific change.
- `Tests/SourceProof.lean`: regress admission and certificate acceptance for a
  union between applications containing strings, rejection of a certificate
  equating their distinct literal children, and rejection of bare string unions.

## Statement changes

None. Every existing theorem name and statement is retained, including
`Term.blt_admissible`. No premise was added or conclusion weakened, and no
existing proof-library definition or test fixture changed. The supplied
specification strengthens `AdmissibleOrder` and relaxes `Fragment.noLitUnion`;
this port does not edit either definition. The two new private test fixtures
are `stringApp` and `stringUnion`.

## Semantic issues and root imports

No new semantic issue was found. String comparisons satisfy the same strict
order properties as integer comparisons, and mixed comparisons consistently
put integers first. Finite lower sets still rely only on a fixed finite
literal vocabulary. The source checker admits the newly supported application
unions while rejecting bare string unions and the attempted equality of
distinct string children. The prior ports' semantic boundaries are unchanged.

No root import or paper assertion change is required. Both root files build
as supplied, without edits or temporary replacements. No additional live
proof uses the changed `Fragment.noLitUnion` field.
