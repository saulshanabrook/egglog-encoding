# Task L: congruence subterm existence from the child rule

## Status and validation

Complete. `lake build EgglogSemantics EgglogPaper` succeeds (1104 jobs),
including all six scoped test modules and all 25 unchanged paper
`assert_no_sorry` checks. No failing module remains in the requested build.

Reproduce from this worktree's `semantics/` directory:

```bash
source /tmp/proof-port-env.sh
lake build EgglogSemantics EgglogPaper
```

Successful full-build log: `/tmp/proof-port-l-build-2.log`. The supplied
environment shim resolved the initial Lake launcher configuration error.
Validation used local Lake builds only, without Makefile or network checks.
Existing unrelated linter warnings remain.

Changed eight proof modules, `Tests/SemanticCong.lean`, and this note. Original
Lean sources are backed up in `/tmp/proof-port-l-original`; initial hashes are
in `/tmp/proof-port-l-initial-hashes.json`. The task-local diff is
`/tmp/proof-port-l.diff`; the statement/scope audit is
`/tmp/proof-port-l-statement-audit.json`. Comparing the original source hashes
confirms no out-of-scope source changed, including either root file or
`Proofs/Congruence/`. Preexisting worktree changes are preserved. Scoped
`git diff --check` and added-line proof-construct, whitespace, and line-length
scans pass. No `sorry`, `axiom`, `native_decide`, or heartbeat increase was added.

## Proof changes

- `Proofs/SemanticCong.lean`: restore `Cong.subterm` as a theorem by induction
  on `Term.IsSubterm`, iterating `Cong.child`; use the new constructor in
  congruence transport proofs.
- `SameMeaning`, `Diagonal`, `InterpBase`, `Merge`, `MatchingCounterexamples`,
  `Subsume`, and `SourceProof/Counterexamples`: replace congruence induction's
  `subterm` branch with `child`. Subterm-based invariants use the immediate
  subterm witness `Term.IsSubterm.arg hs (.refl _)`.
- `Tests/SemanticCong.lean`: update the same constructor case in
  `empty_has_no_facts`; its statement is unchanged.

The interpreter's closure specification and all existing regression statements
build unchanged. The closure computation itself required no edits.

## Statement changes

None. Every existing theorem name and statement is preserved. `Cong.subterm`
retains the former constructor's statement as a derived theorem:

```lean
theorem Cong.subterm {db : Database} {t s : Term} (h : Cong db t t)
    (hs : s ∈ t.subterms) : Cong db s s
```

No proof-library definition changed, and no premise was added or conclusion
weakened. The specification's constructor replacement was supplied with the task.

## Semantic issues and root imports

No new semantic issue was found. Induction on `Term.IsSubterm` proves that the
child rule provides the same reflexive-transitive subterm existence as the old
constructor. The semantic boundaries documented in the previous ports remain
unchanged.

No root import or paper assertion change is needed. Both root files build as
supplied, without edits or temporary replacements.
