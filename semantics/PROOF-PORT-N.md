# Task N: source proofs with computed claims

## Status and validation

Complete. `lake build EgglogSemantics EgglogPaper` succeeds (1104 jobs),
including all five scoped test modules and all 25 unchanged paper
`assert_no_sorry` checks. No failing module remains in the requested build.

Reproduce from this worktree's `semantics/` directory:

```bash
source /tmp/proof-port-env.sh
lake build EgglogSemantics EgglogPaper
```

Successful full-build log: `/tmp/proof-port-n-build-1.log`. The supplied shim
resolved the initial Lake installation configuration error. Validation used
local Lake builds only, without Makefile or network checks. Existing linter
warnings remain; no warning was introduced by the new proof code.

Changed only `Proofs/SourceProof/{Matching,Rules,Soundness}.lean` and this note.
The downstream resugaring and provenance proofs and all tests build unchanged
from their supplied state. Existing worktree edits are preserved. Starting
Lean sources and hashes are saved under `/tmp/proof-port-n-original`; the
task-local source diff is `/tmp/proof-port-n.diff`, and the statement/scope
audit is `/tmp/proof-port-n-statement-audit.json`. Hash comparison confirms no
out-of-scope Lean source changes, including either root module. Scoped
`git diff --check` and added-line whitespace, line-length, and prohibited
proof-construct scans pass. No `sorry`, `axiom`, `native_decide`, or heartbeat
increase was introduced.

## Proof changes

- `Matching.lean`: prove by mutual expression/list recursion that a bound
  variable occurring in an ordering-free expression is a subterm of its
  evaluated instance. Matching places that value under one of the premise
  claim's sides. A query's variable list is duplicate-free, so the domain
  permutation makes every environment binding its variable's lookup value;
  subterm closure then supplies membership in the database's terms.
- `Rules.lean`: use this argument in the completion database to derive the
  substitution-value premise required by the existing source-rule transport.
  The soundness statement and its assumptions are unchanged.
- `Soundness.lean`: use the computed symmetry and transitivity claims directly.
  For congruence, derive `k < args.length` from the accepted child lookup and
  reduce the computed claim to the `args.set` form. Adapt recursive constructor
  patterns without changing any soundness statement.

## Statement changes

All surviving theorem names and statements are unchanged, including
`SourceProof.check_infers`, `Provenance.extract_checked`,
`Provenance.Generated.check_uf_infers`, `Resugar.extractAll_infers`, and
`Resugar.certificates_infers`. No existing theorem gained a premise or had
its conclusion weakened.

Removed `SourceProof.supportedValue_sound`, whose old statement was:

```lean
theorem supportedValue_sound {db : Database} (hw : db.WF) {cs : List Claim}
    (hc : ∀ c ∈ cs, c.Holds db) {t : Term} (ht : supportedValue cs t = true) :
    t ∈ db.terms
```

Its Boolean premise refers to the deleted checker definition. The replacement
is `premisesMatch_values`, supported by three new lemmas. These are the only
added theorem statements, all in `Egglog.SourceProof`:

```lean
theorem eval_lookup_subterm {σ : Env} {v : Var} {s : Term}
    (hv : Env.lookup v σ = some s) :
    ∀ {e : Expr} {t : Term}, e.OrderingFree → e.eval σ = some t →
      v ∈ e.vars → s ∈ t.subterms

theorem evalList_lookup_subterm {σ : Env} {v : Var} {s : Term}
    (hv : Env.lookup v σ = some s) :
    ∀ {es : List Expr} {ts : List Term}, Expr.OrderingFreeList es →
      Expr.evalList es σ = some ts → v ∈ Expr.varsList es →
      ∃ t ∈ ts, s ∈ t.subterms

theorem premiseMatches_lookup_subterm {σ : Env} {p : Pattern} {c : Claim}
    (ho : p.OrderingFree) (h : premiseMatches σ p c = true)
    {v : Var} {s : Term} (hv : v ∈ p.vars) (hs : Env.lookup v σ = some s) :
    s ∈ c.lhs.subterms ∨ s ∈ c.rhs.subterms

theorem premisesMatch_values {db : Database} (hw : db.WF) {σ : Env}
    {q : Query} {cs : List Claim} (ho : ∀ p ∈ q, p.OrderingFree)
    (hc : ∀ c ∈ cs, c.Holds db) (hdom : (Env.dom σ).Perm q.vars)
    (h : premisesMatch σ q cs = true) : ∀ b ∈ σ, b.2 ∈ db.terms
```

## Semantic issues and root imports

No new semantic issue was found. The subterm argument requires `OrderingFree`:
a variable in an unchosen `min` operand need not occur in the result.
`sourceOk` already supplies this restriction. Domain permutation is also
essential to exclude hidden duplicate bindings. Both conditions are existing
checker requirements; no additional acceptance restriction is needed.

No root import or paper assertion change is required. Both root modules build
as supplied, without edits or temporary replacements.
