# Port the egglog Redex semantics to Lean 4

## Context

egglog's proof encoding (`egglog/src/proofs/`, designed in
`egglog/src/proofs/proof_encoding.md`) replaces built-in congruence and rebuilding
with an explicit per-sort union-find and per-constructor view tables maintained by
ordinary rules, so that *every equality has a rule firing behind it*. We want to
prove things about that encoding — that it simulates the ideal semantics, and that
the proof terms it stores really witness the equalities they claim.

To state any such theorem we first need the ideal semantics written down formally.
That exists already as a Redex model — [egglog PR #324](https://github.com/egraphs-good/egglog/pull/324)
(`semantics/semantics.rkt`, `semantics.scrbl`, `test.rkt`; closed, branch
`oflatt-ideal-semantics`, head `e46aef4`). This document plans its port to Lean 4.

Two things shape the design beyond a literal transcription:

- **The encoding's *target* language needs `:merge` functions.** `@UF_<Sort>` and
  `@<C>View` are both merge functions, and the view's `:merge` *is* congruence
  resolution. So the `:merge` extension is not a later nicety — it is a
  prerequisite for the eventual theorem. Phase 1 must be structured so adding it
  is additive.
- **Proof terms are derivations.** Reasoning about `@Trans`/`@Sym`/`@Congr` nodes
  means inducting on how an equality was derived, so congruence must be an
  inductive relation, not a computed fixpoint.

## Decisions

- Project lives at `semantics/` in the workspace root, alongside `egglog/` and
  `egglog-experimental/`, keeping those subtrees clean per `AGENTS.md`.
- Mathlib (`Set`, indexed unions, `Relation.*`, and later lattices for merge
  functions), pinned to `v4.32.2` on Lean `v4.32.2` in `lakefile.toml` and
  `lake-manifest.json`; binaries come from `lake exe cache get`.
- Congruence as an inductive relation; the database stores only *asserted*
  equalities.
- Validation by Lean proofs of the ported test cases; an executable interpreter
  with a decidable congruence procedure is a later milestone (M10).

## What the Redex model contains

| Redex | Role |
| --- | --- |
| `Egglog` grammar | `Program`/`Cmd`/`Rule`/`Query`/`Pattern`/`Action`/`expr` |
| `Database = (Terms Congr Env Rules)` | global state: ground terms, equality pairs, bindings, rules |
| `Eval-Expr`, `Eval-Action`, `Eval-Global/Local-Actions`, `Eval-Actions` | actions add terms and equalities |
| `Congruence-Reduction` + `restore-congruence` | refl/symm/trans/congr + "presence of children", to a fixpoint |
| `valid-env`, `valid-subst`, `valid-query-subst` | declarative e-matching ("pattern instance is equal to a witness term already present") |
| `valid-subst-faster` | operational e-matching, unused by the main relation |
| `Command-Reduction`, `Egglog-Reduction` | run one command; run a program, restoring congruence between commands |
| `typed-*` judgments | scope checking only (a single type `no-type`) |
| `test.rkt` | ~25 unit checks plus `redex-check` random testing |

## Target design

Package `EgglogSemantics`. The tree separates *what is being claimed* from *why it
holds*, so the first can be read closely and the second skimmed — `Spec/` and `Impl/`
contain **no theorems at all**.

```
Spec/     the semantics (definitions only)
  Syntax      Lit, Expr, Pattern, Action (incl. set), Rule, Cmd, Program;
              MergeSpec/FnDecl/Signature; the syntactic vars functions
  Term        Term, decEq, IsSubterm, subterms, subtermList; Row, ctorRows
  Database    Env (lookup/dom/Agree/Refines/Union2/UnionAll); Database with rows,
              addTerm/addRow/addEq/sUnion, Contained, WF, EnvAgree, CtorRows
  Congruence  Cong / CongList
  Merge       MCong (the functional dependency), MergeStep, Expr.MEval, Out/Current,
              Prim/Term.blt, RunStep/CmdStep/ProgramStep
  Eval        Expr.eval, evalAction, evalActions, evalLocalActions
  Match       freeVars, ValidEnv, ValidSubst, ValidQuerySubst
  Step        ruleResults, runRules, stepCmd, runProgram, run, runRounds, Saturated
  Scope       Scoped predicates, bind functions, Models, WellScoped
Impl/     the reference implementation (definitions only)
  Closure     candidates, congrPair, stepAdds, congStep, closure, closureTotal
  Interp      FDatabase, toDatabase, assignments, Env.canon, patternHolds,
              matchQuery, exec*, fireInto/fireRule, rowCount
Proofs/   everything proved about the two, one file per subject
  Syntax, Term, Database, Congruence, Eval, Match, Step, Scope, Closure, Interp
Tests/
  Examples    the Redex checks, as proofs and as `#guard`s
  Egg         rendering a Program as egglog source, for differential testing
```

The one exception to "definitions only" is a proof the language requires to *make* a
definition — the `decreasing_by` on `closure`, and decidability instances. Those are
inlined rather than pulled out into named lemmas, so nothing in `Spec/` or `Impl/` is
there for a proof's sake.

### Syntax

`Expr` and `Term` are nested inductives over `List`. `Term` gets a hand-written
induction principle (`∀ f args, (∀ a ∈ args, P a) → P (.app f args)`) written once
and used everywhere; recursive definitions use the mutual `Term`/`List Term`
pattern, which is the reliable way to get structural recursion through the
nesting. `Lit` is `Int` for now, deliberately a separate type so base sorts can be
added when merge functions arrive.

A `Cmd.decl` case and a `Signature` (`FnName → Option FnDecl`, `FnDecl` carrying
arity and a `MergeSpec` of `.union | .merge Expr | .noMerge`) go in **from day
one**, with Phase 1 theorems carrying an `AllConstructors sig` hypothesis. This is
what keeps the `:merge` extension from churning the AST.

### Database and congruence

```lean
structure Database where
  sig   : Signature
  terms : Set Term
  eqs   : Set (Term × Term)      -- asserted only
  env   : List (Var × Term)      -- order matters: first binding wins
  rules : Set Rule
```

`Cong db : Term → Term → Prop` is the inductive closure with `assert` / `refl`
(restricted to `t ∈ db.terms`, faithful to the Redex, where reflexivity only fires
for terms actually present) / `symm` / `trans` / `congr`. The `congr` rule is
written as a mutual inductive with a `CongList` companion rather than an
`∀ i, i < length` premise — same relation, workable induction — with a
`List.Forall₂ (Cong db)` bridge lemma.

`restore-congruence` **disappears entirely**, which is the main simplification:

- refl/symm/trans/congr become `Cong`'s constructors.
- "presence of children" becomes a structural invariant: `Database.addTerm`
  inserts a term together with all its subterms, and `Database.WF` asserts
  subterm-closedness plus that every asserted equality's endpoints and every
  binding's value are in `terms`.

This is observationally equivalent because `Eval-Action` never reads `Congr`, so
deferring subterm insertion to a later rebuild is unobservable — recorded in the
source as a documented deviation with that justification.

### Where "restored congruence" went

There is deliberately **no post-restore database state**, and no "the reduction
can no longer step" predicate. The Redex has two kinds of database — one whose
`Congr` holds just the asserted pairs, and one whose `Congr` is closed — and
`restore-congruence` moves between them. Here the database always holds only
asserted equalities, and closure is a predicate rather than a state. Its two
halves are handled differently:

- The **relation** half (refl/symm/trans/congr) is never materialized. The only
  place the Redex reads the closed `Congr` is the `valid-subst` side conditions;
  those become `Cong (db.addTerm t) w t` directly. `Eval-Action`,
  `Command-Reduction` and `Egglog-Reduction` never consult `Congr` at all, so
  nothing else needs it.
- The **term-set** half ("presence of children") is a real state change, and is
  the one part that stays in the state — as the `addTerm`/`WF.subtermClosed`
  invariant above.

The observable meaning of a finished program is therefore the pair
`(db.terms, Cong db)`, not a database with a big closed equality set.

If an explicit closed representation is wanted — to check faithfulness against the
Redex, or for the executable layer in M10 — the right way round is to *define* it
as a comprehension over the relation and *derive* the fixpoint property:

```lean
noncomputable def restore (db : Database) : Database :=
  { db with eqs := {p | Cong db p.1 p.2} }

theorem cong_restore   : Cong (restore db) a b ↔ Cong db a b   -- idempotent
theorem restore_normal : ∀ db', CongStep (restore db) db' → db' = restore db
```

so "no congruence step applies" is a theorem about `restore`, not the definition of
it. Defining the closure this way is far cheaper than defining it as a fixpoint and
then proving it *is* the closure.

The e-graph as a *data structure* — a set of e-classes rather than a relation — is
then `Quotient` of `db.terms` by `Cong db` (an equivalence on `db.terms` by the M2
lemmas). That quotient is the bridge to M11: an e-class on this side corresponds to
an `@UF` leader on the encoded side.

### E-matching

Ported structurally from `valid-subst`, keeping the witness formulation: a
substitution is valid when the pattern instance is `Cong`-equal, *in the database
extended with that instance*, to some witness term already in the database. The
witness is what forbids matching a term the e-graph does not contain.

Three deviations and facts worth recording:

* `ValidEnv` requires the substitution's domain to be a *permutation* of the
  pattern's free variables, where the Redex pins it to the order `varset-union`
  happens to produce. The extra substitutions this admits are permutations of Redex
  ones, which no `lookup` can distinguish; making that precise is the
  environment-agreement lemma in M8.

Two facts the Redex leaves implicit and Lean needs as lemmas:

- `free-vars pat db.env` excludes globally-bound variables, so `σ`'s domain is
  disjoint from `db.env`'s and `Env-Union db.env σ` never fails — plain append is
  correct. (This also preserves the real quirk that a globally-bound variable in a
  pattern denotes its value rather than being a match variable.)
- Envs only ever get consulted through `lookup`, so `evalLocalActions` is
  invariant under extensional agreement of environments. That lemma, rather than a
  list-level normal form, is what lets `Env-Union`'s duplicate bindings be ignored.

### Steps

Because the database's components are `Set`s, an indexed union over *all* matching
substitutions is directly expressible, so `(run)` is a function rather than a
nondeterministic relation, and the whole semantics becomes
`noncomputable def runProgram : Program → Database → Option Database`:

```lean
noncomputable def runRules (db : Database) : Database :=
  db.sUnion { d | ∃ r ∈ db.rules, ∃ σ, ValidQuerySubst db r.query σ ∧
                    evalLocalActions r.actions db σ = some d }
```

`sUnion` is left-biased on `env` and `rules`; `ruleResults_env` and
`ruleResults_rules` show every `d` in that set has `d.env = db.env` and
`d.rules = db.rules`, which is what makes the bias faithful to Redex `U_d`. The
Redex's `skip` command is an artifact of its two-level reduction relation and is
dropped. `Option` carries the partiality of variable lookup; `Scope.lean` proves
well-scoped programs never hit `none`.

`Cmd.decl` updates `db.sig` and nothing reads it yet, so declarations are inert in
this phase — the point is that M9 turns them on without touching the AST or any
`match` over `Cmd`.

## Milestones

The port proper — **all of M0–M7 is done**, `lake build` is clean and `sorry`-free.

- **M0 — scaffold.** ✅ `elan`; `lake init EgglogSemantics math` in `semantics/`
  pinned to Mathlib `v4.32.2` on Lean `v4.32.2`; `lake exe cache get`;
  `make lean-check` in the root `Makefile`, kept out of `make check` so the
  Rust/Python suites stay unaffected. Mathlib's copyright-header linter is off;
  the rest of `mathlibStandardSet` is on.
- **M1 — `Syntax.lean`, `Term.lean`.** ✅ Includes `Term.recTerm` (the induction
  principle through the `List Term` nesting), `IsSubterm`/`subterms` with inversion
  lemmas, and the purely syntactic `Expr.vars`/`Pattern.vars`/`Query.vars`.
- **M2 — `Database.lean`, `Congruence.lean`.** ✅ `Env` with `lookup`/`dom`/`Agree`;
  `Database` with `addTerm`/`addEq`/`sUnion`/`Contained`/`WF`. `Cong`/`CongList` plus
  monotonicity, `Cong db a b → a ∈ db.terms ∧ b ∈ db.terms` under `WF`,
  `Cong.setoid` (the e-class quotient), and `Cong.le` — the least-congruence
  principle, which is how every negative fact about the closure gets proved and the
  shape the M11 checker-soundness argument will take.
- **M3 — `Eval.lean`.** ✅ `Expr.eval`, `evalAction`, `evalActions`,
  `evalLocalActions`, with `Contained`/`WF`/env/rules lemmas for each, plus
  `Expr.eval_agree` (evaluation reads the environment only through `lookup`) and
  `Expr.eval_isSome`.
- **M4 — `Match.lean`.** ✅ `freeVars` with `mem_freeVars` relating it to `vars`;
  `Env.Union2`/`UnionAll` with `mem_iff`; `ValidEnv`, `ValidSubst`,
  `ValidQuerySubst` with `mem_terms` and `mem_dom_iff`.
- **M5 — `Step.lean`.** ✅ `ruleResults`, `runRules`, `stepCmd`, `runProgram`, `run`,
  with `Contained`/`WF` preservation and `runProgram_append`.
- **M6 — `Scope.lean`.** ✅ `Expr.Scoped` and the `bind` functions for actions,
  queries, commands and programs; `Scope.Models` tying the static scope to the
  runtime environment; `run_isSome` (a well-scoped program runs to completion) and
  `evalLocalActions_isSome_of_scoped` (a well-scoped rule contributes on every
  substitution its query admits — `runRules` silently drops stuck firings, so this
  is the statement worth having).
- **M7 — `Examples.lean`.** ✅ The `test.rkt` unit checks as closed proofs: scope
  checks, congruence closure (positive and negative), the `(wrapper 1)`/`(wrapper 2)`
  witness example, the `(let v (b 1)) (union 7 7) (union v 4)` program with its exact
  term and equality sets, and `(Add 1 2)` + `rule` + `run` producing `(Add 2 1)`.

Follow-ups, in rough dependency order:

- **M8 — metatheory.** Partly done.
  - ✅ *Environment agreement.* `Env.Agree.of_perm` and `.append_left`,
    `Database.EnvAgree`, and `evalAction`/`evalActions`/`evalLocalActions_agree`.
    This is `Expr.eval_agree` lifted to whole action sequences, and it discharges
    both places the semantics is deliberately loose about environments: the Redex
    `Env-Union` leaving a variable bound twice, and `ValidEnv` fixing a domain only up
    to permutation. `ruleResults_of_agree` is the payoff — `runRules` sees a
    substitution only up to agreement, so an enumerator may emit one representative
    per class.
  - ✅ *Rounds.* `runRounds` (egglog's `(run n)`; `Cmd.run` is one round),
    `runRounds_succ'`, `Saturated`, and the `Contained`/`WF`/env/rules lemmas.
  - ~~`ValidSubst` inversion, without which no example can state what a `run` does *not*
    produce~~ — **superseded by M10.** `exec_toDatabase` makes any statement about a
    *specific* program's result decidable: it transfers to the interpreter, where the
    closure computes. The `#guard` showing one round is not enough for the `Wrapper`
    example is already such a negative fact. Inversion is still wanted for statements
    quantified over *all* programs, which is where M11 will need it.
  - Remaining: nothing on the critical path. The matcher is the slow one by
    construction — `assignments` is `|terms| ^ |vars|` and `patternHolds` recomputes a
    closure per candidate — which is what keeps the differential cases tiny. The fix is
    **not** to port the Redex's `valid-subst-faster`: `exec_toDatabase` is the contract,
    so the reference implementation can be optimized wherever profiling says it is slow
    and the refinement re-established against the unchanged spec. Porting
    `valid-subst-faster` specifically would settle a conjecture the Redex left open,
    which is a nice-to-have rather than a need.
- **M9 — `:merge` functions.** Designed in [`MERGE.md`](MERGE.md). Partly done, and
  **merged into the main development** — there is one `Database`, one `Action`, one
  `Cmd`, and `Spec/Merge.lean` holds only what is genuinely new.
  - ✅ *The compatibility theorem.* `mcong_toM_iff`: on all-constructor signatures the
    functional dependency `MCong.fd` **is** `Cong`, so `MCong` needs no `congr`
    constructor and every M2–M8 theorem transports rather than being reproved. Proved,
    with `MergeStep.saturated_of_allConstructors` as its step-side companion — together
    they say M9 restricted to constructors is M0–M8 unchanged.
  - ✅ *Unification.* `Action` gained `set`; `Database` gained `rows`, maintained by
    `addTerm` through `Term.ctorRows`. `RowAction`, `MDatabase`, `MRule`, `MCmd`,
    `MProgram` and `Database.toM` are gone. `Spec/Merge.lean` fell from 640 lines to
    476 and `Impl/Merge.lean` from 280 to 160, all of it now genuinely M9-only.
  - ✅ *`Spec/Merge.lean`.* `MCong` (the FD congruence), `MergeStep`, `Expr.MEval`,
    `RunStep`, `Prim`/`Term.blt`. The headline shape change: a `:merge` body is an
    action list and a non-constructor application is a lookup, so evaluation — and with
    it `runProgram` — becomes a **relation**.
  - ✅ *`Impl/Merge.lean` and differential testing.* An M9 interpreter, `:merge`
    rendering in `Tests/EggMerge.lean`, and 7 merge cases. `make lean-difftest` is now
    **77 cases**, all passing.
  - ✅ *The metatheory.* 17 of the 22 stated theorems are proved — `MCong.le`, the
    monotonicity family, the `Contained` chain through `CmdStep`/`ProgramStep`,
    `MergeStep.wf`, `Term.blt_linear`, `Out.union_cong` and `closureF_ok`. Four of the 22
    statements turned out to be **false or vacuous** and are corrected in place, each with
    a machine-checked counterexample or a hypothesis added and flagged; `MERGE.md` lists
    them. 5 remain: the two confluence guesses and three interpreter-refinement ones.
  - ✅ *Multi-column outputs.* `Action.set` takes a `List Expr` and `Pattern` gained
    `values`, egglog's tuple destructure `(= (values v…) (f a…))` — the only way egglog
    offers to read a value column other than the first. This is what `CHECKER.md` called
    the one blocker on M11's proof column.
  - ✅ *The implementation deletes; the specification does not.* `Spec/` stays
    append-only — the M11 invariant depends on it — while `Impl/Merge.lean`'s merge phase
    drops the two rows it combined, as egglog does, and nothing else.
    `FDatabase.mergeRound_confined` proves the "nothing else": no term, no equality, no
    `.union` row, no `.noMerge` row. The contract between the two therefore splits: a
    containment for soundness (`MValidSubst.mono` is the half that makes fewer rows mean
    fewer matches), the untouched equality on the constructor fragment (where the pass is
    the identity, `mergeRound_eq_self`), and `Current` for lattice merges. It also makes
    merge saturation genuinely terminate.
  - Remaining: `Cong` and `MCong` still coexist over the one `Database`; collapsing them
    is the rest of stage 2 and is cheap, since `mcong_iff_cong` is the theorem that
    licenses it.
  See below for the original proposal and what `MERGE.md` revises in it.
- **M10 — executable layer.** A `Finset`-based interpreter, a decidable congruence
  closure, and a refinement theorem `↑(exec p d) = spec p (↑d)`.
  - ✅ `DecidableEq Term`, hand-written and mutual since `deriving` cannot see through
    the `List Term` nesting — verified to actually compute.
  - ✅ *Congruence closure* (`Closure.lean`). `congStep` is one round of
    one-step-derivable pairs over the candidate universe `terms ×ˢ terms`; `closure`
    iterates it by well-founded recursion on how much of that universe is still
    missing. `mem_closure_iff` proves it decides `Cong` exactly: soundness by induction
    over the iteration, completeness by `Cong.le` against the fixpoint, one closure rule
    per premise. Stopping *only* at a fixpoint is what makes `Cong.le` applicable, and
    is why this is well-founded rather than fuel-bounded recursion.

    Deliberately the obvious algorithm, not the efficient one. Union-find with upward
    merging is what egglog does and what the M11 theorems are *about*; using it here
    would put the thing under study inside the thing doing the studying.

    Well-founded definitions are sealed against kernel reduction, so `decide` does not
    see through `closure`. Two ways round, neither adding an axiom: `#guard`, which is a
    command and so enters no proof term, and `unseal closure`, which lets `decide`
    through where a real proof wants it. `native_decide` is *not* used — it would add
    `Lean.ofReduceBool` to every downstream theorem's axiom set.
  - ✅ *The interpreter* (`Interp.lean`). `FDatabase` (a `List`-backed database) with
    `toDatabase` giving its denotation; `assignments` and `matchQuery` for e-matching;
    `execAction`/`execActions`/`execLocalActions`/`execRunRules`/`execRunRounds`/
    `execCmd`/`execProgram`/`exec`; and `rowCount`/`rowCounts` producing what
    `files.rs` snapshots.

    The components are `List`s rather than `Finset`s for one blunt reason:
    `Finset.toList` is noncomputable, so nothing that must *enumerate* a `Finset` can be
    compiled. Duplicates are harmless — the denotation is the set of members, and
    `closureF` dedups through `List.toFinset` where the closure wants a `Finset`.

    The enumerator departs from the spec deliberately: the spec takes one substitution
    per pattern and joins them (`Env.UnionAll`, faithful to the Redex `Env-Union`), while
    the enumerator assigns the whole query's free variables at once and restricts to each
    pattern with `Env.canon`. `Env.agree_canon` shows the two agree up to `Env.Agree`,
    which by `evalLocalActions_agree` is all `runRules` can see.

    It runs, and reproduces the Redex `execute` cases as `#guard`s in `Examples.lean` —
    including the two-round `Wrapper` test, which has no hand proof because stating it as
    a theorem needs `ValidSubst` inversion.
  - ✅ *Refinement, action level.* `execAction_toDatabase`, `execActions_toDatabase` and
    `execLocalActions_toDatabase`: each interpreter action denotes the spec's, as
    `(exec… ).map toDatabase = eval…`. `FDatabase.WF` is stated as `d.toDatabase.WF` so
    every `Database.WF` lemma transfers through the bridges, and
    `mem_closureF_iff_of_wf` reads the closure's side condition off it.
  - ✅ *Refinement, e-matching.* `patternHolds_iff`: given a `valid-env` for the pattern,
    the interpreter's check decides `ValidSubst` exactly, via `mem_closureF_iff_of_wf`.
    `mem_matchQuery_iff`: the enumerator produces exactly the substitutions assigning the
    query's free variables to terms the database holds and satisfying every pattern under
    restriction. Supporting: `ValidSubst.of_agree` (transfer along agreement given the
    right domain — agreement alone does not suffice, because `ValidEnv` pins the domain,
    which is *why* an enumerator must canonicalize), `Expr.freeVars_nodup`,
    `Env.mem_of_lookup`, and the `Query.freeVars` membership lemmas.
  - ✅ *Refinement, the enumerator against the spec.* Both directions:
    `validQuerySubst_of_mem_matchQuery` (every substitution the enumerator produces is, up
    to `Env.Agree`, one the spec admits) and `mem_matchQuery_of_validQuerySubst` (every
    substitution the spec admits has a representative in the enumerator's output). This is
    the shape mismatch closed: the spec joins one substitution per pattern with
    `Env.UnionAll`; the enumerator restricts a single one.

    The load-bearing lemma is `Env.UnionAll.refines_of_mem` — every operand's bindings stay
    reachable in the union. Its induction has to carry **self-refinement**
    (`∀ b ∈ ρ, lookup b.1 ρ = some b.2`) rather than `Nodup`, because appending two
    substitutions that share a variable duplicates it in the domain while leaving every
    lookup intact, so `Nodup` is not preserved by a `Union2` step and self-refinement is.
    Also `Env.Refines` with its append/transitivity lemmas, `Env.exists_unionAll`,
    `Env.agree_of_refines` and `Env.canon_canon`.
  - ✅ *Refinement, the fold and the top level.* `mem_terms_foldl`/`mem_eqs_foldl` and the
    field-preservation lemmas, stated once over an abstract step and contribution and
    applied to the substitution fold and the rule fold in turn — which needed
    `execRunRules` refactored into named `fireInto`/`fireRule` steps so the step function
    is a closed term the lemmas can be instantiated at. Then `execRunRules_toDatabase`,
    `execCmd_toDatabase`, `execProgram_toDatabase`, and

    ```lean
    theorem exec_toDatabase {p : Program} :
        (exec p).map FDatabase.toDatabase = run p
    ```

    Well-formedness came free: `FDatabase.WF` is the spec's, so `execCmd_wf` is
    `stepCmd_wf` read through the refinement rather than a separate induction.

**M10 is done.** The consequence is what it was for: the `#guard` cases in `Examples.lean`
and the 70 differential cases against the Rust now constrain the *specification*, not just
the interpreter. Before this they sat on the interpreter's side of an unproved gap.

  Two obligations writing the implementation forces:
  1. *Enumeration completeness* — the spec's `{σ | ValidQuerySubst db q σ}` against an
     enumeration of `freeVars → terms`. Prepared by `ValidEnv.mem_dom_iff` (the domain
     is precisely the free variables) and `mem_terms`.
  2. *Order-insensitivity* — ✅ discharged by M8's agreement lemma.

  *Finiteness* is **not** an obligation: the implementation is a `Finset` function by
  construction, so finiteness of the spec's output falls out of the refinement theorem
  as a corollary rather than needing to be proved first.

### Differential testing — ✅ running

`make lean-difftest` (`scripts/difftest.sh`) compares the Lean interpreter against the
Rust. 77 cases pass: 10 curated, 60 randomly generated, and 7 M9 `:merge` cases.

The oracle is **`(print-size)`**, which prints one row count per function — the same
quantity `egglog/tests/files.rs` snapshots. egglog's table for `f` holds one row per
distinct *canonical* argument tuple, so the Lean-side quantity is the number of congruence
classes of `f`-applications, which is `FDatabase.rowCount`. `DiffTest.lean` writes a `.egg`
file and the predicted counts per case; the script runs egglog and diffs. One invocation
per case, with a timeout, so a program that blows up cannot take the run down.

**No egglog test file is portable.** Of the 104 in `egglog/tests`, zero are in the
fragment: `function` appears in 47, `relation` in 35, `constructor` in 35, `sort` in 32,
`set` in 31, `run-schedule` in 21. Even the 7 whose top-level commands are all core use
numeric or string literals. `before-proofs.egg` is the closest and needs exactly two cheap
things — a `Lit.str` constructor, and desugaring `(rewrite lhs rhs)` to
`⟨[.expr lhs], [.union lhs rhs]⟩`, which the fragment already expresses. Everything else
needs primitives with arithmetic, or M9.

**Curated cases are only as good as whoever chose them**, so the random ones matter more.
Getting them to matter took two corrections worth remembering:

* A freely generated pattern almost never matches anything, so most programs produced no
  rows beyond their seeded terms — 31 of 60 gave an identical trivial profile. Patterns are
  now built by *abstracting subterms of a term the program actually builds*, which
  guarantees the rule fires. That took the spread from 8 distinct profiles to 20, and the
  largest case from 6 rows to 41.
* The script therefore reports the row-count distribution on every run. A pass count alone
  hides a generator that has stopped exercising anything.

Two expressiveness findings, both showing the fragment is **not a subset** of egglog's
language:

* A bare variable *was* a legal query fact and a legal `expr` action here — it matches, or
  adds, any term — and egglog's grammar rejects both. 34 of the first 60 generated cases
  died on this. Now **banned**: `Expr.IsApp` is a conjunct of `Pattern.Scoped` and of
  `Action.Scoped`'s `expr` case, so every later phase is spared a case the real system
  cannot express. This is the one place `WellScoped` is deliberately stricter than the
  Redex `typed-program`, which costs one ported check — `((let v1 2) v1)` — kept in
  `Examples.lean` with the bare `v1` wrapped in a constructor, alongside two new examples
  pinning the restriction.
* `Database.rules` is a `Set`, so a repeated rule is silently ignored; egglog panics with
  "was already present". The Redex `U_d` dedups too, so this is faithful to the model being
  ported rather than a defect, but it is a real difference from egglog.

What this establishes: it is the only check that the *model* matches egglog rather than
matching itself, and `rand-37` — a rule matching every `F` application and building nested
terms over two rounds, agreeing at `F 17` and `G 22` — is not coincidence. What it does not:
anything outside the fragment, and, until the refinement theorem lands, a divergence
between the spec and the interpreter, since both difftest and the `#guard`s sit on the
interpreter's side of that gap.

One performance note that is really a design note: `FDatabase` insertions deduplicate. A
round's `union` copies every operand's terms, so without dedup the list length multiplies
each round and the per-substitution `List.toFinset` inside `closureF` goes quadratic on it
— `wrapper-3` did not terminate. Dedup is invisible to `toDatabase`.

- **M11 — the proof encoding.** See below.

- **M12 — one evaluator.** `Expr.eval`/`evalAction`/`stepCmd`/`runProgram` (functions,
  M0–M8) and `Expr.MEval`/`ActionStep`/`CmdStep`/`ProgramStep` (relations, M9) both run
  over the one `Database` and the one `Action`. Collapsing them is the last of the
  unification and is **deliberately deferred**, because it is where the cost is. Three
  things planned in rather than discovered mid-refactor:

  - *The cost.* `Proofs/{Eval,Match,Step,Scope,Interp}` are built on `Option` algebra —
    `evalAction db a = some db'`, `Option.map`, `Option.bind`. Against a relation each
    such statement becomes an existential and each proof an induction over a derivation
    rather than a `cases` on an `Option`. Roughly 1000–1400 lines touched, against the
    ~450 that stages 1 and 2 cost.
  - *The framing.* This is not "merge two things". It is **moving determinism out of the
    spec and into the implementation, where it belongs**. The spec is functional today
    only because M0–M8 happens to be deterministic; M9 showed that is an accident of the
    fragment, not a property of egglog. `Expr.MEval_of_eval` is the guard against the two
    drifting apart while both exist.
  - *The recovery.* `exec_toDatabase` is currently an **equality**, and it is what makes
    the 77 differential cases bear on the specification rather than only on the
    interpreter. Against a relation it weakens to reachability. Plan the equality back
    in: prove `ProgramStep` **deterministic under `AllConstructors`**, and the equality
    returns as a corollary for the constructor fragment — which is exactly the fragment
    the differential test covers.

## Extending with `:merge` (M9)

**Superseded by [`MERGE.md`](MERGE.md)**, which is the current design; this section is
the starting proposal it revises. Three of the five points below did not survive
contact with egglog's actual `:merge`: a merge body is an action list, so the
observable value cannot be a fold over asserted rows (3); a non-constructor
application is a *lookup* with no `:default`, so evaluation and `runProgram` become
relations; and the base-sort work (4) is deferred rather than done. Points 1, 2 and 5
stand as written.

Designed so it generalizes rather than rewrites:

1. **Signature is already there** (M1), so only `MergeSpec`'s other cases become
   reachable and `Cmd.decl` gains meaning.
2. **Rows replace the bare term set.** `rows : Set (FnName × List Term × Term)`
   maps an application to its output value; for a constructor the invariant is
   `out = .app f args`, so `terms` stays derivable. Congruence then *is* the
   functional dependency: colliding rows over congruent arguments merge their
   outputs, with `.union` merging by equality — exactly
   `proof_encoding.md`'s "the view's `:merge` resolves congruence directly". The
   theorem that makes this a safe refactor is that the generalized relation
   restricted to `AllConstructors` coincides with M2's `Cong`.
3. **Keep the database monotone.** A merge overwrite is not additive, which would
   break every monotonicity lemma. Instead accumulate *asserted* rows and define
   the observable value of a key-class as the merge-fold over all congruent
   asserted rows. Prove that fold well-defined (independent of order) when the
   merge is a semilattice join, using Mathlib's `SemilatticeSup`; leave the
   general case relational, matching egglog's actual order-dependence for
   non-lattice merges.
4. **Base sorts.** Merge functions have non-eq outputs, so `Lit` grows (`i64`,
   `Unit`, `String`) and the Redex's placeholder `no-type` becomes a real sort
   discipline in `Scope.lean` — that is where the Redex's "add types" to-do gets
   discharged.
5. **No termination claim.** Merge closure need not terminate; it stays a
   relation, with saturation as a separate hypothesis where needed.

## Path to the proof-encoding theorem (M11)

With M9 in place, the encoding becomes a translation between two instances of the
same semantics, and the theorems are about that translation:

- The target needs **fresh ids** (`get-fresh!`), which the source has no notion of.
  An earlier draft of this plan said to add an id supply to the target configuration;
  that turned out to be unnecessary. Terms *are* the ids: the id for `f` over canonical
  children `cs` is the term `.app f cs`, the standard skolem encoding of `get-fresh!`.
  Source terms and target ids then share one type, so the simulation theorem compares
  them directly with no correspondence relation. The deviation this buys is in row
  counts, not equalities — egglog mints per construction *site*, so it holds strictly
  more `@UF` rows than the skolem encoding does. Any theorem about row counts must
  account for that; the simulation theorem, being about equality, need not. The only
  supply `encode` still threads is generated variable names (`@v0`, `@v1`, …), which
  is code generation, not semantics.
- Define `encode : Program → Program` for a fragment first: constructors only, no
  containers, no delete/subsume, no schedules.

Three theorems, in increasing order of what they buy:

1. **Every proof the encoding writes is accepted by the checker.** Prove that for every
   `@Proof` row in `runProgram (encode P)`, `Checks` holds. This is the lemma that would
   catch encoder bugs — a proof row written with the wrong column, the wrong bridge, or a
   `@Congr` at the wrong child position fails it. It is worth stating separately from (2)
   because it is about the *encoder*, and holds without reference to the source
   semantics.

   [`CHECKER.md`](CHECKER.md) scopes what `Checks` is, and revises the shape of this
   theorem in three ways. **The checker is not what reads the rows**: a conversion stage
   parses rows into `RawProof` and replays the rule head to produce a `Justification`, and
   it is where the encoder's mistakes are actually caught — 23 `panic!` in
   `proof_format.rs` against 3 in `proof_checker.rs`. So (1) decomposes into *conversion
   does not panic*, then *`check_proof` returns `Ok`*, and the first conjunct is the
   substantial one. **The checker reads the source program, not the e-graph** —
   `check_proof(proof_id, program: &[ResolvedNCommand])`, with no tables, backend or
   extraction — so `Checks` is a predicate over syntax `Spec/` already models. And **the
   constructor-only fragment needs only five justifications** (`Fiat`, `Rule`, `Trans`,
   `Sym`, `Congr`), estimated at 150–250 lines of Lean; the rest of the checker is out of
   scope for a first target. The remaining risk is not the checker but `Firing`'s
   cross-row memoized walk in `proof_head.rs`.

2. **The checker is sound.** If `Checks p` and `p` concludes `a = b`, then
   `Cong (runProgram P) ⟦a⟧ ⟦b⟧` in the source semantics. This is what makes (1)
   worth having: (1) + (2) give that every proof the encoding stores witnesses a
   real equality of the ideal semantics.

3. **Simulation.** For well-scoped `P`, `Cong (runProgram P) a b` iff `a` and `b`
   have the same `@UF` leader in `runProgram (encode P)`. The `⇐` direction is
   (1) + (2) specialized to the union-find; the `⇒` direction is completeness —
   the encoding loses no equality — and needs the rebuild schedule to have
   saturated.

`Cong` being inductive is what makes all three tractable: **all five** justifications the
constructor fragment needs map onto `Cong`'s constructors, so (2) is a structural
induction on the proof and (3)'s `⇒` an induction on the `Cong` derivation.

`CHECKER.md` also suggests splitting (1) at the layer boundary `proof_encoding.md`
already draws — prove it for layer 1, where there is no column arithmetic, and leave
"layer 2 recovers layer 1" to the two Rust tests that pin exactly that.

One deviation to record, because it bears on (1): the Redex (and this port) returns
**all** matching substitutions, where egglog is seminaive and returns only new ones.
Deliberately **not** modelled — a reference semantics should be simple, and naive
evaluation is the simple choice. It is sound for the theorems above rather than
merely tolerable: a naive round fires a *superset* of what a seminaive one fires, so
"every proof row written is checker-valid" proved here covers rows the real encoder
never writes. It would only bite for claims about row *counts*, which are not among
the goals.

Two places to revisit it. Differential testing compares per round rather than only at
saturation, since that localizes a discrepancy — and if one ever traces to seminaive,
this is the note to reread. And once M9 admits merge functions that are not idempotent
joins (`:merge (+ old new)`, say), the *number* of firings changes the result, so naive
and seminaive genuinely diverge there in a way they cannot for constructors.

**M9 over-approximates in the same direction, and for the same reason.** With merge
functions, a lookup reads any recorded output rather than the current one, and a round
takes any number of merge steps rather than all of them, so the spec reaches every state
egglog reaches plus some it does not. That is sound for (1) and (2) because theorem (1)
is an *invariant* over the step relation — it holds at every reachable state, so it
needs neither termination nor confluence, and a diverging or differently-ordered run
satisfies it throughout — and because term and proof rows are append-only, so a stale
read yields a different proof of the same fact rather than an invalid one. It bites the
same place seminaive does: claims about row counts, and theorem (3), which therefore
takes saturation and a join condition as hypotheses. There is also a positive argument
for it rather than only a tolerance: an order-dependent merge has no order-independent
answer, egglog calls that undefined behaviour, and a semantics that declines to pin an
order the programmer never specified is arguably the more honest one. See
[`MERGE.md`](MERGE.md), "The framing".

Other omissions inherited from the Redex to-do list: schedules, extraction,
containers, primitives.

## Verification

- `cd semantics && lake build` — the whole development typechecks.
- No `sorry`: `lake build` reports `declaration uses 'sorry'`; grep the build
  output and the sources so an unfinished proof cannot pass silently.
- `EgglogSemantics/Examples.lean` compiling *is* the test suite for M7 — each
  ported Redex check is a closed Lean proof.
- `make lean-check` from the workspace root runs the above (it adds
  `~/.elan/bin` to `PATH` itself). Verified to fail on an injected `sorry`.

## `set` legality is a separate predicate, for now

`Database.CtorRows` — the rows are exactly the ones the terms induce — is one of the two
hypotheses `mcong_iff_cong` takes, so it is the on-ramp from "a database you can run a
program to" to "the functional dependency *is* congruence". It is preserved by every
step of the semantics only if `set` is restricted, and egglog restricts it the same way:
`set` on a constructor is a type error (`egglog/src/constraint.rs`, "Check that we're not
trying to set a constructor"). Since constructors are exactly the `.union`-merge
functions, the side condition is `mergeOf f ≠ .union`.

That check is `Action.SetLegal`/`Program.SetLegal` in `Spec/Scope.lean`, **beside**
`Scoped` rather than inside it. It belongs inside eventually — a front end rejects both
in one pass — and it is out for one reason: the parameter. `Scoped` relates syntax to a
`Scope`; this relates it to a `Signature`. Threading a signature through
`Actions.Scoped`, `Rule.Scoped`, `Cmd.Scoped` and `Program.Scoped` would put a signature
argument on every lemma in `Proofs/Scope.lean` and a new hypothesis on
`exec_toDatabase`, and none of the scope theorems would use it. Fold the two together
when `Program.Scoped` needs the signature for its own sake — M9's sort discipline (M9,
point 4) is that reason, since a merge function's output has a base sort. Until then the
pair to carry is `WellScoped p ∧ p.SetLegal sig`.

One thing the port learned writing this down: **`SetLegal` alone is not enough**, and the
gap is not about actions at all. Declaring `f` a `:merge` function makes the constructor
row `f ↦ (f)` *already in the database* collide with itself, and `MergeStep` then writes
whatever the merge body computes at that key — a non-constructor row, with no `set`
anywhere. So `Cmd.CtorDecl` ("this declaration declares a constructor") is a second,
independent side condition. `Proofs/Step.lean`'s `exists_mergeStep_not_ctorRows` is that
counterexample as a theorem.
