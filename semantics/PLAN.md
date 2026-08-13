# A Lean 4 model of egglog's semantics

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
`oflatt-ideal-semantics`, head `e46aef4`) — and this development began as its port to
Lean 4. That is the only debt worth recording up front; "The Redex model this was ported
from", below, is the one place it is discussed, and nothing in the development itself
refers to it.

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
  `egglog-experimental/`, keeping those subtrees clean per `AGENTS.md`. Mathlib and the
  toolchain are pinned in `lakefile.toml` / `lake-manifest.json`; `README.md` has the build.
- Congruence as an inductive relation; the database stores only *asserted* equalities. Both
  held, and the second went further than planned — asserted equalities are now the *whole*
  state that grows, existence and function tables included.
- Validation by Lean proofs of the ported test cases. **Superseded**: differential testing
  against the real binary is the check that decides whether the model is right about egglog,
  and Lean proofs decide whether `Impl/` is right about `Spec/`.

## Current priority

**The goal is to model egglog as cleanly as possible for a paper, and then prove things
about an implementation.** That is a different goal from wanting a sound and fast verified
engine, and it changes what counts as progress: `Spec/` being readable *as a description of
what egglog means* is the deliverable, not a convenience.

**`Spec/` is frozen**: 8 files, ~975 lines, one theorem (`eqsInTerms_free`), and roughly one
comment line per two of code. It got there by deletion — a row set, a term field, a second
congruence relation, a functional command semantics and a generic front-end walk all came out —
and the standard for putting anything back is that a reimplementer would get it wrong without it.
One thing has gone back in since: `Spec/Scope.lean`'s sixth check, `WidthOk`, which four separate
pieces of work independently needed. Rationale, egglog citations and design history live in these
documents, not in its comments.

(The contrast is worth keeping in mind. `lambdaclass/truth_research` — OptiSat — is a Lean 4
verified equality-saturation engine, ~370 theorems and no `sorry`, whose "specification" is a
five-line `Prop` plus 12k lines of Lean with the load-bearing definitions living inside the
proof files. There is no artifact you can read to learn what the system means. It also has
no differential testing, and a no-op engine satisfies its entire soundness chain.)

**The immediate work is a faithful executable model of egglog, validated against the real
implementation by `make lean-difftest`.** Differential testing comes before proof work: a
proof relates `Impl/` to *our* `Spec/`, and difftest is the only check that can tell us
`Spec/` itself is wrong about egglog — which it has been (see `MERGE.md`, "The merge phase
runs between commands").

**The proof encoding (M11) is parked, and its theorems are deleted.** `Encoding/` now holds
`encode` and nothing else. The three theorems and their vacuity witnesses were removed
rather than carried through the `Spec/` simplification: two defects made statements true
without saying anything, and the remaining eleven were never checked for the same, so what
was there was a liability rather than an asset. [`ENCODING.md`](ENCODING.md) is what survives them — the two defects, the
repairs that do and do not work, and the SHA to recover the Lean from. Read it before
restating anything. The encoding is downstream of a model we trust, and we do not have one
yet.

**So the work queue is short.** M0–M10 and M12 are done; M11 is parked. What is open:

| open | where |
| --- | --- |
| `Proofs/Merge.lean`'s `Action.SetWidthOk` against `Spec/Scope.lean`'s `WidthOk`, and the `ProgramLegal` clause that would let them be one predicate | `MERGE.md`, constraint (5) |
| `Database.DeclaredTerms` has no preservation lemma, so `WidthOk` funds nothing yet | `Spec/Congruence.lean`, `Proofs/` |
| `Matches.values` is split-blind and e-class-blind | `MERGE.md`, open question 1 |
| base sorts, in place of the single untyped `Term` | `MERGE.md`, constraint (5) |
| restating M11 against a reachable saturation condition | `ENCODING.md` |

**Where the library stands.** **Zero `sorry` and zero `sorryAx`.** `execM_contained` was the last
theorem depending on either and lost them at `04eb89e`; `execM_eq_exec` and `exec_programStep` were
already clean and are unchanged. The whole library builds, `Proofs/Lattice.lean` and
`Proofs/Counterexamples.lean` included, and difftest is **166 passed / 0 failed**. So the chain from
the egglog binary to `ProgramStep` is unbroken: difftest compares egglog against `execM`,
`execM_eq_exec` carries `execM` to `exec` on the constructor fragment, and `exec_programStep` is a
biconditional against `ProgramStep`. The 166 cases constrain the **specification**, not only the
interpreter.

### What is covered, and what is not

`execM_contained` bought its last two `sorry`s with a hypothesis rather than a weakening:
`p.UnionFree ∨ p.OrderingFree`. The conclusion and `FDatabase.ProgramLegal` are unchanged. The two
arms work differently — union-freedom makes the state diagonal, so `Cong` is equality and
`Recorded` *is* `Contained`; ordering-freedom makes `Expr.eval` congruence-stable, so a moved
environment computes congruent answers.

| | `union` | `:merge` functions |
| --- | --- | --- |
| `exec_programStep` | ✓ | ✗ — constructor fragment (`p.CtorDecls`) |
| `execM_contained` | ✓ via `OrderingFree` | ✓ |
| both at once | ✓ — unless the program also applies an ordering primitive | |

`min`/`max` are *not* restricted: congruent operands to them are those operands, by
`Cong.eq_of_isLit` under `WF.litsIsolated`, so the condition is ordering-free rather than
primitive-free and a `:merge` body of `(min old new)` is covered.

**The whole tested corpus is inside the theorem.** No rendered difftest case applies an ordering
primitive, so all 166 satisfy the second arm; 105 contain a `union` and would fail the first, and
the 64 carrying both a `union` and a `:merge` — what difftest exists to exercise — are admitted.
Excluded: only a program that applies `ordering-min`/`ordering-max` *and* emits an `Action.union`.
`encode` is not one — it uses `ordering-max` but emits no `union` — which is why both arms are
kept.

**A second, ordering-free arm is being added**, which would cover much of that gap: every generated
merge body is `min`/`max`/`old`/`new`, and `ordering-min`/`ordering-max` appear only under
`Encoding/`. Its shape is not settled and is deliberately not pinned here — what stays true either
way is the table above. One thing to check rather than assume: ordering-freeness is believed **not**
to reach `MergeStep.transport_recorded`, whose `mergeEnv` moves before any expression is evaluated,
and that belief is structural reasoning with no counterexample behind it (`MERGE.md`, "The
representative deviation").

**Why union-freedom is what buys the transports.** A `union` is the only action asserting an
equation between distinct terms, so a program with none never leaves a **diagonal** state, and there
`Cong` is equality: `Database.Recorded` *is* `Database.Contained` (`Recorded.contained_of_diag`),
along which the transports were already proved. `MergeStep.transport_recorded` and
`RuleResults.mono_recorded` are two-line compositions of that; both **lost** `A.WF` and **gained**
`C.Diag`, so they are incomparable to their old forms rather than weaker. `NoUnions.of_recorded`
pushes diagonality from the specification witness back onto the interpreter's state, so there is no
interpreter-side union-freedom lemma anywhere. It follows that on this arm the conclusion is a
`Contained` claim wearing `Recorded`'s clothes — the witnesses that force the contract onto
`Recorded` all `union` (`MERGE.md`, "Why `Recorded` is weaker than `Contained`"). `Recorded` stays
in the statement for the arm being added, not for the one that landed.

**It does not exclude M11**, which is why this arm was worth landing first. `encodeAction` turns a
source `union` into `.set @UF [ordering-max x₁ x₂] [ordering-min x₁ x₂]`: `encode` emits
`ordering-max` inside a rule action — the position an ordering-free hypothesis forbids — and no
`Action.union` at all. That was checked by a compiled proof, `encode_unionFree`, axioms
`[propext, Quot.sound]`; **that proof is one of the probes now missing from the tree**, and what
survives it is the argument at `Proofs/Merge.lean`'s "Union-freedom, and where it puts `Recorded`".

**`Database.Out.mono_recorded` is deleted as false** in every form that would serve. The queue row
that called it "a restatement, at the congruent key `Recorded` supplies" was wrong: `Out` reads the
key up to congruence but the value columns *syntactically*, and `Recorded` moves those too. What
replaced it is not a weaker lemma but the premise its consumer's caller already maintains —
`mergeOneOriented_mergeStep` and `mergeOneWith_mergeStep` take the two entries' `Out` facts, and
`mergeRound_contained`'s fold invariant discharges them.

This document mentions the encoding often because much of what we know about egglog came
from reading `egglog/src/proofs/`. Those are findings about egglog, which is what we are
modelling.

### The two contracts

`Spec/` is append-only: nothing is ever removed from `eqs`, which is the whole state that
grows, and a merge adds the combined entry *beside* the two it merged. `Impl/` has **two**
interpreters with **different** contracts, and confusing them wastes time:

| | merge phase? | contract |
| --- | --- | --- |
| `exec` (`Impl/Interp.lean`) | none | **exact, both directions** — `exec_programStep`, on `p.CtorDecls` |
| `execM` (`Impl/Merge.lean`) | yes, and it **deletes** from the row index | **containment** — `execM_contained`, on `p.UnionFree ∨ p.OrderingFree` |

`execM` is not a state the specification can reach, hence containment. Containment is
satisfied by a do-nothing implementation, and that is *fine for soundness* — the safety
property is "everything written is valid", so writing nothing is vacuously valid. What rules
out a degenerate implementation is difftest, not a theorem. `execM_current_of_lattice` was
meant to add machine-checked completeness for merges that are joins; it is **false as stated**,
refuted three ways in `Proofs/Lattice.lean`, and is now **deleted**. `Proofs/Merge.lean`'s "Two
statements removed rather than carried" says what a corrected statement has to carry, and notes it
may still be false for programs with rules. Until someone writes it, nothing machine-checked says
the merge interpreter finds anything at all.

### The consolidation arc — ✅ closed

M9 introduced a shadow of each M0–M8 notion. All four pairs have now collapsed, and the
answer was different each time, which is why the arc is worth keeping:

| M0–M8 | M9 shadow | how it resolved |
| --- | --- | --- |
| `Database`, `Action`, `Cmd`, `Rule` | `MDatabase`, `RowAction`, `MCmd`, `MRule` | merged outright — one of each |
| `Expr.eval`, `evalAction`, `evalActions` | `MEval`, `ActionStep`, `ActionsStep` | the **functional** side won, once reads became query atoms |
| `stepCmd`, `runProgram` | `CmdStep`, `ProgramStep` | the **relational** side won; the functional semantics was deleted |
| `Cong` | `MCong` | `MCong` deleted; the functional dependency is `Cong.congr`, a rule of the one relation |

The two step rows went opposite ways for one reason. Below an action nothing reads the
database — `Expr.eval` wants only a `Signature` — so evaluation is a function
unconditionally. Above an action `MergeStep` chooses *which* entries collide and
`MergeClosure` *how many* steps to take, and neither choice can be made by a function.
So `Spec/` has one evaluator and one action evaluator, both functions, under step relations
that stay relations by design. The functional half was deleted, and with it the standing
inconsistency that `CmdStep.action`'s merge phase had landed in the relation and not in
`stepCmd`. (The file now called `Spec/Step.lean` is *not* that half returning: it is
`Spec/Merge.lean` renamed, and it holds the relations.)

**The `Cong`/`MCong` row is the one worth reading, and it is now closed.** It was argued to be
blocked: collapsing the two was supposed to push `Database.CtorRows` hypotheses into the refinement
theorem. The blockage argument was wrong at both of the two steps it resolved in, and the deletion
cost `exec_programStep` nothing. `MERGE.md`, "Congruence is the functional dependency", has both
steps and what became of the one gap between the two relations.

### Which primitives, and why

`Prim` exists for one reason: so a `:merge` body can **compute**. Without it a body can only
select (`old`, `new`) or build a term, so there are no lattice merges and no analyses.

- **`min`/`max`** are what make `:merge` mean anything — every differential merge case uses
  them, `execM_current_of_lattice` is about them, and without them `:merge (min old new)`
  silently built the *term* `min(5, 3)`.
- **`ordering-min`/`ordering-max`** serve the encoding's union-find leader selection and
  nothing else. They are live: `Encoding/Encode.lean`'s `mergeBody` and `mergeResult` —
  the `:merge` shared by `@UF` and every view — are literally `(set (@UF (ordering-max old
  new)) (ordering-min old new))`, so `encode` cannot be stated without them. Only a
  union-find-free encoding would retire them.
  - They also carry the model's one deviation on merge results — `Term.blt` is structural where
    egglog's order is allocation order — and it is not repairable by a better operator, because
    **no** choice operator is congruence-stable across the two databases `Recorded` relates.
    `MERGE.md`, "The representative deviation", has the repros and the impossibility.

Dropping all four would take `Prim` out of `Expr.eval` entirely, which is the smallest the
semantics can be — at the price of `:merge` becoming decorative, with no lattice for the
completeness half to be complete about.

### Checking a change

Five theorems are load-bearing enough to check every time, with `lean_verify` (lean-lsp MCP) or
`#print axioms` rather than by grepping for `sorry` — it asks the kernel what a theorem actually
depends on and traces into Mathlib. Verified at `04eb89e`:

| theorem | axioms |
| --- | --- |
| `FDatabase.toDatabase_cong_mem` (`Impl/Interp.lean`) | **none at all** |
| `exec_programStep`, `execM_eq_exec`, `execM_contained`, `mem_closure_iff`, `Database.Recorded.trans` | `propext, Classical.choice, Quot.sound` |

The first is the canary the `Spec/` rewrite left behind: it is the bridge from the
interpreter's term list to the diagonal of `eqs`, every refinement theorem reads through it,
and it is short enough that anything appearing in its axiom set got there by accident. The second
row is the load-bearing one: `execM_eq_exec` and `exec_programStep` clean together are what make
difftest a check on `Spec/`. **`sorryAx` is no longer allowed anywhere**, which is a change from
"allowed at `execM_contained` until the transports land".

Statements known to be **false** carry compiling counterexamples in
`Proofs/Counterexamples.lean` and `Proofs/Lattice.lean`, so a refuted statement cannot
quietly come back — read them before trying to prove anything they refute. **Several refutations
the other documents cite by name are in neither file and in no file at all**: they were checked as
scratch probes and the scratch was not kept. That is the work queue's second row, and it is worse
than "unhomed" — `no_stable_choice`, `fst_stable`, `const_stable`, `orderingMin_not_stable`,
`cmin_not_stable`, `transport_recorded_false`, `recorded_iff_subset`,
`mergeRound_contained_needs_recorded`, `spec_never_distA` and `encode_unionFree` are prose now. Two
separate sessions have found a scratch file silently red, so this is a known failure mode rather
than bad luck.

Two traps that a green build will not catch. Writing `h.ge` for a set inclusion silently
pulls `Classical.choice` into every downstream axiom set. And `lake build` does not rebuild
the difftest executable — `lake build difftest` does, which `scripts/difftest.sh` handles but
a manual run may not.

## The Redex model this was ported from

**This section is the whole of the port record.** `Spec/`, `Impl/`, `Proofs/` and
`Tests/` name nothing here: the Lean development is meant to be read on its own, by
someone who has never seen the source model. Anything that only makes sense by contrast
with the source belongs on this page.

| source | role | Lean |
| --- | --- | --- |
| `Egglog` grammar | `Program`/`Cmd`/`Rule`/`Query`/`Pattern`/`Action`/`expr` | `Spec/Syntax.lean` |
| `Database = (Terms Congr Env Rules)` | global state: ground terms, equality pairs, bindings, rules | `Database` — but `sig`/`eqs`/`env`/`rules`, with the terms read back off `eqs`' diagonal |
| `Lookup`, `free-vars`, `Env-Union`, `Env-Union2` | environments | `Env.lookup`, `Expr.freeVars`, `Env.UnionAll`, `Env.Union2` |
| `Eval-Expr`, `Eval-Action`, `Eval-Global/Local-Actions`, `Eval-Actions` | actions add terms and equalities | `Expr.eval`, `evalAction`, `evalActions`, `evalLocalActions`, `RuleResults` |
| `Congruence-Reduction` + `restore-congruence` | refl/symm/trans/congr + "presence of children", to a fixpoint | `Cong` (no `refl` rule — reflexivity is an asserted equation), plus `Database.WF.subtermClosed` |
| `valid-env`, `valid-subst`, `valid-query-subst` | declarative e-matching ("pattern instance is equal to a witness term already present") | `ValidEnv`, `ValidSubst`, `ValidQuerySubst` |
| `valid-subst-faster` | operational e-matching, unused by the main relation | not ported |
| `U_d` | union of databases | `Database.sUnion` |
| `Command-Reduction`, `Egglog-Reduction` | run one command; run a program, restoring congruence between commands | `CmdStep`, `ProgramStep` |
| `typed-*` judgments | scope checking only (a single type `no-type`) | the `Scoped` family, `Spec/Scope.lean` |
| `test.rkt` | ~25 unit checks plus `redex-check` random testing | `Tests/Examples.lean`, `DiffTest.lean` |

### What the port changed, and why

* **`skip` is gone.** It exists only so `Command-Reduction` can signal completion to
  `Egglog-Reduction`. That two-level arrangement is there because `(run)` picks a set of
  substitutions nondeterministically; here the database's components are `Set`s, so the
  union is expressible directly and `RunRules` is a plain function. `CmdStep`/`ProgramStep`
  are still relations, but for an unrelated reason — the merge phase, not the match set.
* **`restore-congruence` is gone.** Congruence is the inductive predicate `Cong` rather
  than a closed set of pairs the state carries — see "Where 'restored congruence' went".
  Its "presence of children" half is the one part that *is* state, and it holds by
  construction because `Database.addTerm` inserts a term with all its subterms.
* **A `Signature` and `Cmd.decl` are new.** The source has no declarations at all and
  treats every applied name as a constructor. Here a name means nothing until it is
  declared, which is egglog's own declare-before-use, and it is what lets `:merge`
  functions be added without reshaping the AST.
* **A bare variable is no longer a fact or an action.** The source admits `expr = var`
  as a query fact, matching any term, and as an action, adding one already present.
  egglog's grammar admits neither — `parse error: expected fact`, `parse error: expected
  action`, `parse error: expected command` — so `Expr.IsApp` bans them. **Stricter than
  the source, not stricter than egglog**: the model matches egglog here and the source
  did not. It was a difftest finding, 34 of the first 60 generated cases.
* **`ValidEnv` is up to permutation.** `valid-env` pins `σ`'s bindings to the order
  `varset-union` happens to produce; `Perm` does not. The extra substitutions this admits
  differ from the pinned ones only by reordering, which no `lookup` can see —
  `Env.Agree.of_perm`, and `evalLocalActions_agree` lifts it to whole rule firings.
* **Appending environments replaces `Env-Union` in the one place it is used.** A
  pattern's free variables exclude the globally-bound ones, so the substitution's domain
  is disjoint from the globals' and the append cannot fail
  (`Pattern.freeVars_lookup_eq_none`).
* **`number` is `Int`,** not Racket's whole numeric tower.
* **`no-type` is a single untyped `Term`.** The source's type judgments check scope and
  nothing else, and so do these. A real sort discipline is deferred — `MERGE.md`, the
  closing section, has the shape it would take.
* **`valid-subst-faster` is not ported.** It is the source's operational matcher, unused
  by its main relation, and proving the two agree is a conjecture the source left open.
  The Lean model reaches an operational matcher from the other end instead:
  `Impl/Interp.lean`'s `matchQuery`, tied to `ValidSubst` by `exec_programStep`.
* **`set`, `Pattern.values`, `:merge` functions and multi-column outputs are all new.**
  None of them exist in the source; they are M9 and M11, designed in `MERGE.md`.

## Target design

Package `EgglogSemantics`; `README.md` has what each directory is for. As it landed:

```
Spec/      Syntax  Term  Database  Congruence  Eval  Match  Step  Scope
Impl/      Closure  Interp  Merge  Check
Proofs/    one file per Spec/ or Impl/ subject, plus:
             Counterexamples   compiling witnesses that a statement is false
             Lattice           the same for execM_current_of_lattice
Tests/     Examples  worked examples, as proofs and as #guards
           Egg       renders a Program as egglog source, for differential testing
Encoding/  Encode                         — parked M11; see ENCODING.md
Scratch/   one surviving witness file; outside the library, so outside `lake build`
```

`Spec/Eval.lean` is what a command *computes* and is `Option`-valued; `Spec/Step.lean` is
what a command *does* and is `Prop`-valued. That is the seam the whole file layout turns on,
and it is why there is no functional/relational pair anywhere in `Spec/`.

### Syntax

`Expr` and `Term` are nested inductives over `List`. `Term` gets a hand-written
induction principle (`∀ f args, (∀ a ∈ args, P a) → P (.app f args)`) written once
and used everywhere; recursive definitions use the mutual `Term`/`List Term`
pattern, which is the reliable way to get structural recursion through the
nesting. `Lit` is `Int` for now, deliberately a separate type so base sorts can be
added when merge functions arrive.

A `Cmd.decl` case and a `Signature` (`FnName → Option FnDecl`) go in **from day one**, with
Phase 1 theorems carrying an `AllConstructors sig` hypothesis. This is what keeps the
`:merge` extension from churning the AST. As it landed, `FnDecl` carries `arity`,
`outArity` and `merge : Option MergeSpec`, where `none` **is** what makes a name a
constructor and `MergeSpec` is `.merge (List Action) (List Expr) | .noMerge`. The draft
here had a third `MergeSpec.union` case for constructors; folding it into the `Option`
removed the state in which a name both had a merge specification and was a constructor.

### Database and congruence

The draft here had six fields, including a term set and (from M9) a row set. Both are gone.
**Four fields, and one of them carries three jobs:**

```lean
structure Database where
  sig   : Signature
  eqs   : Set (Term × Term)      -- asserted only, and never shrinks
  env   : List (Var × Term)      -- order matters: first binding wins
  rules : Set Rule
```

`eqs` records what a `union` asserted, *and* what exists — the reflexive equation `t = t` is
what it means for `t` to have been built — *and* every function's table, since a merge
function's entry at the key `a…` with value columns `v…` **is** the term `f(a…, v…)`.
`Database.terms` is then a `def` after the relation, `{t | Cong db t t}`, so every use site
reads unchanged.

A constructor's entry is `f(a…)` **alone**, with no value appended, because a constructor's
value is its own application. `FnDecl.entryWidth` is what decides which of the two shapes a
name gets, and `Database.DeclaredTerms` is the invariant that every application the database
holds has its declaration's width. Appending the value for a constructor as well would put
`f(as)` and `f(as ++ [f as])` in the state under one head at two widths, which makes that
invariant unstatable — `MERGE.md`, "Representation", has the argument.

`Cong db : Term → Term → Prop` is the inductive closure with `assert` / `symm` / `trans` /
`congr`. **There is no `refl` rule**: `Cong db t t` is derived from an asserted reflexive
pair like anything else, which is what makes being a *partial equivalence relation*
structural rather than a side condition restated in every docstring. `congr` is written as a
mutual inductive with a `CongList` companion rather than an `∀ i, i < length` premise — same
relation, workable induction — with a `List.Forall₂ (Cong db)` bridge lemma.

A congruence-restoring pass **disappears entirely**, which is the main simplification:

- symm/trans/congr become `Cong`'s constructors, and reflexivity becomes an assertion.
- "presence of children" becomes a structural invariant: `Database.addTerm` records a term
  together with all its subterms, and `Database.WF` asks for subterm-closedness, that every
  present term is self-equal in `eqs` (`eqsRefl`), and that every binding's value is present.

This is observationally equivalent because no action ever consults congruence, so
deferring subterm insertion to a later rebuild is unobservable — recorded in the
source as a documented deviation with that justification.

**`eqsRefl` is a real invariant, not bookkeeping.** Without it a term can be present by
`symm`/`trans` alone, and then `addTerm` on a term the database already holds is not the
identity. Since `MergeSaturated` is "every step is a no-op" and every entry collides with
itself, a state missing one reflexive equation is not `MergeSaturated` however settled it
looks. `eqsInTerms` came out of `WF` in the same move: it is now the free theorem
`eqsInTerms_free`, `h.trans h.symm`.

### Where "restored congruence" went

There is deliberately **no closed-equality state**, and no "the reduction can no
longer step" predicate. The database always holds only asserted equalities, and
closure is a predicate rather than a state. Its two halves are handled
differently:

- The **relation** half is never materialized. Two places consult congruence:
  `Matches`' side conditions, which ask `CongOn` — `Cong (db.withOperands ts)` — for a
  derivation directly, and `MergeStep`, which compares two entries' keys with `CongList`.
  Evaluating an action never consults it at all.
- The **term-set** half ("presence of children") is a real state change, and stays in the
  state — as the `addTerm`/`WF.subtermClosed`/`WF.eqsRefl` invariants above.

The observable meaning of a finished program is therefore `Cong db` and nothing else: the
term set is its diagonal, so the pair this section used to name has collapsed to its second
component.

This section used to sketch a `restore` that materialized the closure as a
comprehension over the relation, for the executable layer to use. **M10 answered it a
different way and the sketch is dropped:** `Impl/Closure.lean`'s `closure` computes the
closure over a `Finset` and `mem_closure_iff` proves it decides `Cong` exactly, so no
state ever carries a closed equality set — not even the interpreter's.

The e-graph as a *data structure* — a set of e-classes rather than a relation — is
then `Quotient` of `db.terms` by `Cong db` (an equivalence on `db.terms` by the M2
lemmas). That quotient is the bridge to M11: an e-class on this side corresponds to
an `@UF` leader on the encoded side.

### E-matching

The witness formulation: a substitution is valid when the pattern instance is
`Cong`-equal, *in the database extended with that instance*, to some witness term
already in the database. The witness is what forbids matching a term the e-graph
does not contain, and it is what `Proofs/Counterexamples.lean`'s `not_matches_empty` checks is not
vacuous.

Two deviations, both recorded elsewhere and neither closed: `ValidEnv` fixes the domain only up to
permutation ("What the port changed", and M8's agreement lemma is what makes it harmless), and the
row atom `Matches.values` is split-blind and e-class-blind (`MERGE.md`, open question 1).

### Steps

Because the database's components are `Set`s, an indexed union over *all* matching
substitutions is directly expressible, so the rule-firing half of a round is a function
rather than a nondeterministic relation:

```lean
def RunRules (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ RuleResults db r}
```

`sUnion` is left-biased on `env` and `rules`; `evalLocalActions_env` and
`evalLocalActions_rules` show every `d` in that set has `d.env = db.env` and
`d.rules = db.rules`, which is what makes the bias harmless.
`RuleResults`' `Option` carries the partiality of variable lookup;
`Proofs/Scope.lean`'s `programStep_isSome` proves well-scoped, evaluable programs never
hit `none`. What the draft got wrong is one level up: a command is *not* a function, because
`CmdStep` composes the deterministic `cmdEffect` with a merge closure that chooses how many
steps to take. That is the whole of the relational layer —

```lean
def CmdStep (db) (c) (db') : Prop := ∃ d, cmdEffect db c = some d ∧ MergeClosure d db'
```

— and it is a `def`, not an inductive, because there is nothing per-command left to say.

`Cmd.decl` updates `db.sig` and nothing reads it yet, so declarations are inert in
this phase — the point is that M9 turns them on without touching the AST or any
`match` over `Cmd`. (M9 turned them on further than expected: a merge phase now follows a
declaration too, which is sound only because the front end checks a `:merge` body's names —
`MERGE.md`, "The merge phase runs between commands".)

## Milestones

The port proper — **all of M0–M7 is done**, `lake build` is clean and `sorry`-free.

| | file | notable |
| --- | --- | --- |
| M0 | scaffold | Mathlib `v4.32.2` on Lean `v4.32.2`; `make lean-check` kept out of `make check` |
| M1 | `Syntax`, `Term` | `Term.recTerm`, the induction principle through the `List Term` nesting |
| M2 | `Database`, `Congruence` | `Cong.le`, the least-congruence principle |
| M3 | `Eval` | `Expr.eval_agree` — evaluation reads the env only through `lookup` |
| M4 | `Match` | `ValidEnv`, `Env.UnionAll` |
| M5 | the step relations | `RunRules`, `CmdStep`, `ProgramStep`, in `Spec/Step.lean` |
| M6 | `Scope` | `programStep_isSome` — a well-scoped, evaluable program runs to completion |
| M7 | `Examples` | the worked examples as closed proofs |

Two of those carry more weight than their size suggests. **`Cong.le`** is how every *negative*
fact about the closure is proved — "this pair is not derivable" means exhibiting a congruence
that omits it — and it is the shape the M11 checker-soundness argument would take. A design
without it cannot state a negative fact at all. **`evalLocalActions_isSome_of_scoped`** says a
well-scoped rule contributes on every substitution its query admits; `RunRules` silently drops
stuck firings, so that is the statement worth having rather than mere totality.

Follow-ups, in rough dependency order:

- **M8 — metatheory.** Partly done.
  - ✅ *Environment agreement.* `Env.Agree.of_perm` and `.append_left`,
    `Database.EnvAgree`, and `evalAction_envAgree` / `evalActions_envAgree` /
    `evalLocalActions_agree`. This is `Expr.eval_agree` lifted to whole action sequences,
    and it discharges both places the semantics is deliberately loose about environments:
    `Env.UnionAll` leaving a variable bound twice, and `ValidEnv` fixing a domain only
    up to permutation. The payoff is that `RunRules` sees a substitution only up to
    agreement, so an enumerator may emit one representative per class — which is exactly
    what `Impl/Interp.lean`'s `Env.canon` does.
  - ~~*Rounds.* `runRounds`, `runRounds_succ'`, `Saturated`~~ — **deleted with the functional
    semantics.** `Cmd.run` is one round and `(run n)` is `n` copies of it, which `CmdStep` says in
    one line; schedules are still unmodelled.
  - ~~`ValidSubst` inversion, without which no example can state what a `run` does *not*
    produce~~ — **superseded by M10.** `exec_programStep` makes any statement about a
    *specific* program's result decidable, by transferring it to the interpreter where the
    closure computes. Inversion is still wanted for statements quantified over *all*
    programs, which is where M11 will need it.
  - Remaining: nothing on the critical path. The matcher is the slow one by
    construction — `assignments` is `|terms| ^ |vars|` and `patternHolds` recomputes a
    closure per candidate — which is what keeps the differential cases tiny. The fix is
    **not** a cleverer *specification*: `exec_programStep` is the contract, so the
    reference implementation can be optimized wherever profiling says it is slow and the
    refinement re-established against the unchanged spec.
- **M9 — `:merge` functions.** Designed in [`MERGE.md`](MERGE.md). Partly done, and
  **merged into the main development** — there is one `Database`, one `Action`, one
  `Cmd`, and `Spec/Step.lean` holds only what is genuinely new.
  - ✅ *Congruence is the functional dependency* — and it ended up being a **rule** of
    `Cong`, not a theorem about it. A constructor's entry is its own application, so "two
    entries with congruent keys have congruent outputs" is `Cong.congr` read at that term,
    with no hypothesis. The route went through a second relation `MCong` carrying the
    dependency as a constructor, then a theorem `Cong.fd` under a row-shape hypothesis;
    both are deleted — see "The consolidation arc".
  - ✅ *The shape change.* A `:merge` body is an action list, so `MergeStep` is a relation
    on databases and `CmdStep`/`ProgramStep` are relations too. `Spec/Step.lean` holds
    `Database.Out`, `MergeStep`/`MergeClosure`/`MergeSaturated`, `Database.NoMergeOk` and
    the step relations; the matching family (`Matches`, `ValidSubst`, `ValidQuerySubst`) is
    `Spec/Match.lean` and `Database.Recorded` sits beside `CongOn` in
    `Spec/Congruence.lean`; `Prim` and `Term.blt` are in `Spec/Term.lean`. Evaluation was
    *also* a relation for a while, because a non-constructor application in an action was a
    lookup; that is now forbidden — see "Reading is a query atom" below — and `Expr.eval` is
    a function again.
  - ✅ *Multi-column outputs.* `Action.set` takes a `List Expr`, and `Pattern` gained
    `values` — egglog's lowered row atom `f(a…, v…)`, written `(= v (f a…))` at one value
    column and `(= (values v…) (f a…))` at more. It is the only read in the language.
  - ✅ *The implementation deletes; the specification does not.* The contract was to split three
    ways: containment (`execM_contained`), the untouched equality on the constructor fragment
    where the merge pass is the identity (`FDatabase.mergeRound_eq_self`), and `Database.Current`
    for lattice merges. **The third never held** — see "The two contracts" — so two of the three
    stand. `MERGE.md` has what is and is not deleted.
  - ✅ *The refinement chain.* **Nine of its seventeen statements were false as written** —
    three in ways their M10 counterparts in `Proofs/Interp.lean` had already solved, so read
    the M10 counterpart before stating an M9 lemma. The five with a defect *in the statement* are
    now **deleted**, each with its defect written up where it stood; `MERGE.md`'s status block
    names them. The port then found three more that were false rather than stale —
    `Cong.mono_recorded` in its old shape, the `ValidEnv`/`ValidSubst`/`ValidQuerySubst` family at
    the same substitution, and "a run under a congruent environment records the run under the
    original". Two more joined them since: `MergeStep.transport_recorded` at an arbitrary recorder,
    and `Database.Out.mono_recorded` in every form.
  - ✅ *The three `Recorded` transports.* Closed two ways: one deleted as false, with its consumers
    handed the premise their caller already maintained, and two proved as compositions under
    `p.UnionFree ∨ p.OrderingFree` — "What is covered, and what is not". **Everything M9 named is done**, and what
    is left is coverage rather than proof.
- **M10 — executable layer.** A `Finset`-based interpreter, a decidable congruence
  closure, and a refinement *biconditional* between the interpreter and `ProgramStep`.
  Proved end to end. Five design notes are worth more than the lemma inventory, which is
  in the code:

  - **The closure is deliberately the obvious algorithm.** `congStep` is one round of
    one-step-derivable pairs over `terms ×ˢ terms`; `closure` iterates by well-founded
    recursion on how much of that universe is missing, and `mem_closure_iff` shows it
    decides `Cong` exactly (completeness by `Cong.le` against the fixpoint). Union-find
    with upward merging is what egglog does and what the M11 theorems are *about* — using
    it here would put the thing under study inside the thing doing the studying. Stopping
    only at a fixpoint is what makes `Cong.le` applicable, hence well-founded rather than
    fuel-bounded.
  - **`FDatabase` uses `List`, not `Finset`**, because `Finset.toList` is noncomputable and
    the interpreter must enumerate. Duplicates are harmless: the denotation is the set of
    members.
  - **The enumerator departs from the spec on purpose, twice.** The spec takes one
    substitution per pattern and joins them (`Env.UnionAll`); the enumerator assigns
    the whole query's free variables at once and restricts per pattern with `Env.canon`.
    `Env.agree_canon` shows they agree up to `Env.Agree`, which is all `RunRules` can see,
    and both directions are stated (`validQuerySubst_of_mem_matchQuery` and
    `mem_matchQuery_of_validQuerySubst`). The second departure came with the entry rewrite:
    `matchQuery` assigns from `FDatabase.valueTerms`, not `terms`, so a variable is never
    bound to a *merge function's entry term* — which `Spec/Match.lean`'s `ValidEnv` permits,
    since it asks only for membership. Firing on fewer substitutions is the safe direction.
    It costs `exec_programStep`'s *statement* nothing, because the two coincide exactly where
    that theorem lives: on an `AllConstructors` signature no name has a merge, so `valueTerms`
    filters nothing out. It does cost the reverse direction a hypothesis — **settled**:
    `mem_matchQuery_of_validQuerySubst` takes `AllConstructors`, which is what closes the gap, and
    so do `patternHolds_iff`, `mem_matchQuery_iff` and `validQuerySubst_of_mem_matchQuery`. All
    four sit under callers that already carry it, so nothing reached the top level. On the M9 side
    it is a genuine refinement and nothing is owed, since the contract there is containment.
  - **`Env.UnionAll.refines_of_mem` had to carry self-refinement, not `Nodup`.** Appending
    two substitutions sharing a variable duplicates it in the domain while leaving every
    lookup intact, so `Nodup` is not preserved by a `Union2` step and
    `∀ b ∈ ρ, lookup b.1 ρ = some b.2` is.
  - **Fold lemmas need a closed step term.** `execRunRules` was refactored into named
    `fireInto`/`fireRule` steps so `mem_terms_foldl` and friends can be instantiated at
    them; inline lambdas leave the lemma's step as an uninferable metavariable.

  Well-founded definitions are sealed against kernel reduction, so `decide` cannot see
  through `closure`. Use `#guard` (a command, so it enters no proof term) or `unseal
  closure`. **Not** `native_decide` — it adds `Lean.ofReduceBool` to every downstream axiom
  set. The interpreter runs whole programs as `#guard`s in `Examples.lean`, including the
  two-round `Wrapper` case, which has no hand proof because stating it needs `ValidSubst`
  inversion.

  The chain ends at

  ```lean
  theorem exec_programStep {p : Program} (hdecl : p.CtorDecls) {D : Database} :
      (exec p).map FDatabase.toDatabase = some D ↔ ProgramStep Database.empty p D
  ```

  **One** hypothesis, which arrived when the spec's command stepping became a relation, and
  it is not decoration: `Falsity.exec_programStep_needs_ctorDecls` exhibits
  `(function f () i64 :merge 7) (set (f) 0)` — a program whose only offence is a `:merge`
  declaration — where the entry collides with *itself*, since `MergeStep` has no `a ≠ b`
  guard, so `ProgramStep` reaches two distinct states and `exec` returns at most one.

  **A second hypothesis `p.SetLegal` sat here and is gone.** *Settled:* the refinement does
  not need it, and the reasoning first recorded for why was wrong. `SetLegal` was said to
  re-establish the row invariant `Database.CtorRows`; what the induction actually
  re-establishes is `Database.CtorState` — `WF` and `AllConstructors` — and a `set` disturbs
  neither. `CtorRows` is now deleted outright, so nothing is left to be confused about: what
  `SetLegal` buys is stated in `Spec/Scope.lean`, and it is the *entry width* invariant
  (`Database.DeclaredTerms`), which the refinement does not read either. Five other theorems
  dropped the hypothesis in the same pass. Well-formedness came free throughout:
  `FDatabase.WF` is *defined* as the spec's through `toDatabase`, so every `WF` fact is read
  through the refinement rather than proved by a separate induction.

**M10 is done**, and that is what makes the `#guard`s in `Examples.lean` and the
differential cases constrain the *specification* rather than only the interpreter. Before
it they sat on the interpreter's side of an unproved gap.

  Two obligations writing the implementation forces:
  1. *Enumeration completeness* — the spec's `{σ | ValidQuerySubst db q σ}` against an
     enumeration of `freeVars → terms`. Prepared by `ValidEnv.mem_dom_iff` (the domain
     is precisely the free variables) and `mem_terms`.
  2. *Order-insensitivity* — ✅ discharged by M8's agreement lemma.

  *Finiteness* is **not** an obligation: the implementation is a `Finset` function by
  construction, so finiteness of the spec's output falls out of the refinement theorem
  as a corollary rather than needing to be proved first.

### Differential testing — ✅ running

`make lean-difftest` (`scripts/difftest.sh`) compares the Lean interpreter against the Rust
binary. **166 cases pass**: 60 random constructor, 30 random `:merge`, 76 curated (10
constructor, 66 `:merge`).

The oracle is **`(print-size)`**, one row count per function — the same quantity
`egglog/tests/files.rs` snapshots. egglog's table for `f` holds one row per distinct
*canonical* argument tuple, so the Lean-side quantity is the number of congruence classes of
`f`-applications. `DiffTest.lean` writes a `.egg` file and the predicted counts; the script
runs egglog and diffs, one invocation per case with a timeout.

**No egglog test file is portable.** Of the 104 in `egglog/tests`, zero are in the fragment:
`function` appears in 47, `relation` 35, `constructor` 35, `sort` 32, `set` 31,
`run-schedule` 21. `before-proofs.egg` is closest and needs only a `Lit.str` constructor and
`(rewrite lhs rhs)` desugaring.

**This is the only check that the model matches egglog rather than matching itself** — and it
has caught things no proof would. The specification, not the implementation, was wrong about
merging between commands (`MERGE.md`).

Three generator lessons, each learned from a green suite that was not testing what it looked
like:

* A freely generated pattern almost never matches, so 31 of 60 cases gave an identical
  trivial profile. Patterns are now built by *abstracting subterms of a term the program
  actually builds*, which guarantees the rule fires.
* `pick` read an LCG's low bits, which have period 4 — all 30 merge cases emitted an
  identical program.
* Hence the script prints the **row-count distribution** every run. A pass count alone hides
  a generator that has stopped exercising anything; treat a narrowing distribution as a
  regression even if the count rises.

Two findings that the fragment was **not a subset** of egglog's language: a bare variable
was a legal query fact and `expr` action here and egglog's grammar rejects both (34 of the
first 60 cases died on it — now banned via `Expr.IsApp`; "What the port changed" has where
that laxity came from); and `Database.rules` is a `Set`, so a repeated rule is silently
ignored where egglog panics.

**Every case is checked for legality before it is written.** `writeCase` refuses to emit a program
egglog would reject, on four counts: an illegal `set` (`Program.illegalSets`), a use whose column
counts disagree with the declaration (`Program.arityErrors`, over `Impl/Check.lean`'s `arityOk`), a
read outside a query atom (`Program.illegalReads`, over `Cmd.noLookup`), and a name used at two
arities, which the emitted `datatype` header cannot express (`Program.arityConflicts`). A rejected
program is a *missing* case, not a failing one, so each check aborts rather than skips.

What it does not cover: anything outside the fragment, and value columns, since
`(print-size)` counts key classes and is blind to them.

A performance note that is really a design note: `FDatabase` insertions deduplicate, because
a round's `union` copies every operand's terms and without dedup the per-substitution
`List.toFinset` inside `closureF` goes quadratic. Invisible to `toDatabase`.

- **M11 — the proof encoding.** Parked. See below.

- **M12 — one semantics. ✅ Done.** M0–M8's functions and M9's relations ran side by side
  over the one `Database` and the one `Action`. `Spec/` now defines egglog **once**:
  `Expr.eval`/`evalAction`/`evalActions`/`cmdEffect` are functions, `MergeStep`/`CmdStep`/
  `ProgramStep` are relations, the functional command semantics is deleted, and `Cong` is
  the only congruence. What was learned:

  - *Determinism is what reopened it.* Evaluation's uniqueness came to hold with **no**
    hypotheses — no `AllConstructors`, no `NoPrim` — because the only rule that read the
    database was `lookup`, and reading became a query atom. A relation that is a function
    unconditionally can simply be replaced by one.
  - *What must stay a relation.* Everything above an action, for a reason that has nothing
    to do with evaluation: `MergeStep` chooses **which** pair of entries collides and in
    which order, and `MergeClosure` chooses how many steps to take.
  - *The cost, as it came out.* Going the functional way below an action was right: the
    `Option` algebra `Proofs/{Eval,Match,Step,Scope,Interp}` is built on survived, and
    `Impl/Merge.lean` lost its whole evaluator, action and matching layer to
    `Impl/Interp.lean`'s. `Proofs/Scope.lean` paid for it: `Expr.eval` returns `none` at a
    lookup and at a mis-sorted primitive, so `Evaluable` threads a `Signature` beside
    `Scoped`'s scope, and `programStep_isSome` takes both.
  - *The recovery, intact.* `exec_programStep` is a **biconditional** on the constructor
    fragment, and that is what makes the differential cases bear on the specification
    rather than only on the interpreter. It holds there because that fragment has no
    `.merge` function, so no `MergeStep`, so `ProgramStep` is deterministic
    (`ProgramStep.det`).

## Extending with `:merge` (M9)

The design is [`MERGE.md`](MERGE.md), whose header has what that file argued for and what became
of each. One fact belongs here rather than there, because it is what makes M9's whole shape a
statement about *our* egglog: **a merge body is an action list, not an expression**, an extension
local to this repo (`egglog/src/ast/parse.rs`, `9828dbf`), deliberate and discussed in the paper.
Upstream `:merge` takes a single expression, so a body that `set`s another table cannot be written
there at all. That is why the observable value of a key class cannot be a fold over asserted
entries, why there is no `SemilatticeSup` to lean on, and why command stepping is a relation.

What this plan got right: the signature was in the AST from M1, so `MergeSpec` only had to become
reachable; congruence really is the functional dependency; merge closure carries no termination
claim. What it got wrong is the *representation* — a row set was added and then removed again, and
a function's table now lives in the term structure itself. Base sorts are still deferred.

## Reading is a query atom

**All reading happens in the query; all writing happens in the actions.** An application of
a non-constructor is a *lookup* — it reads a recorded entry rather than building a term — and
`Impl/Check.lean`'s `Program.noLookup` says a program contains none, anywhere. The one place
a program reads is the query atom `Pattern.values`, which is egglog's lowered
`f(a…, v…)` and now covers every width: `(= v (f a…))` at one value column,
`(= (values v…) (f a…))` at more.

**What it buys.** Evaluation loses its `lookup` case, so it needs nothing of the database
but its signature and is a **function** again — `Expr.eval : Signature → Expr → Env →
Option Term` — and with it `evalAction`/`evalActions`. That is what closed M12. What remains is
that the query atom itself over-approximates, in two ways: it matches *any* recorded entry where
egglog matches the current one, and it is **split-blind and e-class-blind** — `MERGE.md`, open
question 1.

**Where it is stricter than egglog, checked against the binary.** egglog runs
`check_no_function_lookups_in_actions` (`src/typechecking.rs:1325`) on a **rule head** only,
and only for a seminaive rule. Three other positions read there and are rejected here:

| position | egglog | repro |
| --- | --- | --- |
| top-level action | accepted, copies the value | `(set (Copy (A)) (Dist (A)))` |
| `:merge` body | accepted; missing row is `Lookup on Zero failed in the merge function for Dist` | `(function Dist (Math) i64 :merge (max old (Zero)))` |
| nested in a query fact | accepted, flattened to two atoms | `(F (Dist k))` |

The first two are `Context::Full` and `Context::Write`, neither of which runs the check; the
third is egglog's query flattening, which this model does not have *as syntax*. Each has a flat
equivalent — `(rule ((= v (Dist k))) ((set (Copy k) v)))` for the first — so the loss is
notation, not expressiveness, except in the `:merge` body, where a body that reads another
table genuinely cannot be written.

Flattening's *effect* on a constructor operand is modelled, and has to be: `Matches.values`
adds the atom's operands to the database before consulting congruence, so `(Dist (G (A) (B)))`
matches an entry written at `(G (B) (A))` after `(union (A) (B))` exactly as the flattened
`G(a, b, x), Dist(x, o)` does — the intermediate class is found by matching rather than by
having been built. `DiffTest.lean`'s `read-unbuilt-key*` cases pin it in both directions.

**What it exposed in `Encoding/Encode.lean`.** `encodeBuild` interns an application by `set`ting
the view and then *reading it back* with `(let x (@fView c…))` — a lookup in a rule head,
which egglog refuses. egglog does the same job with `set-if-empty-<View>!`, registered as a
**primitive** (`src/proofs/proof_fresh.rs`), and `expr_has_function_lookup` flags only
`ResolvedCall::Func`. So `encode` emits rule heads the real system rejects, and the fix is
the one egglog made: a `Prim`-style get-or-insert, which is a write. Recorded in
`Encoding/Encode.lean`, not done — it is M11 work.

## The minimal proof encoding (M11-min) — the road not taken

**A design record, superseded.** `Encoding/Encode.lean` builds the *full* encoding — `@UF`,
per-constructor views, rebuild rules, path compression — and the three theorems were stated over
that, then deleted (`ENCODING.md`). Of what this sketch proposed dropping — the union-find, the
view tables, the proof skeletons — **only the third held**, and structural fresh ids are what
replaced `get-fresh!`. It is kept for the three things below that are still current, and because a
union-find-free encoding is the only thing that would retire `ordering-min`/`ordering-max` and with
them a congruence-instability that **no** operator repairs (`MERGE.md`) — the only way the model as
a whole escapes it, though not the only way M11 does (`ENCODING.md`).

**Proved against the specification, not against the Rust.** That is the decision that makes
this tractable, and it did carry over: no differential testing against real egglog, no
matching its row counts, no conversion layer. The claim is about our `encode` and our
`Cong`.

### The side condition that makes it work

Since the source constructors carry over, built-in congruence still applies to them in the target,
which would mean some equalities have no rule behind them. That collapses to nothing **provided
`encode` emits no `union` actions**, which it does not — the same fact that puts encoded programs
inside `execM_contained`'s hypothesis. `ENCODING.md`, "What survives", has the exact statement and
why the obvious phrasing of it is wrong.

### What a proof value is

egglog's **user-facing** `Proof`, not `RawProof`; `CHECKER.md`, "Node kinds", has the eight
`Justification`s, what checking each needs, and which five the constructor fragment actually
uses. They map onto `Cong` almost one for one — `Fiat`/`Rule`/`Trans`/`Sym`/`Congr` against
`assert`, a rule firing, `trans`, `symm`, `congr`, and `MergeFn` against `MergeStep` — which is
why checking is a structural induction with no conversion layer, the payoff for `Cong` being
inductive rather than a computed closure, and why dropping the skeletons costs nothing (they
exist to make proofs *small*, not checkable).

Two mismatches to settle before writing `encode`:

- **`Congr` is incremental, `Cong.congr` is n-ary.** egglog extends `t1 = f(…, ci, …)` to
  `t1 = f(…, c2, …)` one `child_index` at a time; ours takes a whole `CongList`. They are
  inter-derivable — n chained steps make one of ours — but the proof *terms* differ in
  shape, so matching the user-facing type needs a bridging lemma by induction on the child
  list. This is the one place the correspondence is not definitional.
- **Reflexivity is not assumed, and the agreement got exact.** "A proof of `t = t` must
  correspond to some `t` added at the top level." `Cong` has no `refl` rule at all now:
  `Cong db t t` holds only where an equation puts it, and the only thing that writes one is
  `addTerm`, on a term the program built. The discipline is the definition.

### The invariant is a precondition of the encoding, not just a style rule

`ProofEncodingUnsupportedReason` (`src/proofs/proof_encoding_helpers.rs:851`) lists
**`FunctionLookupInAction`** — "action contains a function lookup. Finding the output of a
function is only supported in queries" — and **`UnsafeSeminaive`** — "Arbitrary RHS database
reads are not representable by the term/proof encoding." egglog's own encoder *refuses* a
program that reads on a right-hand side. So "reads in the query, writes in the actions" is
not merely egglog's default typechecking rule; it is what the proof encoding requires in
order to exist.

Its three theorems are the next section's, restricted. Its cost is size: without
canonicalization the encoded database is much larger — transitivity and congruence generate
quadratically many `@Eq` rows and nothing dedups them. Fine for a semantics, which is about
what is *derivable*, but row-count claims are out.

## Path to the full proof-encoding theorem (M11)

With M9 in place, the encoding becomes a translation between two instances of the same
semantics. **This is what was built, stated, and then cut back to the encoder alone**:
`Encoding/Encode.lean`'s `encode` survives; the three theorems below were stated over it
and deleted. [`ENCODING.md`](ENCODING.md) has why and what a restatement must avoid;
[`CHECKER.md`](CHECKER.md) scopes the checker half.

Three theorems, in increasing order of what they buy:

1. **Every proof the encoding writes is accepted by the checker** — for every `@Proof` row
   in the state `ProgramStep` reaches on `encode P`, `Checks` holds. About the *encoder*,
   with no reference to the source semantics, so it is what would catch a proof row written
   with the wrong column or a `@Congr` at the wrong child position.
2. **The checker is sound** — `Checks p` and `p` concludes `a = b` gives
   `Cong src ⟦a⟧ ⟦b⟧`. With (1), every stored proof witnesses a real equality.
3. **Simulation** — `Cong src a b` iff `a` and `b` share an `@UF` leader in the target.
   `⇐` is (1)+(2) at the union-find; `⇒` is completeness and needs the rebuild to have
   saturated. All three were stated with `src`/`tgt` the two states
   `ProgramStep Database.empty` reaches on `P` and `encode P`; the shape carries over, and
   what does not is `Rebuilt` as the saturation hypothesis for (3).

`Cong` being inductive is what makes all three tractable: all five justifications the
constructor fragment needs map onto `Cong`'s constructors, so (2) is a structural induction
on the proof and (3)'s `⇒` an induction on the `Cong` derivation. This is the reason the
whole development uses a derivation relation rather than a computed closure.

**Fresh ids are structural.** An earlier draft said to add an id supply to the target; that
was unnecessary. Terms *are* the ids — the id for `f` over canonical children `cs` is the
term `.app f cs`, the skolem encoding of `get-fresh!` — so source terms and target ids share
one type and the simulation theorem needs no correspondence relation. The cost is in row
counts, not equalities: egglog mints per construction *site* and so holds strictly more
`@UF` rows.

**Naive, not seminaive.** This port returns *all* matching substitutions where egglog
returns only new ones. Deliberate: a reference semantics should be simple, and a naive round
fires a superset of a seminaive one, so "every proof row written is valid" covers rows the
real encoder never writes. It bites only claims about row *counts* — and, once merges are
not idempotent joins, the number of firings does change the result, so the two genuinely
diverge there. M9's over-approximation is the same trade for the same reason
([`MERGE.md`](MERGE.md), "The framing").

Other omissions, unaddressed since the port: schedules, extraction, containers.

## Verification

- `cd semantics && lake build` — the whole development typechecks, and that is the state to keep.
- `make lean-difftest` — 166 cases against the real egglog binary. Watch the profile
  distribution, not only the pass count. It reaches `Impl/` through `Tests/Egg.lean` without
  touching `Proofs/`. It shares one scratch directory, so two runs at once will report spurious
  failures.
- `make lean-check` additionally fails on any `sorry`. There are none, so it is a regression check
  rather than a count: any hit is new.
- Axioms, on every change: `lean_verify` or `#print axioms` against the table in "Checking a
  change". A green build does not catch an axiom leak.
- `Tests/Examples.lean` compiling *is* the M7 suite — each check is a closed proof or a
  `#guard`.

## The front end's six checks

`Spec/Scope.lean` holds `Scoped`, `Evaluable`, `SetLegal`, `WidthOk`, `DeclsFresh` and
`MergeDeclared`. They are **six separate predicates**, and each threads exactly what it needs:
`Scoped` a `Scope`, extended by a `let` and by a query; the other five a `Signature`, moved only by
`Cmd.sigBind`. Folding the signature ones into `Scoped` would put a signature argument on
every lemma in `Proofs/Scope.lean` that none of them would use, and the theorems take
different subsets anyway — `programStep_isSome` wants `Scoped` and `Evaluable`, the state
invariants want `SetLegal`, `WidthOk` and `DeclsFresh`.

**They are written out, not generated.** A `Check` record used to parameterise one traversal
by three questions and three context binders, with four instances and fourteen `inherit_doc`
aliases giving them their real names. Nothing in `Proofs/` or `Impl/` was ever generic over
it — the aliases were its entire public surface — so the genericity bought nothing and cost
a five-definition indirection to read what `Program.Evaluable` means. It also charged proof
effort for sites it had nothing to ask: the walk made `Rule.Evaluable` elaborate to
`(∀ p ∈ r.query, True) ∧ …`, and `DeclsFresh`'s `.rule` case a five-line induction over a
question that does not exist. Written directly those are `Actions.Evaluable r.actions sig`
and `trivial`. Deleted; all 15 exported names kept their types and argument order.

**`set` legality, and the widths beside it.** A constructor's entry is `f(a…)` alone, so
`(set (f a…) v)` would record `f(a…, v)` — an application of `f` one column too wide for its
declaration, which `Database.DeclaredTerms` forbids. `Action.SetLegal` is the syntactic check that
keeps that out, and its condition is `mergeOf f ≠ none`: it admits `:no-merge`, rejects an
undeclared name, and rejects a constructor, all checked against the binary. egglog restricts `set`
the same way, as a type error (`egglog/src/constraint.rs`).

**`SetLegal` alone does not make the entry-width claim**, and `WidthOk` is why it is a sixth check
rather than a clause of an existing one. `SetLegal` decides *which* width an entry is held to —
`FnDecl.entryWidth` is `arity` for a constructor and `arity + outArity` otherwise — and `WidthOk`
supplies the counts; only the two together say every entry has its declaration's width, and alone
`SetLegal` says nothing about an entry no `set` wrote. Four independent needs forced it:
`DeclaredTerms` is **false** without it, `FDatabase.IndexOk.width` has nothing funding it,
`MergeStep.collide`'s two `arity` premises are unfunded, and `Proofs/Merge.lean` had re-introduced
a local copy. It sits beside `SetLegal` and not inside `Evaluable` because egglog raises arity as a
*type* error on the same AST node, in the same pass, that raises `SetConstructorDisallowed`
(`constraint.rs:924-938`, `TypeError::Arity`; the parser holds no `TypeInfo`), and because
`Evaluable` structurally could not say it — it quantifies over `Expr.fns`, a list of *names* that
has lost the application structure. It is also the second check that walks into a `:merge`, since
`res` is what `MergeStep` writes into the value columns.

*What they buy, and what they do not.* Neither is a hypothesis of the refinement theorem — see M10,
where `SetLegal` was removed. They maintain a state invariant (`DeclaredTerms`, the entry widths)
that the refinement does not read. **Nothing outside `Spec/Scope.lean` consumes `WidthOk` yet**:
`Proofs/Merge.lean` carries `Action.SetWidthOk`, its `set` clause alone, because substituting the
whole check makes `Action.WriteLegal.update` false — `MERGE.md`, constraint (5), has that argument,
and making the two one predicate is the work queue's third row.

**`SetLegal` would not be enough anyway**, and the gap is not about actions. Declaring `f` a
`:merge` function makes an entry of `f` *already in the database* collide with itself, and
`MergeStep` then writes whatever the body computes, with no `set` anywhere. Hence the
second, independent condition `Cmd.CtorDecl`, which *is* a hypothesis of the refinement;
`Falsity.exec_programStep_needs_ctorDecls` is the witness, where the self-collision makes
the specification reach two states and the interpreter one.

**`MergeDeclared`**, with `WidthOk`, is one of the two checks that walk into a `:merge`
body — `Scoped`, `Evaluable` and `SetLegal` all say nothing about one, because it runs in
the environment `mergeEnv` builds rather than in the ambient context. It asks that every
name a body or result applies is a primitive or a declared function of any kind, and it asks
it of the signature the declaration **installs**, so a `:merge` may name the function it
resolves. That is the mirror image of `DeclsFresh`, which is asked before. `Evaluable` would
be the wrong demand there: a merge body is exactly where primitives are legal and where a
`set` on another merge function is legal. Why it is load-bearing rather than tidy —
`MERGE.md`, "The merge phase runs between commands".

## Arity checking

egglog fixes a function's column counts at declaration and checks every use against them.
`FnDecl` recorded both counts from M1, but until the check existed nothing read them outside
`Tests/Egg.lean`'s renderer, so the model accepted programs egglog's typechecker throws out.

egglog's check is one equation on the lowered atom: for an atom headed by `f`,
`|args| = |inputs f| + |outputs f|` (`constraint.rs`, `get_atom_application_constraints`), reported
as `TypeError::Arity`, "Arity mismatch, expected {expected} args". What each surface form
contributes to `|args|` is what makes the one equation say different things:

* an *expression* `(f a…)` — a top-level action, a rule head, a merge body, an argument — and a
  *query fact* `(f a…)` or `(= e (f a…))` each append exactly one fresh output variable, so both
  need `|a| = arity f` and `outArity f = 1`. A two-column function is rejected in all of those
  positions; the binary answers `expected 2 args: (Dist k)`.
* `(set (f a…) v)` appends the value list — one entry for a bare `v`, `|v…|` for `(values v…)` —
  so it needs `|a| + |v…| = arity f + outArity f`.
* the row atom `Pattern.values` appends the read values and needs the same sum. It has no single
  surface form: egglog writes it `(= v (f a…))` at one value column and `(= (values v…) (f a…))` at
  more, and answers "Unbound function values" if the tuple form is used on a one-column function.
  `Tests/Egg.lean` renders whichever fits, so the check is on the columns and not on the notation.

The last two are modelled by the stronger **split**, `|a| = arity f` alongside the sum, rather than
by the sum alone. egglog's sum really does admit moving a column across the divide — with every sort
`i64`, `(= (values v) (Dist k j))` is accepted for `(function Dist (i64) (i64 i64) …)` — but only
because the sorts happen to agree. The model is untyped, so the sum alone would let it accept a
program whose meaning it then gets wrong. **This is the one place the check is stricter than
egglog's.**

The sum the row atom is checked against is `FnDecl.entryWidth`, not `arity + outArity`, and the
difference is the whole point of `entryWidth`: it is `arity` for a constructor, whose entry carries
no value columns at all. So `(= v (Add a b))` on a *constructor* `Add` is not a row atom in this
model and `Pattern.arityOk` rejects it — binding a constructor's value is the `.eq` atom, since the
value *is* the application. Before `entryWidth`, that atom passed the front end, matched in `Impl/`
through the row scan, and was unmatchable in `Spec/`.

Two declaration-side rules from the same pass:

* a `:merge` result has one expression per value column — `TupleMergeArity`, "The :merge of tuple-output
  function {name} has {actual} columns but the function has {expected} output columns" — and must be
  a `(values …)` at all for a tuple-output function (`TupleMergeNotValues`);
* a constructor has exactly one value column — `TupleOutputNotAllowed`, "Function {0} has a tuple
  output, which is only allowed for plain functions (not constructors, relations, or view tables)".

A merge body is checked against the signature *including* the function being declared, so it may
`set` its own table; a forward reference to a function declared later is instead "Unbound function".
Both checked against the release binary.

**Why a static check and not a premise.** Arity is a typechecking error, raised per command by
`get_atom_application_constraints` before that command runs — the same pass, on the same AST node,
that raises `SetConstructorDisallowed` ten lines above it, which is what `Action.SetLegal` already
models. Two alternatives were rejected. A premise on `Expr.eval` would reject at *run* time what
egglog rejects statically, and would put a hypothesis on every lemma in `Proofs/Merge.lean`. A state
invariant "every row has its declared width" is the *derived* form and is what would let
`Impl/Merge.lean`'s row reads be proved total, but it belongs inside `Database.WF` and needs
preservation lemmas through `evalAction` and `MergeStep`; it is the follow-on, not this.

**`Bool`, unlike `Scoped` and `SetLegal`.** Those are `Prop`s with no computable counterpart, so
`Tests/Egg.lean` restates `SetLegal` as `illegalSets` and the two can drift. `arityOk` is defined
once and `Program.ArityOk` reads it, so the difftest gets its check for free — and deciding it
needs no instance through the `List Expr` nesting.

*That is now half true.* `Spec/Scope.lean`'s `WidthOk` is a second, `Prop`-side statement of the
same discipline, and it is **not** `arityOk` read through a coercion. They agree on the `set` case
and on a `:merge` result, and `arityOk` demands three things besides: the row atom's split and
`entryWidth` sum (`WidthOk` has no `Pattern` case at all), `outArity = 1` at an application in an
expression, and `outArity = 1` on a constructor's declaration. So `arityOk` is strictly the
stronger, they are consistent today, and they can drift. Which is which: `arityOk` is what the
difftest enforces before writing a case; `WidthOk` is the front-end predicate a theorem would take
as a hypothesis, and nothing takes it yet. `Program.ArityOk` and `WellArity` likewise have no
consumers outside `Impl/Check.lean`.

Two things are deliberately not covered, both because `arityOk` reads the signature and nothing
else. That every *undeclared* name is used at one arity: outside the row atom, a name with no entry
has no declared column counts to disagree with, so `Tests/Egg.lean`, which invents the `datatype`
header from uses, carries that half as `Program.arityConflicts`. (That a program must declare before
it uses is `Program.Evaluable`'s business, and `Program.declared` is how the difftest supplies the
declarations.) And a primitive's arity, which egglog also checks ("Arity mismatch, expected 2 args:
(min old new 3)"): `Prim.ofName` lives in `Spec/Term.lean` and is never in the signature, so this
is permissive rather than wrong.

The row atom is the exception to the first, and needs to be: `Pattern.arityOk` rejects a `.values`
naming an undeclared function outright, because the key/value split is exactly what a declaration
supplies and there is nothing to check it against otherwise. It still does **not** want the
`SetLegal` companion restriction `sig.mergeOf f ≠ none` — not because that would reject something
useful, but because `entryWidth` already decides the case: a `.values` on a constructor is
admissible only at zero value columns, which is a bare existence read and not a program anything
writes.
