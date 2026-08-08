import EgglogSemantics.Proofs.Interp

/-!
# The Redex test suite, as Lean proofs

Ports the unit checks in `test.rkt` of
[egglog PR #324](https://github.com/egraphs-good/egglog/pull/324). Each `example`
here is a closed proof, so this file compiling *is* the test run.

Two of the Redex checks are not reproduced as stated:

* `redex-check`'s random testing has no counterpart.
* The checks starting from a database with equalities but no terms
  (`(restore-congruence ((tset) (congr (= 1 2) (= 2 3)) () ()))`) describe states the
  semantics never reaches — a `union` always inserts its operands — so they are
  ported with the terms present.

Checks about what a `run` does *not* produce need `ValidSubst` inversion, which is
`PLAN.md`'s M8; the `run` example below is the forward direction only.
-/

namespace Egglog.Examples

/-- An integer term. -/
private def num (n : Int) : Term := .lit (.int n)

/-- An integer expression. -/
private def eNum (n : Int) : Expr := .lit (.int n)

/-- The empty signature; nothing in this phase reads it. -/
private abbrev noSig : Signature := fun _ => none

/-! ### Scope checking -/

/-- `(check-false (judgment-holds (typed-program (v1) TypeEnv)))`. -/
example : ¬ WellScoped [.action (.expr (.var "v1"))] := by
  simp [WellScoped, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped]

/-- `(check-not-false (judgment-holds (typed-program ((let v1 2) v1) TypeEnv)))`, with the
bare `v1` wrapped in a constructor. A global is in scope for a later command, which is what
the Redex check is about. -/
example : WellScoped
    [.action (.letBind "v1" (eNum 2)), .action (.expr (.app "cwrap" [.var "v1"]))] := by
  simp [WellScoped, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped, Expr.IsApp,
    Cmd.bind, Action.bind, eNum]

/-- The Redex form itself is rejected: a bare variable is a legal `expr` action there and
in egglog is not a legal action at all, so `Action.Scoped` requires an application. -/
example : ¬ WellScoped [.action (.letBind "v1" (eNum 2)), .action (.expr (.var "v1"))] := by
  simp [WellScoped, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.IsApp]

/-- Likewise for a query fact. -/
example : ¬ Rule.Scoped ⟨[.expr (.var "a")], []⟩ [] := by
  simp [Rule.Scoped, Pattern.Scoped, Expr.IsApp]

/-- `(check-false (judgment-holds (typed-rule (rule ((= v1 2)) ((cadd v1 v2))) ())))`:
`v2` is bound by neither the query nor the globals. -/
example : ¬ Rule.Scoped
    ⟨[.eq (.var "v1") (eNum 2)], [.expr (.app "cadd" [.var "v1", .var "v2"])]⟩ [] := by
  simp [Rule.Scoped, Pattern.Scoped, Actions.Scoped, Action.Scoped, Expr.Scoped,
    Expr.IsApp, Query.bind, Pattern.vars, eNum]

/-- `(check-not-false (judgment-holds (typed-rule (rule ((= v1 2)) ((cadd v1 v2)))
((v2 : no-type)))))`: with `v2` a global it does scope. -/
example : Rule.Scoped
    ⟨[.eq (.var "v1") (eNum 2)], [.expr (.app "cadd" [.var "v1", .var "v2"])]⟩ ["v2"] := by
  simp [Rule.Scoped, Pattern.Scoped, Actions.Scoped, Action.Scoped, Expr.Scoped,
    Expr.IsApp, Query.bind, Pattern.vars, eNum]

/-! ### Congruence

`(restore-congruence ((tset 1 2 3) (congr (= 1 2) (= 2 3)) () ()))` closes to all
nine pairs over `{1, 2, 3}`. -/

/-- `1 = 2` and `2 = 3` asserted over `{1, 2, 3}`. -/
private def chain : Database where
  sig := noSig
  terms := {num 1, num 2, num 3}
  rows := Database.ctorRowsOf {num 1, num 2, num 3}
  eqs := {(num 1, num 2), (num 2, num 3)}
  env := []
  rules := ∅

private theorem chain_wf : chain.WF where
  subtermClosed := by
    intro t ht
    simp only [chain, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl <;> simp [chain, num]
  eqsInTerms := by
    intro p hp
    simp only [chain, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> simp [chain]
  envInTerms := by simp [chain]

example : Cong chain (num 1) (num 3) :=
  .trans (b := num 2) (.assert (by simp [chain])) (.assert (by simp [chain]))

example : Cong chain (num 3) (num 1) :=
  .symm (.trans (b := num 2) (.assert (by simp [chain])) (.assert (by simp [chain])))

example : Cong chain (num 2) (num 2) := .refl (by simp [chain])

/-- The closure relates nothing to a term the database does not hold. The Redex
fixpoint leaves this implicit; here it follows from reflexivity being restricted to
`db.terms`. -/
example : ¬ Cong chain (num 1) (num 4) := by
  intro h
  have hm : num 4 ∈ chain.terms := h.mem_right chain_wf
  simp [chain, num] at hm

/-- `(restore-congruence ((tset 1 2 (wrapper 2) (wrapper 1)) (congr (= 1 2)) () ()))`
derives `(= (wrapper 1) (wrapper 2))`. -/
private def wrapped : Database where
  sig := noSig
  terms := {num 1, num 2, .app "wrapper" [num 1], .app "wrapper" [num 2]}
  rows := Database.ctorRowsOf {num 1, num 2, .app "wrapper" [num 1], .app "wrapper" [num 2]}
  eqs := {(num 1, num 2)}
  env := []
  rules := ∅

example : Cong wrapped (.app "wrapper" [num 1]) (.app "wrapper" [num 2]) :=
  .congr (by simp [wrapped]) (by simp [wrapped])
    (.cons (.assert (by simp [wrapped])) .nil)

/-- Congruence derives nothing beyond what is asserted. Over `{1, 4, 7}` with only
`4 = 7`, the term `1` stays alone — proved by exhibiting a congruence containing the
assertions that `(1, 4)` is not in (`Cong.le`). -/
private def separate : Database where
  sig := noSig
  terms := {num 1, num 4, num 7}
  rows := Database.ctorRowsOf {num 1, num 4, num 7}
  eqs := {(num 4, num 7)}
  env := []
  rules := ∅

example : ¬ Cong separate (num 1) (num 4) := by
  intro h
  have hR := h.le (R := fun a b => a = b ∨ (a = num 4 ∧ b = num 7) ∨ (a = num 7 ∧ b = num 4))
    (fun a b hm => by simp only [separate, Set.mem_singleton_iff, Prod.mk.injEq] at hm
                      exact Or.inr (Or.inl ⟨hm.1, hm.2⟩))
    (fun _ _ => Or.inl rfl)
    (by rintro a b (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp)
    (by rintro a b c (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (rfl | ⟨h1, rfl⟩ | ⟨h1, rfl⟩) <;>
          simp_all [num])
    (fun f as bs hm _ _ => by simp [separate, num] at hm)
  simp [num] at hR

/-! ### E-matching

`(judgment-holds (valid-subst ((tset 1 2 (wrapper 2)) (congr …) () ()) (wrapper 1) Env) Env)`
is `'(())`: the pattern `(wrapper 1)` matches under the empty substitution even
though the database holds no such term, because `1 = 2` makes it congruent to
`(wrapper 2)`.

This is the witness mechanism. The instance `(wrapper 1)` is added to the database
before `Cong` is asked; the witness `(wrapper 2)` is drawn from the terms the
database held beforehand, which is what stops the pattern from matching in a database
that knows nothing about it. -/

/-- `1 = 2` over `{1, 2, (wrapper 2)}`. -/
private def preWrapped : Database where
  sig := noSig
  terms := {num 1, num 2, .app "wrapper" [num 2]}
  rows := Database.ctorRowsOf {num 1, num 2, .app "wrapper" [num 2]}
  eqs := {(num 1, num 2)}
  env := []
  rules := ∅

example : ValidSubst preWrapped (.expr (.app "wrapper" [eNum 1])) [] :=
  .expr (w := .app "wrapper" [num 2]) (t := .app "wrapper" [num 1])
    ⟨by simp [eNum], by simp⟩
    (by simp [preWrapped])
    (by simp [Expr.eval, Expr.evalList, eNum, num])
    (.congr (by simp [preWrapped]) (by simp [preWrapped])
      (.cons (.symm (.assert (by simp [preWrapped]))) .nil))

/-- `(judgment-holds (valid-env (v1) ((tset 1) (congr (= 1 1)) () ()) Env))` is
`'(((v1 -> 1)))`. -/
example : ValidEnv ["v1"]
    { sig := noSig, terms := {num 1}, rows := Database.ctorRowsOf {num 1}, eqs := ∅,
      env := [], rules := ∅ } [("v1", num 1)] := by
  refine ⟨by simp, ?_⟩
  intro b hb
  rw [List.mem_singleton] at hb
  simp [hb]

/-! ### Running a program of actions

`(execute ((let v (b 1)) (union 7 7) (union v 4)))` gives terms `{(b 1), 4, 7, 1}`
and, after closure, `(b 1) = 4`. -/

private def b1 : Term := .app "b" [num 1]

private def actionsProgram : Program :=
  [.action (.letBind "v" (.app "b" [eNum 1])),
   .action (.union (eNum 7) (eNum 7)),
   .action (.union (.var "v") (eNum 4))]

example : WellScoped actionsProgram := by
  simp [WellScoped, actionsProgram, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped,
    Cmd.bind, Action.bind, eNum]

example : ∃ db, run actionsProgram = some db ∧
    db.terms = {b1, num 1, num 7, num 4} ∧
    db.eqs = {(num 7, num 7), (b1, num 4)} ∧
    Env.lookup "v" db.env = some b1 ∧
    Cong db (num 4) b1 := by
  refine ⟨_, rfl, ?_, ?_, rfl, ?_⟩
  · ext t; simp [b1, num]; tauto
  · ext p; simp [b1, num]; tauto
  · exact .symm (.assert (by simp [b1, num]))

/-! ### Running a rule

`(execute ((Add 1 2) (rule ((Add a b)) ((Add b a))) (run)))` produces `(Add 2 1)`.
Only the forward direction is shown: the substitution `a ↦ 1, b ↦ 2` satisfies the
query and its actions build `(Add 2 1)`. That nothing *else* is produced needs
`ValidSubst` inversion (`PLAN.md`, M8). -/

private def add12 : Term := .app "Add" [num 1, num 2]

private def add21 : Term := .app "Add" [num 2, num 1]

private def swapRule : Rule where
  query := [.expr (.app "Add" [.var "a", .var "b"])]
  actions := [.expr (.app "Add" [.var "b", .var "a"])]

private def ruleProgram : Program :=
  [.action (.expr (.app "Add" [eNum 1, eNum 2])), .rule swapRule, .run]

example : WellScoped ruleProgram := by
  simp [WellScoped, ruleProgram, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped,
    Expr.IsApp, Cmd.bind, Action.bind, Rule.Scoped, Pattern.Scoped, Actions.Scoped,
    Query.bind, Pattern.vars, swapRule, eNum]

/-- The database just before the `(run)`: `(Add 1 2)` with its children, plus the rule. -/
private def preRun : Database where
  sig := noSig
  terms := add12.subterms
  rows := add12.ctorRows
  eqs := ∅
  env := []
  rules := insert swapRule ∅

private theorem preRun_eq :
    runProgram Database.empty [.action (.expr (.app "Add" [eNum 1, eNum 2])), .rule swapRule]
      = some preRun := by
  simp [runProgram, stepCmd, evalAction, Expr.eval, Expr.evalList, Database.empty, preRun,
    eNum, num, add12, Database.addTerm]

private theorem run_ruleProgram : run ruleProgram = some (runRules preRun) := by
  change runProgram Database.empty
    ([.action (.expr (.app "Add" [eNum 1, eNum 2])), .rule swapRule] ++ [Cmd.run]) = _
  rw [runProgram_append, preRun_eq]
  simp [stepCmd]

/-- The one firing of the rule: `a ↦ 1`, `b ↦ 2`, witnessed by `(Add 1 2)` itself. -/
private theorem swap_matches :
    ValidQuerySubst preRun swapRule.query [("a", num 1), ("b", num 2)] := by
  refine ⟨[[("a", num 1), ("b", num 2)]], .cons ?_ .nil, .single _⟩
  refine ValidSubst.expr (w := add12) (t := add12) ⟨?_, ?_⟩ ?_ ?_ (.refl ?_)
  · simp [Env.dom, preRun]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [preRun, add12, num]
  · simp [preRun, add12]
  · simp [Expr.eval, Expr.evalList, Env.lookup, preRun, add12, num]
  · simp [preRun, add12]

/-- Running that firing adds `(Add 2 1)` and its children. -/
private theorem swap_fires :
    evalLocalActions preRun swapRule.actions [("a", num 1), ("b", num 2)]
      = some { preRun with terms := preRun.terms ∪ add21.subterms,
                           rows := preRun.rows ∪ add21.ctorRows } := by
  simp [evalLocalActions, evalActions, evalAction, Expr.eval, Expr.evalList, Env.lookup,
    swapRule, preRun, add21, num, Database.addTerm]

/-- `(Add 2 1)` is in the database after the run. -/
example : ∃ db, run ruleProgram = some db ∧ add21 ∈ db.terms := by
  refine ⟨runRules preRun, run_ruleProgram, ?_⟩
  have hmem : ({ preRun with terms := preRun.terms ∪ add21.subterms,
                             rows := preRun.rows ∪ add21.ctorRows } : Database) ∈
      {d | ∃ r ∈ preRun.rules, d ∈ ruleResults preRun r} :=
    ⟨swapRule, by simp [preRun], _, swap_matches, swap_fires⟩
  exact Or.inr (Set.mem_biUnion hmem (Or.inr add21.self_mem_subterms))

/-! ### The closure, computed

The Redex checks `restore-congruence` by writing out the closed `congr` set in full.
With `Closure.closure` those become computations. `#guard` is checked at compile time
and, being a command rather than a proof, puts nothing into any proof term; `closure`
is well-founded recursion and so sealed against the kernel, which `unseal` lifts where
a real proof wants it. -/

section Computed
set_option linter.hashCommand false

/-- `(tset 1 2 3)` with `(congr (= 1 2) (= 2 3))`: the Redex expects all nine pairs. -/
private def chainTerms : Finset Term := {num 1, num 2, num 3}

private def chainEqs : Finset (Term × Term) := {(num 1, num 2), (num 2, num 3)}

private theorem chainEqs_sub : chainEqs ⊆ candidates chainTerms := by decide

#guard (closure chainTerms chainEqs chainEqs_sub).card = 9

/-- `(tset 1 2 (wrapper 2) (wrapper 1))` with `(congr (= 1 2))`: the Redex expects the
eight pairs of the two classes `{1, 2}` and `{(wrapper 1), (wrapper 2)}` — congruence
propagating under `wrapper`, and nothing across the two classes. -/
private def wrappedTerms : Finset Term :=
  {num 1, num 2, .app "wrapper" [num 1], .app "wrapper" [num 2]}

private def wrappedEqs : Finset (Term × Term) := {(num 1, num 2)}

private theorem wrappedEqs_sub : wrappedEqs ⊆ candidates wrappedTerms := by decide

#guard (closure wrappedTerms wrappedEqs wrappedEqs_sub).card = 8

#guard decide ((Term.app "wrapper" [num 1], Term.app "wrapper" [num 2])
  ∈ closure wrappedTerms wrappedEqs wrappedEqs_sub)

#guard decide ((num 1, Term.app "wrapper" [num 1])
  ∈ closure wrappedTerms wrappedEqs wrappedEqs_sub) = false

-- `closure` is well-founded recursion, so it is sealed against kernel reduction;
-- `unseal` lets `decide` through for the example below.
unseal closure

/-- The computation transfers to the spec: `mem_closure_iff` turns a decidable
membership into a `Cong` derivation, which is what an executable interpreter will lean
on throughout. -/
example : Cong chain (num 1) (num 3) := by
  refine (mem_closure_iff (terms := chainTerms) (rel := chainEqs) ?_ ?_ chainEqs_sub).mp
    (by decide)
  · simp [chain, chainTerms]
  · simp [chain, chainEqs]

/-! ### Running programs

The Redex `execute` cases, run by the interpreter rather than proved. This includes the
two-round `Wrapper` test, which needs `ValidSubst` inversion to state as a theorem and so
had no hand proof. -/

/- `(execute ((Add 1 2) (rule ((Add a b)) ((Add b a))) (run)))`: the Redex expects terms
`{(Add 1 2), 1, 2, (Add 2 1)}`. `Add` holds two rows — `1` and `2` are not equal, so the
two argument lists are not congruent. -/
#guard (exec ruleProgram).map (fun d => d.terms.toFinset.card) = some 4

#guard (exec ruleProgram).map (fun d => decide (add21 ∈ d.terms)) = some true

#guard (exec ruleProgram).map (fun d => d.rowCount "Add") = some 2

/-- `(execute ((Wrapper (Add 1 2)) (rule ((Add a b)) ((union (Add a b) (Add b a))))
(rule ((= (Wrapper (Add 1 2)) (Wrapper (Add 2 1)))) ((success))) (run) (run)))`: the
second rule fires only because `(Wrapper (Add 2 1))` is *congruent* to a term the database
holds, not because that term was ever built — the witness mechanism, end to end. -/
private def commuteRule : Rule where
  query := [.expr (.app "Add" [.var "a", .var "b"])]
  actions := [.union (.app "Add" [.var "a", .var "b"]) (.app "Add" [.var "b", .var "a"])]

private def detectRule : Rule where
  query := [.eq (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])
                (.app "Wrapper" [.app "Add" [eNum 2, eNum 1]])]
  actions := [.expr (.app "success" [])]

private def wrapperProgram : Program :=
  [.action (.expr (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])),
   .rule commuteRule, .rule detectRule, .run, .run]

#guard (exec wrapperProgram).map (fun d => decide (Term.app "success" [] ∈ d.terms))
  = some true

/- One round is not enough: the union has to happen before the second rule can match. -/
#guard (exec [.action (.expr (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])),
    .rule commuteRule, .rule detectRule, .run]).map
  (fun d => decide (Term.app "success" [] ∈ d.terms)) = some false

#guard (exec wrapperProgram).map (fun d => d.rowCounts ["Add", "Wrapper", "success"])
  = some [("Add", 2), ("Wrapper", 1), ("success", 1)]

end Computed

end Egglog.Examples
