import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Source.Execution
import EgglogSemantics.Proofs.NoUnions
import EgglogSemantics.Impl.Observe

/-! Worked examples for the untyped, declaration-free language. -/

namespace Egglog.Examples

private instance (p : Program) : Decidable (WellScoped p) :=
  inferInstanceAs (Decidable (Program.Scoped p []))

private def num (n : Int) : Term := .lit (.int n)
private def eNum (n : Int) : Expr := .lit (.int n)
private def cnst (n : String) : Term := .app n []

/-- Global actions are runs of empty-query rules. -/
private def global (as : List Action) : List Cmd := [.run [⟨[], as⟩]]

example : ¬ WellScoped ⟨global [.expr (.var "v1")], []⟩ := by decide
example : WellScoped ⟨global [.expr (.app "cwrap" [eNum 2])], []⟩ := by decide
example : ¬ WellScoped ⟨global [.expr (.app "cwrap" [eNum 2])] ++
    global [.expr (.app "cwrap" [.var "v1"])], []⟩ := by decide
example : ¬ Rule.Scoped ⟨[.expr (.var "a")], []⟩ [] := by decide
example : ¬ Rule.Scoped
    ⟨[.eq (.var "v1") (eNum 2)], [.expr (.app "cadd" [.var "v1", .var "v2"]) ]⟩ [] := by
  decide
example : Rule.Scoped
    ⟨[.eq (.var "v1") (eNum 2)], [.expr (.app "cadd" [.var "v1", .var "v2"]) ]⟩ ["v2"] := by
  decide

example : (Expr.min (eNum 1) (eNum 2)).eval [] = some (num 1) := by decide
example : (Expr.min (eNum 2) (eNum 1)).eval [] = some (num 1) := by decide
example : (Expr.app "anyName" [eNum 1, eNum 2]).eval [] =
    some (.app "anyName" [num 1, num 2]) := rfl

private def chain : Database := (Database.empty.addEq (cnst "a") (cnst "b")).addEq (cnst "b") (cnst "c")

example : chain.WF := by
  apply Database.WF.addEq
  · exact Database.WF.empty.addEq _ _ (by simp [cnst, Term.isLit])
  · simp [cnst, Term.isLit]
example : Cong chain (cnst "a") (cnst "c") :=
  .trans (.direct (Or.inr (Set.mem_insert _ _))) (.direct (Set.mem_insert _ _))
example : Cong chain (cnst "c") (cnst "a") :=
  .symm (.trans (.direct (Or.inr (Set.mem_insert _ _))) (.direct (Set.mem_insert _ _)))

private def wrapped : Database :=
  (Database.empty.addEq (cnst "a") (cnst "b")).addTerm (.app "wrapper" [cnst "a"])

/-- The alternate spelling need not have been stored. -/
example : Cong wrapped (.app "wrapper" [cnst "a"]) (.app "wrapper" [cnst "b"]) :=
  .congr (.direct (Set.mem_insert _ _))
    (.cons (.direct (Or.inr (Set.mem_insert _ _))) .nil)

example : Matches wrapped (.expr (.app "wrapper" [.app "b" []])) [] := by
  have h : Cong wrapped (.app "wrapper" [cnst "a"]) (.app "wrapper" [cnst "b"]) :=
    .congr (.direct (Set.mem_insert _ _))
      (.cons (.direct (Or.inr (Set.mem_insert _ _))) .nil)
  exact .atom rfl (h.symm.trans h)

example : ValidEnv ["v1"] (Database.empty.addTerm (num 1)) [("v1", num 1)] := by
  refine ⟨by simp, ?_⟩
  intro b hb
  obtain rfl := List.mem_singleton.mp hb
  exact Database.mem_addTerm _ _

example {db : Database} : evalAction [] db (.union (eNum 7) (eNum 7)) = none := rfl

private def add12 : Term := .app "Add" [num 1, num 2]
private def add21 : Term := .app "Add" [num 2, num 1]
private def swapRule : Rule :=
  ⟨[.expr (.app "Add" [.var "a", .var "b"])],
    [.expr (.app "Add" [.var "b", .var "a"])]⟩
private def preRun : Database :=
  Database.empty.addTerm add12

private theorem swap_matches :
    QueryMatches preRun swapRule.query [("a", num 1), ("b", num 2)] := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact preRun.subtermClosed add12 (Database.mem_addTerm _ _)
        (.arg (by simp [add12]) (.refl _))
    · exact preRun.subtermClosed add12 (Database.mem_addTerm _ _)
        (.arg (by simp [add12]) (.refl _))
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact .atom rfl (.direct (Set.mem_insert _ _))

example : add21 ∈ (RunRules [swapRule] preRun).terms := by
  refine ⟨(add21, add21), Or.inr ?_, Or.inl (.refl _)⟩
  exact ⟨{(add21, add21)}, ⟨swapRule, by simp,
    [("a", num 1), ("b", num 2)], swap_matches, by simp [swapRule, Action.writes,
      Action.write, Expr.eval, Expr.evalList, Env.lookup, add21, num]⟩, rfl⟩

section Computed
set_option linter.hashCommand false

private def chainTerms : Finset Term := {cnst "a", cnst "b", cnst "c"}
private def chainEqs : Finset (Term × Term) :=
  {(cnst "a", cnst "b"), (cnst "b", cnst "c")}
#guard (closureTotal chainTerms chainEqs).card = 9

private def ruleProgram : Program :=
  ⟨global [.expr (.app "Add" [eNum 1, eNum 2])] ++ [.run [swapRule]], []⟩
#guard WellScoped ruleProgram
#guard (exec ruleProgram).map (fun d => d.terms.toFinset.card) = some 4
#guard (exec ruleProgram).map (fun d => decide (add21 ∈ d.terms)) = some true
#guard (exec ruleProgram).map (fun d => d.rowCount "Add") = some 2

private def commuteRule : Rule :=
  ⟨[.expr (.app "Add" [.var "a", .var "b"])],
    [.union (.app "Add" [.var "a", .var "b"]) (.app "Add" [.var "b", .var "a"])]⟩
private def detectRule : Rule :=
  ⟨[.eq (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])
        (.app "Wrapper" [.app "Add" [eNum 2, eNum 1]])], [.expr (.app "success" [])]⟩
private def wrapperProgram : Program :=
  ⟨global [.expr (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])] ++
    [.run [commuteRule, detectRule], .run [commuteRule, detectRule]], []⟩
#guard (exec wrapperProgram).map (fun d => d.terms.contains (cnst "success")) = some true

private def N (i : Int) : Expr := .app "N" [.lit (.int i)]
private def trans : Rule :=
  ⟨[.expr (.app "E" [.var "a", .var "b"]), .expr (.app "E" [.var "b", .var "c"])],
    [.expr (.app "E" [.var "a", .var "c"])]⟩
private def path (cs : List Cmd) : Program :=
  ⟨global ((List.range 3).map fun i => Action.expr (.app "E" [N i, N (i+1)])) ++ cs, []⟩
private def edges (p : Program) : Option Nat := (exec p).map fun d => d.rowCount "E"
#guard edges (path []) = some 3
#guard edges (path [.run [trans]]) = some 5
#guard edges (path [.run [trans], .run [trans]]) = some 6
#guard edges (path [.saturate [trans]]) = some 6
#guard edges (path [.run []]) = some 3

/-- The interpreter may record a redundant spelling before structural saturation.
Its successful result still witnesses the specification's semantic saturation. -/
private def redundantSpellings : Program :=
  ⟨global [.union (.app "a" []) (.app "b" []), .expr (.app "R" [.app "a" []])] ++
    [.saturate [⟨[.expr (.app "R" [.var "x"])], [.expr (.app "R" [.app "b" []])]⟩]], []⟩

example : ∃ out, ProgramStep Database.empty redundantSpellings.commands out := by
  have hs : (exec redundantSpellings).isSome = true := by decide +kernel
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨out, hout, _⟩ := exec_programStep (by decide) (by decide) he
  exact ⟨out, hout⟩

/-- A round deletes before writing, regardless of head-action order. -/
private def deleteWrite : Program := ⟨global [.expr (.app "R" [N 0])] ++
  global [.expr (.app "R" [N 0]), .delete (.app "R" [N 0])], []⟩
#guard (exec deleteWrite).map (fun d => d.terms.contains (.app "R" [.app "N" [num 0]])) = some true

private def diseq : Program :=
  ⟨global [.expr (.app "A" []), .expr (.app "B" [])],
    [.ne (.app "A" []) (.app "B" [])]⟩
#guard (observe diseq).any ExecutionResult.succeeded
private def failedDiseq : Program :=
  ⟨diseq.commands ++ global [.union (.app "A" []) (.app "B" [])], diseq.check⟩
#guard (exec failedDiseq).isSome
#guard (observe failedDiseq).any fun r => !r.succeeded

/-- Commands finish successfully even when the final check fails. -/
example : Eval Database.empty failedDiseq .checkFailed := by
  have hn : (observe failedDiseq).any (fun r => !r.succeeded) = true := by decide +kernel
  have hs : observe failedDiseq = some .checkFailed := by
    cases he : observe failedDiseq with
    | none => simp [he] at hn
    | some r =>
      cases r with
      | ok d => simp [he, ExecutionResult.succeeded] at hn
      | checkFailed => rfl
  obtain ⟨result, hr, hb⟩ := observe_eval (by decide) (by decide) hs
  cases result with
  | ok => cases hb
  | checkFailed => exact hr

end Computed
end Egglog.Examples
