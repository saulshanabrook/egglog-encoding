import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Step

namespace Egglog
theorem Scope.Models.empty : Scope.Models [] ([] : Env) := by simp [Models]

/-! ### Scoped expressions evaluate -/
theorem Expr.eval_isSome_of_scoped {e : Expr} {Γ : Scope} {σ : Env} (hm : Γ.Models σ)
    (h : e.Scoped Γ) : ∃ t, e.eval σ = some t :=
  e.eval_isSome fun v hv => (hm v).mp (h v hv)

/-! ### Actions do not get stuck -/
theorem evalAction_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {a : Action} (h : a.Scoped Γ) :
    ∃ db', evalAction db a = some db' ∧ (a.bind Γ).Models db'.env := by
  cases a with
  | expr e =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm h.2
    exact ⟨db.addTerm t, by simp [evalAction, ht], hm⟩
  | letBind v e =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm h
    refine ⟨{ db.addTerm t with env := (v, t) :: db.env }, by simp [evalAction, ht], ?_⟩
    intro w
    simp only [Action.bind, List.mem_cons, Env.dom_cons]
    exact or_congr_right (hm w)
  | union e₁ e₂ =>
    obtain ⟨t₁, ht₁⟩ := Expr.eval_isSome_of_scoped hm h.1
    obtain ⟨t₂, ht₂⟩ := Expr.eval_isSome_of_scoped hm h.2
    exact ⟨db.addEq t₁ t₂, by simp [evalAction, ht₁, ht₂], hm⟩
  | set f args out =>
    obtain ⟨as, has⟩ := Expr.evalList_isSome args fun v hv => by
      obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
      exact (hm v).mp (h.1 e he v hve)
    obtain ⟨vs, hvs⟩ := Expr.evalList_isSome out fun v hv => by
      obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
      exact (hm v).mp (h.2 e he v hve)
    refine ⟨db.addRow f as vs, by simp [evalAction, has, hvs], ?_⟩
    simpa [Action.bind] using hm

theorem evalActions_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {as : List Action} (h : Actions.Scoped as Γ) :
    ∃ db', evalActions db as = some db' ∧ (Actions.bind as Γ).Models db'.env := by
  induction as generalizing db Γ with
  | nil => exact ⟨db, rfl, hm⟩
  | cons a as ih =>
    obtain ⟨db₁, h₁, hm₁⟩ := evalAction_isSome_of_scoped hm h.1
    obtain ⟨db₂, h₂, hm₂⟩ := ih hm₁ h.2
    exact ⟨db₂, by simp [h₁, h₂], hm₂⟩

/-! ### A well-scoped rule contributes on every match

`runRules` unions the results of the firings whose actions succeed, so a rule whose
actions get stuck silently contributes nothing. This says that never happens for a
well-scoped rule: the query binds exactly the pattern variables the actions were
checked against. -/
/-- A query substitution together with the globals models exactly the scope the
query binds. -/
theorem Query.bind_models {db : Database} {Γ : Scope} (hm : Γ.Models db.env) {q : Query}
    {σ : Env} (hσ : ValidQuerySubst db q σ) : (Query.bind q Γ).Models (db.env ++ σ) := by
  intro v
  rw [Query.bind, List.mem_union_iff, Env.dom_append, List.mem_append, hm v,
    hσ.mem_dom_iff, Query.mem_vars]
  constructor
  · rintro (hv | ⟨p, hp, hv⟩)
    · exact Or.inl hv
    · by_cases hd : v ∈ Env.dom db.env
      · exact Or.inl hd
      · exact Or.inr ⟨p, hp, p.mem_freeVars.mpr ⟨hv, hd⟩⟩
  · rintro (hv | ⟨p, hp, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨p, hp, (p.mem_freeVars.mp hv).1⟩

theorem evalLocalActions_isSome_of_scoped {db : Database} {Γ : Scope}
    (hm : Γ.Models db.env) {r : Rule} (hr : r.Scoped Γ) {σ : Env}
    (hσ : ValidQuerySubst db r.query σ) : ∃ d, evalLocalActions db r.actions σ = some d := by
  obtain ⟨d, hd, _⟩ := evalActions_isSome_of_scoped
    (db := { db with env := db.env ++ σ }) (Query.bind_models hm hσ) hr.2
  exact ⟨{ d with env := db.env, rules := db.rules }, by simp [evalLocalActions, hd]⟩

/-! ### Well-scoped programs do not get stuck -/
theorem stepCmd_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {c : Cmd} (h : c.Scoped Γ) :
    ∃ db', stepCmd db c = some db' ∧ (c.bind Γ).Models db'.env := by
  cases c with
  | action a => exact evalAction_isSome_of_scoped hm h
  | rule r => exact ⟨_, rfl, hm⟩
  | run => exact ⟨_, rfl, hm⟩
  | decl f d => exact ⟨_, rfl, hm⟩

theorem runProgram_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {p : Program} (h : Program.Scoped p Γ) :
    ∃ db', runProgram db p = some db' ∧ (Program.bind p Γ).Models db'.env := by
  induction p generalizing db Γ with
  | nil => exact ⟨db, rfl, hm⟩
  | cons c cs ih =>
    obtain ⟨db₁, h₁, hm₁⟩ := stepCmd_isSome_of_scoped hm h.1
    obtain ⟨db₂, h₂, hm₂⟩ := ih hm₁ h.2
    exact ⟨db₂, by simp [h₁, h₂], hm₂⟩

/-- A well-scoped program runs to completion. -/
theorem run_isSome {p : Program} (h : WellScoped p) : ∃ db, run p = some db := by
  obtain ⟨db, hdb, _⟩ := runProgram_isSome_of_scoped
    (db := Database.empty) Scope.Models.empty h
  exact ⟨db, hdb⟩

end Egglog
