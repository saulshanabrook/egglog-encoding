import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.Result

namespace Egglog

def Scope.Models (Γ : Scope) (σ : Env) : Prop := ∀ v, v ∈ Γ ↔ v ∈ Env.dom σ

theorem Scope.Models.empty : Scope.Models [] ([] : Env) := by simp [Models]

theorem Expr.eval_isSome_of_scoped {e : Expr} {Γ : Scope} {σ : Env}
    (hm : Γ.Models σ) (h : e.Scoped Γ) : ∃ t, e.eval σ = some t :=
  e.eval_isSome (fun v hv => (hm v).mp (h v hv))

theorem Expr.not_isLit_of_isApp {e : Expr} {σ : Env} {t : Term}
    (ha : e.IsApp) (h : e.eval σ = some t) : ¬ t.isLit := by
  cases e with
  | app f args =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Term.isLit]
  | lit | var | min => exact ha.elim

/-- Precisely the extra progress condition needed by an evaluated union. -/
def Action.UnionSafe (σ : Env) (a : Action) : Prop :=
  ∀ e₁ e₂, a = .union e₁ e₂ → ∀ t₁ t₂,
    e₁.eval σ = some t₁ → e₂.eval σ = some t₂ → ¬ (t₁.isLit ∨ t₂.isLit)

theorem evalAction_isSome_of_scoped {σ : Env} {db : Database} {Γ : Scope}
    (hm : Γ.Models σ) {a : Action} (h : a.Scoped Γ) (hu : a.UnionSafe σ) :
    ∃ db', evalAction σ db a = some db' := by
  cases a with
  | expr e =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm h.2
    exact ⟨db.addTerm t, by simp [evalAction, ht]⟩
  | delete e =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm h.2
    exact ⟨db.deleteRows {t}, by simp [evalAction, ht]⟩
  | union a b =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm h.1
    obtain ⟨u, hu'⟩ := Expr.eval_isSome_of_scoped hm h.2
    have hn := hu a b rfl t u ht hu'
    exact ⟨db.addEq t u, by simpa [evalAction, ht, hu'] using hn⟩

theorem evalActions_isSome_of_scoped {σ : Env} {db : Database} {Γ : Scope}
    (hm : Γ.Models σ) {as : List Action} (h : Actions.Scoped as Γ)
    (hu : ∀ a ∈ as, a.UnionSafe σ) : ∃ db', evalActions σ db as = some db' := by
  induction as generalizing db with
  | nil => exact ⟨db, rfl⟩
  | cons a as ih =>
    obtain ⟨d, hd⟩ := evalAction_isSome_of_scoped (db := db) hm h.1 (hu a (by simp))
    obtain ⟨e, he⟩ := ih h.2 (fun a ha => hu a (by simp [ha])) (db := d)
    exact ⟨e, by simp [evalActions, hd, he]⟩

theorem Query.bind_models {db : Database} {Γ : Scope} {ρ : Env} (hm : Γ.Models ρ)
    {q : Query} {σ : Env} (hσ : ValidQuerySubst db q σ) :
    (Query.bind q Γ).Models (σ ++ ρ) := by
  intro v
  rw [Query.bind, List.mem_union_iff, Env.dom_append, List.mem_append, hm v,
    hσ.mem_dom_iff, Query.mem_vars]
  simp only [Pattern.mem_freeVars, Env.dom_nil, List.not_mem_nil, not_false_eq_true, and_true]
  exact or_comm

theorem evalLocalActions_isSome_of_scoped {db : Database} {r : Rule}
    (hr : r.Scoped []) {σ : Env} (hσ : ValidQuerySubst db r.query σ)
    (hu : ∀ a ∈ r.actions, a.UnionSafe σ) :
    ∃ d, evalActions σ db r.actions = some d := by
  have hm : (Query.bind r.query []).Models σ := by
    simpa using Query.bind_models Scope.Models.empty hσ
  exact evalActions_isSome_of_scoped hm hr.2 hu

/-- A bounded command always returns a database. -/
theorem CmdStep.exists_of_scoped {db : Database} {Γ : Scope} {c : Cmd}
    (hns : c.NoSaturate) (_h : c.Scoped Γ) : ∃ d, CmdStep db c d := by
  cases c with
  | run R => exact ⟨_, rfl⟩
  | saturate R => exact hns.elim

theorem ProgramStep.exists_of_noSaturate {db : Database} {cs : List Cmd}
    (hns : ∀ c ∈ cs, c.NoSaturate) : ∃ d, ProgramStep db cs d := by
  induction cs generalizing db with
  | nil => exact ⟨_, .nil⟩
  | cons c cs ih =>
    cases c with
    | saturate R => exact (show False from hns (.saturate R) (by simp)).elim
    | run R =>
      obtain ⟨d, hd⟩ := ih (db := RunRules R db) (fun c hc => hns c (by simp [hc]))
      exact ⟨d, .cons rfl hd⟩

theorem Eval.exists_of_scoped {db : Database} {Γ : Scope} {p : Program}
    (hns : p.NoSaturate) (_h : Program.Scoped p Γ) : ∃ r, Eval db p r := by
  classical
  obtain ⟨d, hd⟩ := ProgramStep.exists_of_noSaturate (db := db) hns
  by_cases hq : QueryHolds d p.check
  · exact ⟨_, .ok hd hq⟩
  · exact ⟨_, .checkFailed hd hq⟩

end Egglog
