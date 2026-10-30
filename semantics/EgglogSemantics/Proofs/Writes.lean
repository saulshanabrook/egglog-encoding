import EgglogSemantics.Proofs.Query

/-!
# Writes and their sequential readings

`Spec/Step.lean` states rounds with `Action.writes`. Many proofs instead run
actions one at a time (`evalActions`), read a round as a union of rule results
(`RuleResults`). For delete-free heads, this file proves these readings equal.
-/

namespace Egglog

theorem Action.write_agree {σ τ : Env} (h : Env.Agree σ τ) (a : Action) :
    a.write σ = a.write τ := by
  cases a <;> simp only [Action.write, Expr.eval_agree h]

theorem Action.writes_agree {σ τ : Env} (h : Env.Agree σ τ) (as : List Action) :
    Action.writes σ as = Action.writes τ as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [Action.writes, Action.write_agree h, ih]

theorem Action.erase_agree {σ τ : Env} (h : Env.Agree σ τ) (a : Action) :
    a.erase σ = a.erase τ := by
  cases a <;> simp only [Action.erase, Action.write_agree h, Expr.eval_agree h]

theorem Action.erases_agree {σ τ : Env} (h : Env.Agree σ τ) (as : List Action) :
    Action.erases σ as = Action.erases τ as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [Action.erases, Action.erase_agree h, ih]


@[simp] theorem Database.addEqs_eqs {db : Database} {ps : Set (Term × Term)} :
    (db.addEqs ps).eqs = db.eqs ∪ ps := rfl

/-! ### Actions -/

/-- Running a delete-free action adds the equations it writes. -/
theorem evalAction_eq_write (σ : Env) (db : Database) (a : Action) (hdf : a.DeleteFree) :
    evalAction σ db a = (a.write σ).map db.addEqs := by
  cases a with
  | expr e =>
    simp only [evalAction, Action.write, Option.map_map]
    congr 1
    funext t
    simp [Function.comp, Database.addEqs, Database.addTerm, Set.union_singleton]
  | union e₁ e₂ =>
    simp only [evalAction, Action.write]
    cases e₁.eval σ <;> cases e₂.eval σ <;>
      simp only [Option.bind_none, Option.bind_some, Option.map_none]
    split <;> simp [Database.addEqs, Database.addEq, Set.union_singleton]
  | delete e => simp [Action.DeleteFree, Action.monotoneB] at hdf

/-- Running delete-free actions in order adds exactly their writes. -/
theorem evalActions_eq_writes (σ : Env) (db : Database) (as : List Action)
    (hdf : Actions.DeleteFree as) :
    evalActions σ db as = (Action.writes σ as).map db.addEqs := by
  induction as generalizing db with
  | nil =>
    simp only [evalActions, Action.writes, Option.map_some, Option.some.injEq]
    cases db
    simp [Database.addEqs]
  | cons a as ih =>
    obtain ⟨ha, has⟩ := Actions.deleteFree_cons.mp hdf
    rw [evalActions, evalAction_eq_write σ db a ha]
    cases hw : a.write σ with
    | none => simp [Action.writes, hw]
    | some W =>
      simp only [Option.map_some, Option.bind_some, Action.writes, hw,
        ih _ has, Option.map_map]
      congr 1
      funext V
      simp [Function.comp, Database.addEqs, Set.union_assoc]

/-- Erases and writes are defined for exactly the same actions. -/
theorem Action.erase_isSome (σ : Env) (a : Action) :
    (a.erase σ).isSome = (a.write σ).isSome := by
  cases a with
  | expr _ | union _ _ => simp only [Action.erase, Option.isSome_map]
  | delete e => simp [Action.erase, Action.write]

theorem Action.erases_isSome (σ : Env) (as : List Action) :
    (Action.erases σ as).isSome = (Action.writes σ as).isSome := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := Action.erase_isSome σ a
    cases he : a.erase σ <;> cases hw : a.write σ <;>
      cases hes : Action.erases σ as <;> cases hws : Action.writes σ as <;>
      simp_all [Action.erases, Action.writes]

theorem Action.erase_eq_empty {σ : Env} {a : Action} {X : Set Term}
    (hdf : a.DeleteFree) (h : a.erase σ = some X) : X = ∅ := by
  cases a with
  | expr e | union e e' =>
    obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp h
    exact he.symm
  | delete e => simp [Action.DeleteFree, Action.monotoneB] at hdf

theorem Action.erases_eq_empty {σ : Env} {as : List Action} {X : Set Term}
    (hdf : Actions.DeleteFree as) (h : Action.erases σ as = some X) : X = ∅ := by
  induction as generalizing X with
  | nil => exact (Option.some.inj h).symm
  | cons a as ih =>
    obtain ⟨Y, hY, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨Z, hZ, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [Action.erase_eq_empty (hdf a (by simp)) hY,
      ih (fun b hb => hdf b (List.mem_cons_of_mem _ hb)) hZ, Set.empty_union]

/-! ### Rounds -/

theorem RunErases.eq_empty {R : List Rule} {db : Database} (hdf : ∀ r ∈ R, r.DeleteFree) :
    RunErases R db = ∅ := by
  ext t
  simp only [RunErases, Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨X, ⟨r, hr, σ, _, hx⟩, ht⟩
  rw [Action.erases_eq_empty (hdf r hr) hx] at ht
  exact ht

theorem RunRules.eq_addEqs {R : List Rule} {db : Database} (hdf : ∀ r ∈ R, r.DeleteFree) :
    RunRules R db = db.addEqs (RunWrites R db) := by
  rw [RunRules, RunErases.eq_empty hdf, Database.deleteRows_empty]

theorem mem_ruleResults_iff_writes {db d : Database} {r : Rule} (hdf : r.DeleteFree) :
    d ∈ RuleResults db r ↔ ∃ σ W, QueryMatches db r.query σ ∧
      Action.writes σ r.actions = some W ∧ d = db.addEqs W := by
  rw [mem_ruleResults_iff_queryMatches]
  simp only [evalActions_eq_writes _ _ _ hdf, Option.map_eq_some_iff]
  constructor
  · rintro ⟨σ, hq, W, hW, rfl⟩
    exact ⟨σ, W, hq, hW, rfl⟩
  · rintro ⟨σ, W, hq, hW, rfl⟩
    exact ⟨σ, hq, W, hW, rfl⟩

/-- A delete-free round is the union of its rule firings' results. -/
theorem RunRules.eq_sUnion (R : List Rule) (db : Database) (hdf : ∀ r ∈ R, r.DeleteFree) :
    RunRules R db = db.sUnion {d | ∃ r ∈ R, d ∈ RuleResults db r} := by
  rw [RunRules.eq_addEqs hdf]
  simp only [RunWrites, Database.addEqs, Database.sUnion]
  congr 1
  ext p
  simp only [Set.mem_union, Set.mem_sUnion, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro (hp | ⟨W, ⟨r, hr, σ, hq, hW⟩, hpW⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨db.addEqs W,
        ⟨r, hr, (mem_ruleResults_iff_writes (hdf r hr)).mpr ⟨σ, W, hq, hW, rfl⟩⟩,
        Or.inr hpW⟩
  · rintro (hp | ⟨d, ⟨r, hr, hd⟩, hp⟩)
    · exact Or.inl hp
    · obtain ⟨σ, W, hq, hW, rfl⟩ := (mem_ruleResults_iff_writes (hdf r hr)).mp hd
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr ⟨W, ⟨r, hr, σ, hq, hW⟩, hp⟩



end Egglog
