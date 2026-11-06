import EgglogSemantics.Proofs.Query

/-!
# Writes and their sequential readings

`Spec/Step.lean` states rounds by applying actions directly (`evalActions`).
This file relates that semantics to the equations and marks collected by
`Spec/Facts.lean`, and to the union of rule results (`RuleResults`).
-/

namespace Egglog

theorem Action.write_agree {σ τ : Env} (h : Env.Agree σ τ) (a : Action) :
    a.write σ = a.write τ := by
  cases a <;> simp only [Action.write, Expr.eval_agree h, Expr.evalList_agree h]

theorem Action.writes_agree {σ τ : Env} (h : Env.Agree σ τ) (as : List Action) :
    Action.writes σ as = Action.writes τ as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [Action.writes, Action.write_agree h, ih]

theorem Action.mark_agree {σ τ : Env} (h : Env.Agree σ τ) (a : Action) :
    a.mark σ = a.mark τ := by
  cases a <;> simp only [Action.mark, Action.write_agree h, Expr.evalList_agree h]

theorem Action.marks_agree {σ τ : Env} (h : Env.Agree σ τ) (as : List Action) :
    Action.marks σ as = Action.marks τ as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [Action.marks, Action.mark_agree h, ih]


@[simp] theorem Database.addEqs_eqs {db : Database} {ps : Set (Term × Term)} :
    (db.addEqs ps).eqs = db.eqs ∪ ps := rfl

/-! ### Actions -/

/-- Running a subsume-free action adds the equations it writes. -/
theorem evalAction_eq_write (σ : Env) (db : Database) (a : Action) (hdf : a.SubsumeFree) :
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
  | subsume e => simp [Action.SubsumeFree, Action.monotoneB] at hdf

/-- Running subsume-free actions in order adds exactly their writes. -/
theorem evalActions_eq_writes (σ : Env) (db : Database) (as : List Action)
    (hdf : Actions.SubsumeFree as) :
    evalActions σ db as = (Action.writes σ as).map db.addEqs := by
  induction as generalizing db with
  | nil =>
    simp only [evalActions, Action.writes, Option.map_some, Option.some.injEq]
    cases db
    simp [Database.addEqs]
  | cons a as ih =>
    obtain ⟨ha, has⟩ := Actions.subsumeFree_cons.mp hdf
    rw [evalActions, evalAction_eq_write σ db a ha]
    cases hw : a.write σ with
    | none => simp [Action.writes, hw]
    | some W =>
      simp only [Option.map_some, Option.bind_some, Action.writes, hw,
        ih _ has, Option.map_map]
      congr 1
      funext V
      simp [Function.comp, Database.addEqs, Set.union_assoc]

/-- Marks and writes are defined for exactly the same actions. -/
theorem Action.mark_isSome (σ : Env) (a : Action) :
    (a.mark σ).isSome = (a.write σ).isSome := by
  cases a with
  | expr _ | union _ _ => simp only [Action.mark, Option.isSome_map]
  | subsume e => simp [Action.mark, Action.write]

theorem Action.marks_isSome (σ : Env) (as : List Action) :
    (Action.marks σ as).isSome = (Action.writes σ as).isSome := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := Action.mark_isSome σ a
    cases he : a.mark σ <;> cases hw : a.write σ <;>
      cases hes : Action.marks σ as <;> cases hws : Action.writes σ as <;>
      simp_all [Action.marks, Action.writes]

theorem Action.mark_eq_empty {σ : Env} {a : Action} {X : Set Term}
    (hdf : a.SubsumeFree) (h : a.mark σ = some X) : X = ∅ := by
  cases a with
  | expr e | union e e' =>
    obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp h
    exact he.symm
  | subsume e => simp [Action.SubsumeFree, Action.monotoneB] at hdf

theorem Action.marks_eq_empty {σ : Env} {as : List Action} {X : Set Term}
    (hdf : Actions.SubsumeFree as) (h : Action.marks σ as = some X) : X = ∅ := by
  induction as generalizing X with
  | nil => exact (Option.some.inj h).symm
  | cons a as ih =>
    obtain ⟨Y, hY, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨Z, hZ, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [Action.mark_eq_empty (hdf a (by simp)) hY,
      ih (fun b hb => hdf b (List.mem_cons_of_mem _ hb)) hZ, Set.empty_union]

/-! ### Rounds -/

theorem RunMarks.eq_empty {R : List Rule} {db : Database} (hdf : ∀ r ∈ R, r.SubsumeFree) :
    RunMarks R db = ∅ := by
  ext t
  simp only [RunMarks, Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨X, ⟨r, hr, σ, _, hx⟩, ht⟩
  rw [Action.marks_eq_empty (hdf r hr) hx] at ht
  exact ht

theorem mem_ruleResults_iff_writes {db d : Database} {r : Rule} (hdf : r.SubsumeFree) :
    d ∈ RuleResults db r ↔ ∃ σ W, QueryMatches db r.query σ ∧
      Action.writes σ r.actions = some W ∧ d = db.addEqs W := by
  rw [mem_ruleResults_iff_queryMatches]
  simp only [evalActions_eq_writes _ _ _ hdf, Option.map_eq_some_iff]
  constructor
  · rintro ⟨σ, hq, W, hW, rfl⟩
    exact ⟨σ, W, hq, hW, rfl⟩
  · rintro ⟨σ, W, hq, hW, rfl⟩
    exact ⟨σ, hq, W, hW, rfl⟩

/-- Every head has the same sequential and union reading, including subsumption. -/
theorem evalAction_eq_write_mark (σ : Env) (db : Database) (a : Action) :
    evalAction σ db a = (a.write σ).bind fun W =>
      (a.mark σ).map fun X => (db.addEqs W).addSubsumed X := by
  cases a with
  | expr e =>
    cases he : e.eval σ <;>
      simp [evalAction, Action.write, Action.mark, he, Database.addEqs,
        Database.addTerm, Database.addSubsumed, Set.union_singleton]
  | subsume f es =>
    cases hes : Expr.evalList es σ <;>
      simp [evalAction, Action.write, Action.mark, hes, Database.addEqs,
        Database.addTerm, Database.addSubsumed, Set.union_singleton]
  | union a b =>
    cases ha : a.eval σ <;> cases hb : b.eval σ <;>
      simp only [evalAction, Action.write, Action.mark, ha, hb,
        Option.bind_some, Option.bind_none, Option.map_none]
    split <;> simp [Database.addEqs, Database.addEq, Database.addSubsumed,
      Set.union_singleton]

theorem evalActions_eq_writes_marks (σ : Env) (db : Database) (as : List Action) :
    evalActions σ db as = (Action.writes σ as).bind fun W =>
      (Action.marks σ as).map fun X => (db.addEqs W).addSubsumed X := by
  induction as generalizing db with
  | nil => simp [evalActions, Action.writes, Action.marks, Database.addEqs]
  | cons a as ih =>
    rw [evalActions, evalAction_eq_write_mark]
    simp only [Action.writes, Action.marks]
    cases hw : a.write σ <;> cases hx : a.mark σ <;>
      cases hws : Action.writes σ as <;> cases hxs : Action.marks σ as <;>
      simp [ih, hw, hx, hws, hxs, Database.addEqs, Database.addSubsumed, Set.union_assoc]

theorem mem_ruleResults_iff_writes_marks {db d : Database} {r : Rule} :
    d ∈ RuleResults db r ↔ ∃ σ W X, QueryMatches db r.query σ ∧
      Action.writes σ r.actions = some W ∧ Action.marks σ r.actions = some X ∧
      d = (db.addEqs W).addSubsumed X := by
  rw [mem_ruleResults_iff_queryMatches]
  simp only [evalActions_eq_writes_marks, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨σ, hq, W, hW, X, hX, rfl⟩
    exact ⟨σ, W, X, hq, hW, hX, rfl⟩
  · rintro ⟨σ, W, X, hq, hW, hX, rfl⟩
    exact ⟨σ, hq, W, hW, X, hX, rfl⟩

/-- Firings commute: their results are unioned componentwise. -/
theorem RunRules.eq_sUnion (R : List Rule) (db : Database) :
    RunRules R db = db.sUnion {d | ∃ r ∈ R, d ∈ RuleResults db r} := by
  simp only [RunRules, mem_ruleResults_iff_queryMatches]

/-- The paper's pair presentation: all equations and marks are retained. -/
theorem RunRules.eq_pair (rs : List Rule) (db : Database) :
    RunRules rs db = ⟨db.eqs ∪ RunWrites rs db, db.subsumed ∪ RunMarks rs db⟩ := by
  have writes_marks : ∀ σ as W, Action.writes σ as = some W →
      ∃ X, Action.marks σ as = some X := by
    intro σ as W hW
    apply Option.isSome_iff_exists.mp
    rw [Action.marks_isSome, hW]
    rfl
  have marks_writes : ∀ σ as X, Action.marks σ as = some X →
      ∃ W, Action.writes σ as = some W := by
    intro σ as X hX
    apply Option.isSome_iff_exists.mp
    rw [← Action.marks_isSome, hX]
    rfl
  rw [RunRules.eq_sUnion]
  symm
  apply Database.ext
  · ext p
    simp only [Database.sUnion, RunWrites, Set.mem_union, Set.mem_sUnion,
      Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro (hp | ⟨W, ⟨r, hr, σ, hq, hW⟩, hpW⟩)
      · exact Or.inl hp
      · obtain ⟨X, hX⟩ := writes_marks σ r.actions W hW
        exact Or.inr ⟨(db.addEqs W).addSubsumed X,
          ⟨r, hr, mem_ruleResults_iff_writes_marks.mpr ⟨σ, W, X, hq, hW, hX, rfl⟩⟩,
          Or.inr hpW⟩
    · rintro (hp | ⟨d, ⟨r, hr, hd⟩, hp⟩)
      · exact Or.inl hp
      · obtain ⟨σ, W, X, hq, hW, hX, rfl⟩ := mem_ruleResults_iff_writes_marks.mp hd
        exact hp.elim Or.inl (fun hp => Or.inr ⟨W, ⟨r, hr, σ, hq, hW⟩, hp⟩)
  · ext t
    simp only [Database.sUnion, RunMarks, Set.mem_union, Set.mem_sUnion,
      Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro (ht | ⟨X, ⟨r, hr, σ, hq, hX⟩, htX⟩)
      · exact Or.inl ht
      · obtain ⟨W, hW⟩ := marks_writes σ r.actions X hX
        exact Or.inr ⟨(db.addEqs W).addSubsumed X,
          ⟨r, hr, mem_ruleResults_iff_writes_marks.mpr ⟨σ, W, X, hq, hW, hX, rfl⟩⟩,
          Or.inr htX⟩
    · rintro (ht | ⟨d, ⟨r, hr, hd⟩, ht⟩)
      · exact Or.inl ht
      · obtain ⟨σ, W, X, hq, hW, hX, rfl⟩ := mem_ruleResults_iff_writes_marks.mp hd
        exact ht.elim Or.inl (fun ht => Or.inr ⟨X, ⟨r, hr, σ, hq, hX⟩, ht⟩)

theorem RunRules.eq_addEqs {R : List Rule} {db : Database} (hdf : ∀ r ∈ R, r.SubsumeFree) :
    RunRules R db = db.addEqs (RunWrites R db) := by
  simp only [RunRules.eq_pair, RunMarks.eq_empty hdf, Set.union_empty, Database.addEqs]

@[simp] theorem RunRules.subsumed_eq {R : List Rule} {db : Database}
    (hdf : ∀ r ∈ R, r.SubsumeFree) : (RunRules R db).subsumed = db.subsumed := by
  rw [RunRules.eq_addEqs hdf]
  rfl

end Egglog
