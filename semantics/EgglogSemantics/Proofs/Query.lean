import EgglogSemantics.Spec.Sequential
import EgglogSemantics.Proofs.Match

/-! Single-substitution queries agree with the join representation. -/

namespace Egglog

/-- Atom and equality matching read the single semantic relation. -/
theorem Matches.expr_iff_cong {db : Database} {e : Expr} {σ : Env} :
    Matches db (.expr e) σ ↔ ∃ t, e.eval σ = some t ∧ Cong db t t := by
  constructor
  · rintro h
    cases h with | atom he hc => exact ⟨_, he, hc⟩
  · rintro ⟨t, he, hc⟩
    exact .atom he hc

theorem Matches.eq_iff_cong {db : Database} {a b : Expr} {σ : Env} :
    Matches db (.eq a b) σ ↔
      ∃ s t, a.eval σ = some s ∧ b.eval σ = some t ∧ Cong db s t := by
  constructor
  · rintro h
    cases h with | equal ha hb hc => exact ⟨_, _, ha, hb, hc⟩
  · rintro ⟨s, t, ha, hb, hc⟩
    exact .equal ha hb hc

theorem Matches.expr_iff_infers {db : Database} {e : Expr} {σ : Env} :
    Matches db (.expr e) σ ↔ ∃ t, e.eval σ = some t ∧ db.Infers t t := by
  simp only [expr_iff_cong, InferredFacts.congr_iff_infers]

theorem Matches.eq_iff_infers {db : Database} {a b : Expr} {σ : Env} :
    Matches db (.eq a b) σ ↔
      ∃ s t, a.eval σ = some s ∧ b.eval σ = some t ∧ db.Infers s t := by
  simp only [eq_iff_cong, InferredFacts.congr_iff_infers]

private def selectEnv (vars : List Var) (σ : Env) : Env :=
  vars.filterMap fun v => (Env.lookup v σ).map (v, ·)

private theorem mem_selectEnv {vars : List Var} {σ : Env} {b : Var × Term}
    (h : b ∈ selectEnv vars σ) : b.1 ∈ vars ∧ Env.lookup b.1 σ = some b.2 := by
  obtain ⟨v, hv, hb⟩ := List.mem_filterMap.mp h
  cases hlk : Env.lookup v σ with
  | none => rw [hlk] at hb; simp at hb
  | some t =>
    rw [hlk] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    exact ⟨hb ▸ hv, hb ▸ hlk⟩

private theorem dom_selectEnv_subset {vars : List Var} {σ : Env} :
    Env.dom (selectEnv vars σ) ⊆ vars := fun _ hv =>
  (mem_selectEnv (Env.mem_dom_iff.mp hv).choose_spec).1

private theorem selectEnv_cons_none {v : Var} {vs : List Var} {σ : Env}
    (h : Env.lookup v σ = none) : selectEnv (v :: vs) σ = selectEnv vs σ := by
  simp [selectEnv, h]

private theorem selectEnv_cons_some {v : Var} {vs : List Var} {σ : Env} {t : Term}
    (h : Env.lookup v σ = some t) : selectEnv (v :: vs) σ = (v, t) :: selectEnv vs σ := by
  simp [selectEnv, h]

private theorem dom_selectEnv {vars : List Var} {σ : Env}
    (h : ∀ v ∈ vars, (Env.lookup v σ).isSome) : Env.dom (selectEnv vars σ) = vars := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h v (by simp))
    rw [selectEnv_cons_some ht, Env.dom_cons, ih fun w hw => h w (by simp [hw])]

private theorem lookup_selectEnv {vars : List Var} {σ : Env} (hnd : vars.Nodup) {v : Var}
    (hv : v ∈ vars) : Env.lookup v (selectEnv vars σ) = Env.lookup v σ := by
  induction vars with
  | nil => simp at hv
  | cons w vs ih =>
    rw [List.nodup_cons] at hnd
    cases hlk : Env.lookup w σ with
    | none =>
      rw [selectEnv_cons_none hlk]
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hlk]
        exact Env.lookup_eq_none_iff.mpr fun hc => hnd.1 (dom_selectEnv_subset hc)
      · exact ih hnd.2 hv
    | some t =>
      rw [selectEnv_cons_some hlk, Env.lookup_cons]
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [hlk]
      · rw [if_neg (fun hc : v = w => hnd.1 (hc ▸ hv)), ih hnd.2 hv]

theorem querySubst_of_matches_terms {db : Database} {q : Query} {σ : Env}
    (hdom : (Env.dom σ).Perm q.vars) (hval : ∀ b ∈ σ, b.2 ∈ db.terms)
    (hm : ∀ p ∈ q, Matches db p σ) :
    ∃ τ, ValidQuerySubst db q τ ∧ Env.Agree τ σ := by
  have hpvar : ∀ p ∈ q, ∀ v ∈ p.freeVars [], v ∈ Env.dom σ := by
    intro p hp v hv
    exact hdom.mem_iff.mpr (Query.mem_vars.mpr ⟨p, hp, (p.mem_freeVars.mp hv).1⟩)
  have hcanon : ∀ p ∈ q, Env.dom (selectEnv (p.freeVars []) σ) = p.freeVars [] := by
    intro p hp
    exact dom_selectEnv fun v hv => Env.lookup_isSome_iff_mem_dom.mpr (hpvar p hp v hv)
  have hvsub : ∀ p ∈ q, ValidSubst db p (selectEnv (p.freeVars []) σ) := by
    intro p hp
    refine ⟨⟨by rw [hcanon p hp], ?_⟩, (hm p hp).of_agreeOn ?_⟩
    · intro b hb
      exact hval b (Env.mem_of_lookup (mem_selectEnv hb).2)
    · intro v hv
      exact (lookup_selectEnv (p.freeVars_nodup [])
        (p.mem_freeVars.mpr ⟨hv, by simp [Env.dom]⟩)).symm
  obtain ⟨τ, hu, hr⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => selectEnv (p.freeVars []) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact fun _ hb => (mem_selectEnv hb).2)
  refine ⟨τ, ⟨_, List.forall₂_map_self hvsub, hu⟩, Env.agree_of_refines hr ?_⟩
  intro v hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp (hdom.mem_iff.mp hv)
  refine hu.mem_dom_iff.mpr ⟨selectEnv (p.freeVars []) σ, List.mem_map_of_mem hp, ?_⟩
  rw [hcanon p hp]
  exact p.mem_freeVars.mpr ⟨hvp, by simp [Env.dom]⟩
theorem querySubst_of_matches {db : Database} {q : Query} {σ : Env}
    (hdom : (Env.dom σ).Perm q.vars) (hval : ∀ b ∈ σ, b.2 ∈ db.terms)
    (hm : ∀ p ∈ q, Matches db p σ) :
    ∃ τ, ValidQuerySubst db q τ ∧ Env.Agree τ σ :=
  querySubst_of_matches_terms hdom hval hm

/-- Query variables are deduplicated. -/
theorem Query.vars_nodup (q : Query) : q.vars.Nodup := by
  induction q with
  | nil => simp [Query.vars]
  | cons p ps ih => exact List.Nodup.union _ ih

namespace QueryMatches

/-- A whole-query substitution binds each variable once. -/
theorem nodup {db : Database} {q : Query} {σ : Env}
    (h : QueryMatches db q σ) : (Env.dom σ).Nodup :=
  h.1.1.symm.nodup q.vars_nodup

/-- Splitting a whole-query substitution into pattern matches preserves every lookup. -/
theorem exists_validQuerySubst {db : Database} {q : Query} {σ : Env}
    (h : QueryMatches db q σ) :
    ∃ τ, ValidQuerySubst db q τ ∧ Env.Agree τ σ :=
  querySubst_of_matches_terms h.1.1 h.1.2 h.2

end QueryMatches

namespace ValidQuerySubst

/-- Joining can duplicate bindings; choosing one per variable preserves every lookup. -/
theorem exists_queryMatches {db : Database} {q : Query} {σ : Env}
    (h : ValidQuerySubst db q σ) :
    ∃ τ, QueryMatches db q τ ∧ Env.Agree τ σ := by
  have hdom : ∀ v, v ∈ Env.dom σ ↔ v ∈ q.vars := by
    intro v
    rw [h.mem_dom_iff, Query.mem_vars]
    constructor
    · rintro ⟨p, hp, hv⟩
      exact ⟨p, hp, (p.mem_freeVars.mp hv).1⟩
    · rintro ⟨p, hp, hv⟩
      exact ⟨p, hp, p.mem_freeVars.mpr ⟨hv, by simp [Env.dom]⟩⟩
  have hselected : Env.dom (selectEnv q.vars σ) = q.vars :=
    dom_selectEnv fun v hv => Env.lookup_isSome_iff_mem_dom.mpr ((hdom v).mpr hv)
  have hag : Env.Agree (selectEnv q.vars σ) σ :=
    Env.agree_of_refines (fun _ hb => (mem_selectEnv hb).2) (by
      intro v hv
      rw [hselected]
      exact (hdom v).mp hv)
  refine ⟨selectEnv q.vars σ, ⟨⟨?_, ?_⟩, ?_⟩, hag⟩
  · rw [hselected]
  · intro b hb
    exact h.mem_terms b (Env.mem_of_lookup (mem_selectEnv hb).2)
  · intro p hp
    exact (h.matches_of_mem hp).of_agreeOn fun v _ => (hag v).symm

end ValidQuerySubst

theorem queryHolds_iff_queryMatches {db : Database} {q : Query} :
    QueryHolds db q ↔ ∃ σ, QueryMatches db q σ := Iff.rfl

/-- Checks hold under the join representation of query matches. -/
theorem queryHolds_iff_validQuerySubst {db : Database} {q : Query} :
    QueryHolds db q ↔ ∃ σ, ValidQuerySubst db q σ := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ, _⟩ := hσ.exists_validQuerySubst
    exact ⟨τ, hτ⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ, _⟩ := hσ.exists_queryMatches
    exact ⟨τ, hτ⟩

/-- Rule firings produce exactly the same databases under either representation. -/
theorem mem_ruleResults_iff_queryMatches {db d : Database} {r : Rule} :
    d ∈ RuleResults db r ↔
      ∃ σ, QueryMatches db r.query σ ∧ evalActions σ db r.actions = some d := by
  constructor
  · rintro ⟨σ, hσ, he⟩
    obtain ⟨τ, hτ, hag⟩ := hσ.exists_queryMatches
    exact ⟨τ, hτ, (evalActions_agree hag db r.actions).trans he⟩
  · rintro ⟨σ, hσ, he⟩
    obtain ⟨τ, hτ, hag⟩ := hσ.exists_validQuerySubst
    exact ⟨τ, hτ, (evalActions_agree hag db r.actions).trans he⟩

end Egglog
