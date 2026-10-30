import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Merge

/-! Surviving matching-domain and non-vacuity counterexamples. -/

namespace Egglog.Falsity

def t0 : Term := .lit (.int 0)

/-- `FDatabase.empty` holding just `t0`. -/
def dEx : FDatabase := FDatabase.empty.addTerm t0

theorem dEx_inv : dEx.Closed := FDatabase.empty_closed.addTerm t0

theorem t0_mem : t0 ∈ dEx.terms := FDatabase.self_mem_addTerm _ _

/-- `t0` is its own witness. There is no `Cong.refl`, so this is the *asserted* reflexive
equation `addTerm` wrote, read back. -/
theorem t0_cong : (t0,t0) ∈ (dEx.addTerm t0).closureF :=
  (FDatabase.mem_closureF_iff (dEx_inv.addTerm t0).subterms
    (FDatabase.self_mem_addTerm _ _) (FDatabase.self_mem_addTerm _ _)).mpr
    (Database.toCong ((FDatabase.mem_toDatabase_terms (dEx_inv.addTerm t0).subterms).mpr
      (FDatabase.self_mem_addTerm _ _)))

/-- The pattern `0` matches under a substitution binding `x`, which the pattern does not
mention: `patternHolds` reads `σ` only through `d.env ++ σ`. -/
theorem holds_lit : patternHolds dEx (.expr (.lit (.int 0))) [("x", t0)] = true := by
  simp only [patternHolds, Expr.eval, decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

/-- **`FDatabase.patternHolds_validSubst` is false without `ValidEnv`.**
`ValidSubst` carries `ValidEnv (p.freeVars db.env) db σ`, which pins `Env.dom σ` to
a permutation of the pattern's free variables; `(Expr.lit _).freeVars` is `[]` and `σ`
binds `x`. -/
theorem patternHolds_validSubst_false :
    ¬ ∀ (d : FDatabase), d.Closed → ∀ (p : Pattern) (σ : Env),
        patternHolds d p σ = true → ValidSubst d.toDatabase p σ := by
  intro H
  have hbad := H dEx dEx_inv (.expr (.lit (.int 0))) [("x", t0)] holds_lit
  simpa [Env.dom, Pattern.freeVars, Expr.freeVars] using hbad.1.1

/-- Two patterns sharing the variable `x`. `Query.freeVars qEx dEx.env = ["x"]`: the
`∪` in `Query.freeVars` deduplicates, so the enumerator assigns `x` once. -/
def qEx : Query := [Pattern.expr (.var "x"), Pattern.expr (.var "x")]

theorem holds_var : patternHolds dEx (.expr (.var "x")) [("x", t0)] = true := by
  change decide (∃ w ∈ dEx.terms, (w, t0) ∈ (dEx.addTerm t0).closureF) = true
  rw [decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

theorem mem_matchQuery_ex : [("x", t0)] ∈ matchQuery dEx qEx := by
  rw [matchQuery, List.mem_filter]
  constructor
  · refine mem_assignments.mpr ⟨rfl, ?_⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact t0_mem
  · change (patternHolds dEx (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) &&
      (patternHolds dEx (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) && true)) = true
    rw [show Env.canon ["x"] [("x", t0)] = [("x", t0)] from rfl, holds_var]
    rfl

/-- `Env.UnionAll` is concatenation: `Union2` fixes `σr = σ₁ ++ σ₂` and the fold ends at
`UnionAll [σ] σ`, so lengths add. This is what the enumerator cannot satisfy. -/
theorem unionAll_sum_length {σs : List Env} {σ : Env} (h : Env.UnionAll σs σ) :
    (σs.map List.length).sum = σ.length := by
  induction h with
  | nil => simp
  | single σ => simp
  | step hu _ ih =>
    obtain ⟨-, rfl⟩ := hu
    simp only [List.map_cons, List.sum_cons, List.length_append] at ih ⊢
    omega

/-- **`FDatabase.matchQuery_validQuerySubst` is false without `Env.Agree`.**
`[("x", t0)]` is enumerated for `qEx`, and `ValidEnv` holds for it at *both* patterns — so
this is not the `ValidEnv` defect again. `ValidQuerySubst` needs one substitution per
pattern, each of length `1`, concatenated to give `σ`; that would make `σ` have length
`2`. -/
theorem matchQuery_validQuerySubst_false :
    ¬ ∀ (d : FDatabase), d.Closed → ∀ (q : Query) (σ : Env),
        σ ∈ matchQuery d q → ValidQuerySubst d.toDatabase q σ := by
  intro H
  obtain ⟨σs, hall, hu⟩ := H dEx dEx_inv qEx [("x", t0)] mem_matchQuery_ex
  have hlen : ∀ ρ, ValidSubst dEx.toDatabase (.expr (.var "x")) ρ → ρ.length = 1 := by
    intro ρ hρ
    have := hρ.1.1.length_eq
    simpa [Env.dom, Pattern.freeVars, Expr.freeVars, Env.lookup]
      using this
  cases hall with
  | cons h1 hrest =>
    cases hrest with
    | cons h2 hnil =>
      cases hnil with
      | nil =>
        have := unionAll_sum_length hu
        simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
          hlen _ h1, hlen _ h2] at this
        simp at this

/-- An empty assertion set cannot derive even reflexivity. -/
theorem not_cong_of_no_eqs {db : Database} (h : db.eqs = ∅) {a b : Term} : ¬ Cong db a b := by
  intro hc
  induction hc using Cong.rec (motive_2 := fun _ _ _ => True) with
  | direct hp => rw [h] at hp; exact hp
  | subterm _ _ ih => exact ih
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | congr _ _ ih _ => exact ih
  | nil => trivial
  | cons => trivial

theorem not_matches_empty {p : Pattern} {σ : Env} : ¬ Matches Database.empty p σ := by
  intro h
  cases h with
  | atom _ hc => exact not_cong_of_no_eqs rfl hc
  | equal _ _ hc => exact not_cong_of_no_eqs rfl hc
  | unequal _ _ hc _ _ => exact not_cong_of_no_eqs rfl hc

theorem recorded_empty {d : Database} (h : d.Recorded Database.empty) : d.eqs = ∅ :=
  Set.eq_empty_of_forall_notMem fun p hp =>
    absurd (h.eqs p hp).choose_spec.1 (Set.notMem_empty _)

namespace Choice

theorem recorded_iff_subset {d e : Database} (h : e.Diag) : d.Recorded e ↔ d.eqs ⊆ e.eqs :=
  ⟨fun hr => (hr.contained_of_diag h).eqs, fun hs => Database.Recorded.of_contained ⟨hs⟩⟩

end Choice
end Egglog.Falsity
