import EgglogSemantics.Proofs.Term

/-! Size-first term ordering, independent of the executable interpreter. -/

namespace Egglog

/-! ### The term order

The structural tie-breaker orders literals, application arities, names, and argument
lists lexicographically. The public order compares node counts first, then uses that
strict total structural order. The list comparison is only total at equal lengths. -/
namespace Lit

/-- Asymmetry, totality and transitivity of the base-value order, each the integer law
under `decide`. `Term.blt`'s literal case is this one. -/
theorem blt_asymm {l m : Lit} (h : Lit.blt l m = true) : Lit.blt m l = false := by
  cases l; cases m; simp_all [Lit.blt]
  omega

theorem blt_total {l m : Lit} (h : l ≠ m) : Lit.blt l m = true ∨ Lit.blt m l = true := by
  cases l; cases m; simp_all [Lit.blt]

theorem blt_trans {l m n : Lit} (h₁ : Lit.blt l m = true) (h₂ : Lit.blt m n = true) :
    Lit.blt l n = true := by
  cases l; cases m; cases n; simp_all [Lit.blt]
  omega

end Lit

namespace Term
@[simp] theorem structuralBlt_lit_lit {l m : Lit} :
    Term.structuralBlt (.lit l) (.lit m) = Lit.blt l m := rfl

@[simp] theorem structuralBlt_lit_app {l : Lit} {f : FnName} {as : List Term} :
    Term.structuralBlt (.lit l) (.app f as) = true := rfl

@[simp] theorem structuralBlt_app_lit {f : FnName} {as : List Term} {l : Lit} :
    Term.structuralBlt (.app f as) (.lit l) = false := rfl

theorem structuralBlt_app_app {f g : FnName} {as bs : List Term} :
    Term.structuralBlt (.app f as) (.app g bs) =
      (if as.length ≠ bs.length then decide (as.length < bs.length)
       else if f ≠ g then decide (f < g) else Term.structuralBltList as bs) := rfl

@[simp] theorem structuralBltList_nil {bs : List Term} : Term.structuralBltList [] bs = false := rfl

@[simp] theorem structuralBltList_cons_nil {a : Term} {as : List Term} :
    Term.structuralBltList (a :: as) [] = false := rfl

theorem structuralBltList_cons_cons {a b : Term} {as bs : List Term} :
    Term.structuralBltList (a :: as) (b :: bs) =
      if a = b then Term.structuralBltList as bs else Term.structuralBlt a b := rfl

end Term
mutual

/-- Structural asymmetry, including argument lists without a length hypothesis. -/
theorem Term.structuralBlt_asymm (s t : Term) (h : Term.structuralBlt s t = true) :
    Term.structuralBlt t s = false := by
  match s, t with
  | .lit _, .lit _ =>
    rw [Term.structuralBlt_lit_lit] at h ⊢
    exact Lit.blt_asymm h
  | .lit _, .app _ _ => rfl
  | .app _ _, .lit _ => simp at h
  | .app f as, .app g bs =>
    rw [Term.structuralBlt_app_app] at h
    rw [Term.structuralBlt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl)] at h
      rw [if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf)] at h
        rw [if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.structuralBltList_asymm as bs h
      · rw [if_pos hf] at h
        rw [if_pos (Ne.symm hf), decide_eq_false_iff_not]
        simp only [decide_eq_true_eq] at h
        exact String.lt_asymm h
    · rw [if_pos hl] at h
      rw [if_pos (Ne.symm hl), decide_eq_false_iff_not]
      simp only [decide_eq_true_eq] at h
      omega

theorem Term.structuralBltList_asymm (as bs : List Term) (h : Term.structuralBltList as bs = true) :
    Term.structuralBltList bs as = false := by
  match as, bs with
  | [], _ => simp at h
  | _ :: _, [] => simp at h
  | a :: as, b :: bs =>
    rw [Term.structuralBltList_cons_cons] at h
    rw [Term.structuralBltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h
      rw [if_pos hab.symm]
      exact Term.structuralBltList_asymm as bs h
    · rw [if_neg hab] at h
      rw [if_neg (Ne.symm hab)]
      exact Term.structuralBlt_asymm a b h

end

mutual

/-- Structural totality. The argument-list comparison is used only at equal lengths. -/
theorem Term.structuralBlt_total (s t : Term) (h : s ≠ t) :
    Term.structuralBlt s t = true ∨ Term.structuralBlt t s = true := by
  match s, t with
  | .lit _, .lit _ =>
    rw [Term.structuralBlt_lit_lit, Term.structuralBlt_lit_lit]
    exact Lit.blt_total fun hlm => h (by rw [hlm])
  | .lit _, .app _ _ => exact Or.inl (by simp)
  | .app _ _, .lit _ => exact Or.inr (by simp)
  | .app f as, .app g bs =>
    rw [Term.structuralBlt_app_app, Term.structuralBlt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl), if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf), if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.structuralBltList_total as bs hl fun hab => h (by rw [hab])
      · rw [if_pos hf, if_pos (Ne.symm hf)]
        simp only [decide_eq_true_eq]
        by_cases hfg : f < g
        · exact Or.inl hfg
        · refine Or.inr ?_
          by_contra hgf
          exact hf (String.le_antisymm (String.not_lt.mp hgf) (String.not_lt.mp hfg))
    · rw [if_pos hl, if_pos (Ne.symm hl)]
      simp only [decide_eq_true_eq]
      omega

theorem Term.structuralBltList_total (as bs : List Term) (hlen : as.length = bs.length)
    (h : as ≠ bs) : Term.structuralBltList as bs = true ∨ Term.structuralBltList bs as = true := by
  match as, bs with
  | [], [] => exact absurd rfl h
  | [], _ :: _ => simp at hlen
  | _ :: _, [] => simp at hlen
  | a :: as, b :: bs =>
    rw [Term.structuralBltList_cons_cons, Term.structuralBltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab.symm]
      subst hab
      exact Term.structuralBltList_total as bs (by simpa using hlen) fun hh => h (by rw [hh])
    · rw [if_neg hab, if_neg (Ne.symm hab)]
      exact Term.structuralBlt_total a b hab

end

mutual

/-- Structural transitivity. The list case uses asymmetry to show that its endpoint
heads differ before the lexicographic comparison can fire. -/
theorem Term.structuralBlt_trans (s t u : Term) (h₁ : Term.structuralBlt s t = true)
    (h₂ : Term.structuralBlt t u = true) : Term.structuralBlt s u = true := by
  match s, t, u with
  | .lit _, .lit _, .lit _ =>
    rw [Term.structuralBlt_lit_lit] at h₁ h₂ ⊢
    exact Lit.blt_trans h₁ h₂
  | .lit _, .lit _, .app _ _ => simp
  | .lit _, .app _ _, .lit _ => simp at h₂
  | .lit _, .app _ _, .app _ _ => simp
  | .app _ _, .lit _, _ => simp at h₁
  | .app _ _, .app _ _, .lit _ => simp at h₂
  | .app f as, .app g bs, .app e cs =>
    rw [Term.structuralBlt_app_app] at h₁ h₂
    rw [Term.structuralBlt_app_app]
    by_cases hab : as.length = bs.length
    · rw [if_neg (not_not_intro hab)] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        rw [if_neg (not_not_intro (hab.trans hbc))]
        by_cases hfg : f = g
        · rw [if_neg (not_not_intro hfg)] at h₁
          by_cases hge : g = e
          · rw [if_neg (not_not_intro hge)] at h₂
            rw [if_neg (not_not_intro (hfg.trans hge))]
            subst hfg; subst hge
            exact Term.structuralBltList_trans as bs cs h₁ h₂
          · rw [if_pos hge] at h₂
            have hfe : f ≠ e := by rintro rfl; exact hge hfg.symm
            rw [if_pos hfe]
            subst hfg
            exact h₂
        · rw [if_pos hfg] at h₁
          by_cases hge : g = e
          · have hfe : f ≠ e := by rintro rfl; exact hfg hge.symm
            rw [if_pos hfe]
            subst hge
            exact h₁
          · rw [if_pos hge] at h₂
            simp only [decide_eq_true_eq] at h₁ h₂
            have hlt : f < e := String.lt_trans h₁ h₂
            have hfe : f ≠ e := by rintro rfl; exact String.lt_irrefl f hlt
            rw [if_pos hfe, decide_eq_true_eq]
            exact hlt
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
    · rw [if_pos hab] at h₁
      simp only [decide_eq_true_eq] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega

theorem Term.structuralBltList_trans (as bs cs : List Term)
    (h₁ : Term.structuralBltList as bs = true)
    (h₂ : Term.structuralBltList bs cs = true) : Term.structuralBltList as cs = true := by
  match as, bs, cs with
  | [], _, _ => simp at h₁
  | _ :: _, [], _ => simp at h₁
  | _ :: _, _ :: _, [] => simp at h₂
  | a :: as, b :: bs, c :: cs =>
    rw [Term.structuralBltList_cons_cons] at h₁ h₂
    rw [Term.structuralBltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h₁
      by_cases hbc : b = c
      · rw [if_pos hbc] at h₂
        rw [if_pos (hab.trans hbc)]
        exact Term.structuralBltList_trans as bs cs h₁ h₂
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by rintro rfl; exact hbc hab.symm
        rw [if_neg hac, hab]
        exact h₂
    · rw [if_neg hab] at h₁
      by_cases hbc : b = c
      · have hac : a ≠ c := by rintro rfl; exact hab hbc.symm
        rw [if_neg hac, ← hbc]
        exact h₁
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by
          rintro rfl
          rw [Term.structuralBlt_asymm a b h₁] at h₂
          simp at h₂
        rw [if_neg hac]
        exact Term.structuralBlt_trans a b c h₁ h₂

end

namespace Term

@[simp] theorem nodeSize_lit (l : Lit) : (Term.lit l).nodeSize = 1 := rfl

@[simp] theorem nodeSize_app (f : FnName) (as : List Term) :
    (Term.app f as).nodeSize = 1 + nodeSizeList as := rfl

@[simp] theorem nodeSizeList_nil : nodeSizeList [] = 0 := rfl

@[simp] theorem nodeSizeList_cons (a : Term) (as : List Term) :
    nodeSizeList (a :: as) = a.nodeSize + nodeSizeList as := rfl

theorem nodeSize_pos (t : Term) : 0 < t.nodeSize := by
  cases t <;> simp only [nodeSize_lit, nodeSize_app] <;> omega

/-- Every immediate argument contributes its entire size to the argument list. -/
theorem nodeSize_le_nodeSizeList {a : Term} {as : List Term} (ha : a ∈ as) :
    a.nodeSize ≤ nodeSizeList as := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · have := ih ha
      simp only [nodeSizeList_cons]
      omega

/-- Wrapping any argument strictly increases its size, independently of names. -/
theorem nodeSize_lt_app {a : Term} {f : FnName} {as : List Term} (ha : a ∈ as) :
    a.nodeSize < (Term.app f as).nodeSize := by
  have := nodeSize_le_nodeSizeList ha
  simp only [nodeSize_app]
  omega

theorem IsSubterm.nodeSize_le {s t : Term} (h : IsSubterm s t) :
    s.nodeSize ≤ t.nodeSize := by
  induction h with
  | refl => exact Nat.le_refl _
  | arg ha _ ih => exact Nat.le_trans ih (Nat.le_of_lt (nodeSize_lt_app ha))

/-- Proper subterms are strictly smaller in the primary comparison key. -/
theorem IsSubterm.nodeSize_lt {s t : Term} (h : IsSubterm s t) (hne : s ≠ t) :
    s.nodeSize < t.nodeSize := by
  cases h with
  | refl => exact False.elim (hne rfl)
  | arg ha hs => exact Nat.lt_of_le_of_lt hs.nodeSize_le (nodeSize_lt_app ha)

theorem blt_iff {s t : Term} : blt s t = true ↔
    s.nodeSize < t.nodeSize ∨
      (s.nodeSize = t.nodeSize ∧ structuralBlt s t = true) := by
  unfold blt
  by_cases h : s.nodeSize = t.nodeSize <;> simp [h]

@[simp] theorem blt_lit_lit {l m : Lit} : Term.blt (.lit l) (.lit m) = Lit.blt l m := by
  simp [blt]

@[simp] theorem blt_lit_app {l : Lit} {f : FnName} {as : List Term} :
    Term.blt (.lit l) (.app f as) = true := by
  rw [blt_iff]
  by_cases h : nodeSizeList as = 0
  · exact Or.inr ⟨by simp [h], rfl⟩
  · exact Or.inl (by simp; omega)

@[simp] theorem blt_app_lit {f : FnName} {as : List Term} {l : Lit} :
    Term.blt (.app f as) (.lit l) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rcases blt_iff.mp h with hs | ⟨_, hs⟩
  · simp only [nodeSize_app, nodeSize_lit] at hs
    omega
  · simp at hs

theorem blt_app_app {f g : FnName} {as bs : List Term} :
    Term.blt (.app f as) (.app g bs) =
      (if nodeSizeList as ≠ nodeSizeList bs then
        decide (nodeSizeList as < nodeSizeList bs)
       else if as.length ≠ bs.length then decide (as.length < bs.length)
       else if f ≠ g then decide (f < g) else structuralBltList as bs) := by
  simp [blt, structuralBlt_app_app]

theorem blt_asymm (s t : Term) (h : Term.blt s t = true) : Term.blt t s = false := by
  apply Bool.eq_false_iff.mpr
  intro hrev
  rw [blt_iff] at h hrev
  rcases h with h | ⟨hs, h⟩
  · omega
  · have hn := structuralBlt_asymm s t h
    simp [hs, hn] at hrev

theorem blt_total (s t : Term) (h : s ≠ t) :
    Term.blt s t = true ∨ Term.blt t s = true := by
  rw [blt_iff, blt_iff]
  by_cases hs : s.nodeSize = t.nodeSize
  · rcases structuralBlt_total s t h with h | h
    · exact Or.inl (Or.inr ⟨hs, h⟩)
    · exact Or.inr (Or.inr ⟨hs.symm, h⟩)
  · omega

theorem blt_trans (s t u : Term) (h₁ : Term.blt s t = true)
    (h₂ : Term.blt t u = true) : Term.blt s u = true := by
  rw [blt_iff] at h₁ h₂ ⊢
  rcases h₁ with h₁ | ⟨hs, h₁⟩
  · rcases h₂ with h₂ | ⟨ht, _⟩ <;> exact Or.inl (by omega)
  · rcases h₂ with h₂ | ⟨ht, h₂⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hs.trans ht, structuralBlt_trans s t u h₁ h₂⟩

@[simp] theorem blt_self (t : Term) : blt t t = false := by
  cases h : blt t t
  · rfl
  · simpa [h] using blt_asymm t t h

theorem nodeSize_le_of_blt {s t : Term} (h : blt s t = true) :
    s.nodeSize ≤ t.nodeSize := by
  rcases blt_iff.mp h with h | ⟨h, _⟩ <;> omega

theorem blt_of_nodeSize_lt {s t : Term} (h : s.nodeSize < t.nodeSize) :
    blt s t = true := blt_iff.mpr (Or.inl h)

/-- The public order puts every proper subterm strictly below its enclosing term. -/
theorem IsSubterm.blt {s t : Term} (h : IsSubterm s t) (hne : s ≠ t) :
    blt s t = true := blt_of_nodeSize_lt (h.nodeSize_lt hne)

end Term

/-- `Term.blt` is a strict linear order. Needed for `min` to be a deterministic choice, and
for "keep the smaller side" to descend. -/
theorem Term.blt_linear : (∀ s t : Term, Term.blt s t = true → Term.blt t s = false) ∧
    (∀ s t : Term, s ≠ t → Term.blt s t = true ∨ Term.blt t s = true) ∧
    (∀ s t u : Term, Term.blt s t = true → Term.blt t u = true → Term.blt s u = true) :=
  ⟨Term.blt_asymm, Term.blt_total, Term.blt_trans⟩

/-! ### `min`, against what it replaces

`Term.least s t` is egglog's `ordering-min`: the right operand when it is strictly below the
left one, else the left. Read the other way round — the left operand when it is strictly
below the right one, else the right — it is the same choice, by `Term.blt_total`: the only
inputs where the two readings could differ are the ones with neither term below the other,
where totality says the two terms are equal. -/

/-- `Term.least`, branching on the other comparison. -/
theorem Term.least_eq_ite (s t : Term) :
    Term.least s t = if Term.blt s t then s else t := by
  unfold Term.least
  by_cases hst : Term.blt s t = true
  · rw [if_pos hst, if_neg (by rw [Term.blt_asymm s t hst]; simp)]
  · rw [if_neg hst]
    by_cases hts : Term.blt t s = true
    · rw [if_pos hts]
    · rw [if_neg hts]
      rcases eq_or_ne s t with rfl | hne
      · rfl
      · exact (Term.blt_total s t hne).elim (absurd · hst) (absurd · hts)

end Egglog
