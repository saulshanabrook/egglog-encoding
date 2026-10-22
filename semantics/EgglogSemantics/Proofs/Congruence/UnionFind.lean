import EgglogSemantics.Proofs.Congruence.Read
import EgglogSemantics.Proofs.Congruence.Properties

/-! Union-find roots for the single-output congruence tables. -/

namespace Egglog.Congruence

/-- A live parent edge that moves to a distinct value. -/
def UFRowEdge (d : FDatabase) (a b : Term) : Prop :=
  (⟨ufName, [a], [b]⟩ : Row) ∈ d.rows ∧ b ≠ a

/-- Reachability through live parent edges. -/
def UFRowReach (d : FDatabase) (a b : Term) : Prop :=
  Relation.ReflTransGen (UFRowEdge d) a b

/-- No nontrivial parent edge leaves a root. -/
def UFRowRoot (d : FDatabase) (a : Term) : Prop := ∀ b, ¬ UFRowEdge d a b

def rowKeyLe (a : Term) (r : Row) : Bool :=
  r.args.all fun k => Term.blt k a || k == a

def UFRowsDescend (d : FDatabase) : Prop :=
  ∀ a b, (UFRowEdge d) a b → Term.blt b a = true

def UFRowsForest (d : FDatabase) : Prop :=
  ∀ a b c, (UFRowEdge d) a b → (UFRowEdge d) a c → b = c

theorem ufRowsDescend_iff {d : FDatabase} : (UFRowsDescend d) ↔
    ∀ a b, (⟨ufName, [a], [b]⟩ : Row) ∈ d.rows → b = a ∨ Term.blt b a = true := by
  constructor
  · intro h a b hmem
    rcases eq_or_ne b a with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr (h a b ⟨hmem, hne⟩)
  · intro h a b hedge
    have hmem := hedge.1
    rcases h a b hmem with hba | hlt
    · exact absurd hba hedge.2
    · exact hlt

theorem UFRowsDescend.mono {d e : FDatabase} (h : (UFRowsDescend d))
    (hsub : ∀ r ∈ e.rows, r ∈ d.rows) : (UFRowsDescend e) := by
  intro a b hedge
  have hmem := hedge.1
  exact h a b ⟨hsub _ hmem, hedge.2⟩

theorem UFRowEdge.measure_lt {d : FDatabase} (hdes : (UFRowsDescend d)) {a b : Term}
    (h : (UFRowEdge d) a b) :
    (d.rows.filter (rowKeyLe b)).length < (d.rows.filter (rowKeyLe a)).length := by
  have hba : Term.blt b a = true := hdes a b h
  have hsub : List.Sublist (d.rows.filter (rowKeyLe b)) (d.rows.filter (rowKeyLe a)) := by
    refine List.monotone_filter_right _ (fun r hr => ?_)
    simp only [rowKeyLe, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hr ⊢
    intro k hk
    rcases hr k hk with hkb | rfl
    · exact Or.inl (Term.blt_trans k b a hkb hba)
    · exact Or.inl hba
  have hmem := h.1
  have hin : (⟨ufName, [a], [b]⟩ : Row) ∈ d.rows.filter (rowKeyLe a) :=
    List.mem_filter.mpr ⟨hmem, by simp [rowKeyLe]⟩
  have hout : (⟨ufName, [a], [b]⟩ : Row) ∉ d.rows.filter (rowKeyLe b) := by
    intro hc
    have hk := (List.mem_filter.mp hc).2
    simp only [rowKeyLe, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.mem_singleton] at hk
    rcases hk a rfl with hab | hab
    · exact absurd hab (by rw [Term.blt_asymm b a hba]; simp)
    · exact h.2 hab.symm
  rcases Nat.lt_or_ge (d.rows.filter (rowKeyLe b)).length
      (d.rows.filter (rowKeyLe a)).length with hlt | hge
  · exact hlt
  · exact absurd (hsub.eq_of_length_le hge ▸ hin) hout

theorem exists_ufRowRoot {d : FDatabase} (hdes : (UFRowsDescend d)) (a : Term) :
    ∃ r, (UFRowReach d) a r ∧ (UFRowRoot d) r := by
  have key : ∀ n : Nat, ∀ a : Term, (d.rows.filter (rowKeyLe a)).length = n →
      ∃ r, (UFRowReach d) a r ∧ (UFRowRoot d) r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha
      by_cases hroot : (UFRowRoot d) a
      · exact ⟨a, .refl, hroot⟩
      · obtain ⟨b, hb⟩ : ∃ b, (UFRowEdge d) a b := by
          simpa [UFRowRoot, not_forall] using hroot
        obtain ⟨r, hr, hrr⟩ := ih _ (ha ▸ hb.measure_lt hdes) b rfl
        exact ⟨r, .head hb hr, hrr⟩
  exact key _ a rfl

theorem UFRowRoot.reach_eq {d : FDatabase} {a b : Term} (hr : (UFRowRoot d) a)
    (h : (UFRowReach d) a b) : b = a := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) (hr _)

theorem ufRowRoot_unique {d : FDatabase} (hf : (UFRowsForest d)) {a r s : Term}
    (hr : (UFRowReach d) a r) (hrr : (UFRowRoot d) r) (hs : (UFRowReach d) a s)
    (hsr : (UFRowRoot d) s) : r = s := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hrr.reach_eq hs).symm
  | head hstep _ ih =>
      rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨c, hc, hcs⟩
      · exact absurd hstep (hsr _)
      · obtain rfl : c = _ := hf _ _ _ hc hstep
        exact ih hcs

theorem UFRowReach.le {d : FDatabase} (hdes : (UFRowsDescend d)) {a b : Term}
    (h : (UFRowReach d) a b) : b = a ∨ Term.blt b a = true := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hr hstep ih =>
      rcases ih with rfl | hlt
      · exact Or.inr (hdes _ _ hstep)
      · exact Or.inr (Term.blt_trans _ _ _ (hdes _ _ hstep) hlt)

end Egglog.Congruence
