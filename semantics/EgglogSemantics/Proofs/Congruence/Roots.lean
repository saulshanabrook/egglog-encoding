import EgglogSemantics.Proofs.Congruence.History

/-! Historical UF paths and the roots found in the live row index. -/

namespace Egglog.Congruence

open Egglog.FDatabase (firstArgLe filter_firstArgLe_le)

/-- Recorded UF edges point downward in the structural ordering, allowing self-loops. -/
def UFTermsDescend (d : FDatabase) : Prop :=
  ∀ a b, UFStep d a b → b = a ∨ Term.blt b a = true

/-- A sound index transfers historical descent to the live rows. -/
theorem UFTermsDescend.rows {d : FDatabase} (h : UFTermsDescend d) (hi : d.IndexOk)
    (hr : d.EqsRefl) (huf : d.sig.mergeOf ufName ≠ none) : UFRowsDescend d := by
  apply ufRowsDescend_iff.mpr
  intro a b hm
  obtain ⟨bs, hcl, ht⟩ := hi.entry _ hm huf
  obtain rfl : [a] = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
  rw [Egglog.FDatabase.toDatabase_terms] at ht
  exact h a b ht

/-- A nontrivial historical edge strictly decreases a measure over the finite term store. -/
theorem UFStep.measure_lt {d : FDatabase} (hdes : UFTermsDescend d) {a b : Term}
    (h : UFStep d a b) (hne : b ≠ a) :
    (d.terms.filter (firstArgLe b)).length < (d.terms.filter (firstArgLe a)).length := by
  have hba : Term.blt b a = true := (hdes a b h).resolve_left hne
  have hsub : List.Sublist (d.terms.filter (firstArgLe b)) (d.terms.filter (firstArgLe a)) :=
    List.monotone_filter_right _ fun _ ht => Egglog.FDatabase.firstArgLe_mono hba ht
  have hin : Term.app ufName [a, b] ∈ d.terms.filter (firstArgLe a) :=
    List.mem_filter.mpr ⟨h, by simp [firstArgLe]⟩
  have hout : Term.app ufName [a, b] ∉ d.terms.filter (firstArgLe b) := by
    intro hc
    have hk := (List.mem_filter.mp hc).2
    simp only [firstArgLe, Bool.or_eq_true, beq_iff_eq] at hk
    rcases hk with hab | hab
    · rw [Term.blt_asymm b a hba] at hab
      contradiction
    · exact hne hab.symm
  rcases Nat.lt_or_ge (d.terms.filter (firstArgLe b)).length
      (d.terms.filter (firstArgLe a)).length with hlt | hge
  · exact hlt
  · exact absurd (hsub.eq_of_length_le hge ▸ hin) hout

theorem UFReach.le {d : FDatabase} (hdes : UFTermsDescend d) {a b : Term}
    (h : UFReach d a b) : b = a ∨ Term.blt b a = true := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      rcases hdes _ _ hstep with rfl | hlt
      · exact ih
      · rcases ih with rfl | hlt'
        · exact Or.inr hlt
        · exact Or.inr (Term.blt_trans _ _ _ hlt hlt')

/-- A retained edge and its live replacement lead to the same root. The row bridge may
return a historical path; strong induction discharges every edge of that smaller path. -/
theorem ufRowRoot_of_ufStep {d : FDatabase} (hbr : EntryRowsUF d)
    (hdc : d.sig ufName = some (tableDecl 1)) (hrd : UFRowsDescend d)
    (hfor : UFRowsForest d) (htd : UFTermsDescend d) :
    ∀ a b, UFStep d a b → ∀ r s, UFRowReach d a r → UFRowRoot d r →
      UFRowReach d b s → UFRowRoot d s → r = s := by
  have key : ∀ n : Nat, ∀ a : Term, (d.terms.filter (firstArgLe a)).length = n →
      ∀ b, UFStep d a b → ∀ r s, UFRowReach d a r → UFRowRoot d r →
        UFRowReach d b s → UFRowRoot d s → r = s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a hn b hstep r s har hrr hbs hsr
      rcases eq_or_ne b a with rfl | hne
      · exact ufRowRoot_unique hfor har hrr hbs hsr
      · obtain ⟨v, hv, hbv⟩ := hbr ufName (tableDecl 1) hdc mergeBody mergeResult rfl
          [a] b rfl hstep
        have hva : UFRowReach d a v := by
          rcases eq_or_ne v a with rfl | hne
          · exact .refl
          · exact .single ⟨hv, hne⟩
        obtain ⟨t, hvt, htr⟩ := exists_ufRowRoot hrd v
        have hvr : UFRowReach d v r :=
          ufRowRoot_unique hfor (hva.trans hvt) htr har hrr ▸ hvt
        have hbnd : ∀ c, UFReach d b c →
            (d.terms.filter (firstArgLe c)).length < n := by
          intro c hbc
          have h₁ : (d.terms.filter (firstArgLe c)).length
              ≤ (d.terms.filter (firstArgLe b)).length :=
            filter_firstArgLe_le (hbc.le htd)
          have h₂ : (d.terms.filter (firstArgLe b)).length < n :=
            hn ▸ hstep.measure_lt htd hne
          omega
        have chain : ∀ y, UFReach d b y →
            ∀ q, UFRowReach d y q → UFRowRoot d q → q = s := by
          intro y hby
          induction hby with
          | refl => intro q hq hqr; exact ufRowRoot_unique hfor hq hqr hbs hsr
          | @tail c y' hbc hstep2 ihc =>
              intro q hq hqr
              obtain ⟨u, hcu, hur⟩ := exists_ufRowRoot hrd c
              have hus : u = s := ihc u hcu hur
              have huq : u = q := ih _ (hbnd c hbc) c rfl y' hstep2 u q hcu hur hq hqr
              rw [← huq]
              exact hus
        exact chain v hbv r hvr hrr
  exact fun a b hstep r s har hrr hbs hsr => key _ a rfl b hstep r s har hrr hbs hsr

/-- Every historical path preserves the root read from the live index. -/
theorem ufRowRoot_of_ufReach {d : FDatabase} (hbr : EntryRowsUF d)
    (hdc : d.sig ufName = some (tableDecl 1)) (hrd : UFRowsDescend d)
    (hfor : UFRowsForest d) (htd : UFTermsDescend d) {a b : Term} (h : UFReach d a b) :
    ∀ r s, UFRowReach d a r → UFRowRoot d r → UFRowReach d b s → UFRowRoot d s → r = s := by
  induction h with
  | refl => intro r s har hrr has hsr; exact ufRowRoot_unique hfor har hrr has hsr
  | @tail c b hac hstep ihc =>
      intro r s har hrr hbs hsr
      obtain ⟨u, hcu, hur⟩ := exists_ufRowRoot hrd c
      exact (ihc r u har hrr hcu hur).trans
        (ufRowRoot_of_ufStep hbr hdc hrd hfor htd c b hstep u s hcu hur hbs hsr)

end Egglog.Congruence
