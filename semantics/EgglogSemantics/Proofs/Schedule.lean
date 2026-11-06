import EgglogSemantics.Proofs.Step
import EgglogSemantics.Impl.Interp

/-! Lifting round invariants and simulations through nested schedules. -/

namespace Egglog

theorem Database.SameMeaning.congr_eq {d e : Database} (h : d.SameMeaning e) :
    Cong d = Cong e := funext fun a => funext fun b => propext (h.congr a b)

theorem Database.SameMeaning.of_congr_eq {d e : Database} (h : Cong d = Cong e) (hX : d.subsumed = e.subsumed) :
    d.SameMeaning e := .of_congr (fun a b => by rw [h]) hX

/-- Lift a round invariant through every finite schedule. -/
theorem Reach.preserves {I : Database → Prop} {good : Rule → Prop}
    (hrun : ∀ rs d, (∀ r ∈ rs, good r) → I d → I (RunRules rs d))
    {S : Schedule} {d e : Database} (h : Reach d S e)
    (hg : ∀ r ∈ S.rules, good r) (hd : I d) : I e := by
  induction h with
  | run => exact hrun _ _ hg hd
  | seq _ _ ih₁ ih₂ =>
    exact ih₂ (fun r hr => hg r (List.mem_append_right _ hr))
      (ih₁ (fun r hr => hg r (List.mem_append_left _ hr)) hd)
  | fixpoint _ _ ih => exact ih hg hd
  | again _ _ _ ih₁ ih₂ => exact ih₂ hg (ih₁ hg hd)

/-- A round simulation on meaning lifts to finite nested schedules. -/
theorem Reach.transport {I : Database → Prop} {good : Rule → Prop}
    (hpres : ∀ rs d, (∀ r ∈ rs, good r) → I d → I (RunRules rs d))
    (hrun : ∀ rs d e, (∀ r ∈ rs, good r) → I d → I e → d.SameMeaning e →
      (RunRules rs d).SameMeaning (RunRules rs e))
    {S : Schedule} {d out e : Database} (h : Reach d S out)
    (hg : ∀ r ∈ S.rules, good r) (hd : I d) (he : I e) (hm : d.SameMeaning e) :
    ∃ out', Reach e S out' ∧ out.SameMeaning out' := by
  induction h generalizing e with
  | run => exact ⟨_, .run, hrun _ _ _ hg hd he hm⟩
  | seq h₁ _ ih₁ ih₂ =>
    have hg₁ := fun r hr => hg r (List.mem_append_left _ hr)
    have hg₂ := fun r hr => hg r (List.mem_append_right _ hr)
    obtain ⟨mid, hs, hm₁⟩ := ih₁ hg₁ hd he hm
    obtain ⟨last, ht, hm₂⟩ := ih₂ hg₂ (h₁.preserves hpres hg₁ hd)
      (hs.preserves hpres hg₁ he) hm₁
    exact ⟨last, .seq hs ht, hm₂⟩
  | fixpoint _ hf ih =>
    obtain ⟨mid, hs, hm₁⟩ := ih hg hd he hm
    exact ⟨mid, .fixpoint hs (hm.symm.trans
      (hf.trans hm₁)), hm₁⟩
  | again h₁ hn _ ih₁ ih₂ =>
    obtain ⟨mid, hs, hm₁⟩ := ih₁ hg hd he hm
    have hn' : ¬ e.SameMeaning mid := fun hh => hn
      (hm.trans (hh.trans hm₁.symm))
    obtain ⟨last, ht, hm₂⟩ := ih₂ hg (h₁.preserves hpres hg hd)
      (hs.preserves hpres hg he) hm₁
    exact ⟨last, .again hs hn' ht, hm₂⟩

/-- A known fixed pass determines the meaning of any finite saturation. -/
theorem Reach.saturation_meaning_of_fixed {S : Schedule} {d mid e : Database}
    (hp : Reach d S mid) (hf : d.SameMeaning mid) (h : Reach d (.saturate S) e) :
    d.SameMeaning e := by
  cases h with
  | fixpoint h _ => exact hp.det h ▸ hf
  | again h hn _ => exact (hn (hp.det h ▸ hf)).elim

/-- Lift an executable round invariant, also through the pass counter. -/
theorem execSchedule_preserves {I : FDatabase → Prop} {good : Rule → Prop}
    (hrun : ∀ rs d, (∀ r ∈ rs, good r) → I d → I (execRunRules rs d))
    {fuel : Nat} {S : Schedule} {d e : FDatabase}
    (hg : ∀ r ∈ S.rules, good r) (hd : I d) (h : execSchedule fuel d S = some e) : I e := by
  induction S generalizing d e with
  | run rs => simp only [execSchedule] at h; cases Option.some.inj h; exact hrun _ _ hg hd
  | seq S₁ S₂ ih₁ ih₂ =>
    simp only [execSchedule] at h
    obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    exact ih₂ (fun r hr => hg r (List.mem_append_right _ hr))
      (ih₁ (fun r hr => hg r (List.mem_append_left _ hr)) hd h₁) h₂
  | saturate S ih =>
    change ∀ r ∈ S.rules, good r at hg
    have aux : ∀ n {d e}, I d → execSaturate fuel n d S = some e → I e := by
      intro n
      induction n with
      | zero =>
        intro d e hd hs
        rw [execSaturate] at hs
        obtain ⟨mid, hm, hs⟩ := Option.bind_eq_some_iff.mp hs
        split at hs
        · cases Option.some.inj hs; exact ih hg hd hm
        · cases hs
      | succ n ihn =>
        intro d e hd hs
        rw [execSaturate] at hs
        obtain ⟨mid, hm, hs⟩ := Option.bind_eq_some_iff.mp hs
        split at hs
        · cases Option.some.inj hs; exact ih hg hd hm
        · exact ihn (ih hg hd hm) hs
    exact aux fuel hd (by simpa only [execSchedule] using h)

/-- Saturation-free schedules execute with any fuel, including zero. -/
theorem execSchedule_exists {fuel : Nat} {S : Schedule} (hn : S.NoSaturate)
    (d : FDatabase) : ∃ e, execSchedule fuel d S = some e := by
  induction S generalizing d with
  | run rs => exact ⟨execRunRules rs d, by rw [execSchedule]⟩
  | saturate S => exact hn.elim
  | seq S₁ S₂ ih₁ ih₂ =>
    obtain ⟨mid, hm⟩ := ih₁ hn.1 d
    obtain ⟨e, he⟩ := ih₂ hn.2 mid
    exact ⟨e, by simp [execSchedule, hm, he]⟩

/-- Structural equality of executable fields implies semantic equality. -/
theorem FDatabase.sameData_sameMeaning {d e : FDatabase} (h : d.sameData e = true) :
    d.toDatabase.SameMeaning e.toDatabase := by
  simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at h
  have he : d.toDatabase = e.toDatabase := by
    unfold FDatabase.toDatabase
    rw [h.1.1.1, h.1.2, h.2]
  exact he ▸ Database.SameMeaning.refl _

/-- Lift a round refinement through nested schedules. A structural fixed point is a
semantic fixed point; extra structural passes after semantic convergence are absorbed. -/
theorem execSchedule_refines {I : FDatabase → Prop} {J : Database → Prop}
    {good : Rule → Prop}
    (hfinite : ∀ rs d, (∀ r ∈ rs, good r) → I d → I (execRunRules rs d))
    (hspec : ∀ rs d, (∀ r ∈ rs, good r) → J d → J (RunRules rs d))
    (hround : ∀ rs d db, (∀ r ∈ rs, good r) → I d → J db →
      d.toDatabase.SameMeaning db → (execRunRules rs d).toDatabase.SameMeaning (RunRules rs db))
    (hmeaning : ∀ rs d e, (∀ r ∈ rs, good r) → J d → J e → d.SameMeaning e →
      (RunRules rs d).SameMeaning (RunRules rs e))
    {fuel : Nat} {S : Schedule} {d e : FDatabase} {db : Database}
    (hg : ∀ r ∈ S.rules, good r) (hd : I d) (hb : J db) (hm : d.toDatabase.SameMeaning db)
    (h : execSchedule fuel d S = some e) :
    ∃ out, Reach db S out ∧ e.toDatabase.SameMeaning out := by
  induction S generalizing d e db with
  | run rs =>
    simp only [execSchedule] at h
    cases Option.some.inj h
    exact ⟨_, .run, hround _ _ _ hg hd hb hm⟩
  | seq S₁ S₂ ih₁ ih₂ =>
    simp only [execSchedule] at h
    obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have hg₁ := fun r hr => hg r (List.mem_append_left _ hr)
    have hg₂ := fun r hr => hg r (List.mem_append_right _ hr)
    obtain ⟨out, hp, hm₁⟩ := ih₁ hg₁ hd hb hm h₁
    obtain ⟨last, ht, hm₂⟩ := ih₂ hg₂ (execSchedule_preserves hfinite hg₁ hd h₁)
      (hp.preserves hspec hg₁ hb) hm₁ h₂
    exact ⟨last, .seq hp ht, hm₂⟩
  | saturate S ih =>
    change ∀ r ∈ S.rules, good r at hg
    have aux : ∀ n {d e db}, I d → J db → d.toDatabase.SameMeaning db →
        execSaturate fuel n d S = some e →
        ∃ out, Reach db (.saturate S) out ∧ e.toDatabase.SameMeaning out := by
      intro n
      induction n with
      | zero =>
        intro d e db hd hb hm hs
        rw [execSaturate] at hs
        obtain ⟨mid, hp, hs⟩ := Option.bind_eq_some_iff.mp hs
        obtain ⟨out, hr, hm₁⟩ := ih hg hd hb hm hp
        split at hs
        · rename_i hf
          cases Option.some.inj hs
          exact ⟨out, .fixpoint hr
            (hm.symm.trans ((FDatabase.sameData_sameMeaning hf).trans hm₁)), hm₁⟩
        · cases hs
      | succ n ihn =>
        intro d e db hd hb hm hs
        rw [execSaturate] at hs
        obtain ⟨mid, hp, hs⟩ := Option.bind_eq_some_iff.mp hs
        obtain ⟨out, hr, hm₁⟩ := ih hg hd hb hm hp
        split at hs
        · rename_i hf
          cases Option.some.inj hs
          exact ⟨out, .fixpoint hr
            (hm.symm.trans ((FDatabase.sameData_sameMeaning hf).trans hm₁)), hm₁⟩
        · have hb₁ := hr.preserves hspec hg hb
          obtain ⟨last, ht, hm₂⟩ := ihn (execSchedule_preserves hfinite hg hd hp) hb₁ hm₁ hs
          by_cases hf : db.SameMeaning out
          · obtain ⟨fixed, hp', hm'⟩ := hr.transport hspec hmeaning hg hb hb₁
              hf
            exact ⟨out, .fixpoint hr hf,
              hm₂.trans (Reach.saturation_meaning_of_fixed hp' hm' ht).symm⟩
          · exact ⟨last, .again hr hf ht, hm₂⟩
    exact aux fuel hd hb hm (by simpa only [execSchedule] using h)

/-- A structural fixed point agrees on all finite-store fields. -/
theorem FDatabase.sameData_eq {d e : FDatabase} (h : d.sameData e = true) : d = e := by
  simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at h
  cases d
  cases e
  simp_all

/-- The retained round-level runner computes saturation of a single run. -/
theorem execSaturate_run (fuel n : Nat) (d : FDatabase) (rs : List Rule) :
    execSaturate fuel n d (.run rs) = d.runSaturateF rs n := by
  induction n generalizing d with
  | zero =>
    rw [execSaturate, execSchedule, Option.bind_some, FDatabase.runSaturateF]
    split
    · rename_i h
      exact congrArg some (FDatabase.sameData_eq h).symm
    · rfl
  | succ n ih =>
    rw [execSaturate, execSchedule, Option.bind_some, FDatabase.runSaturateF]
    split
    · rename_i h
      exact congrArg some (FDatabase.sameData_eq h).symm
    · exact ih _

theorem execSchedule_saturate_run (fuel : Nat) (d : FDatabase) (rs : List Rule) :
    execSchedule fuel d (.saturate (.run rs)) = d.runSaturateF rs fuel := by
  rw [execSchedule, execSaturate_run]

end Egglog
