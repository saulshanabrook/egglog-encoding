import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.DiagonalPreservation

/-! Union-free executable runs have diagonal congruence, including runs with subsumption. -/

namespace Egglog

abbrev Database.EqsRefl := Database.Diag

theorem Cong.eq_of_eqsRefl {d : Database} (hr : d.EqsRefl) {a b : Term}
    (h : Cong d a b) : a = b := h.eq_of_diag hr

theorem CongList.eq_of_eqsRefl {d : Database} (hr : d.EqsRefl) {as bs : List Term}
    (h : CongList d as bs) : as = bs := h.eq_of_diag hr

def FDatabase.EqsRefl (d : FDatabase) : Prop := ∀ p ∈ d.eqs, p.1 = p.2

def FDatabase.eqsReflB (d : FDatabase) : Bool := d.eqs.all fun p => p.1 == p.2

theorem FDatabase.eqsReflB_iff (d : FDatabase) : d.eqsReflB = true ↔ d.EqsRefl := by
  simp [FDatabase.eqsReflB, FDatabase.EqsRefl, List.all_eq_true]

theorem FDatabase.EqsRefl.toDatabase {d : FDatabase} (h : d.EqsRefl) :
    d.toDatabase.EqsRefl := by
  rintro p (⟨he, _⟩ | ⟨hp, _, _⟩)
  · exact he
  · exact h p hp

def FDatabase.subtermClosedB (d : FDatabase) : Bool :=
  d.terms.all fun t => t.subtermList.all fun s => d.terms.contains s

theorem FDatabase.subtermClosedB_iff (d : FDatabase) :
    d.subtermClosedB = true ↔ d.SubtermClosed := by
  simp [FDatabase.subtermClosedB, FDatabase.SubtermClosed, Term.ListClosed, List.all_eq_true]

/-- No raw equations have been asserted. -/
structure FDatabase.NoUnions (d : FDatabase) : Prop where
  eqs : d.eqs = []

theorem FDatabase.NoUnions.union {d₁ d₂ : FDatabase} (h₁ : d₁.NoUnions)
    (h₂ : d₂.eqs = []) : (d₁.union d₂).NoUnions :=
  ⟨by simp [FDatabase.union, h₁.eqs, h₂]⟩

theorem FDatabase.NoUnions.subsume {d : FDatabase} (hn : d.NoUnions) (t : Term) :
    (d.subsume t).NoUnions := ⟨by simpa using hn.eqs⟩

theorem execAction_noUnions {σ : Env} {d d' : FDatabase} {a : Action}
    (hu : a.UnionFree) (hn : d.NoUnions) (h : execAction σ d a = some d') : d'.NoUnions := by
  cases a with
  | expr e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hn.eqs⟩
  | union _ _ => exact hu.elim
  | subsume e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hn.subsume _

theorem execActions_noUnions {σ : Env} {d d' : FDatabase} {as : List Action}
    (hu : Actions.UnionFree as) (hn : d.NoUnions) (h : execActions σ d as = some d') :
    d'.NoUnions := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact hn
  | cons a as ih =>
    obtain ⟨e, he, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih hu.2 (execAction_noUnions hu.1 hn he) ht

theorem fireInto_noUnions {r : Rule} {d : FDatabase} {σ : Env}
    (hu : Actions.UnionFree r.actions) (hn : d.NoUnions) :
    (fireInto r d σ).NoUnions := by
  unfold fireInto
  cases h : execActions σ d r.actions with
  | none => exact hn
  | some e => exact execActions_noUnions hu hn h

theorem execRunRules_noUnions {R : List Rule} {d : FDatabase}
    (hn : d.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) :
    (execRunRules R d).NoUnions :=
  execRunRules_induction_ruleset hn
    (fun r hr _ _ _ ha => fireInto_noUnions (hu r hr) ha)

theorem runSaturateF_noUnions {R : List Rule} (hu : ∀ r ∈ R, r.UnionFree) :
    ∀ (n : Nat) {d d' : FDatabase},
    d.NoUnions → d.runSaturateF R n = some d' → d'.NoUnions := by
  intro n
  induction n with
  | zero =>
    intro d d' hn h
    unfold FDatabase.runSaturateF at h
    split at h
    · cases Option.some.inj h; exact hn
    · cases h
  | succ n ih =>
    intro d d' hn h
    unfold FDatabase.runSaturateF at h
    split at h
    · cases Option.some.inj h; exact hn
    · exact ih (execRunRules_noUnions hn hu) h

theorem execCmd_noUnions {d d' : FDatabase} {c : Schedule} {fuel : Nat}
    (hu : c.UnionFree) (hn : d.NoUnions) (h : execSchedule fuel d c = some d') :
    d'.NoUnions :=
  execSchedule_preserves (fun _ _ hg h => execRunRules_noUnions h hg) hu hn h

theorem execProgram_noUnions {p : Schedule} {fuel : Nat} {d d' : FDatabase}
    (hu : p.UnionFree) (hn : d.NoUnions) (h : execSchedule fuel d p = some d') :
    d'.NoUnions := execCmd_noUnions hu hn h

theorem FDatabase.NoUnions.empty : FDatabase.empty.NoUnions := ⟨rfl⟩

theorem FDatabase.NoUnions.toDatabase {d : FDatabase} (hn : d.NoUnions) :
    d.toDatabase.NoUnions :=
  ⟨(show d.EqsRefl by simp [FDatabase.EqsRefl, hn.eqs]).toDatabase⟩

theorem exec_noUnions {p : Program} {d : FDatabase} (hu : p.UnionFree)
    (h : exec p = some d) : d.NoUnions := execProgram_noUnions hu .empty h

end Egglog
