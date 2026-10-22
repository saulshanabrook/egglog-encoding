import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.DiagonalPreservation

/-! Union-free executable runs have diagonal congruence, including runs with deletes. -/

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

theorem FDatabase.NoUnions.deleteAtoms {d : FDatabase} (hn : d.NoUnions)
    (cl : Finset (Term × Term)) (X : List Term) : (d.deleteAtoms cl X).NoUnions := by
  unfold FDatabase.deleteAtoms
  split <;> exact ⟨hn.eqs⟩

theorem execAction_noUnions {σ : Env} {d d' : FDatabase} {a : Action}
    (hu : a.UnionFree) (hn : d.NoUnions) (h : execAction σ d a = some d') : d'.NoUnions := by
  cases a with
  | expr e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hn.eqs⟩
  | union _ _ => exact hu.elim
  | delete e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hn.deleteAtoms _ _

theorem execActions_noUnions {σ : Env} {d d' : FDatabase} {as : List Action}
    (hu : Actions.UnionFree as) (hn : d.NoUnions) (h : execActions σ d as = some d') :
    d'.NoUnions := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact hn
  | cons a as ih =>
    obtain ⟨e, he, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih hu.2 (execAction_noUnions hu.1 hn he) ht

theorem execWrite_noUnions {σ : Env} {d d' : FDatabase} {a : Action}
    (hu : a.UnionFree) (hn : d.NoUnions) (h : execWrite σ d a = some d') : d'.NoUnions := by
  cases a with
  | expr e => exact execAction_noUnions hu hn h
  | union _ _ => exact hu.elim
  | delete e => obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact hn

theorem execWrites_noUnions {σ : Env} {d d' : FDatabase} {as : List Action}
    (hu : Actions.UnionFree as) (hn : d.NoUnions) (h : execWrites σ d as = some d') :
    d'.NoUnions := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact hn
  | cons a as ih =>
    obtain ⟨e, he, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih hu.2 (execWrite_noUnions hu.1 hn he) ht

theorem fireWritesInto_noUnions {r : Rule} {d : FDatabase} {σ : Env}
    (hu : Actions.UnionFree r.actions) (hn : d.NoUnions) :
    (fireWritesInto r d σ).NoUnions := by
  unfold fireWritesInto
  cases h : execWrites σ d r.actions with
  | none => exact hn
  | some e => exact execWrites_noUnions hu hn h

theorem execRunRules_noUnions {R : List Rule} {d : FDatabase}
    (hn : d.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) :
    (execRunRules R d).NoUnions :=
  execRunRules_induction_ruleset (fun X => hn.deleteAtoms _ X)
    (fun r hr _ _ _ ha => fireWritesInto_noUnions (hu r hr) ha)

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

theorem execCmd_noUnions {d d' : FDatabase} {c : Cmd} (hu : c.UnionFree)
    (hn : d.NoUnions) (h : execCmd d c = some d') : d'.NoUnions := by
  cases c with
  | run R => cases Option.some.inj h; exact execRunRules_noUnions hn hu
  | saturate R => exact runSaturateF_noUnions hu _ hn h

theorem execProgram_noUnions {p : List Cmd} {d d' : FDatabase}
    (hu : ∀ c ∈ p, c.UnionFree) (hn : d.NoUnions) (h : execProgram d p = some d') :
    d'.NoUnions := by
  induction p generalizing d with
  | nil => cases Option.some.inj h; exact hn
  | cons c cs ih =>
    obtain ⟨e, hc, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih (fun c hc => hu c (by simp [hc])) (execCmd_noUnions (hu c (by simp)) hn hc) ht

theorem FDatabase.NoUnions.empty : FDatabase.empty.NoUnions := ⟨rfl⟩

theorem FDatabase.NoUnions.toDatabase {d : FDatabase} (hn : d.NoUnions) :
    d.toDatabase.NoUnions :=
  ⟨(show d.EqsRefl by simp [FDatabase.EqsRefl, hn.eqs]).toDatabase⟩

theorem exec_noUnions {p : Program} {d : FDatabase} (hu : p.UnionFree)
    (h : exec p = some d) : d.NoUnions := execProgram_noUnions hu .empty h

end Egglog
