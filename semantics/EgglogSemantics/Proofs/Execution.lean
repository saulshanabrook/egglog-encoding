import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Source.Domain

/-! Executable actions only add terms, equations, and marks. -/

namespace Egglog

theorem FDatabase.toDatabase_contained_of_lists {d e : FDatabase}
    (ht : d.terms ⊆ e.terms) (he : d.eqs ⊆ e.eqs) (hx : d.subsumed ⊆ e.subsumed) :
    d.toDatabase.Contained e.toDatabase := by
  refine ⟨?_, hx⟩
  rintro p (⟨hp, hm⟩ | ⟨hp, h1, h2⟩)
  · exact Or.inl ⟨hp, ht hm⟩
  · exact Or.inr ⟨he hp, ht h1, ht h2⟩

theorem execActions_lists {σ : Env} {d e : FDatabase} {as : List Action}
    (h : execActions σ d as = some e) :
    d.terms ⊆ e.terms ∧ d.eqs ⊆ e.eqs ∧ d.subsumed ⊆ e.subsumed := by
  apply execActions_preserves
    (P := fun e => d.terms ⊆ e.terms ∧ d.eqs ⊆ e.eqs ∧ d.subsumed ⊆ e.subsumed)
    ?_ ?_ ?_ ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩ h
  · intro e t he
    exact ⟨fun _ hm => FDatabase.mem_addTerm_of_mem (he.1 hm), he.2⟩
  · intro e a b he _
    refine ⟨fun _ hm => FDatabase.mem_addTerm_of_mem
      (FDatabase.mem_addTerm_of_mem (he.1 hm)), ?_, he.2.2⟩
    intro p hp
    exact List.mem_dedup.mpr (List.mem_cons_of_mem _ (he.2.1 hp))
  · intro e t he
    refine ⟨fun _ hm => FDatabase.mem_addTerm_of_mem (he.1 hm), he.2.1, ?_⟩
    exact fun _ hm => (FDatabase.mem_subsume_subsumed _ _ _).mpr (Or.inr (he.2.2 hm))

theorem fireInto_lists (r : Rule) (d : FDatabase) (σ : Env) :
    d.terms ⊆ (fireInto r d σ).terms ∧ d.eqs ⊆ (fireInto r d σ).eqs ∧
    d.subsumed ⊆ (fireInto r d σ).subsumed := by
  unfold fireInto
  cases h : execActions σ d r.actions with
  | none => exact ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩
  | some e => exact execActions_lists h

namespace FDatabase

theorem execRunRules_lists {R : List Rule} {d : FDatabase} :
    d.terms ⊆ (execRunRules R d).terms ∧ d.eqs ⊆ (execRunRules R d).eqs ∧
    d.subsumed ⊆ (execRunRules R d).subsumed := by
  apply execRunRules_induction_ruleset
    (P := fun e => d.terms ⊆ e.terms ∧ d.eqs ⊆ e.eqs ∧ d.subsumed ⊆ e.subsumed)
    ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩
  intro r _ σ _ acc h
  have hm := fireInto_lists r acc σ
  exact ⟨List.Subset.trans h.1 hm.1, List.Subset.trans h.2.1 hm.2.1, List.Subset.trans h.2.2 hm.2.2⟩

theorem execRunRules_terms {R : List Rule} {d : FDatabase} (_hd : ∀ r ∈ R, r.SubsumeFree) :
    d.terms ⊆ (execRunRules R d).terms := execRunRules_lists.1

theorem execRunRules_eqs {R : List Rule} {d : FDatabase} :
    d.eqs ⊆ (execRunRules R d).eqs := execRunRules_lists.2.1

theorem execRunRules_marks {R : List Rule} {d : FDatabase} :
    d.subsumed ⊆ (execRunRules R d).subsumed := execRunRules_lists.2.2

theorem runSaturateF_terms {R : List Rule} : ∀ (n : Nat) {d e : FDatabase},
    (∀ r ∈ R, r.SubsumeFree) → d.runSaturateF R n = some e → d.terms ⊆ e.terms := by
  intro n
  induction n with
  | zero =>
    intro d e _ h
    unfold runSaturateF at h
    split at h
    · cases Option.some.inj h; exact fun _ h => h
    · cases h
  | succ n ih =>
    intro d e hd h
    unfold runSaturateF at h
    split at h
    · cases Option.some.inj h; exact fun _ h => h
    · exact List.Subset.trans (execRunRules_terms hd)
        (ih hd h)

theorem runSaturateF_eqs {R : List Rule} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateF R n = some e → d.eqs ⊆ e.eqs := by
  intro n
  induction n with
  | zero =>
    intro d e h
    unfold runSaturateF at h
    split at h
    · cases Option.some.inj h; exact fun _ h => h
    · cases h
  | succ n ih =>
    intro d e h
    unfold runSaturateF at h
    split at h
    · cases Option.some.inj h; exact fun _ h => h
    · exact List.Subset.trans execRunRules_eqs (ih h)

theorem execCmd_terms {d e : FDatabase} {c : Schedule} {fuel : Nat}
    (hd : ∀ r ∈ c.rules, r.SubsumeFree) (h : execSchedule fuel d c = some e) :
    d.terms ⊆ e.terms :=
  execSchedule_preserves (I := fun e => d.terms ⊆ e.terms)
    (fun _ _ hg hs => List.Subset.trans hs (execRunRules_terms hg)) hd (fun _ h => h) h

theorem execCmd_eqs {d e : FDatabase} {c : Schedule} {fuel : Nat}
    (h : execSchedule fuel d c = some e) : d.eqs ⊆ e.eqs :=
  execSchedule_preserves (I := fun e => d.eqs ⊆ e.eqs) (good := fun _ => True)
    (fun _ _ _ hs => List.Subset.trans hs execRunRules_eqs) (fun _ _ => trivial)
    (fun _ h => h) h

theorem execProgram_terms {p : Schedule} {fuel : Nat} {d e : FDatabase}
    (hp : p.monotoneB = true) (h : execSchedule fuel d p = some e) :
    d.terms ⊆ e.terms := execCmd_terms (Schedule.subsumeFree_of_monotone hp) h

theorem execProgram_eqs {p : Schedule} {fuel : Nat} {d e : FDatabase}
    (h : execSchedule fuel d p = some e) : d.eqs ⊆ e.eqs := execCmd_eqs h

theorem execProgram_subsumed {p : Schedule} {fuel : Nat} {d e : FDatabase}
    (h : execSchedule fuel d p = some e) : d.subsumed ⊆ e.subsumed :=
  execSchedule_preserves (I := fun e => d.subsumed ⊆ e.subsumed) (good := fun _ => True)
    (fun _ _ _ hs => List.Subset.trans hs execRunRules_marks) (fun _ _ => trivial)
    (fun _ h => h) h

theorem execProgram_toDatabase_contained {p : Schedule} {fuel : Nat} {d e : FDatabase}
    (hp : p.monotoneB = true) (h : execSchedule fuel d p = some e) :
    d.toDatabase.Contained e.toDatabase :=
  toDatabase_contained_of_lists (execProgram_terms hp h) (execProgram_eqs h) (execProgram_subsumed h)

theorem execProgram_append {p q : Schedule} {fuel : Nat} {d e : FDatabase} :
    execSchedule fuel d (.seq p q) = some e ↔
      ∃ m, execSchedule fuel d p = some m ∧ execSchedule fuel m q = some e := by
  rw [execSchedule, Option.bind_eq_some_iff]

end FDatabase

/-- A syntactic build action; unions and subsumes are excluded. -/
def Action.IsAtomWrite : Action → Prop
  | .expr _ => True
  | _ => False

end Egglog
