import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Source.Domain

/-! Persistent assertions and delete-free term growth in executable programs. -/

namespace Egglog

theorem FDatabase.toDatabase_contained_of_lists {d e : FDatabase}
    (ht : d.terms ⊆ e.terms) (he : d.eqs ⊆ e.eqs) : d.toDatabase.Contained e.toDatabase := by
  constructor
  rintro p (⟨hp, hm⟩ | ⟨hp, h1, h2⟩)
  · exact Or.inl ⟨hp, ht hm⟩
  · exact Or.inr ⟨he hp, ht h1, ht h2⟩

theorem execWrites_lists {σ : Env} {d e : FDatabase} {as : List Action}
    (h : execWrites σ d as = some e) : d.terms ⊆ e.terms ∧ d.eqs ⊆ e.eqs := by
  apply execWrites_preserves (P := fun e => d.terms ⊆ e.terms ∧ d.eqs ⊆ e.eqs) ?_ ?_ ⟨fun _ h => h, fun _ h => h⟩ h
  · intro e t he
    exact ⟨fun _ hm => FDatabase.mem_addTerm_of_mem (he.1 hm), he.2⟩
  · intro e a b he _
    refine ⟨fun _ hm => FDatabase.mem_addTerm_of_mem (FDatabase.mem_addTerm_of_mem (he.1 hm)), ?_⟩
    intro p hp
    exact List.mem_dedup.mpr (List.mem_cons_of_mem _ (he.2 hp))

theorem fireWritesInto_lists (r : Rule) (d : FDatabase) (σ : Env) :
    d.terms ⊆ (fireWritesInto r d σ).terms ∧ d.eqs ⊆ (fireWritesInto r d σ).eqs := by
  unfold fireWritesInto
  cases h : execWrites σ d r.actions with
  | none => exact ⟨fun _ h => h, fun _ h => h⟩
  | some e => exact execWrites_lists h

private theorem foldl_mono {α β : Type} (f : FDatabase → α → FDatabase)
    (field : FDatabase → List β) (hf : ∀ d a, field d ⊆ field (f d a))
    (xs : List α) (d : FDatabase) : field d ⊆ field (xs.foldl f d) := by
  induction xs generalizing d with
  | nil => exact fun _ h => h
  | cons x xs ih => exact List.Subset.trans (hf d x) (ih _)

namespace FDatabase

theorem execRunRules_terms {R : List Rule} {d : FDatabase} (hd : ∀ r ∈ R, r.DeleteFree) :
    d.terms ⊆ (execRunRules R d).terms := by
  rw [execRunRules_eq_fold_of_deleteFree R hd]
  exact foldl_mono _ FDatabase.terms
    (fun acc (rs : Rule × List Env) => foldl_mono _ FDatabase.terms (fun d σ => (fireWritesInto_lists rs.1 d σ).1) _ acc) _ d

theorem execRunRules_eqs {R : List Rule} {d : FDatabase} :
    d.eqs ⊆ (execRunRules R d).eqs := by
  apply execRunRules_induction_ruleset (P := fun e => d.eqs ⊆ e.eqs)
  · intro X
    unfold deleteAtoms
    split <;> exact fun _ h => h
  · intro r _ σ _ acc h
    exact List.Subset.trans h (fireWritesInto_lists r acc σ).2


theorem runSaturateF_terms {R : List Rule} : ∀ (n : Nat) {d e : FDatabase},
    (∀ r ∈ R, r.DeleteFree) → d.runSaturateF R n = some e → d.terms ⊆ e.terms := by
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

theorem execCmd_terms {d e : FDatabase} {c : Cmd} (hd : ∀ r ∈ c.rules, r.DeleteFree)
    (h : execCmd d c = some e) : d.terms ⊆ e.terms := by
  cases c with
  | run R => cases Option.some.inj h; exact execRunRules_terms hd
  | saturate R => exact runSaturateF_terms _ hd h

theorem execCmd_eqs {d e : FDatabase} {c : Cmd} (h : execCmd d c = some e) :
    d.eqs ⊆ e.eqs := by
  cases c with
  | run R => cases Option.some.inj h; exact execRunRules_eqs
  | saturate R => exact runSaturateF_eqs _ h

theorem execProgram_terms {p : List Cmd} {d e : FDatabase}
    (hp : ∀ c ∈ p, c.monotoneB = true) (h : execProgram d p = some e) :
    d.terms ⊆ e.terms := by
  induction p generalizing d with
  | nil => cases Option.some.inj h; exact fun _ h => h
  | cons c cs ih =>
    obtain ⟨m, hc, hm⟩ := Option.bind_eq_some_iff.mp h
    exact List.Subset.trans (execCmd_terms (Cmd.deleteFree_of_monotone (hp c (by simp))) hc)
      (ih (fun c hc => hp c (by simp [hc])) hm)

theorem execProgram_eqs {p : List Cmd} {d e : FDatabase}
    (h : execProgram d p = some e) : d.eqs ⊆ e.eqs := by
  induction p generalizing d with
  | nil => cases Option.some.inj h; exact fun _ h => h
  | cons c cs ih =>
    obtain ⟨m, hc, hm⟩ := Option.bind_eq_some_iff.mp h
    exact List.Subset.trans (execCmd_eqs hc) (ih hm)

theorem execProgram_toDatabase_contained {p : List Cmd} {d e : FDatabase}
    (hp : ∀ c ∈ p, c.monotoneB = true) (h : execProgram d p = some e) :
    d.toDatabase.Contained e.toDatabase :=
  toDatabase_contained_of_lists (execProgram_terms hp h) (execProgram_eqs h)

theorem execProgram_append {p q : List Cmd} : ∀ {d e : FDatabase},
    execProgram d (p ++ q) = some e ↔
      ∃ m, execProgram d p = some m ∧ execProgram m q = some e := by
  induction p with
  | nil => simp [execProgram]
  | cons c cs ih =>
    intro d e
    simp only [List.cons_append, execProgram, Option.bind_eq_some_iff, ih]
    aesop

end FDatabase

/-- A syntactic build action; unions and deletes are excluded. -/
def Action.IsAtomWrite : Action → Prop
  | .expr _ => True
  | _ => False

end Egglog
