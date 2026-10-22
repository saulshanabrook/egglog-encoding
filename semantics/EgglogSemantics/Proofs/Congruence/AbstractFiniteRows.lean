import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.Congruence.AbstractState

/-! Source soundness supplies a uniform finite universe of generated rows, even when
rebuilding re-keys a view to a tuple absent from the original source syntax. -/

namespace Egglog.Congruence.Abstract

/-- The generated rows that can be justified in one fixed source state. -/
def SoundRows (src : Database) : Set Term :=
  {t | (∃ f cs e, t = .app (viewName f) (cs ++ [e]) ∧ EntrySound src f cs e) ∨
    (∃ a b, t = .app ufName [a, b] ∧ StoredCong src a b)}

private def viewCandidates (src : Database) : Term → Set Term
  | .lit _ => ∅
  | .app f as =>
      (fun p : List Term × Term => Term.app (viewName f) (p.1 ++ [p.2])) ''
        ({cs | cs.length = as.length ∧ ∀ c ∈ cs, c ∈ src.terms} ×ˢ src.terms)

private theorem finite_viewCandidates {src : Database} (hf : src.terms.Finite)
    (t : Term) : (viewCandidates src t).Finite := by
  cases t with
  | lit _ => exact Set.finite_empty
  | app f as => exact ((finite_lists hf as.length).prod hf).image _

/-- Finitely many source applications determine the possible view names and arities;
every view column and union-find endpoint is a held source term. -/
theorem SoundRows.finite {src : Database} (hf : src.terms.Finite) :
    (SoundRows src).Finite := by
  have hv := hf.biUnion (fun t _ => finite_viewCandidates hf t)
  have hu := (hf.prod hf).image (fun p : Term × Term => Term.app ufName [p.1, p.2])
  apply (hv.union hu).subset
  intro t ht
  rcases ht with ⟨f, cs, e, rfl, as, ha, hcs, he⟩ | ⟨a, b, rfl, hab⟩
  · apply Or.inl
    apply Set.mem_iUnion₂.mpr
    refine ⟨.app f as, ha, (cs, e), ?_, rfl⟩
    refine ⟨⟨hcs.length_eq.symm, ?_⟩, he.mem_right⟩
    intro c hc
    exact hcs.mem_of.2 c hc
  · exact Or.inr ⟨(a, b), ⟨hab.mem_left, hab.mem_right⟩, rfl⟩

/-- Proper subterms of a source-sound generated row are source values. -/
theorem SoundRows.subterms_subset {src : Database} (hw : src.WF) {t : Term}
    (ht : t ∈ SoundRows src) {s : Term} (hs : s ∈ t.subterms) (hne : s ≠ t) :
    s ∈ src.terms := by
  rcases ht with ⟨f, cs, e, rfl, as, _, hcs, he⟩ | ⟨a, b, rfl, hab⟩
  · apply subterms_of_columns hw ?_ hs hne
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcs.mem_of.2 c hc
    · exact List.mem_singleton.mp hc ▸ he.mem_right
  · apply subterms_of_columns hw ?_ hs hne
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab.mem_left
    · exact List.mem_singleton.mp hc ▸ hab.mem_right

end Egglog.Congruence.Abstract
