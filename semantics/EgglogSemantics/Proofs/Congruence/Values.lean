import EgglogSemantics.Proofs.Congruence.State
import EgglogSemantics.Proofs.Entries

namespace Egglog.Congruence

/-- A held source value can be assigned by the compiled matcher. Function-entry terms
are excluded by the matcher's value filter, but source constructors pass it. -/
theorem source_mem_valueTerms {src : Database} {d : FDatabase} (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) {t : Term}
    (hs : t ∈ src.terms) (ht : t ∈ d.terms) : t ∈ d.valueTerms := by
  apply List.mem_filter.mpr ⟨ht, ?_⟩
  cases t with
  | lit _ => rfl
  | app f as =>
      obtain ⟨dc, hd, hm⟩ := hc f (hb f as hs)
      simp [Signature.mergeOf, hd, hm]

/-- Sound retained entries justify every live view column as an existing source value. -/
theorem viewRow_sourceColumns {src : Database} {d : FDatabase} (hr : d.EqsRefl)
    (hi : d.IndexOk) (h : SoundTerms d src) {f : FnName} {cs : List Term} {e : Term}
    (hm : d.sig.mergeOf (viewName f) ≠ none)
    (hrow : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows) :
    ∀ t ∈ cs ++ [e], t ∈ src.terms := by
  obtain ⟨as, _, hcs, he⟩ := h.1 f cs e (mem_terms_of_indexOk hr hi hrow hm)
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hcs.mem_of.2 t ht
  · exact List.mem_singleton.mp ht ▸ he.mem_of.2

/-- Those same columns pass the executable matcher's value filter. -/
theorem viewRow_valueColumns {src : Database} {d : FDatabase} (hr : d.EqsRefl)
    (hi : d.Inv) (h : SoundTerms d src) (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) {f : FnName} {cs : List Term} {e : Term}
    (hm : d.sig.mergeOf (viewName f) ≠ none)
    (hrow : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows) :
    ∀ t ∈ cs ++ [e], t ∈ d.valueTerms := by
  intro t ht
  exact source_mem_valueTerms hb hc (viewRow_sourceColumns hr hi.index h hm hrow t ht)
    (FDatabase.mem_terms_of_column (Egglog.FDatabase.SubtermClosed.of_wf hi.wf)
      (mem_terms_of_indexOk hr hi.index hrow hm) ht)

/-- A live UF row likewise carries source values at both endpoints. -/
theorem ufRow_valueColumns {src : Database} {d : FDatabase} (hr : d.EqsRefl)
    (hi : d.Inv) (h : SoundTerms d src) (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) {a b : Term}
    (hm : d.sig.mergeOf ufName ≠ none) (hrow : (⟨ufName, [a], [b]⟩ : Row) ∈ d.rows) :
    a ∈ d.valueTerms ∧ b ∈ d.valueTerms := by
  have ht := mem_terms_of_indexOk hr hi.index hrow hm
  have hab := h.2 a b ht
  have hcols : ∀ t ∈ [a, b], t ∈ d.terms :=
    fun t ht' => FDatabase.mem_terms_of_column (Egglog.FDatabase.SubtermClosed.of_wf hi.wf) ht ht'
  exact ⟨source_mem_valueTerms hb hc hab.mem_of.1 (hcols a (by simp)),
    source_mem_valueTerms hb hc hab.mem_of.2 (hcols b (by simp))⟩

end Egglog.Congruence
