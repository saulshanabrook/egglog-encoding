import EgglogSemantics.Proofs.Congruence.EntryShape
import EgglogSemantics.Proofs.Congruence.SourceState
import EgglogSemantics.Proofs.SignatureLookup
import EgglogSemantics.Proofs.Completion

/-! Source values do not contain generated entries. -/

namespace Egglog.Congruence

/-- Source values cannot masquerade as generated table entries. -/
def SourceSafe (src : Database) : Prop :=
  ∀ t ∈ src.terms, ¬ EntryShaped t

theorem sourceSafe_of_names {src : Database} (hb : src.TermsBuild)
    (hn : ∀ f dc, src.sig f = some dc → ¬ "@".isPrefixOf f) : SourceSafe src := by
  intro t ht hs
  rcases hs with ⟨f, cs, e, rfl⟩ | ⟨a, b, rfl⟩
  · obtain ⟨dc, hdc, -⟩ := hb _ _ ht
    exact hn _ dc hdc (by
      simp [viewName, String.isPrefixOf, String.startsWith_string_iff, String.toList_append])
  · obtain ⟨dc, hdc, -⟩ := hb _ _ ht
    exact hn _ dc hdc (by decide +kernel)

/-- Inferred constructor spellings still avoid every generated table name. -/
theorem sourceSafe_completion {src : Database} (hw : src.WF) (hs : src.StoreOk)
    (hc : src.sig.AllConstructors)
    (hn : ∀ f dc, src.sig f = some dc → ¬ "@".isPrefixOf f) :
    SourceSafe src.completion := by
  apply sourceSafe_of_names (src := src.completion) ?_ hn
  intro f cs ht
  exact (Term.isValue_app_iff.mp
    ((hs.completion hw hc).values_of_allConstructors hc _ ht)).1

/-- A source execution cannot declare names from the generated namespace. -/
theorem sourceNames_of_programStep {P p : Program} {src : Database}
    (hdom : P.Fragment) (hp : ∀ c ∈ p, c ∈ P)
    (run : ProgramStep Database.empty p src) :
    ∀ f dc, src.sig f = some dc → ¬ "@".isPrefixOf f := by
  intro f dc hf
  rcases run.declared hf with he | hc
  · cases he
  · apply hdom.noAt f
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(f, dc.arity), ?_, rfl⟩
    exact List.mem_dedup.mpr (List.mem_flatMap.mpr
      ⟨.decl f dc, hp _ hc, by simp [Cmd.ctors]⟩)

/-- Reserved-name separation follows from the original program, including at prefixes. -/
theorem sourceSafe_of_programStep {P p : Program} {src : Database}
    (hdom : P.Fragment) (hp : ∀ c ∈ p, c ∈ P)
    (run : ProgramStep Database.empty p src) : SourceSafe src :=
  sourceSafe_of_names (termsBuild_of_programStep (fun c hc => hdom.ctorsOnly c (hp c hc)) run)
    (sourceNames_of_programStep hdom hp run)

theorem sourceSubterms {src : Database} (hw : src.WF) (hs : SourceSafe src)
    {f : FnName} {cols : List Term} (hc : ∀ t ∈ cols, t ∈ src.terms) :
    ∀ s ∈ (Term.app f cols).subtermList, s ≠ Term.app f cols → ¬ EntryShaped s := by
  intro s hm hn
  rw [Term.subtermList, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact (hn rfl).elim
  · obtain ⟨t, ht, hst⟩ := (Term.mem_subtermListL cols).mp hm
    exact hs s (hw.subtermClosed t (hc t ht) hst)

end Egglog.Congruence
