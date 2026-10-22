import EgglogSemantics.Proofs.Congruence.AbstractForward
import EgglogSemantics.Proofs.Congruence.AbstractState
import EgglogSemantics.Proofs.Congruence.LiveRead
import EgglogSemantics.Proofs.Completion

/-! Boundary checks compare inferred source facts with rebuilt current tables. -/

namespace Egglog.Congruence.Live

theorem completion_termsBuild {src : Database} (hw : src.WF) (hs : src.StoreOk)
    (hc : src.sig.AllConstructors) : src.completion.TermsBuild := by
  intro f args ht
  exact (Term.isValue_app_iff.mp
    ((hs.completion hw hc).values_of_allConstructors hc _ ht)).1

theorem Reads.inferred {src d : Database} (hr : Reads d src) (h : Abstract.Rebuilt d)
    (hs : d.StoreOk) (he : EdgesSound d src.completion) (hw : src.WF)
    {a b : Term} (hi : src.Infers a b) : SameClass d a b := by
  obtain ⟨hex, hun⟩ := hr.normalize h hs he hw.completion
  obtain ⟨w, hwit, hwa, hab⟩ := hi
  obtain ⟨i, hwi⟩ := hex w hwit
  have ha := Abstract.view_of_congOn h he hw.completion hun hwa hwi
  have hb := Abstract.view_of_congOn h he hw.completion hun hab ha
  exact ⟨h.root i, ha, by simpa only [h.root_idem] using hb⟩

theorem Reads.completion {src d : Database} (hr : Reads d src) (h : Abstract.Rebuilt d)
    (hd : d.Diag) (hs : d.StoreOk) (he : EdgesSound d src.completion) (hw : src.WF) :
    Reads d src.completion := by
  refine ⟨fun t ht => ?_, fun a b hab _ => ?_⟩
  · obtain ⟨i, hi, _⟩ := hr.inferred h hs he hw ((Database.mem_completion_iff hw).mp ht)
    exact ⟨i, .of_view hd hi⟩
  · obtain ⟨i, ha, hb⟩ := hr.inferred h hs he hw hab
    exact ⟨i, .of_view hd ha, .of_view hd hb⟩

/-- Sound rows and preserved source readings suffice for success/failure agreement. -/
theorem queryHolds_iff {src d : Database} (h : Abstract.Rebuilt d)
    (hd : d.Diag) (hstore : d.StoreOk) (htables : ViewTables d)
    (hdecl : Abstract.ViewDeclared d) (hsound : Abstract.SoundTerms d src.completion)
    (hr : Reads d src) (hw : src.WF) (hs : src.StoreOk) (hc : src.sig.AllConstructors)
    {q : Query} (hof : ∀ p ∈ q, p.OrderingFree) (hg : ∀ p ∈ q, p.Grounded)
    (hk : Query.VarsKeyed q) (hn : ∀ v ∈ Query.vars q, ¬ "@".isPrefixOf v = true)
    (n : Nat) : QueryHolds src q ↔ QueryHolds d (encodeQuery q n).1 := by
  have he := hsound.edgesSound hd
  obtain ⟨hex, hun⟩ := hr.normalize h hstore he hw.completion
  simp only [queryHolds_iff_validQuerySubst]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨ρ, hρ, _⟩ := Abstract.encodedQuery_match_of_source h hd hstore hdecl he
      hw.completion hc hun hex hof hk hg hn hσ n
    exact ⟨ρ, hρ⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨σ, hσ, _, _⟩ := sourceMatch_of_encodedQuery
      (completion_termsBuild hw hs hc) hw.completion (hsound.viewsSound hd)
      hd hstore htables hof hg hk hρ
    apply queryHolds_iff_validQuerySubst.mp
    exact (SourceMeaning.queryHolds_completion_iff hw hs hc hof).mp
      (queryHolds_iff_validQuerySubst.mpr ⟨σ, hσ⟩)

end Egglog.Congruence.Live
