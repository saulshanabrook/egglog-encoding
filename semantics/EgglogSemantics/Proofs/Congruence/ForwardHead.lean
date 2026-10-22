import EgglogSemantics.Proofs.Congruence.Forward
import EgglogSemantics.Proofs.Congruence.ForwardBuild

/-! Source rule firings lift to executable compiled firings that retain their source facts. -/

namespace Egglog.Congruence

/-- A source firing lifts to an actual compiled match and successful compiled firing.
The source state being matched may be earlier than the state justifying target entries. -/
theorem encodedRule_firing_reads {P : Program} {d : FDatabase} {src querySrc post : Database}
    (h : Rebuilt d) (htables : RebuildTables P d) (hs : SoundTerms d src)
    (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hreads : SourceReads d.toDatabase querySrc)
    (henv : querySrc.env = []) {r : Rule} {σ : Env}
    (hqp : ∀ p ∈ r.query, p.OrderingFree)
    (hqk : Query.VarsKeyed r.query) (hqg : ∀ p ∈ r.query, p.Grounded)
    (hqn : ∀ v ∈ Query.vars r.query, ¬ "@".isPrefixOf v = true)
    (hp : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hctor : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      querySrc.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (hm : ValidQuerySubst querySrc r.query σ)
    (hf : evalLocalActions querySrc r.actions σ = some post) :
    ∃ ρ d', ρ ∈ matchQuery d (encodeRule r).query ∧ Fired d (encodeRule r) ρ d' ∧
      SourceReads d'.toDatabase post := by
  have hun := unionsRead_of_unionsJoined (h.viewLeader htables hs hb hctors hc hw) hreads.unions
  obtain ⟨ρ, hmatch, hρ⟩ := encodedQuery_match_of_source h htables hs hb hctors hc hw
    hcs hun hreads.terms hqp hqk hqg hqn hm 0
  obtain ⟨sp, hsp, rfl⟩ := Option.map_eq_some_iff.mp hf
  have henvread : Env.Reads ({ d with env := ρ ++ d.env } : FDatabase).toDatabase
      (σ ++ querySrc.env) (ρ ++ d.env) := by
    intro v t ht
    rw [henv, List.append_nil] at ht
    obtain ⟨i, hi, hv, _⟩ := hρ v t ht
    exact ⟨i, Env.lookup_append_of_some hi,
      hv.mono (show d.toDatabase.Contained
        ({ d with env := ρ ++ d.env } : FDatabase).toDatabase from ⟨Set.Subset.refl _⟩)⟩
  have hstart : SourceReads ({ d with env := ρ ++ d.env } : FDatabase).toDatabase
      { querySrc with env := σ ++ querySrc.env } :=
    (hreads.mono (d' := ({ d with env := ρ ++ d.env } : FDatabase).toDatabase)
      ⟨Set.Subset.refl _⟩).restrict
        (src' := { querySrc with env := σ ++ querySrc.env }) ⟨Set.Subset.refl _⟩
  obtain ⟨tp, htp, hpost⟩ := encodeActions_reads (src := { querySrc with env := σ ++ querySrc.env })
    (d := { d with env := ρ ++ d.env })
    hcs (Egglog.FDatabase.SubtermClosed.of_wf (d := d) h.inv.wf) hp hctor hd (by simp [h.uf])
    henvread hstart hsp
  refine ⟨ρ, { tp with env := d.env, rules := d.rules }, hmatch, ?_, ?_⟩
  · change (execActions { d with env := ρ ++ d.env } (encodeActions r.actions)).map _ = _
    rw [htp]; rfl
  · exact (hpost.mono
      (d' := ({ tp with env := d.env, rules := d.rules } : FDatabase).toDatabase)
      ⟨Set.Subset.refl _⟩).restrict
        (src' := { sp with env := querySrc.env, rules := querySrc.rules }) ⟨Set.Subset.refl _⟩

end Egglog.Congruence
