import EgglogSemantics.Proofs.Congruence.LiveRunRead
import EgglogSemantics.Proofs.FiniteSaturation
import EgglogSemantics.Proofs.StepMonotone

/-! Completed generated rounds progress by adding keys or decreasing their outputs. -/

namespace Egglog.Congruence.Live

/-- Value assertions persist; an existing key can only select a smaller output. -/
structure Advances (d e : Database) : Prop where
  values : d.ValueContained e
  env : d.env = e.env
  rules : d.rules = e.rules
  rows : ∀ f cs a, Entry.mk f cs [a] ∈ d.entries →
    ∃ b, Entry.mk f cs [b] ∈ e.entries ∧ IdLe b a

theorem Advances.refl (d : Database) : Advances d d :=
  ⟨.refl d, rfl, rfl, fun _ _ a ha => ⟨a, ha, .refl a⟩⟩

theorem Advances.trans {d e f : Database} (h : Advances d e) (h' : Advances e f) :
    Advances d f := by
  refine ⟨h.values.trans h'.values, h.env.trans h'.env, h.rules.trans h'.rules, ?_⟩
  intro g cs a ha
  obtain ⟨b, hb, hab⟩ := h.rows g cs a ha
  obtain ⟨c, hc, hbc⟩ := h'.rows g cs b hb
  exact ⟨c, hc, hbc.trans hab⟩

theorem Advances.runStep {d e : Database} (h : Runtime d) {R : RulesetName}
    (hr : RunStep R d e) : Advances d e := by
  refine ⟨hr.valueContained, hr.env.symm, hr.1.envRules.2.symm, ?_⟩
  intro f cs a ha
  obtain ⟨b, hb, _, hle⟩ := row_closure (h.runRules R).state
    (h.runRules R).noUnions.diag hr.1 (show Entry.mk f cs [a] ∈ (RunRules R d).entries
      from ⟨ha.1, Or.inl ha.2⟩)
  exact ⟨b, hb, hle⟩

private theorem Advances.entries_subset {d e : Database} (h : Advances d e)
    (h' : Advances e d) (hs : State d) (hstore : d.StoreOk) (hn : MergeNormal d) :
    d.entries ⊆ e.entries := by
  intro row hrow
  obtain ⟨a, ha⟩ := (hs.rows row hrow).output
  rcases row with ⟨f, cs, vs⟩
  dsimp only at ha
  subst vs
  obtain ⟨b, hb, hba⟩ := h.rows f cs a hrow
  obtain ⟨c, hc, hcb⟩ := h'.rows f cs b hb
  have hca : c = a := List.singleton_inj.mp
    (hn.out_unique (Abstract.out_of_current hstore hc) (Abstract.out_of_current hstore hrow))
  have hba' : b = a := hba.antisymm (hca ▸ hcb)
  exact hba' ▸ hb

theorem Advances.antisymm {d e : Database} (h : Advances d e) (h' : Advances e d)
    (hd : Runtime d) (he : Runtime e) (hnd : MergeNormal d) (hne : MergeNormal e) : d = e := by
  have hdrows := h.entries_subset h' hd.state hd.storeOk hnd
  have herows := h'.entries_subset h he.state he.storeOk hne
  have hsub {d e : Database} (hv : d.ValueContained e) (hs : d.StoreOk)
      (hr : d.entries ⊆ e.entries) : d.eqs ⊆ e.eqs := by
    intro p hp
    rcases hs.typed p hp with ⟨ha, hb⟩ | ⟨row, hrow, rfl⟩
    · exact hv.eqs p hp ha hb
    · exact (hr ⟨hrow.shape, hp⟩).2
  exact Database.ext h.values.sig
    (Set.Subset.antisymm (hsub h.values hd.storeOk hdrows) (hsub h'.values he.storeOk herows))
    h.env h.rules

/-- A finite reachable store universe suffices for generated saturation, despite row deletion. -/
theorem saturate_exists_of_finite_bound {d : Database} (h : Runtime d)
    (hn : MergeNormal d) (R : RulesetName) {bound : Set (Term × Term)}
    (hb : bound.Finite)
    (hbound : ∀ e, Relation.ReflTransGen (RunStep R) d e → e.eqs ⊆ bound) :
    ∃ e, SaturateReach R d e := by
  classical
  let states : Set Database := {e | Relation.ReflTransGen (RunStep R) d e}
  have hfinite : states.Finite := by
    apply (hb.finite_subsets.image (fun E => { d with eqs := E })).subset
    intro e he
    refine ⟨e.eqs, hbound e he, ?_⟩
    exact Database.ext (RunReach.sig he).symm rfl (RunReach.env he).symm
      (runReach_rules he).symm
  let below (e : Database) : Set Database := {s | s ∈ states ∧ Advances s e}
  have hbelow (e : Database) : (below e).Finite := hfinite.subset (fun _ hs => hs.1)
  have hnormal : ∀ e ∈ states, MergeNormal e := by
    intro e he
    induction he with
    | refl => exact hn
    | tail _ hs _ => exact hs.normal
  apply saturateReach_exists_of_measure R d (fun e => states.ncard - (below e).ncard)
  · intro e he
    exact (h.runReach he).state.runStep_exists (h.runReach he).generated
      (h.runReach he).storeOk (h.runReach he).rulesSafe (h.runReach he).noUnions R
  · intro e e' he hs hchange
    have he' : e' ∈ states := he.tail hs
    have hadv := Advances.runStep (h.runReach he) hs
    have hss : below e ⊂ below e' := by
      refine ⟨fun s hse => ⟨hse.1, hse.2.trans hadv⟩, ?_⟩
      intro hback
      have hreverse := (hback ⟨he', Advances.refl e'⟩).2
      have heq := hadv.antisymm hreverse (h.runReach he) (h.runReach he')
        (hnormal e he) (hnormal e' he')
      exact hchange (heq ▸ Database.SameMeaning.refl e)
    have hlt := Set.ncard_lt_ncard hss (hbelow e')
    have hle := Set.ncard_le_ncard (show below e' ⊆ states from fun _ hs => hs.1) hfinite
    omega

end Egglog.Congruence.Live
