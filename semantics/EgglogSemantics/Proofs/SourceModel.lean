import EgglogSemantics.Proofs.Completion
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.Finite

/-! Semantic saturation makes the completed source a model of its rules. -/

namespace Egglog.SourceMeaning

open InferredFacts

theorem firing_contained_round {d out : Database} {r : Rule} {R : List Rule}
    (hdf : ∀ r ∈ R, r.SubsumeFree) (hr : r ∈ R) (ho : out ∈ RuleResults d r) :
    out.Contained (RunRules R d) := by
  rw [RunRules.eq_sUnion _ _]
  exact Database.Contained.mem_sUnion ⟨r, hr, ho⟩

theorem round_extends (d : Database) (R : List Rule) (hdf : ∀ r ∈ R, r.SubsumeFree) :
    d.Contained (RunRules R d) := by
  rw [RunRules.eq_addEqs hdf]
  exact ⟨Set.subset_union_left, subset_rfl⟩

theorem firing_transport {d e out : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) (hX : d.subsumed = e.subsumed) (hre : e.HasReps)
    {r : Rule} (hn : r.OrderingFree) (hdf : r.SubsumeFree)
    (ho : out ∈ RuleResults d r) :
    ∃ out', out' ∈ RuleResults e r ∧ out.SameMeaning out' := by
  obtain ⟨σ, hσ, hfire⟩ := ho
  obtain ⟨τ, hτ, hrel⟩ := validQuerySubst_transport hd he h hre hn.1 hσ
  obtain ⟨out', hfire', hsame⟩ := evalLocalActions_transport hd he h hX hrel hn.2 hdf hfire
  exact ⟨out', ⟨τ, hτ, hfire'⟩, hsame⟩

private theorem round_infers {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) (hX : d.subsumed = e.subsumed) (hre : e.HasReps)
    {R : List Rule} (hdf : ∀ r ∈ R, r.SubsumeFree)
    (hn : ∀ r ∈ R, r.OrderingFree) {a b : Term}
    (hi : (RunRules R d).Infers a b) : (RunRules R e).Infers a b := by
  apply infers_of_assertions_only (RunRules.wf he) ?_ hi
  rw [RunRules.eq_sUnion R d]
  rintro p (hp | hp)
  · exact infers_mono (round_extends e R hdf)
      ((h.inferred _ _).mp (infers_of_cong (.direct hp)))
  · obtain ⟨out, ⟨r, hr, ho⟩, hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨out', ho', hh⟩ := firing_transport hd he h hX hre (hn r hr) (hdf r hr) ho
    exact infers_mono (firing_contained_round hdf hr ho')
      ((hh.inferred _ _).mp (infers_of_cong (.direct hp)))

/-- Source rounds depend only on inferred facts when both stores have representatives. -/
theorem round_sameMeaning {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) (hX : d.subsumed = e.subsumed) (hrd : d.HasReps) (hre : e.HasReps)
    {R : List Rule} (hdf : ∀ r ∈ R, r.SubsumeFree)
    (hn : ∀ r ∈ R, r.OrderingFree) :
    (RunRules R d).SameMeaning (RunRules R e) := by
  refine Database.SameMeaning.of_inferred (by simpa only [RunRules.subsumed_eq hdf] using hX)
    (fun a b => ⟨?_, ?_⟩)
  · exact round_infers hd he h hX hre hdf hn
  · exact round_infers he hd h.symm hX.symm hrd hdf hn

/-- Completing a semantic fixed point yields an ordinary assertion fixed point. -/
theorem completion_closed {d : Database} (hw : d.WF) (hrd : d.HasReps)
    {R : List Rule} (hdf : ∀ r ∈ R, r.SubsumeFree)
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hfixed : d.SameMeaning (RunRules R d)) :
    RunRules R d.completion = d.completion := by
  apply (runRules_eq_self_iff R d.completion hdf).mpr
  intro r hr out ho
  obtain ⟨out', ho', hh⟩ := firing_transport hw.completion hw
    (d.sameMeaning_completion hw).symm rfl hrd (hn r hr) (hdf r hr) ho
  refine ⟨?_, ?_⟩
  · intro p hp
    exact (hfixed.inferred _ _).mpr
      (infers_mono (firing_contained_round (d := d) hdf hr ho')
        ((hh.inferred _ _).mp (infers_of_cong (.direct hp))))
  · obtain ⟨σ, _, hs⟩ := ho
    exact (evalActions_subsumed (hdf r hr) hs).subset

theorem completion_closed_of_saturated {d : Database} (hw : d.WF) (hrd : d.HasReps)
    {R : List Rule} (hdf : ∀ r ∈ R, r.SubsumeFree)
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hfixed : RunSaturated R d) : RunRules R d.completion = d.completion :=
  completion_closed hw hrd hdf hn hfixed

/-- The returned state of source saturation is closed, including its last round. -/
theorem saturation_completion_closed {d e : Database} (hw : d.WF)
    (hf : d.eqs.Finite)
    {R : List Rule} (hdf : ∀ r ∈ R, r.SubsumeFree)
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hr : Reach d (.saturate (.run R)) e) : RunRules R e.completion = e.completion := by
  generalize hS : Schedule.saturate (.run R) = S at hr
  induction hr with
  | run => cases hS
  | seq => cases hS
  | @fixpoint d out S hp heq _ =>
    cases hS
    cases hp
    have hh : d.SameMeaning (RunRules R d) := heq
    rw [← hh.completion_eq (RunRules.subsumed_eq hdf).symm]
    exact completion_closed hw (Database.hasReps_of_finite hf) hdf hn hh
  | again hp _ _ _ ih =>
    cases hS
    exact ih (hp.wf hw) (hp.finite hf) rfl

end Egglog.SourceMeaning
