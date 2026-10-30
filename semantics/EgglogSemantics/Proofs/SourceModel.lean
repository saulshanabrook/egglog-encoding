import EgglogSemantics.Proofs.Completion
import EgglogSemantics.Proofs.Step

/-! Semantic saturation makes the completed source a model of its rules. -/

namespace Egglog.SourceMeaning

open InferredFacts

theorem firing_contained_round {d out : Database} {r : Rule} {R : List Rule}
    (hdf : ∀ r ∈ R, r.DeleteFree) (hr : r ∈ R) (ho : out ∈ RuleResults d r) :
    out.Contained (RunRules R d) := by
  rw [RunRules.eq_sUnion _ _ hdf]
  exact ⟨fun _ hp => Or.inr (Set.mem_iUnion₂.mpr ⟨out, ⟨r, hr, ho⟩, hp⟩)⟩

theorem round_extends (d : Database) (R : List Rule) (hdf : ∀ r ∈ R, r.DeleteFree) :
    d.Contained (RunRules R d) := by
  rw [RunRules.eq_addEqs hdf]
  exact ⟨Set.subset_union_left⟩

theorem firing_transport {d e out : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e)
    {r : Rule} (hn : r.OrderingFree) (hdf : r.DeleteFree)
    (ho : out ∈ RuleResults d r) :
    ∃ out', out' ∈ RuleResults e r ∧ out.SameMeaning out' := by
  obtain ⟨σ, hσ, hfire⟩ := ho
  obtain ⟨τ, hτ, hrel⟩ := validQuerySubst_transport hd he h hn.1 hσ
  obtain ⟨out', hfire', hsame⟩ := evalLocalActions_transport hd he h hrel hn.2 hdf hfire
  exact ⟨out', ⟨τ, hτ, hfire'⟩, hsame⟩

private theorem round_infers {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e)
    {R : List Rule} (hdf : ∀ r ∈ R, r.DeleteFree)
    (hn : ∀ r ∈ R, r.OrderingFree) {a b : Term}
    (hi : (RunRules R d).Infers a b) : (RunRules R e).Infers a b := by
  apply infers_of_assertions_only (RunRules.wf he) ?_ hi
  rw [RunRules.eq_sUnion R d hdf]
  rintro p (hp | hp)
  · exact infers_mono (round_extends e R hdf)
      ((h.inferred _ _).mp (infers_of_cong (.direct hp)))
  · obtain ⟨out, ⟨r, hr, ho⟩, hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨out', ho', hh⟩ := firing_transport hd he h (hn r hr) (hdf r hr) ho
    exact infers_mono (firing_contained_round hdf hr ho')
      ((hh.inferred _ _).mp (infers_of_cong (.direct hp)))

/-- Source rounds depend only on inferred facts, despite different stored spellings. -/
theorem round_sameMeaning {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e)
    {R : List Rule} (hdf : ∀ r ∈ R, r.DeleteFree)
    (hn : ∀ r ∈ R, r.OrderingFree) :
    (RunRules R d).SameMeaning (RunRules R e) := by
  refine Database.SameMeaning.of_inferred (fun a b => ⟨?_, ?_⟩)
  · exact round_infers hd he h hdf hn
  · exact round_infers he hd h.symm hdf hn

/-- Completing a semantic fixed point yields an ordinary assertion fixed point. -/
theorem completion_closed {d : Database} (hw : d.WF)
    {R : List Rule} (hdf : ∀ r ∈ R, r.DeleteFree)
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hfixed : d.SameMeaning (RunRules R d)) :
    RunRules R d.completion = d.completion := by
  apply (runRules_eq_self_iff R d.completion hdf).mpr
  intro r hr out ho
  obtain ⟨out', ho', hh⟩ := firing_transport hw.completion hw
    (d.sameMeaning_completion hw).symm (hn r hr) (hdf r hr) ho
  constructor
  intro p hp
  exact (hfixed.inferred _ _).mpr
    (infers_mono (firing_contained_round (d := d) hdf hr ho')
      ((hh.inferred _ _).mp (infers_of_cong (.direct hp))))

theorem completion_closed_of_saturated {d : Database} (hw : d.WF)
    {R : List Rule} (hdf : ∀ r ∈ R, r.DeleteFree)
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hfixed : RunSaturated R d) : RunRules R d.completion = d.completion :=
  completion_closed hw hdf hn hfixed

/-- The returned state of source saturation is closed, including its last round. -/
theorem saturation_completion_closed {d e : Database} (hw : d.WF)
    {R : List Rule} (hdf : ∀ r ∈ R, r.DeleteFree)
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hr : SaturateReach R d e) : RunRules R e.completion = e.completion := by
  induction hr with
  | @fixpoint d heq =>
    have hh : d.SameMeaning (RunRules R d) := ⟨fun a b => by rw [heq]⟩
    rw [← hh.completion_eq]
    exact completion_closed hw hdf hn hh
  | again _ _ ih => exact ih (RunRules.wf hw)

end Egglog.SourceMeaning
