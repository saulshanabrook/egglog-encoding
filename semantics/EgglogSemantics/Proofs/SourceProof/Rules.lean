import EgglogSemantics.Proofs.SourceProof.Matching
import EgglogSemantics.Proofs.SourceProof.Support
import EgglogSemantics.Proofs.SourceModel
import EgglogSemantics.Proofs.Source.Domain

namespace Egglog.SourceProof

/-- `sourceOk` is `Program.Fragment`, decided. -/
theorem sourceOk_fragment {P : Program} (h : sourceOk P = true) : P.Fragment :=
  of_decide_eq_true h

/-- The fragment computes with no `min`, so neither does any of its rules. -/
theorem sourceOk_rule {P : Program} (h : sourceOk P = true) {r : Rule}
    (hr : r ∈ P.rules) : r.OrderingFree :=
  (sourceOk_fragment h).noMin.1 r hr

/-- A checked head fact follows from a valid source rule firing, up to supported terms. -/
theorem ruleFacts_supported {P : Program} {db : Database}
    (hs : Reach Database.empty P.schedule db) (hw : db.WF)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db) (hok : sourceOk P = true) {r : Rule}
    (hr : r ∈ P.rules) {σ : Env} {premises fs : List Claim}
    (hp : ∀ c ∈ premises, c.Supported db) (hf : ruleFacts r σ premises = some fs) :
    ∀ c ∈ fs, c.Supported db := by
  obtain ⟨rs, hrs, hr⟩ := Program.mem_rules_iff.mp hr
  have hmem : ∀ r ∈ rs, r ∈ P.rules := fun r hr => Program.mem_rules_iff.mpr ⟨rs, hrs, hr⟩
  have hdf : ∀ r ∈ rs, r.SubsumeFree := fun r hr =>
    Schedule.subsumeFree_of_monotone
      (Bool.and_eq_true_iff.mp (sourceOk_fragment hok).monotone).1 r (hmem r hr)
  have hX : db.subsumed = ∅ := hs.subsumed_eq
    (Schedule.subsumeFree_of_monotone (Bool.and_eq_true_iff.mp (sourceOk_fragment hok).monotone).1)
  unfold ruleFacts at hf
  split at hf
  · rename_i hchecks
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at hchecks
    have hh : ∀ c ∈ premises, c.Holds db.completion :=
      fun c hc => (hp c hc).completion hw
    have hval : ∀ b ∈ σ, b.2 ∈ db.completion.terms := fun b hb =>
      supportedValue_sound hw.completion hh (hchecks.1.2 b hb)
    have hn := (sourceOk_fragment hok).noMin.1 r (hmem r hr)
    have hsmean := (db.sameMeaning_completion hw).symm
    obtain ⟨τ, hτ, hrel⟩ := SourceMeaning.querySubst_of_matches_transport
      hw.completion hw hsmean (Database.hasReps_of_finite hs.finite_from_empty)
      hchecks.1.1 hval hn.1 (premisesMatch_sound hX hn.1 hh hchecks.2)
    obtain ⟨d, hd, hfacts⟩ := actionsFacts_sound (db := db.completion) hf
    obtain ⟨out, hout, hsame⟩ := SourceMeaning.evalLocalActions_transport
      hw.completion hw hsmean rfl hrel hn.2 (hdf r hr) hd
    have hpost := SourceMeaning.firing_contained_round hdf hr ⟨τ, hτ, hout⟩
    intro c hc
    apply Claim.Supported.of_completion hw
    apply (Database.cong_completion_iff hw).mpr
    exact ((hclosed rs hrs).inferred _ _).mpr
      (InferredFacts.infers_mono hpost
        ((hsame.inferred _ _).mp (InferredFacts.infers_of_cong (hfacts c hc))))
  · contradiction

end Egglog.SourceProof
