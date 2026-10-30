import EgglogSemantics.Proofs.Congruence.LiveCoverage
import EgglogSemantics.Proofs.SourceMeaning

/-! Live readings survive completed rounds and are closed at a target fixed point. -/

namespace Egglog.Congruence.Live

theorem Covers.runRules (d : Database) (R : RulesetName) : Covers d (RunRules R d) :=
  .of_entries rfl (fun _ hr => ⟨hr.1, Or.inl hr.2⟩)

theorem Covers.runStep {d e : Database} (h : Runtime d) {R : RulesetName}
    (hr : RunStep R d e) : Covers d e :=
  (Covers.runRules d R).trans
    (.mergeClosure (h.runRules R).state (h.runRules R).noUnions.diag hr.1)

theorem Covers.runReach {d e : Database} (h : Runtime d) {R : RulesetName}
    (hr : Relation.ReflTransGen (RunStep R) d e) : Covers d e := by
  induction hr with
  | refl => exact .refl d
  | tail hs he ih => exact ih.trans (.runStep (h.runReach hs) he)

theorem saturated_endpoint {d e : Database} (h : Runtime d) {R : RulesetName}
    (hr : SaturateReach R d e) : RunSaturated R e := by
  induction hr using SaturateReach.induction with
  | @done a b hs hm =>
      exact ⟨hs.normal, b,
        hs.self_of_sameMeaning h.noUnions h.storeOk h.rulesSafe h.mergesWidthOk hm,
        Database.SameMeaning.refl b⟩
  | step hs _ _ ih => exact ih (h.runStep hs)

theorem Covers.firing {d post : Database} (h : Runtime d) {R : RulesetName}
    (hs : RunSaturated R d) {r : Rule} (hr : r ∈ d.rules) (hR : r.ruleset = R)
    (hf : post ∈ RuleResults d r) : Covers post d := by
  obtain ⟨out, hstep, heq⟩ := hs.2
  have hentries := h.storeOk.entries_eq_of_terms_eq (h.runStep hstep).storeOk heq.sig
    (heq.terms_eq_of_diag h.noUnions.diag (h.runStep hstep).noUnions.diag)
  exact (Covers.of_entries (e := RunRules R d)
    (show post.sig = (RunRules R d).sig from RuleResults.sig (db := d) hf)
    (fun _ he => ruleResult_row hr hR hf he)).trans
    ((Covers.mergeClosure (h.runRules R).state (h.runRules R).noUnions.diag hstep.1).trans
      (Covers.of_entries heq.sig.symm hentries.symm.subset))

theorem Reads.round {d src : Database} {R : RulesetName} (h : Reads d src)
    (hf : ∀ r ∈ src.rules, r.ruleset = R →
      ∀ post ∈ RuleResults src r, Reads d post) : Reads d (RunRules R src) := by
  rw [RunRules.eq_sUnion]
  apply h.sUnion
  rintro post ⟨r, hr, hR, hp⟩
  exact hf r hr hR post hp

end Egglog.Congruence.Live
