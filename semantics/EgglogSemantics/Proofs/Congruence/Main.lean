import EgglogSemantics.Proofs.Congruence.Diverge
import EgglogSemantics.Proofs.Congruence.Check
import EgglogSemantics.Proofs.Congruence.Exact
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Source.WellFormed

/-! Congruence pass correctness from the empty state: preservation of outcomes and
divergence, exposed to the paper as `ExtlogTheorems.congruence_pass_correct`. A program
whose rules and check take no minimum is simulated up to the meaning of the source state; a
program without saturation, whose rules and check may take minima over query variables, is
simulated exactly. -/

namespace Egglog.Congruence

/-- Compiler correctness for a program whose rules and check take no minimum, by the
simulation up to meaning. -/
theorem encode_correct_orderingFree (P : Program) (hP : P.Fragment)
    (hO : Program.OrderingFree P) :
    (∀ o : Result, Eval Database.empty (encode P) o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty (encode P).schedule ↔ Diverges Database.empty P.schedule) := by
  have hinv : SrcInv P Database.empty := SrcInv.empty P
  have hrel : RelC P Database.empty Database.empty :=
    ⟨Database.empty, hinv, Database.SameMeaning.refl _, rel_empty, canon_empty⟩
  have hS : P.schedule.rules ⊆ P.rules := fun _ hr => hr
  -- A finite source result and a finite compiled result with related final states agree on
  -- the check.
  have hcheck : ∀ {e d : Database}, SrcInv P e → RelC P e d →
      (QueryHolds e P.check ↔ QueryHolds d (encode P).check) := by
    intro e d he ⟨x, hx, hm, hd, hc⟩
    rw [encode_check, ← check_corr hP hx hd hc]
    exact SourceMeaning.queryHolds_iff he.wf hx.wf hm he.hasReps hx.hasReps hO.2
  refine ⟨fun o => ?_, ?_⟩
  · cases o with
    | ok =>
      rw [Eval.ok_iff, Eval.ok_iff, encode_schedule]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel'⟩ := bwd_relC hP hO.1 hS hinv hrel hd
        exact ⟨e, he, (hcheck (hinv.reach hP hS he) hrel').mpr hq⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel'⟩ := fwd_relC hP hO.1 hS hinv hrel he
        exact ⟨d, hd, (hcheck (hinv.reach hP hS he) hrel').mp hq⟩
    | checkFailed =>
      rw [Eval.failed_iff, Eval.failed_iff, encode_schedule]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel'⟩ := bwd_relC hP hO.1 hS hinv hrel hd
        exact ⟨e, he, fun h => hq ((hcheck (hinv.reach hP hS he) hrel').mp h)⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel'⟩ := fwd_relC hP hO.1 hS hinv hrel he
        exact ⟨d, hd, fun h => hq ((hcheck (hinv.reach hP hS he) hrel').mpr h)⟩
  · rw [encode_schedule]
    exact (sim_div hP hO.1 P.schedule hS hinv hrel).symm

/-- The compiled program's outcomes and divergence agree with the source's. -/
theorem encode_correct (P : Program) (_hW : P.WellFormed) (hP : P.Fragment) :
    (∀ o : Result, Eval Database.empty (encode P) o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty (encode P).schedule ↔ Diverges Database.empty P.schedule) := by
  rcases hP.ordering with hO | ⟨hn, _⟩
  · exact encode_correct_orderingFree P hP hO
  · exact encode_correct_noSaturate hP hn

end Egglog.Congruence
