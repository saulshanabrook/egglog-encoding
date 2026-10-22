import EgglogSemantics.Proofs.SourceMeaning

/-! A proof-only completion records exactly the facts already inferred. -/

namespace Egglog

open InferredFacts

/-- This may be infinite; operational executions still use the original database. -/
def Database.completion (d : Database) : Database :=
  {d with eqs := {p | d.Infers p.1 p.2}}

theorem Database.contained_completion (d : Database) : d.Contained d.completion :=
  ⟨fun _ hp => infers_of_cong (.direct hp)⟩

theorem Database.cong_completion_iff {d : Database} (hw : d.WF) {a b : Term} :
    StoredCong d.completion a b ↔ d.Infers a b := by
  refine ⟨fun hc => ?_, fun hi => .direct hi⟩
  exact infers_of_assertions_only (e := d.completion) hw (fun _ hp => hp)
    (infers_of_cong hc)

theorem Database.mem_completion_iff {d : Database} (hw : d.WF) {t : Term} :
    t ∈ d.completion.terms ↔ d.Infers t t :=
  Database.mem_terms_iff_storedCong.trans (cong_completion_iff hw)

theorem Database.WF.completion {d : Database} (hw : d.WF) : d.completion.WF where
  litsIsolated := fun _ hp hl => infers_eq_of_isLit hw hp hl

theorem Database.sameMeaning_completion {d : Database} (hw : d.WF) :
    d.SameMeaning d.completion :=
  Database.SameMeaning.of_inferred (fun _ _ => ⟨infers_mono d.contained_completion,
    infers_of_assertions_only (e := d.completion) hw (fun _ hp => hp)⟩)

theorem Database.completion_idempotent {d : Database} (hw : d.WF) :
    d.completion.completion = d.completion := by
  apply Database.ext <;> try rfl
  ext p
  exact (d.sameMeaning_completion hw).inferred p.1 p.2 |>.symm

theorem Database.SameMeaning.completion_eq {d e : Database} (h : d.SameMeaning e) :
    d.completion = e.completion := by
  apply Database.ext
  · exact Set.ext (fun p => h.inferred p.1 p.2)

theorem Database.sameMeaning_iff_completion_eq {d e : Database} :
    d.SameMeaning e ↔ d.completion = e.completion := by
  refine ⟨Database.SameMeaning.completion_eq, fun h => ?_⟩
  apply Database.SameMeaning.of_inferred
  exact fun a b => Set.ext_iff.mp (congrArg Database.eqs h) (a, b)

theorem SourceMeaning.queryHolds_completion_iff {d : Database}
    (hw : d.WF)
    {q : Query} (hq : ∀ p ∈ q, p.OrderingFree) :
    QueryHolds d.completion q ↔ QueryHolds d q :=
  (queryHolds_iff hw hw.completion
    (d.sameMeaning_completion hw) hq).symm

end Egglog
