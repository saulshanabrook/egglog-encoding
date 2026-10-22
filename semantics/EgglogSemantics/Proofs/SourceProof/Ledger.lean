import EgglogSemantics.Proofs.SourceProof.Support

namespace Egglog.SourceProof

open Conservativity

theorem Claim.Supported.addEq_wf {A db : Database} (hA : A.WF) (hw : db.WF)
    {c : Claim} (hc : c.Supported db) : (A.addEq c.lhs c.rhs).WF := by
  refine hA.addEq _ _ (StoredCong.eq_of_isLit ?_ hc.equality)
  intro p hp hl
  exact (show p ∈ db.eqs ∨ p.1 = p.2 from hp).elim (fun hp => hw.litsIsolated p hp hl) id

def ledger : List Claim → Database
  | [] => Database.empty
  | c :: cs => (ledger cs).addEq c.lhs c.rhs

theorem ledger_contained_completion {db : Database} (hw : db.WF)
    {cs : List Claim} (hc : ∀ c ∈ cs, c.Supported db) :
    (ledger cs).Contained db.completion := by
  induction cs with
  | nil => exact ⟨by simp [ledger, Database.empty]⟩
  | cons c cs ih =>
      have hclaim := (hc c (by simp)).completion hw
      have htail := ih (fun c h => hc c (by simp [h]))
      refine ⟨?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with rfl | hp
      · exact (Database.cong_completion_iff hw).mp hclaim
      · exact htail.eqs hp

theorem ledger_wf {db : Database} (hw : db.WF) {cs : List Claim}
    (hc : ∀ c ∈ cs, c.Supported db) : (ledger cs).WF := by
  induction cs with
  | nil => exact Database.WF.empty
  | cons c cs ih =>
      exact (hc c (by simp)).addEq_wf (ih fun c h => hc c (by simp [h])) hw

theorem ledger_holds {cs : List Claim} {c : Claim} (hc : c ∈ cs) :
    c.Holds (ledger cs) := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact StoredCong.direct (Set.mem_insert _ _)
      · exact (ih hc).mono (Database.Contained.addEq _ _ _)

end Egglog.SourceProof
