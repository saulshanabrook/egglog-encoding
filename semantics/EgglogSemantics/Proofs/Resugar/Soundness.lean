import EgglogSemantics.Resugar.Execute
import EgglogSemantics.Proofs.SourceProof.Soundness
import EgglogSemantics.Proofs.Provenance.Soundness

namespace Egglog.Resugar

/-- Lifting checks the source claim corresponding to the relational fact. -/
theorem lift_checked {P : Program} {input : Provenance.Proof}
    {output : SourceProof.Proof} {fact : Term} {claim : SourceProof.Claim}
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P fact = some claim) (h : lift P input = some output) :
    SourceProof.check P output = some claim := by
  unfold lift at h
  split at h
  · contradiction
  · have hf' : Provenance.check (Congruence.compile P).program
        input = some fact := hf
    simp only [hf', hc, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨result, _, hresult⟩ := Option.bind_eq_some_iff.mp h
    split at hresult
    · rename_i hcheck
      cases Option.some.inj hresult
      exact beq_iff_eq.mp hcheck
    · contradiction

/-- A successful lift is accepted for the claim written on its root. -/
theorem lift_check_claim {P : Program} {input : Provenance.Proof}
    {output : SourceProof.Proof} (h : lift P input = some output) :
    SourceProof.check P output = some output.claim := by
  unfold lift at h
  split at h
  · contradiction
  · obtain ⟨fact, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨claim, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨result, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hc
      cases Option.some.inj h
      have hc' := beq_iff_eq.mp hc
      unfold SourceProof.check at hc'
      split at hc'
      · contradiction
      · split at hc'
        · simp_all [SourceProof.check]
        · contradiction
    · contradiction

/-- Every proof returned by extraction and lifting checks against the source program. -/
theorem extractAll_checked {P : Program} {terms : List Term} {outputs : List SourceProof.Proof}
    (h : extractAll P terms = some outputs) :
    ∀ output ∈ outputs, SourceProof.check P output = some output.claim := by
  obtain ⟨rows, _, h⟩ := Option.bind_eq_some_iff.mp h
  have aux : ∀ (xs : Provenance.Facts) (ys : List SourceProof.Proof),
      xs.mapM (fun tp => lift P tp.2) = some ys →
      ∀ output ∈ ys, SourceProof.check P output = some output.claim := by
    intro xs
    induction xs with
    | nil => intro ys he output hm; simp at he; subst ys; simp at hm
    | cons x xs ih =>
      intro ys he output hm
      simp only [List.mapM_cons, Option.bind_eq_bind] at he
      obtain ⟨y, hy, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ys', hys, he⟩ := Option.bind_eq_some_iff.mp he
      cases Option.some.inj he
      rcases List.mem_cons.mp hm with rfl | hm
      · exact lift_check_claim hy
      · exact ih _ hys _ hm
  exact aux rows outputs h

/-- The public execution wrapper inherits the same checker guarantee. -/
theorem certificates_checked {exec : Program → Option FDatabase} {P : Program}
    {outputs : List SourceProof.Proof} (h : certificates exec P = some outputs) :
    ∀ output ∈ outputs, SourceProof.check P output = some output.claim := by
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact extractAll_checked h

/-- Lifting establishes the mapped claim in the reached, saturated source state. -/
theorem lift_supported {P : Program} {db : Database}
    {input : Provenance.Proof} {output : SourceProof.Proof}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : Reach Database.empty P.schedule db) (hw : db.WF)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P fact = some claim) (h : lift P input = some output) :
    claim.Supported db :=
  SourceProof.check_supported hs hw hclosed (lift_checked hf hc h)

theorem lift_sound {P : Program} {db : Database}
    {input : Provenance.Proof} {output : SourceProof.Proof}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : Reach Database.empty P.schedule db) (hw : db.WF)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P fact = some claim) (h : lift P input = some output)
    (hl : claim.lhs ∈ db.terms) (hr : claim.rhs ∈ db.terms) :
    StoredCong db claim.lhs claim.rhs :=
  (lift_supported hs hw hclosed hf hc h).holds hw hl hr

/-- Lifted claims have represented existence even at spellings absent from the store. -/
theorem lift_infers {P : Program} {db : Database}
    {input : Provenance.Proof} {output : SourceProof.Proof}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : Reach Database.empty P.schedule db) (hw : db.WF)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P fact = some claim) (h : lift P input = some output) :
    db.Infers claim.lhs claim.rhs :=
  SourceProof.check_infers hs hw hclosed (lift_checked hf hc h)

/-- Every extracted source proof infers its claim in the reached, saturated source model. -/
theorem extractAll_infers {P : Program} {db : Database} {terms : List Term}
    {outputs : List SourceProof.Proof}
    (hs : Reach Database.empty P.schedule db) (hw : db.WF)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db) (h : extractAll P terms = some outputs) :
    ∀ output ∈ outputs, db.Infers output.claim.lhs output.claim.rhs :=
  fun output ho => SourceProof.check_infers hs hw hclosed (extractAll_checked h output ho)

/-- Running the public certificate pipeline has the same source inference guarantee. -/
theorem certificates_infers {exec : Program → Option FDatabase} {P : Program} {db : Database}
    {outputs : List SourceProof.Proof}
    (hs : Reach Database.empty P.schedule db) (hw : db.WF)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db) (h : certificates exec P = some outputs) :
    ∀ output ∈ outputs, db.Infers output.claim.lhs output.claim.rhs :=
  fun output ho => SourceProof.check_infers hs hw hclosed (certificates_checked h output ho)

end Egglog.Resugar
