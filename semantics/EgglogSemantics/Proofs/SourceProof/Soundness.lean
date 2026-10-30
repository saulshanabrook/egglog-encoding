import EgglogSemantics.Proofs.SourceProof.Rules

namespace Egglog.SourceProof

private theorem option_true {b : Option Bool} (h : b.getD false = true) : b = some true := by
  cases b with
  | none => simp at h
  | some b => simpa using h

/-- A valid node's claim is supported when its subproofs' claims are. -/
theorem checkNode_supported {P : Program} {db : Database}
    (hs : ProgramStep Database.empty P.commands db) (hw : db.WF)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules db) (hok : sourceOk P = true)
    {pf : Proof} (hp : ∀ q ∈ pf.subproofs, q.claim.Supported db)
    (h : checkNode P pf = true) : pf.claim.Supported db := by
  cases pf with
  | symm c p =>
      simp only [checkNode, beq_iff_eq] at h
      change Claim.Supported db c
      rw [h]
      exact (hp p (by simp [Proof.subproofs])).symm
  | trans c p q =>
      simp only [checkNode, Bool.and_eq_true_iff, beq_iff_eq] at h
      change Claim.Supported db c
      rw [h.2]
      have hq : Claim.Supported db ⟨p.claim.rhs, q.claim.rhs⟩ := by
        rw [h.1]; exact hp q (by simp [Proof.subproofs])
      exact Claim.Supported.trans (hp p (by simp [Proof.subproofs])) hq
  | congr c p k q =>
      simp only [checkNode] at h
      cases he : p.claim.rhs with
      | lit l => simp [he] at h
      | app f args =>
          simp only [he, Bool.and_eq_true_iff, beq_iff_eq] at h
          have hbase : Claim.Supported db ⟨p.claim.lhs, .app f args⟩ := by
            rw [← he]; exact hp p (by simp [Proof.subproofs])
          change Claim.Supported db c
          rw [h.2]
          exact hbase.congr (hp q (by simp [Proof.subproofs])) h.1
  | rule c i σ ps =>
      simp only [checkNode] at h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp (option_true h)
      obtain ⟨fs, hfs, h⟩ := Option.bind_eq_some_iff.mp h
      have hc : c ∈ fs := by simpa using h
      refine ruleFacts_supported hs hw hclosed hok (List.mem_of_getElem? hr) ?_ hfs c hc
      intro d hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
      exact hp q hq

mutual

theorem valid_supported {P : Program} {db : Database}
    (hs : ProgramStep Database.empty P.commands db) (hw : db.WF)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules db) (hok : sourceOk P = true) :
    (pf : Proof) → valid P pf = true → pf.claim.Supported db
  | .symm c p, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ih := valid_supported hs hw hclosed hok p h.1
      refine checkNode_supported hs hw hclosed hok ?_ h.2
      intro q hq
      simp only [Proof.subproofs, List.mem_singleton] at hq
      subst hq
      exact ih
  | .trans c p q, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ihp := valid_supported hs hw hclosed hok p h.1.1
      have ihq := valid_supported hs hw hclosed hok q h.1.2
      refine checkNode_supported hs hw hclosed hok ?_ h.2
      intro r hr
      simp only [Proof.subproofs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ihp
      · exact ihq
  | .congr c p k q, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ihp := valid_supported hs hw hclosed hok p h.1.1
      have ihq := valid_supported hs hw hclosed hok q h.1.2
      refine checkNode_supported hs hw hclosed hok ?_ h.2
      intro r hr
      simp only [Proof.subproofs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ihp
      · exact ihq
  | .rule c i σ ps, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      exact checkNode_supported hs hw hclosed hok
        (allValid_supported hs hw hclosed hok ps h.1) h.2
termination_by structural pf => pf

theorem allValid_supported {P : Program} {db : Database}
    (hs : ProgramStep Database.empty P.commands db) (hw : db.WF)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules db) (hok : sourceOk P = true) :
    (ps : List Proof) → allValid P ps = true → ∀ q ∈ ps, q.claim.Supported db
  | [], _, _, hq => by simp at hq
  | p :: ps, h, q, hq => by
      simp only [allValid, Bool.and_eq_true_iff] at h
      rcases List.mem_cons.mp hq with hqp | hq
      · rw [hqp]
        exact valid_supported hs hw hclosed hok p h.1
      · exact allValid_supported hs hw hclosed hok ps h.2 q hq
termination_by structural ps => ps

end

/-- Accepted claims retain source existence witnesses, including intermediate terms. -/
theorem check_supported {P : Program} {db : Database} {pf : Proof} {c : Claim}
    (hs : ProgramStep Database.empty P.commands db) (hw : db.WF)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules db) (h : check P pf = some c) :
    c.Supported db := by
  unfold check at h
  split at h
  · contradiction
  · rename_i hok
    have hok' : sourceOk P = true := by simpa using hok
    split at h
    · rename_i hv
      cases Option.some.inj h
      exact valid_supported hs hw hclosed hok' pf hv
    · contradiction

/-- Checking proves an inferred source equality, even at unstored constructor spellings. -/
theorem check_infers {P : Program} {db : Database} {pf : Proof} {c : Claim}
    (hs : ProgramStep Database.empty P.commands db) (hw : db.WF)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules db) (h : check P pf = some c) :
    db.Infers c.lhs c.rhs :=
  (check_supported hs hw hclosed h).infers hw

/-- On endpoints held by the source, checking implies its original congruence relation. -/
theorem check_sound {P : Program} {db : Database} {pf : Proof} {c : Claim}
    (hs : ProgramStep Database.empty P.commands db) (hw : db.WF)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules db) (h : check P pf = some c)
    (hl : c.lhs ∈ db.terms) (hr : c.rhs ∈ db.terms) : StoredCong db c.lhs c.rhs :=
  (check_supported hs hw hclosed h).holds hw hl hr

end Egglog.SourceProof
