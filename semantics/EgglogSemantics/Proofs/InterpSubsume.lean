import EgglogSemantics.Proofs.NoUnions
import EgglogSemantics.Proofs.Subsume
import EgglogSemantics.Proofs.Congruence.Properties

/-! Interpreter refinement for union-free programs with subsumption, disequality and `min`. -/

namespace Egglog

/-- Listed marks are held by the finite store's index invariant. -/
theorem FDatabase.IndexOk.marksExist {d : FDatabase} (hi : d.IndexOk)
    (hc : d.SubtermClosed) : d.toDatabase.MarksExist := by
  intro t ht
  exact Database.toCong ((FDatabase.mem_toDatabase_terms hc).mpr (hi.subsumed t ht))

/-- Equal meaning transports every lookup, including `min` and disequality. -/
theorem Database.SameMeaning.matches_iff {d e : Database} (h : d.SameMeaning e)
    (p : Pattern) (σ : Env) : Matches d p σ ↔ Matches e p σ :=
  ⟨Matches.sameMeaning h, Matches.sameMeaning h.symm⟩

/-- On diagonal states with the same meaning, valid environments coincide. -/
theorem Database.SameMeaning.queryMatches_iff_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag) (q : Query) (σ : Env) :
    QueryMatches d q σ ↔ QueryMatches e q σ := by
  simp only [QueryMatches, ValidEnv, h.reps_eq (h.terms_eq_of_diag hd he), h.matches_iff]

theorem Database.SameMeaning.queryHolds_iff_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag) (q : Query) :
    QueryHolds d q ↔ QueryHolds e q := by
  simp only [QueryHolds, h.queryMatches_iff_of_diag hd he]

/-- Existing marks make diagonal round transport independent of their spelling. -/
theorem Database.SameMeaning.runRules_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag)
    (hmd : d.MarksExist) (hme : e.MarksExist) (R : List Rule) :
    (RunRules R d).SameMeaning (RunRules R e) := by
  have hw : RunWrites R d = RunWrites R e := by
    simp only [RunWrites, h.queryMatches_iff_of_diag hd he]
  have hx : RunMarks R d = RunMarks R e := by
    simp only [RunMarks, h.queryMatches_iff_of_diag hd he]
  simp only [RunRules.eq_pair, hw, hx]
  exact (h.addEqs_of_app_marks (h.app_marks_iff_of_diag hd he hmd hme) _).addSubsumed _

theorem execRunRules_RunRules_of_eqs_empty {R : List Rule} {d : FDatabase}
    (hc : d.SubtermClosed) (he : d.eqs = []) (hi : d.IndexOk) (hj : d.IndexCurrent) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R d.toDatabase) :=
  execRunRules_RunRules ⟨by simp [he], hc⟩ hi hj

/-- On a subterm-closed state with valid indices and no asserted unions, an executable
round refines the specification up to meaning. -/
theorem execRunRules_RunRules_noUnions {R : List Rule} {d : FDatabase}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R d.toDatabase) :=
  execRunRules_RunRules_of_eqs_empty hc hn.eqs hi hj

theorem closed_execRunRules_noUnions {R : List Rule} {d : FDatabase}
    (hc : d.SubtermClosed) (hn : d.NoUnions) : (execRunRules R d).Closed :=
  closed_execRunRules ⟨by simp [hn.eqs], hc⟩

private structure UnionFreeInterpReady (d : FDatabase) : Prop where
  closed : d.Closed
  indexOk : d.IndexOk
  indexCurrent : d.IndexCurrent
  noUnions : d.NoUnions

private theorem UnionFreeInterpReady.of_invariants {d : FDatabase}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions) :
    UnionFreeInterpReady d := ⟨⟨by simp [hn.eqs], hc⟩, hi, hj, hn⟩

private theorem UnionFreeInterpReady.round {d : FDatabase} (h : UnionFreeInterpReady d)
    (R : List Rule) (hu : ∀ r ∈ R, r.UnionFree) : UnionFreeInterpReady (execRunRules R d) :=
  let hi := execRunRules_index (R := R) h.indexOk h.indexCurrent
  ⟨closed_execRunRules_noUnions h.closed.subterms h.noUnions, hi.1, hi.2,
    execRunRules_noUnions h.noUnions hu⟩

private theorem UnionFreeInterpReady.empty : UnionFreeInterpReady FDatabase.empty := by
  exact ⟨FDatabase.empty_closed, ⟨by simp [FDatabase.empty], by simp [FDatabase.empty]⟩,
    by simp [FDatabase.IndexCurrent, FDatabase.empty], .empty⟩

private theorem UnionFreeInterpReady.schedule {d e : FDatabase}
    (h : UnionFreeInterpReady d) {S : Schedule} {fuel : Nat} (hu : S.UnionFree)
    (he : execSchedule fuel d S = some e) : UnionFreeInterpReady e :=
  execSchedule_preserves (fun rs _ hg h => h.round rs hg) hu h he

private theorem round_transport_noUnions {d : FDatabase} {db : Database}
    (h : UnionFreeInterpReady d) (hn : db.NoUnions) (hm : db.MarksExist)
    (hh : d.toDatabase.SameMeaning db) (R : List Rule) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R db) :=
  (execRunRules_RunRules_noUnions h.closed.subterms h.indexOk h.indexCurrent h.noUnions).trans
    (hh.runRules_of_diag h.noUnions.toDatabase.diag hn.diag
      (h.indexOk.marksExist h.closed.subterms) hm R)

private theorem execSchedule_transport_noUnions {d e : FDatabase} {db : Database}
    (h : UnionFreeInterpReady d) (hn : db.NoUnions) (hm : db.MarksExist)
    (hh : d.toDatabase.SameMeaning db) {S : Schedule} {fuel : Nat} (hu : S.UnionFree)
    (he : execSchedule fuel d S = some e) :
    ∃ out, Reach db S out ∧ e.toDatabase.SameMeaning out :=
  execSchedule_refines (I := UnionFreeInterpReady)
    (J := fun db => db.NoUnions ∧ db.MarksExist)
    (good := Rule.UnionFree) (fun rs _ hg h => h.round rs hg)
    (fun _ _ hg h => ⟨RunRules.noUnions h.1 hg, RunRules.marksExist h.2⟩)
    (fun rs _ _ _ h hn hh => round_transport_noUnions h hn.1 hn.2 hh rs)
    (fun rs _ _ _ hd he hm => hm.runRules_of_diag hd.1.diag he.1.diag hd.2 he.2 rs)
    hu h ⟨hn, hm⟩ hh he

/-- Successful union-free schedules refine the specification, including nested saturation. -/
theorem execSchedule_reach_noUnions {d e : FDatabase} (hc : d.SubtermClosed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions) {S : Schedule} {fuel : Nat}
    (hu : S.UnionFree) (hs : execSchedule fuel d S = some e) :
    ∃ out, Reach d.toDatabase S out ∧ e.toDatabase.SameMeaning out :=
  execSchedule_transport_noUnions (.of_invariants hc hi hj hn) hn.toDatabase (hi.marksExist hc) (.refl _) hu hs

/-- Every successful union-free execution from empty has a specification result of the
same meaning, including programs using subsumption, disequality and `min`. -/
theorem exec_programStep_noUnions {p : Program} {e : FDatabase}
    (hu : p.UnionFree) (hs : exec p = some e) :
    ∃ out, Reach Database.empty p.schedule out ∧ e.toDatabase.SameMeaning out := by
  have h := UnionFreeInterpReady.empty
  simpa only [FDatabase.toDatabase_empty] using
    execSchedule_reach_noUnions h.closed.subterms h.indexOk h.indexCurrent h.noUnions hu hs

/-- Every saturation-free union-free specification execution has an executable result
of the same meaning. Subsumption, disequality and `min` require no extra premises. -/
theorem execProgram_complete_noUnions {p : Schedule} {fuel : Nat}
    {d : FDatabase} {out : Database}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions)
    (hu : p.UnionFree) (hns : p.NoSaturate) (hs : Reach d.toDatabase p out) :
    ∃ e, execSchedule fuel d p = some e ∧ e.toDatabase.SameMeaning out := by
  obtain ⟨e, hex⟩ := execSchedule_exists (fuel := fuel) hns d
  obtain ⟨out', hr, hm⟩ := execSchedule_reach_noUnions hc hi hj hn hu hex
  exact ⟨e, hex, hr.det hs ▸ hm⟩

theorem exec_complete_noUnions {p : Program} {out : Database}
    (hu : p.UnionFree) (hns : p.NoSaturate) (hs : Reach Database.empty p.schedule out) :
    ∃ e, exec p = some e ∧ e.toDatabase.SameMeaning out := by
  have h := UnionFreeInterpReady.empty
  exact execProgram_complete_noUnions h.closed.subterms h.indexOk h.indexCurrent h.noUnions
    hu hns (by simpa only [FDatabase.toDatabase_empty] using hs)

/-- Successful execution of the compiled program refines its specification up to meaning.
Source-to-target equivalence is stated in `ExtlogTheorems.congruence_pass_correct`. -/
theorem Congruence.exec_encode_programStep {p : Program} {e : FDatabase}
    (hs : exec (Congruence.encode p) = some e) :
    ∃ out, Reach Database.empty (Congruence.encode p).schedule out ∧
      e.toDatabase.SameMeaning out :=
  exec_programStep_noUnions (Congruence.encode_unionFree p) hs

/-- Union-free command execution also agrees on its final check, including disequality. -/
theorem exec_programStep_check_noUnions {p : Program} {e : FDatabase}
    (hu : p.UnionFree) (hs : exec p = some e) :
    ∃ out, Reach Database.empty p.schedule out ∧ e.toDatabase.SameMeaning out ∧
      (e.holds p.check = true ↔ QueryHolds out p.check) := by
  obtain ⟨out, hout, hm⟩ := exec_programStep_noUnions hu hs
  have he := UnionFreeInterpReady.empty.schedule hu hs
  exact ⟨out, hout, hm, (FDatabase.holds_iff_queryHolds he.closed he.indexOk
    he.indexCurrent p.check).trans (hm.queryHolds_iff_of_diag he.noUnions.toDatabase.diag
      (hout.noUnions Database.NoUnions.empty hu).diag p.check)⟩

/-- The observer refines both finite outcomes for arbitrary union-free programs. -/
theorem observe_eval_noUnions {p : Program} {r : ExecutionResult}
    (hu : p.UnionFree) (hs : observe p = some r) :
    ∃ result, Eval Database.empty p result ∧ result.succeeded = r.succeeded := by
  apply observe_eval_of_exec ?_ hs
  intro e he
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check_noUnions hu he
  exact ⟨out, hout, hq⟩

end Egglog
