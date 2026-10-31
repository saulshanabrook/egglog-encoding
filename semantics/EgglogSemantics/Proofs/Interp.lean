import EgglogSemantics.Proofs.InterpRound

namespace Egglog

private structure InterpReady (d : FDatabase) : Prop where
  closed : d.Closed
  indexOk : d.IndexOk
  indexCurrent : d.IndexCurrent
  wf : d.toDatabase.WF

private theorem InterpReady.round {d : FDatabase} (h : InterpReady d) (R : List Rule) :
    InterpReady (execRunRules R d) := by
  have hi := execRunRules_index (R := R) h.indexOk h.indexCurrent
  refine ⟨closed_execRunRules h.closed, hi.1, hi.2, ?_⟩
  exact FDatabase.wf_of_sameMeaning
    (execRunRules_RunRules h.closed h.indexOk h.indexCurrent) (RunRules.wf h.wf)

private theorem InterpReady.empty : InterpReady FDatabase.empty := by
  exact ⟨FDatabase.empty_closed, ⟨by simp [FDatabase.empty], by simp [FDatabase.empty]⟩,
    by simp [FDatabase.IndexCurrent, FDatabase.empty], FDatabase.empty_wf⟩

private theorem round_transport {d : FDatabase} {db : Database} (h : InterpReady d)
    (hw : db.WF) (hf : db.eqs.Finite) (hh : d.toDatabase.SameMeaning db)
    (hX : d.toDatabase.subsumed = db.subsumed) (R : List Rule)
    (hd : ∀ r ∈ R, r.SubsumeFree) (hn : ∀ r ∈ R, r.OrderingFree) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R db) :=
  (execRunRules_RunRules h.closed h.indexOk h.indexCurrent).trans
    (SourceMeaning.round_sameMeaning h.wf hw hh hX
      (Database.hasReps_of_finite d.finite_toDatabase) (Database.hasReps_of_finite hf) hd hn)

private theorem InterpReady.schedule {d e : FDatabase} (h : InterpReady d)
    {S : Schedule} {fuel : Nat} (he : execSchedule fuel d S = some e) : InterpReady e :=
  execSchedule_preserves (good := fun _ => True) (fun rs _ _ h => h.round rs)
    (fun _ _ => trivial) h he

private theorem execSchedule_transport {d e : FDatabase} {db : Database}
    (h : InterpReady d) (hw : db.WF) (hf : db.eqs.Finite) (hh : d.toDatabase.SameMeaning db)
    (hX : d.toDatabase.subsumed = db.subsumed)
    {S : Schedule} {fuel : Nat} (hd : ∀ r ∈ S.rules, r.SubsumeFree) (hn : S.OrderingFree)
    (he : execSchedule fuel d S = some e) :
    ∃ out, Reach db S out ∧ e.toDatabase.SameMeaning out := by
  apply execSchedule_refines
    (I := fun e => InterpReady e ∧ e.toDatabase.subsumed = db.subsumed)
    (J := fun e => e.WF ∧ e.eqs.Finite ∧ e.subsumed = db.subsumed)
    (good := fun r => r.SubsumeFree ∧ r.OrderingFree)
    (fun rs _ hg h => ⟨h.1.round rs,
      (execRunRules_subsumed_of_subsumeFree h.1.closed h.1.indexOk h.1.indexCurrent
        (fun r hr => (hg r hr).1)).trans h.2⟩)
    (fun rs _ hg hw => ⟨RunRules.wf hw.1, RunRules.finite_eqs hw.2.1 rs,
      (RunRules.subsumed_eq (fun r hr => (hg r hr).1)).trans hw.2.2⟩)
    (fun rs _ _ hg h hw hh => round_transport h.1 hw.1 hw.2.1 hh
      (h.2.trans hw.2.2.symm) rs (fun r hr => (hg r hr).1) (fun r hr => (hg r hr).2))
    (fun _ _ _ hg hw hw' hm => SourceMeaning.round_sameMeaning hw.1 hw'.1 hm
      (hw.2.2.trans hw'.2.2.symm)
      (Database.hasReps_of_finite hw.2.1) (Database.hasReps_of_finite hw'.2.1)
      (fun r hr => (hg r hr).1) (fun r hr => (hg r hr).2))
    (fun r hr => ⟨hd r hr, hn r hr⟩) ⟨h, hX⟩ ⟨hw, hf, rfl⟩ hh he

/-- Successful execution of a nested schedule has a specification result of the same meaning. -/
theorem execSchedule_reach {d e : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) (hw : d.toDatabase.WF) {S : Schedule} {fuel : Nat}
    (hd : ∀ r ∈ S.rules, r.SubsumeFree) (hc : S.OrderingFree)
    (hs : execSchedule fuel d S = some e) :
    ∃ out, Reach d.toDatabase S out ∧ e.toDatabase.SameMeaning out :=
  execSchedule_transport ⟨he, hi, hj, hw⟩ hw d.finite_toDatabase (.refl _) rfl hd hc hs

/-- The former command-refinement interface now accepts a nested schedule. -/
theorem execCmd_cmdStep {d e : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) (hw : d.toDatabase.WF) {c : Schedule} {fuel : Nat}
    (hd : ∀ r ∈ c.rules, r.SubsumeFree) (hc : c.OrderingFree)
    (hs : execSchedule fuel d c = some e) :
    ∃ out, Reach d.toDatabase c out ∧ e.toDatabase.SameMeaning out :=
  execSchedule_reach he hi hj hw hd hc hs

private theorem schedule_subsumeFree {S : Schedule} (h : S.monotoneB = true) :
    ∀ r ∈ S.rules, r.SubsumeFree := by
  intro r hr
  exact Actions.subsumeFree_of_all (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h r hr)).2

theorem execProgram_programStep {p : Schedule} {fuel : Nat} {d e : FDatabase}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hp : p.monotoneB = true) (ho : p.OrderingFree)
    (hs : execSchedule fuel d p = some e) :
    ∃ out, Reach d.toDatabase p out ∧ e.toDatabase.SameMeaning out :=
  execSchedule_reach he hi hj hw (schedule_subsumeFree hp) ho hs

/-- `exec` executes the schedule; the final check is a separate observation. -/
theorem exec_programStep {p : Program} {e : FDatabase}
    (hp : p.schedule.monotoneB = true) (ho : p.OrderingFree)
    (hs : exec p = some e) :
    ∃ out, Reach Database.empty p.schedule out ∧ e.toDatabase.SameMeaning out := by
  have h := InterpReady.empty
  simpa only [FDatabase.toDatabase_empty] using
    execProgram_programStep h.closed h.indexOk h.indexCurrent h.wf hp ho.1 hs

theorem closed_iterate {R : List Rule} (k : Nat) {d : FDatabase}
    (he : d.Closed) (hd : ∀ r ∈ R, r.SubsumeFree) : ((execRunRules R)^[k] d).Closed := by
  induction k generalizing d with
  | zero => exact he
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (closed_execRunRules he)

theorem execCmd_closed {d e : FDatabase} (he : d.Closed) {c : Schedule} {fuel : Nat}
    (hd : ∀ r ∈ c.rules, r.SubsumeFree) (hs : execSchedule fuel d c = some e) : e.Closed :=
  execSchedule_preserves (fun _ _ hg h => closed_execRunRules h) hd he hs

/-- Successful saturation refines the semantic fixed point for these rules. -/
theorem runSaturateF_saturateReach {R : List Rule} {n : Nat} {d e : FDatabase}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hd : ∀ r ∈ R, r.SubsumeFree) (hn : ∀ r ∈ R, r.OrderingFree)
    (hs : d.runSaturateF R n = some e) :
    ∃ out, Reach d.toDatabase (.saturate (.run R)) out ∧ e.toDatabase.SameMeaning out :=
  execSchedule_reach he hi hj hw hd hn (by rwa [execSchedule_saturate_run])

private theorem iterate_transport {R : List Rule}
    (hd : ∀ r ∈ R, r.SubsumeFree) (hn : ∀ r ∈ R, r.OrderingFree) : ∀ (k : Nat)
    {d : FDatabase} {db : Database}, InterpReady d → db.WF → db.eqs.Finite →
    d.toDatabase.SameMeaning db → d.toDatabase.subsumed = db.subsumed →
    ((execRunRules R)^[k] d).toDatabase.SameMeaning ((RunRules R)^[k] db) := by
  intro k
  induction k with
  | zero => intro d db _ _ _ hh _; exact hh
  | succ k ih =>
    intro d db h hw hf hh hX
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (h.round R) (RunRules.wf hw) (RunRules.finite_eqs hf R)
      (round_transport h hw hf hh hX R hd hn)
      (by rw [execRunRules_subsumed_of_subsumeFree h.closed h.indexOk h.indexCurrent hd,
        RunRules.subsumed_eq hd, hX])

theorem execRunRules_iterate {R : List Rule} (k : Nat) {d : FDatabase}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hd : ∀ r ∈ R, r.SubsumeFree) (hn : ∀ r ∈ R, r.OrderingFree) :
    ((execRunRules R)^[k] d).toDatabase.SameMeaning ((RunRules R)^[k] d.toDatabase) :=
  iterate_transport hd hn k ⟨he, hi, hj, hw⟩ hw d.finite_toDatabase (.refl _) rfl

/-- Every saturation-free schedule succeeds, independently of its rule heads and fuel. -/
theorem execCmd_toDatabase {d : FDatabase} {c : Schedule} {fuel : Nat}
    (hns : c.NoSaturate) :
    (execSchedule fuel d c).isSome = true ↔ ∃ out, Reach d.toDatabase c out := by
  constructor
  · intro _; exact Reach.exists_of_noSaturate hns
  · intro _
    obtain ⟨e, he⟩ := execSchedule_exists (fuel := fuel) hns d
    simp [he]

theorem execProgram_complete {p : Schedule} {fuel : Nat} {d : FDatabase} {out : Database}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hp : p.monotoneB = true) (ho : p.OrderingFree)
    (hns : p.NoSaturate) (hs : Reach d.toDatabase p out) :
    ∃ e, execSchedule fuel d p = some e ∧ e.toDatabase.SameMeaning out := by
  obtain ⟨e, hex⟩ := execSchedule_exists (fuel := fuel) hns d
  obtain ⟨out', hr, hm⟩ := execProgram_programStep he hi hj hw hp ho hex
  exact ⟨e, hex, hr.det hs ▸ hm⟩

theorem exec_complete {p : Program} {out : Database}
    (hp : p.schedule.monotoneB = true) (ho : p.OrderingFree) (hns : p.NoSaturate)
    (hs : Reach Database.empty p.schedule out) :
    ∃ e, exec p = some e ∧ e.toDatabase.SameMeaning out := by
  have h := InterpReady.empty
  exact execProgram_complete h.closed h.indexOk h.indexCurrent h.wf hp ho.1 hns
    (by simpa only [FDatabase.toDatabase_empty] using hs)

/-- The executable final check agrees with the existential specification query. -/
theorem FDatabase.holds_iff_queryHolds {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) (q : Query) :
    d.holds q = true ↔ QueryHolds d.toDatabase.forgetSubsumed q := by
  simpa only [FDatabase.holds, Bool.not_eq_true', FDatabase.toDatabase_forgetSubsumed] using
    (queryHolds_iff_matchQuery he.forgetSubsumed hi.forgetSubsumed hj.forgetSubsumed q).symm

/-- Command refinement and final-check agreement for the source fragment. -/
theorem exec_programStep_check {p : Program} {e : FDatabase}
    (hp : p.schedule.monotoneB = true) (ho : p.OrderingFree)
    (hs : exec p = some e) :
    ∃ out, Reach Database.empty p.schedule out ∧ e.toDatabase.SameMeaning out ∧
      (e.holds p.check = true ↔ QueryHolds out.forgetSubsumed p.check) := by
  obtain ⟨out, hout, hm⟩ := exec_programStep hp ho hs
  have he := InterpReady.empty.schedule hs
  exact ⟨out, hout, hm, (FDatabase.holds_iff_queryHolds he.closed he.indexOk
    he.indexCurrent p.check).trans
    (SourceMeaning.queryHolds_iff he.wf.forgetSubsumed (hout.wf Database.WF.empty).forgetSubsumed hm.forgetSubsumed
      (Database.hasReps_of_finite e.finite_toDatabase)
      (Database.hasReps_of_finite hout.finite_from_empty) ho.2)⟩

/-- The observer executes exactly the commands before testing the final query. -/
theorem observe_eq_exec (p : Program) : observe p = (exec p).map
    (fun d => if d.holds p.check then .ok d else .checkFailed) := rfl

/-- A command simulation with check agreement gives both observable finite outcomes. -/
theorem observe_eval_of_exec {p : Program} {r : ExecutionResult}
    (hcheck : ∀ e, exec p = some e → ∃ out, Reach Database.empty p.schedule out ∧
      (e.holds p.check = true ↔ QueryHolds out.forgetSubsumed p.check))
    (hs : observe p = some r) :
    ∃ result, Eval Database.empty p result ∧ result.succeeded = r.succeeded := by
  rw [observe_eq_exec] at hs
  obtain ⟨e, he, hr⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨out, hout, hq⟩ := hcheck e he
  split at hr
  · rename_i hc
    cases hr
    exact ⟨.ok, .ok hout (hq.mp hc), rfl⟩
  · rename_i hc
    cases hr
    exact ⟨.checkFailed, .checkFailed hout (fun h => hc (hq.mpr h)), rfl⟩

/-- The source interpreter's observable success or failure is a specification outcome. -/
theorem observe_eval {p : Program} {r : ExecutionResult}
    (hp : p.schedule.monotoneB = true) (ho : p.OrderingFree)
    (hs : observe p = some r) :
    ∃ result, Eval Database.empty p result ∧ result.succeeded = r.succeeded := by
  apply observe_eval_of_exec ?_ hs
  intro e he
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check hp ho he
  exact ⟨out, hout, hq⟩

end Egglog
