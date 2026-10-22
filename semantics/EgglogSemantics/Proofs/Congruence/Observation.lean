import EgglogSemantics.Congruence.Correctness
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Proofs.Step

/-! Observational correctness reduces to query agreement at aligned check boundaries.
Neither successful execution of a suffix after failure nor termination preservation is used. -/

namespace Egglog.Congruence

theorem encodeCmd_no_checks (i : Nat) {c : Cmd} (hc : ∀ q, c ≠ .check q) :
    ∀ q, Cmd.check q ∉ (encodeCmd i c).map Command.command := by
  intro q
  cases c with
  | check p => exact (hc p rfl).elim
  | decl _ _ | rule _ | run _ | saturate _ => simp [encodeCmd, taggedRule]

theorem prelude_no_checks (P : Program) :
    ∀ q, Cmd.check q ∉ (encodePrelude P).map Command.command := by
  have hbase : ∀ c ∈ maintenanceRules P, ∃ r, c.command = .rule r := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, rfl⟩
    obtain ⟨⟨f, k⟩, _, hc⟩ := List.mem_flatMap.mp hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, rfl⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact ⟨_, rfl⟩
  have hall : ∀ c ∈ allMaintenanceRules P, ∃ r, c.command = .rule r := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hbase c hc
    obtain ⟨R, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcbase, rfl⟩ := List.mem_map.mp hc
    obtain ⟨r, hr⟩ := hbase c hcbase
    exact ⟨{ r with ruleset := R }, by simp [inRuleset, hr]⟩
  intro q hq
  obtain ⟨c, hc, heq⟩ := List.mem_map.mp hq
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · cases heq
    obtain ⟨⟨f, k⟩, _, hc⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> cases heq
  · obtain ⟨r, hr⟩ := hall c hc
    rw [hr] at heq
    cases heq

theorem encodeCmds_append (pre rest : Program) (i : Nat) :
    encodeCmds (pre ++ rest) i = encodeCmds pre i ++ encodeCmds rest (i + pre.length) := by
  induction pre generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih => simp [encodeCmds, ih, List.append_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- The execution obligation left to the congruence simulation. It quantifies over
arbitrary mathematical executions of both aligned prefixes. -/
def CheckAgreement (P : Program) : Prop :=
  ∀ pre q post src tgt, P = pre ++ .check q :: post →
    ProgramStep Database.empty pre src →
    ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) tgt →
    (QueryHolds src q ↔ QueryHolds tgt (encodeQuery q 0).1)

private theorem observation_from_prefix {P : Program} (ha : CheckAgreement P) :
    ∀ rest pre src tgt source target,
      P = pre ++ rest → ProgramStep Database.empty pre src →
      ProgramStep Database.empty
        ((encodePrelude P ++ encodeCmds pre 0).map Command.command) tgt →
      Eval src rest source →
      Eval tgt ((encodeCmds rest pre.length).map Command.command) target →
      source.succeeded = target.succeeded := by
  intro rest
  induction rest with
  | nil =>
      intro pre src tgt source target _ _ _ hs ht
      cases hs
      cases ht
      rfl
  | cons c cs ih =>
      intro pre src tgt source target hP hpre htpre hs ht
      have hnext : ∀ s t, CmdStep src c s →
          ProgramStep tgt ((encodeCmd pre.length c).map Command.command) t →
          Eval s cs source → Eval t ((encodeCmds cs (pre.length + 1)).map Command.command) target →
          source.succeeded = target.succeeded := by
        intro s t hsc htc hs ht
        apply ih (pre ++ [c]) s t source target
          (by simpa only [List.append_assoc, List.singleton_append] using hP)
          (hpre.append (.cons hsc .nil))
        · convert htpre.append htc using 1
          simp [encodeCmds_append, encodeCmds, List.map_append, List.append_assoc]
        · exact hs
        · simpa using ht
      by_cases hcheck : ∃ q, c = .check q
      · obtain ⟨q, rfl⟩ := hcheck
        have hq := ha pre q cs src tgt hP hpre htpre
        have ht' : Eval tgt (.check (encodeQuery q 0).1 ::
            (encodeCmds cs (pre.length + 1)).map Command.command) target := by
          simpa only [encodeCmds, encodeCmd, List.map_append, List.map_cons, List.map_nil,
            List.singleton_append] using ht
        rcases Eval.check_cons_iff.mp hs with ⟨hqs, hs⟩ | ⟨hqs, rfl⟩
        · rcases Eval.check_cons_iff.mp ht' with ⟨hqt, ht⟩ | ⟨hqt, rfl⟩
          · exact hnext src tgt ⟨hqs, rfl⟩ (.cons ⟨hqt, rfl⟩ .nil) hs ht
          · exact (hqt (hq.mp hqs)).elim
        · rcases Eval.check_cons_iff.mp ht' with ⟨hqt, _⟩ | ⟨_, rfl⟩
          · exact (hqs (hq.mpr hqt)).elim
          · rfl
      · have hnc : ∀ q, c ≠ .check q := fun q heq => hcheck ⟨q, heq⟩
        have ht' : Eval tgt ((encodeCmd pre.length c).map Command.command ++
            (encodeCmds cs (pre.length + 1)).map Command.command) target := by
          simpa only [encodeCmds, List.map_append] using ht
        obtain ⟨mid, hcmd, hrest⟩ := ht'.append_of_no_checks (encodeCmd_no_checks _ hnc)
        cases hs with
        | cons hc hs => exact hnext _ mid (CmdEval.ok_iff.mp hc) hcmd hs hrest
        | fail hc =>
            cases hc with
            | checkFailed _ => exact (hnc _ rfl).elim

/-- Agreement at check boundaries proves agreement of complete finite observations.
This reduction deliberately has no termination-preservation premise. -/
theorem observations_of_checkAgreement {P : Program} (ha : CheckAgreement P)
    {source target : Result} (hs : Eval Database.empty P source)
    (ht : Eval Database.empty (encode P) target) : source.succeeded = target.succeeded := by
  have ht' : Eval Database.empty ((encodePrelude P).map Command.command ++
      (encodeCmds P 0).map Command.command) target := by
    simpa only [encode, compile, List.map_append] using ht
  obtain ⟨mid, hp, ht⟩ := ht'.append_of_no_checks (prelude_no_checks P)
  exact observation_from_prefix ha P [] Database.empty mid source target (by simp) .nil
    (by simpa [encodeCmds] using hp) hs ht

end Egglog.Congruence
