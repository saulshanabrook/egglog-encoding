import EgglogSemantics.Proofs.Congruence.Execution
import EgglogSemantics.Proofs.Source.Arity
import EgglogSemantics.Proofs.Signature

/-! Exact declarations installed by the congruence prelude. -/

namespace Egglog.Congruence

/-- All commands following the prelude preserve its signature. -/
theorem execProgram_sig_of_noDecl {p : Program} (hp : ∀ c ∈ p, NoDecl c) :
    ∀ {d e : FDatabase}, d.execProgramM p = some e → e.sig = d.sig := by
  induction p with
  | nil => intro d e h; exact Option.some.inj h ▸ rfl
  | cons c cs ih =>
      intro d e h
      obtain ⟨m, hm, he⟩ := Option.bind_eq_some_iff.mp h
      rw [ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) he,
        FDatabase.execCmdM_sig hm]
      have hc := hp c List.mem_cons_self
      cases c <;> first | rfl | contradiction

theorem execM_encode_sig {P : Program} {d : FDatabase}
    (h : execM (encode P) = some d) : d.sig = encodeSig P := by
  change FDatabase.empty.execProgramM _ = some d at h
  rw [encode, compile, List.map_append] at h
  obtain ⟨m, hm, hd⟩ := FDatabase.execProgramM_append h
  rw [execProgram_sig_of_noDecl (cmds_noDecl P 0) hd]
  exact Egglog.FDatabase.execProgramM_sig hm

end Egglog.Congruence
