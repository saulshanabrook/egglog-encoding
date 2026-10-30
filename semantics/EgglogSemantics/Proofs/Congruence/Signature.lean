import EgglogSemantics.Proofs.Congruence.Read
import EgglogSemantics.Proofs.Congruence.MetadataSyntax

/-! Declaration invariants for the generated single-output tables. -/

namespace Egglog.Congruence

theorem execCmd_mergeShape {d e : FDatabase} {c : Cmd} (hc : CommandShape c)
    (h : MergeShape d.sig) (hs : d.execCmdM c = some e) : MergeShape e.sig := by
  rw [FDatabase.execCmdM_sig hs]
  cases c with
  | decl f dc => exact h.update hc
  | _ => exact h

theorem execProgram_mergeShape {p : Program} (hp : ∀ c ∈ p, CommandShape c) :
    ∀ {d e : FDatabase}, MergeShape d.sig → d.execProgramM p = some e → MergeShape e.sig := by
  induction p with
  | nil =>
      intro d e h he
      obtain rfl := Option.some.inj he
      exact h
  | cons c cs ih =>
      intro d e h he
      obtain ⟨m, hm, hrest⟩ := Option.bind_eq_some_iff.mp he
      exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))
        (execCmd_mergeShape (hp c List.mem_cons_self) h hm) hrest

theorem execM_encode_mergeShape {P : Program} {tgt : FDatabase}
    (h : execM (encode P) = some tgt) : MergeShape tgt.sig :=
  execProgram_mergeShape (encode_commandShape P) MergeShape.empty h

/-- Complete atoms make body writes legal independently of the signature; the declared
output count also agrees with the merge result. -/
theorem MergeShape.mergesLegal {sig : Signature} (h : MergeShape sig) :
    Signature.MergesLegal sig := by
  intro f dc oldVars newVars body res hdc hm
  obtain ⟨-, rfl, rfl, ho, -, -⟩ := h f dc hdc body res hm
  exact ⟨⟨trivial, trivial, trivial⟩, ho.symm⟩

end Egglog.Congruence
