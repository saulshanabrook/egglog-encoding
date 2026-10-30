import EgglogSemantics.Proofs.Congruence.Signature

/-! Basic execution invariants. Declarations occur before any data is written, and
all later merge results have the declared width. -/

namespace Egglog.Congruence

theorem actions_writeLegal (as : List Action) (sig : Signature) :
    Actions.WriteLegal as sig := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨trivial, ih⟩

private theorem cmd_writeLegal (c : Cmd) (sig : Signature) : c.WriteLegal sig := by
  cases c with
  | action a => trivial
  | rule r => exact actions_writeLegal r.actions sig
  | _ => trivial

theorem execCmd_inv {d e : FDatabase} {c : Cmd} (hc : NoDecl c)
    (hi : d.Inv) (hs : MergeShape d.sig) (h : d.execCmdM c = some e) : e.Inv :=
  hi.execCmdM (cmd_writeLegal c d.sig) hs.mergesLegal
    (by cases c <;> trivial) (fun r _ => actions_writeLegal r.actions d.sig) h

theorem execProgram_inv {p : Program} (hp : ∀ c ∈ p, NoDecl c) :
    ∀ {d e : FDatabase}, d.Inv → MergeShape d.sig → d.execProgramM p = some e → e.Inv := by
  induction p with
  | nil =>
      intro d e hi _ h
      obtain rfl := Option.some.inj h
      exact hi
  | cons c cs ih =>
      intro d e hi hs h
      obtain ⟨m, hm, hrest⟩ := Option.bind_eq_some_iff.mp h
      have hc := hp c List.mem_cons_self
      exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))
        (execCmd_inv hc hi hs hm)
        (execCmd_mergeShape (by cases c <;> trivial) hs hm) hrest

/-- Every successful compiled execution has a well-formed denotation and a sound,
correctly sized live row index. No source-fragment assumptions are needed here. -/
theorem execM_encode_inv {P : Program} {tgt : FDatabase}
    (h : execM (encode P) = some tgt) : tgt.Inv := by
  change FDatabase.empty.execProgramM _ = some tgt at h
  rw [encode, compile, List.map_append] at h
  obtain ⟨d, hpre, hrest⟩ := FDatabase.execProgramM_append h
  obtain ⟨ht, hr, he, hv⟩ := execProgramM_data_of_declOrRule (prelude_setup P) hpre
  have hs : MergeShape d.sig := execProgram_mergeShape
    (fun c hc => encode_commandShape P c (by
      simp only [encode, compile, List.map_append, List.mem_append]
      exact Or.inl hc)) MergeShape.empty hpre
  exact execProgram_inv (cmds_noDecl P 0) (FDatabase.Inv.of_empty_data ht hr he hv) hs hrest

end Egglog.Congruence
