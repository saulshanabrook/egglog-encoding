import EgglogSemantics.Proofs.Congruence.Rounds

namespace Egglog.Congruence

/-- The actual prelude starts the command simulation with empty source facts, settled
rows, all rebuilding rules, and the fixed compiled signature. -/
theorem prelude_state {P : Program} (hdom : P.Fragment) {d : FDatabase}
    (run : FDatabase.empty.execProgramM ((encodePrelude P).map Command.command) = some d) :
    RunState Database.empty d ∧ Rebuilt d ∧ SourceReads d.toDatabase Database.empty ∧
      RebuildTables P d ∧ RulesEncoded P Database.empty d ∧ d.sig = encodeSig P := by
  obtain ⟨ht, hr, he, hv⟩ := execProgramM_data_of_declOrRule (prelude_setup P) run
  change d.terms = [] at ht
  change d.rows = [] at hr
  change d.eqs = [] at he
  change d.env = [] at hv
  have hshape : MergeShape d.sig := execProgram_mergeShape
    (fun c hc => encode_commandShape P c (by
      simp only [encode, compile, List.map_append, List.mem_append]
      exact Or.inl hc)) MergeShape.empty run
  have hstore : RulesEncoded P Database.empty d :=
    rulesEncoded_of_prefix (pre := []) .nil run (i := 0) rfl
  have hmaint : ∀ r ∈ d.rules, ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
    intro r hr
    rcases (hstore r).mp hr with h | ⟨s, hs, _⟩
    · exact h
    · exact (Set.notMem_empty s hs).elim
  have hn : d.NoUnions := by
    refine ⟨he, hshape.unionFree, ?_⟩
    intro r hr
    obtain ⟨c, hc, hcr⟩ := hmaint r hr
    obtain ⟨f, cols, ha, _⟩ := maintenance_headShape hc hcr
    rw [ha]
    exact ⟨trivial, trivial⟩
  have hstate : RunState Database.empty d :=
    { inv := Egglog.FDatabase.Inv.of_empty_data ht hr he hv
      noUnions := hn
      shape := hshape
      uf := (Egglog.FDatabase.execProgramM_sig run) ▸ encodeSig_ufName hdom
      sound := ⟨fun f cs e hm => False.elim (by simp [ht] at hm),
        fun a b hm => False.elim (by simp [ht] at hm)⟩
      history := by intro f dc hd oldVars newVars body res hm cs x hlen hmem; simp [ht] at hmem
      descend := by intro a b hab; simp [UFStep, ht] at hab }
  have hsettled : d.settled = true := by
    simp [Egglog.FDatabase.settled, Egglog.FDatabase.mergeRound,
      Egglog.FDatabase.hasMergeRow, hr, Egglog.FDatabase.sameData]
  have hclosed : d.RoundClosed rebuildRuleset :=
    Egglog.FDatabase.roundClosed_of_empty ht hr fun r hr _ =>
      let ⟨c, hc, hcr⟩ := hmaint r hr
      maintenance_query_ne_nil hc hcr
  exact ⟨hstate, ⟨hstate.inv, hn, hshape, hstate.uf, hstate.descend, hstate.history,
    hsettled, hclosed⟩,
    ⟨by simp, by intro a b hab; exact (Set.notMem_empty (a, b) hab).elim⟩,
    rebuildTables_of_prelude hdom run, hstore, Egglog.FDatabase.execProgramM_sig run⟩

end Egglog.Congruence
