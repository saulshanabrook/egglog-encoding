import EgglogSemantics.Proofs.Congruence.Declared
import EgglogSemantics.Proofs.Congruence.Rebuilt
import EgglogSemantics.Proofs.Source.Ctors
import EgglogSemantics.Proofs.Rules

/-! The declarations and rebuilding rules that compiled executions actually retain. -/

namespace Egglog.Congruence

/-- Per-constructor declarations and all rules needed to rebuild that constructor's view. -/
structure RebuildTables (P : Program) (d : FDatabase) : Prop where
  view : ∀ f k, (f, k) ∈ P.ctors → d.sig (viewName f) = some (tableDecl k)
  output : ∀ f k, (f, k) ∈ P.ctors → eclassRule f k ∈ d.rules
  child : ∀ f k, (f, k) ∈ P.ctors → ∀ i < k, childRule f k i ∈ d.rules

/-- All generated rules are registered by the prelude. -/
theorem prelude_registered {P : Program} {d : FDatabase}
    (run : FDatabase.empty.execProgramM ((encodePrelude P).map Command.command) = some d)
    {c : Command} (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) :
    r ∈ d.rules := by
  apply (Egglog.FDatabase.execProgramM_mem_rules_iff run r).mpr
  exact Or.inr (List.mem_map.mpr ⟨c, maintenance_mem_prelude hc, hr⟩)

/-- The actual compiler prelude provides the full rebuilding interface. -/
theorem rebuildTables_of_prelude {P : Program} (hdom : P.Fragment) {d : FDatabase}
    (run : FDatabase.empty.execProgramM ((encodePrelude P).map Command.command) = some d) :
    RebuildTables P d := by
  have hsig : d.sig = encodeSig P := Egglog.FDatabase.execProgramM_sig run
  refine ⟨fun f k hk => hsig ▸ (encodeSig_tables hdom hk).2, ?_, ?_⟩
  · intro f k hk
    exact prelude_registered run (eclassRule_mem_maintenance hk) rfl
  · intro f k hk i hi
    exact prelude_registered run (childRule_mem_maintenance hk hi) rfl

/-- Later commands do not redeclare generated tables or remove their rebuilding rules. -/
theorem RebuildTables.execProgram {P p : Program} {d e : FDatabase} (h : RebuildTables P d)
    (hp : ∀ c ∈ p, NoDecl c) (run : d.execProgramM p = some e) : RebuildTables P e := by
  refine ⟨?_, ?_, ?_⟩
  · intro f k hk
    rw [execProgram_sig_of_noDecl hp run]
    exact h.view f k hk
  · exact fun f k hk => Egglog.FDatabase.execProgramM_rules_mono run _ (h.output f k hk)
  · exact fun f k hk i hi => Egglog.FDatabase.execProgramM_rules_mono run _ (h.child f k hk i hi)

/-- Every successful compiled execution retains the declarations and rebuilding rules. -/
theorem execM_encode_rebuildTables {P : Program} (hdom : P.Fragment) {d : FDatabase}
    (run : execM (encode P) = some d) : RebuildTables P d := by
  change FDatabase.empty.execProgramM _ = some d at run
  rw [encode, compile, List.map_append] at run
  obtain ⟨m, hm, hd⟩ := FDatabase.execProgramM_append run
  exact (rebuildTables_of_prelude hdom hm).execProgram (cmds_noDecl P 0) hd

/-- Soundness locates every historical view entry in the source constructor census. -/
theorem view_entry_ctors {P : Program} {d : FDatabase} {src : Database}
    (hs : SoundTerms d src) (hc : src.CtorsIn P) {f : FnName} {cs : List Term} {e : Term}
    (ht : Term.app (viewName f) (cs ++ [e]) ∈ d.terms) : (f, cs.length) ∈ P.ctors := by
  obtain ⟨as, ha, hcs, _⟩ := hs.1 f cs e ht
  rw [← hcs.length_eq]
  exact hc f as ha

/-- A live row with a value cannot be a constructor-index row. -/
theorem row_mergeOf_ne_none {d : FDatabase} (hi : d.IndexOk) {r : Row}
    (hr : r ∈ d.rows) (hne : r.out ≠ []) : d.sig.mergeOf r.fn ≠ none :=
  fun hm => hne (hi.ctor r hr hm).1

/-- Sound live views have the same source constructor and key width as their retained entry. -/
theorem view_row_ctors {P : Program} {d : FDatabase} {src : Database}
    (hi : d.Inv) (hn : d.NoUnions) (hs : SoundTerms d src) (hc : src.CtorsIn P)
    {f : FnName} {cs : List Term} {e : Term}
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows) : (f, cs.length) ∈ P.ctors :=
  view_entry_ctors hs hc (mem_terms_of_indexOk hn.eqsRefl hi.index hr
    (row_mergeOf_ne_none hi.index hr (by simp)))

end Egglog.Congruence
