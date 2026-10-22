import EgglogSemantics.Proofs.Congruence.Relational
import EgglogSemantics.Proofs.Congruence.SourceSetup
import EgglogSemantics.Proofs.Congruence.Globals
import EgglogSemantics.Proofs.Congruence.Prelude

/-! Command simulation and completeness of congruence compilation. -/

namespace Egglog.Congruence

/-- Source and compiled command registration preserve exact rule correspondence. -/
theorem RulesEncoded.step {P : Program} {src post : Database} {d e : FDatabase}
    (h : RulesEncoded P src d) {c : Cmd} (hs : CmdStep src c post) {i : Nat}
    (run : d.execProgramM ((encodeCmd i c).map Command.command) = some e) :
    RulesEncoded P post e := by
  intro r
  rw [Egglog.FDatabase.execProgramM_mem_rules_iff run, rule_mem_encodeCmd, h r]
  simp only [hs.mem_rules_iff, or_and_right, exists_or, or_assoc]

/-- Prelude table metadata survives every subsequent compiled command. -/
theorem RebuildTables.step {P : Program} {d e : FDatabase} (h : RebuildTables P d)
    {c : Cmd} {i : Nat}
    (run : d.execProgramM ((encodeCmd i c).map Command.command) = some e) :
    RebuildTables P e := by
  have hsig : e.sig = d.sig := execProgram_sig_of_noDecl (by
    intro cmd hcmd
    apply cmds_noDecl [c] i cmd
    simpa only [encodeCmds, List.append_nil] using hcmd) run
  exact ⟨fun f k hk => hsig ▸ h.view f k hk,
    fun f k hk => Egglog.FDatabase.execProgramM_rules_mono run _ (h.output f k hk),
    fun f k hk j hj => Egglog.FDatabase.execProgramM_rules_mono run _ (h.child f k hk j hj)⟩

/-- The state carried between original commands. -/
structure Simulation (P : Program) (src : Database) (d : FDatabase) : Prop where
  rebuilt : Rebuilt d
  sound : SoundTerms d src
  reads : SourceReads d.toDatabase src
  tables : RebuildTables P d
  rules : RulesEncoded P src d
  sig : d.sig = encodeSig P
  env : d.env = []

theorem Simulation.state {P : Program} {src : Database} {d : FDatabase}
    (h : Simulation P src d) : RunState src d :=
  ⟨h.rebuilt.inv, h.rebuilt.noUnions, h.rebuilt.shape, h.rebuilt.uf, h.sound,
    h.rebuilt.history, h.rebuilt.descend⟩

theorem simulation_prelude {P : Program} (hdom : P.Fragment) {d : FDatabase}
    (run : FDatabase.empty.execProgramM ((encodePrelude P).map Command.command) = some d) :
    Simulation P Database.empty d := by
  obtain ⟨hs, hr, hreads, ht, hstore, hsig⟩ := prelude_state hdom run
  exact ⟨hr, hs.sound, hreads, ht, hstore, hsig, Egglog.FDatabase.execProgramM_env run⟩

/-- Data simulation and generic metadata preservation compose to a full command step. -/
theorem Simulation.step_of_data {P : Program} {src post : Database} {d e : FDatabase}
    (h : Simulation P src d) {c : Cmd} (hs : CmdStep src c post) {i : Nat}
    (run : d.execProgramM ((encodeCmd i c).map Command.command) = some e)
    (hr : Rebuilt e) (hsound : SoundTerms e post) (hreads : SourceReads e.toDatabase post) :
    Simulation P post e := by
  have hsig : e.sig = d.sig := execProgram_sig_of_noDecl (by
    intro cmd hcmd
    apply cmds_noDecl [c] i cmd
    simpa only [encodeCmds, List.append_nil] using hcmd) run
  exact ⟨hr, hsound, hreads, h.tables.step run, h.rules.step hs run, hsig.trans h.sig,
    (Egglog.FDatabase.execProgramM_env run).trans h.env⟩

/-- Source declarations require no target commands because the prelude declared all tables. -/
theorem Simulation.decl {P : Program} {src post : Database} {d e : FDatabase}
    (h : Simulation P src d) (hcs : src.sig.AllConstructors) {f : FnName} {dc : FnDecl}
    (hdecl : (Cmd.decl f dc).CtorDecl) (hs : CmdStep src (.decl f dc) post) {i : Nat}
    (run : d.execProgramM ((encodeCmd i (.decl f dc)).map Command.command) = some e) :
    Simulation P post e := by
  have hde : d = e := Option.some.inj run
  subst e
  have heq := source_setup_eqs hcs (c := .decl f dc) trivial hdecl hs
  exact h.step_of_data hs run h.rebuilt (h.sound.mono_src hs.contained.eqs)
    (h.reads.restrict (src' := post) ⟨by rw [heq]⟩)

/-- Registering an unrelated union-free rule preserves rebuilding closure. -/
theorem Rebuilt.addRule {d : FDatabase} (h : Rebuilt d) {r : Rule}
    (hu : Actions.UnionFree r.actions) (hR : r.ruleset ≠ rebuildRuleset) :
    Rebuilt { d with rules := r :: d.rules } := by
  refine ⟨h.inv.setEnvRules h.inv.wf.envInTerms,
    ⟨h.noUnions.eqs, h.noUnions.sig, ?_⟩, h.shape, h.uf, h.descend, h.history, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hu
    · exact h.noUnions.rules s hs
  · rw [Egglog.FDatabase.settled_setRules]; exact h.settled
  · apply h.closed.setRules
    intro s hs hsR
    rcases List.mem_cons.mp hs with rfl | hs
    · exact (hR hsR).elim
    · exact hs

/-- Source rule registration adds the compiled rule without changing represented data. -/
theorem Simulation.rule {P : Program} {src post : Database} {d e : FDatabase}
    (h : Simulation P src d) (hcs : src.sig.AllConstructors) {r : Rule}
    (hR : r.ruleset ≠ rebuildRuleset) (hs : CmdStep src (.rule r) post) {i : Nat}
    (run : d.execProgramM ((encodeCmd i (.rule r)).map Command.command) = some e) :
    Simulation P post e := by
  have hde : { d with rules := encodeRule r :: d.rules } = e := Option.some.inj run
  subst e
  have heq := source_setup_eqs hcs (c := .rule r) trivial trivial hs
  apply h.step_of_data hs run (h.rebuilt.addRule (encodeActions_unionFree r.actions) hR)
    (h.sound.mono_src hs.contained.eqs)
  exact (h.reads.restrict (src' := post) ⟨by rw [heq]⟩).mono
    (Egglog.FDatabase.toDatabase_contained_of_lists (fun _ ht => ht) (fun _ he => he))

/-- A source round followed by target rebuilding preserves the command invariant. -/
theorem Simulation.run {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ Cmd.run R :: rest) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) (hs : CmdStep src (.run R) post)
    {d e : FDatabase} (h : Simulation P src d) {i : Nat}
    (run : d.execProgramM ((encodeCmd i (.run R)).map Command.command) = some e) :
    Simulation P post e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hstep : RunStep R src post := by
    obtain ⟨m, hm, hcl⟩ := hs
    obtain rfl := hm
    exact hcl
  obtain ⟨m, hm, hrb⟩ := Option.bind_eq_some_iff.mp run
  have hm' : d.runRoundM R = some m := hm
  have hrb' : m.runSaturateM rebuildRuleset runFuel = some e := by
    simpa only [List.map_cons, List.map_nil, Egglog.FDatabase.execProgramM,
      Egglog.FDatabase.execCmdM, Option.bind_some, Option.bind_fun_some] using hrb
  obtain ⟨hmstate, hmreads⟩ := round_simulation hdom hP hpre hstep h.rebuilt
    h.tables h.sound h.sig h.rules h.reads hm'
  have hmaint : ∀ r ∈ m.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
    rw [(Egglog.FDatabase.runRoundM_fields hm').2.2]
    exact h.rules.rebuild_only hdom hpre hsub
  obtain ⟨hre, hse⟩ := hmstate.rebuilt hmaint hrb'
  exact h.step_of_data hs run hre hse
    (hmreads.mono (Egglog.FDatabase.runSaturateM_toDatabase_contained hrb'))

/-- Saturation is simulated against its final source state, then explicitly rebuilt. -/
theorem Simulation.saturate {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ Cmd.saturate R :: rest) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) (hs : CmdStep src (.saturate R) post)
    {d e : FDatabase} (h : Simulation P src d) {i : Nat}
    (run : d.execProgramM ((encodeCmd i (.saturate R)).map Command.command) = some e) :
    Simulation P post e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hPpost : P = (pre ++ [Cmd.saturate R]) ++ rest := by
    simpa only [List.append_assoc, List.singleton_append] using hP
  have hnext : ProgramStep Database.empty (pre ++ [Cmd.saturate R]) post :=
    hpre.append (.cons hs .nil)
  have hreach := cmdStep_saturate_iff.mp hs
  have hstore : RulesEncoded P post d := by
    simpa only [RulesEncoded, cmdStep_rules_of_saturate hs] using h.rules
  have hR : R ∈ P.saturateRulesets := by
    rw [hP]
    simp [Program.saturateRulesets]
  obtain ⟨m, hm, hrb⟩ := Option.bind_eq_some_iff.mp run
  have hm' : d.runSaturateM R runFuel = some m := hm
  have hrb' : m.runSaturateM rebuildRuleset runFuel = some e := by
    simpa only [List.map_cons, List.map_nil, Egglog.FDatabase.execProgramM,
      Egglog.FDatabase.execCmdM, Option.bind_some, Option.bind_fun_some] using hrb
  obtain ⟨hmstate, _, hmreads⟩ := saturation_simulation hdom hPpost hnext hreach hpre.env
    (h.state.mono_src hs.contained) h.tables h.sig hstore h.reads hR hm'
  have hmaint : ∀ r ∈ m.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
    rw [(Egglog.FDatabase.runSaturateM_fields runFuel hm').2.2]
    exact h.rules.rebuild_only hdom hpre hsub
  obtain ⟨hre, hse⟩ := hmstate.rebuilt hmaint hrb'
  exact h.step_of_data hs run hre hse
    (hmreads.mono (Egglog.FDatabase.runSaturateM_toDatabase_contained hrb'))

/-- Each original command preserves the simulation invariant. -/
theorem Simulation.step {P pre rest : Program} (hdom : P.Fragment) {c : Cmd}
    (hP : P = pre ++ c :: rest) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) (hs : CmdStep src c post)
    {d e : FDatabase} (h : Simulation P src d) {i : Nat}
    (run : d.execProgramM ((encodeCmd i c).map Command.command) = some e) :
    Simulation P post e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hmem : c ∈ P := hP ▸ List.mem_append_right _ List.mem_cons_self
  have hcs := (hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))).sig
  cases c with
  | decl f dc => exact h.decl hcs (hdom.ctorsOnly _ hmem) hs run
  | rule r => exact h.rule hcs (ruleset_ne_rebuild hdom hmem) hs run
  | action a =>
      obtain ⟨hr, hs', hreads⟩ := global_cmd_simulation hdom hsub hpre hmem hs
        h.state h.tables h.sig h.env h.rules h.reads run
      exact h.step_of_data hs run hr hs' hreads
  | run R => exact Simulation.run hdom hP hpre hs h run
  | saturate R => exact Simulation.saturate hdom hP hpre hs h run
  | check q =>
      obtain ⟨_, rfl⟩ := hs
      have he : d.execCmdM (.check (encodeQuery q 0).1) = some e := by
        simpa only [encodeCmd, List.map_cons, List.map_nil,
          Egglog.FDatabase.execProgramM, Option.bind_fun_some] using run
      rw [Egglog.FDatabase.execCheck_eq he]
      exact h

/-- Compose command simulations along the original program. -/
theorem Simulation.program {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) (hs : ProgramStep src rest post)
    {d e : FDatabase} (h : Simulation P src d) {i : Nat}
    (run : d.execProgramM ((encodeCmds rest i).map Command.command) = some e) :
    Simulation P post e := by
  induction rest generalizing pre src d i with
  | nil =>
      obtain rfl := hs.nil_inv
      obtain rfl := Option.some.inj run
      exact h
  | cons c cs ih =>
      obtain ⟨mid, hcmd, hrest⟩ := hs.cons_inv
      have run' : d.execProgramM ((encodeCmd i c).map Command.command ++
          (encodeCmds cs (i + 1)).map Command.command) = some e := by
        simpa only [encodeCmds, List.map_append] using run
      obtain ⟨m, hm, he⟩ := Egglog.FDatabase.execProgramM_append run'
      have hmid := Simulation.step hdom hP hpre hcmd h hm
      have hP' : P = (pre ++ [c]) ++ cs := by
        simpa only [List.append_assoc, List.singleton_append] using hP
      exact ih hP' (hpre.append (.cons hcmd .nil)) hrest hmid he

/-- Successful source and compiled executions satisfy the full simulation invariant. -/
theorem execM_encode_simulation {P : Program} (hdom : P.Fragment)
    {src : Database} (hsrc : ProgramStep Database.empty P src)
    {d : FDatabase} (run : execM (encode P) = some d) : Simulation P src d := by
  change FDatabase.empty.execProgramM _ = some d at run
  rw [encode, compile, List.map_append] at run
  obtain ⟨m, hm, he⟩ := Egglog.FDatabase.execProgramM_append run
  exact Simulation.program hdom (pre := []) (by simp) .nil hsrc
    (simulation_prelude hdom hm) he

/-- Source congruence agrees with the explicit table reading after congruence compilation. -/
theorem encode_corresponds {P : Program} (hdom : P.Fragment)
    {src : Database} (hsrc : ProgramStep Database.empty P src)
    {d : FDatabase} (run : execM (encode P) = some d)
    (a b : Term) (ha : a ∈ src.terms) (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass d.toDatabase a b := by
  have h := execM_encode_simulation hdom hsrc run
  have hbuild := termsBuild_of_programStep hdom.ctorsOnly hsrc
  have hctors := ctorsIn_of_prefixStep hdom (fun _ hm => hm) hsrc
  have hcoverage := sourceConstructors_of_programStep hdom (fun _ hm => hm) hsrc h.sig
  have hw := hsrc.wf Database.WF.empty
  have hlead := h.rebuilt.viewLeader h.tables h.sound hbuild hctors hcoverage hw
  exact h.rebuilt.corresponds h.tables h.sound hbuild hctors hcoverage hw h.reads.terms
    (unionsRead_of_unionsJoined hlead h.reads.unions) a b ha hb

/-- Completeness with structural matching and table operations only in the target. -/
theorem encode_corresponds_relational {P : Program} (hdom : P.Fragment)
    {src : Database} (hsrc : ProgramStep Database.empty P src)
    {d : FDatabase} (run : Relational.exec (encode P) (encode_unionFree P) = some d)
    (a b : Term) (ha : a ∈ src.terms) (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass d.toDatabase a b :=
  encode_corresponds hdom hsrc ((encode_relational P).symm.trans run) a b ha hb

end Egglog.Congruence
