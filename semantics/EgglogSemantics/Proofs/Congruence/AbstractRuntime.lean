import EgglogSemantics.Proofs.Congruence.QuerySafety
import EgglogSemantics.Proofs.Congruence.LiveState
import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.RuleStore
import EgglogSemantics.Proofs.DiagonalPreservation

namespace Egglog.Congruence.Live

theorem generatedTables_of_mergeShape {sig : Signature} (h : MergeShape sig) :
    GeneratedTables sig := by
  intro f dc hd hm
  cases he : dc.merge with
  | none => exact (hm he).elim
  | some ms =>
    cases ms with
    | merge oldVars newVars body res =>
      obtain ⟨_, hb, hr, ho, _, hov, hnv⟩ := h f dc hd body res he
      refine ⟨dc.arity, ?_⟩
      cases dc
      simp_all [tableDecl]

theorem GeneratedTables.mergesWidthOk {sig : Signature} (h : GeneratedTables sig)
    (hu : sig ufName = some (tableDecl 1)) : sig.MergesWidthOk := by
  intro f dc ms hd hm
  obtain ⟨k, rfl⟩ := h f dc hd (by simp [hm])
  obtain rfl : ms = .merge ["old"] ["new"] mergeBody mergeResult := by
    simpa [tableDecl, eq_comm] using hm
  simp [MergeSpec.WidthOk,
    mergeResult, mergeBody, Action.WidthOk,
    Expr.AtomWidthOk, Expr.WidthOk, Expr.WidthOkList, hu, tableDecl, FnDecl.entryWidth]

structure Runtime (d : Database) : Prop where
  wf : d.WF
  storeOk : d.StoreOk
  noUnions : d.NoUnions
  state : State d
  generated : GeneratedTables d.sig
  rulesSafe : d.RulesSafe

theorem Runtime.action {d e : Database} (h : Runtime d) {a : Action}
    (hu : a.UnionFree) (he : evalAction d a = some e) : Runtime e where
  wf := evalAction_wf h.wf he
  storeOk := evalAction_storeOk h.storeOk he
  noUnions := ⟨evalAction_diag hu h.noUnions.diag he,
    by rw [evalAction_sig he]; exact h.noUnions.sig,
    by rw [evalAction_rules he]; exact h.noUnions.rules⟩
  state := h.state.evalAction h.generated h.storeOk he
  generated := by rw [evalAction_sig he]; exact h.generated
  rulesSafe := by simpa only [Database.RulesSafe, evalAction_rules he] using h.rulesSafe

theorem Runtime.mergesWidthOk {d : Database} (h : Runtime d) : d.sig.MergesWidthOk :=
  h.generated.mergesWidthOk h.state.uf

theorem Runtime.merge {d e : Database} (h : Runtime d) (hm : MergeClosure d e) :
    Runtime e where
  wf := hm.wf h.wf h.storeOk h.mergesWidthOk
  storeOk := hm.storeOk h.storeOk h.mergesWidthOk
  noUnions := ⟨hm.diag h.noUnions.sig h.noUnions.diag,
    by rw [hm.sig]; exact h.noUnions.sig,
    by rw [hm.envRules.2]; exact h.noUnions.rules⟩
  state := (state_closure h.state (outputsIn_self _) hm).1
  generated := by rw [hm.sig]; exact h.generated
  rulesSafe := by simpa only [Database.RulesSafe, hm.envRules.2] using h.rulesSafe

theorem Runtime.runRules {d : Database} (h : Runtime d) (R : RulesetName) :
    Runtime (RunRules R d) where
  wf := RunRules.wf h.wf
  storeOk := RunRules.storeOk h.storeOk h.rulesSafe
  noUnions := ⟨RunRules.diag h.noUnions, h.noUnions.sig, h.noUnions.rules⟩
  state := h.state.runRules h.generated h.storeOk h.rulesSafe R
  generated := h.generated
  rulesSafe := h.rulesSafe

theorem Runtime.runStep {d e : Database} (h : Runtime d) {R : RulesetName}
    (hr : RunStep R d e) : Runtime e := (h.runRules R).merge hr.1

theorem Runtime.runReach {d e : Database} (h : Runtime d) {R : RulesetName}
    (hr : Relation.ReflTransGen (RunStep R) d e) : Runtime e :=
  RunReach.induction (fun _ _ h hs => h.runStep hs) hr h

private theorem noDecl_sigBind {c : Cmd} (h : NoDecl c) (sig : Signature) :
    c.sigBind sig = sig := by
  cases c <;> first | rfl | contradiction

private theorem noDecl_fresh {c : Cmd} (h : NoDecl c) (sig : Signature) :
    c.DeclFresh sig := by
  cases c <;> trivial

theorem Runtime.cmd {d e : Database} (h : Runtime d) {c : Cmd}
    (hn : NoDecl c) (hu : c.UnionFree) (hq : c.QueriesSafe) (hc : CmdStep d c e) : Runtime e := by
  have hsig : e.sig = d.sig := hc.sig.trans (noDecl_sigBind hn d.sig)
  have hmw : (c.sigBind d.sig).MergesWidthOk := by
    rw [noDecl_sigBind hn d.sig]; exact h.mergesWidthOk
  refine ⟨hc.wf h.wf h.storeOk h.rulesSafe (noDecl_fresh hn _) hmw,
    hc.storeOk h.storeOk h.rulesSafe (noDecl_fresh hn _) hmw, hc.noUnions h.noUnions hu,
    State.of_generated (hc.finiteStore h.state.finite) ?_ ?_
      (fun _ hr => (hc.storeOk h.storeOk h.rulesSafe (noDecl_fresh hn _) hmw).entry_valid hr),
    ?_, hc.rulesSafe h.rulesSafe hq⟩
  all_goals rw [hsig]
  · exact h.state.uf
  · exact h.generated
  · exact h.generated

theorem Runtime.program {d e : Database} (h : Runtime d) {p : Program}
    (hn : ∀ c ∈ p, NoDecl c) (hu : p.UnionFree) (hq : p.QueriesSafe)
    (hp : ProgramStep d p e) :
    Runtime e := by
  induction hp with
  | nil => exact h
  | cons hc _ ih =>
    exact ih (h.cmd (hn _ List.mem_cons_self) hu.1 hq.1 hc)
      (fun c hm => hn c (List.mem_cons_of_mem _ hm)) hu.2 hq.2

private theorem foldl_noDecl {p : Program} (hp : ∀ c ∈ p, NoDecl c) (s : Signature) :
    p.foldl (fun sig c => c.sigBind sig) s = s := by
  induction p generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih (fun c hm => hp c (List.mem_cons_of_mem _ hm)),
      noDecl_sigBind (hp c List.mem_cons_self) s]

theorem prefix_sig {P pre : Program} {d : Database} {i : Nat}
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) :
    d.sig = encodeSig P := by
  rw [ht.sig, List.map_append, List.foldl_append, foldl_noDecl (cmds_noDecl pre i)]
  rfl

theorem prelude_empty {P : Program} {d : Database}
    (h : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) :
    d.eqs = ∅ ∧ d.terms = ∅ ∧ d.env = [] := by
  have he := h.eqs_empty_of_declOrRule (prelude_setup P) rfl
  exact ⟨he, Database.terms_empty_of_eqs_empty he, h.env⟩

theorem prelude_runtime {P : Program} {d : Database} (hp : P.Fragment)
    (h : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) :
    Runtime d := by
  have hsig : d.sig = encodeSig P := h.sig
  have hg : GeneratedTables d.sig :=
    hsig ▸ generatedTables_of_mergeShape (encodeSig_mergeShape P)
  have hu : d.sig ufName = some (tableDecl 1) := hsig ▸ encodeSig_ufName hp
  obtain ⟨he, _, hen⟩ := prelude_empty h
  have hs : d.StoreOk := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro row hr; exact (he ▸ hr.2).elim
    · intro row hr; exact (he ▸ hr.2).elim
    · intro p hp; exact (he ▸ hp).elim
    · simp [hen]
  have hn : d.NoUnions := by
    apply h.noUnions Database.NoUnions.empty
    simpa [encodeCmds] using encodePrefix_unionFree P [] 0
  refine ⟨Database.WF.empty.congr he.symm hen.symm, hs, hn,
    State.of_generated h.finiteStore_from_empty hu hg (fun _ hr => hs.entry_valid hr), hg, ?_⟩
  intro r hr
  have hmem : Cmd.rule r ∈ (encodePrelude P).map Command.command := by
    simpa [Database.empty] using (h.mem_rules_iff r).mp hr
  exact prelude_querySafe P r hmem

private theorem append_inv {p q : Program} {d e : Database}
    (hr : ProgramStep d (p ++ q) e) : ∃ mid, ProgramStep d p mid ∧ ProgramStep mid q e := by
  induction p generalizing d with
  | nil => exact ⟨d, .nil, hr⟩
  | cons c cs ih =>
    obtain ⟨mid, hc, hrest⟩ := hr.cons_inv
    obtain ⟨post, hp, hq⟩ := ih hrest
    exact ⟨post, .cons hc hp, hq⟩

private theorem unionFree_append_right {p q : Program} (h : (p ++ q).UnionFree) :
    q.UnionFree := by
  induction p with
  | nil => exact h
  | cons _ _ ih => exact ih h.2

private theorem orderingFree_of_mem : ∀ p : Program,
    (∀ c ∈ p, c.OrderingFree) → p.OrderingFree
  | [], _ => trivial
  | c :: cs, h => ⟨h c List.mem_cons_self,
      orderingFree_of_mem cs (fun c hc => h c (List.mem_cons_of_mem _ hc))⟩

theorem prefix_runtime {P pre : Program} {d : Database} {i : Nat} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) : Runtime d := by
  rw [List.map_append] at ht
  obtain ⟨mid, hm, hrest⟩ := append_inv ht
  have ho : pre.OrderingFree := orderingFree_of_mem pre
    (fun c hc => Program.OrderingFree.of_mem hp.noMin (hsub c hc))
  apply (prelude_runtime hp hm).program (cmds_noDecl pre i) ?_ ?_ hrest
  · apply unionFree_append_right (p := (encodePrelude P).map Command.command)
    simpa only [List.map_append] using encodePrefix_unionFree P pre i
  · exact Program.queriesSafe_of_rules _ (encodeCmds_querySafe ho i)

def RulesEncoded (P : Program) (src d : Database) : Prop :=
  ∀ r, r ∈ d.rules ↔ (∃ c ∈ allMaintenanceRules P, c.command = .rule r) ∨
    ∃ s ∈ src.rules, r = encodeRule s

theorem rulesEncoded_of_prefix {P pre : Program} {src d : Database} {i : Nat}
    (hs : ProgramStep Database.empty pre src)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) :
    RulesEncoded P src d := by
  intro r
  rw [ht.mem_rules_iff]
  simp only [Database.empty, Set.mem_empty_iff_false, false_or, List.map_append,
    List.mem_append, rule_mem_prelude, rule_mem_encodeCmds]
  have hm : ∀ s, s ∈ src.rules ↔ Cmd.rule s ∈ pre := by
    intro s
    simpa [Database.empty] using hs.mem_rules_iff s
  simp only [hm]

theorem RulesEncoded.maintenance {P : Program} {src d : Database}
    (h : RulesEncoded P src d) {c : Command} (hc : c ∈ allMaintenanceRules P)
    {r : Rule} (hr : c.command = .rule r) : r ∈ d.rules :=
  (h r).mpr (Or.inl ⟨c, hc, hr⟩)

end Egglog.Congruence.Live
