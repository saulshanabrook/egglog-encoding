import EgglogSemantics.Proofs.Congruence.AbstractMetadata
import EgglogSemantics.Proofs.Congruence.AbstractMerge
import EgglogSemantics.Proofs.Congruence.AbstractRunState

/-! Generated actions and retained rows have their declared widths in mathematical runs. -/

namespace Egglog.Congruence.Abstract

private theorem widthOkList_append {as bs : List Expr} {sig : Signature}
    (ha : Expr.WidthOkList as sig) (hb : Expr.WidthOkList bs sig) :
    Expr.WidthOkList (as ++ bs) sig := by
  induction as with
  | nil => exact hb
  | cons a as ih => exact ⟨ha.1, ih ha.2⟩

private theorem actions_width_append {as bs : List Action} {sig : Signature}
    (ha : Actions.WidthOk as sig) (hb : Actions.WidthOk bs sig) :
    Actions.WidthOk (as ++ bs) sig := by
  induction as with
  | nil => exact hb
  | cons a as ih => exact ⟨ha.1, ih ha.2⟩

mutual

/-- The whole-program constructor census fixes the width of every structural id. -/
theorem sourceExpr_width {P : Program} (hp : P.Fragment) : ∀ e : Expr,
    (∀ fk ∈ e.ctors, fk ∈ P.ctors) → e.WidthOk (encodeSig P)
  | .lit _, _ => trivial
  | .var _, _ => trivial
  | .min a b, hc => ⟨sourceExpr_width hp a (fun fk hk => hc fk (List.mem_append_left _ hk)),
      sourceExpr_width hp b (fun fk hk => hc fk (List.mem_append_right _ hk))⟩
  | .ite lhs rhs yes no, hc =>
      ⟨sourceExprs_width hp lhs (fun fk hk => hc fk (by simp [Expr.ctors, hk])),
       sourceExprs_width hp rhs (fun fk hk => hc fk (by simp [Expr.ctors, hk])),
       sourceExpr_width hp yes (fun fk hk => hc fk (by simp [Expr.ctors, hk])),
       sourceExpr_width hp no (fun fk hk => hc fk (by simp [Expr.ctors, hk]))⟩
  | .app f es, hc => by
      refine ⟨?_, sourceExprs_width hp es (fun fk hk => hc fk (List.mem_cons_of_mem _ hk))⟩
      intro dc hd
      rw [(encodeSig_tables hp (hc (f, es.length) List.mem_cons_self)).1] at hd
      cases hd
      rfl

theorem sourceExprs_width {P : Program} (hp : P.Fragment) : ∀ es : List Expr,
    (∀ fk ∈ Expr.ctorsList es, fk ∈ P.ctors) → Expr.WidthOkList es (encodeSig P)
  | [], _ => trivial
  | e :: es, hc =>
      ⟨sourceExpr_width hp e (fun fk hk => hc fk (List.mem_append_left _ hk)),
       sourceExprs_width hp es (fun fk hk => hc fk (List.mem_append_right _ hk))⟩

end

mutual

/-- Each compiled construction writes exactly the keys and one id of its view table. -/
theorem encodeBuild_width {P : Program} (hp : P.Fragment) : ∀ e : Expr,
    (∀ fk ∈ e.ctors, fk ∈ P.ctors) → Actions.WidthOk (encodeBuild e) (encodeSig P)
  | .lit _, _ => trivial
  | .var _, _ => trivial
  | .min a b, hc => actions_width_append
      (encodeBuild_width hp a (fun fk hk => hc fk (List.mem_append_left _ hk)))
      (encodeBuild_width hp b (fun fk hk => hc fk (List.mem_append_right _ hk)))
  | .ite _ _ _ _, _ => trivial
  | .app f es, hc => by
      apply actions_width_append
        (encodeBuildArgs_width hp es (fun fk hk => hc fk (List.mem_cons_of_mem _ hk)))
      refine ⟨⟨?_, widthOkList_append
        (sourceExprs_width hp es (fun fk hk => hc fk (List.mem_cons_of_mem _ hk)))
        ⟨sourceExpr_width hp (.app f es) hc, trivial⟩⟩, trivial⟩
      intro dc hd
      rw [(encodeSig_tables hp (hc (f, es.length) List.mem_cons_self)).2] at hd
      cases hd
      simp [FnDecl.entryWidth, tableDecl]

theorem encodeBuildArgs_width {P : Program} (hp : P.Fragment) : ∀ es : List Expr,
    (∀ fk ∈ Expr.ctorsList es, fk ∈ P.ctors) →
      Actions.WidthOk (encodeBuildArgs es) (encodeSig P)
  | [], _ => trivial
  | e :: es, hc => actions_width_append
      (encodeBuild_width hp e (fun fk hk => hc fk (List.mem_append_left _ hk)))
      (encodeBuildArgs_width hp es (fun fk hk => hc fk (List.mem_append_right _ hk)))

end

private theorem uf_atom_width {P : Program} (hp : P.Fragment) {a b : Expr}
    (ha : a.WidthOk (encodeSig P)) (hb : b.WidthOk (encodeSig P)) :
    (Action.expr (.app ufName [a, b])).WidthOk (encodeSig P) := by
  refine ⟨?_, ha, hb, trivial⟩
  intro dc hd
  rw [encodeSig_ufName hp] at hd
  cases hd
  rfl

/-- Source unions compile to two width-correct UF entries. -/
theorem encodeAction_width {P : Program} (hp : P.Fragment) (a : Action)
    (hc : ∀ fk ∈ a.ctors, fk ∈ P.ctors) :
    Actions.WidthOk (encodeAction a) (encodeSig P) := by
  cases a with
  | expr e => exact encodeBuild_width hp e hc
  | union a b =>
      have ha := sourceExpr_width hp a (fun fk hk => hc fk (List.mem_append_left _ hk))
      have hb := sourceExpr_width hp b (fun fk hk => hc fk (List.mem_append_right _ hk))
      apply actions_width_append
        (actions_width_append
          (encodeBuild_width hp a (fun fk hk => hc fk (List.mem_append_left _ hk)))
          (encodeBuild_width hp b (fun fk hk => hc fk (List.mem_append_right _ hk))))
      exact ⟨uf_atom_width hp ha ⟨ha, hb⟩, uf_atom_width hp hb ⟨ha, hb⟩, trivial⟩

theorem encodeActions_width {P : Program} (hp : P.Fragment) (as : List Action)
    (hc : ∀ a ∈ as, ∀ fk ∈ a.ctors, fk ∈ P.ctors) :
    Actions.WidthOk (encodeActions as) (encodeSig P) := by
  induction as with
  | nil => trivial
  | cons a as ih =>
      exact actions_width_append (encodeAction_width hp a (hc a List.mem_cons_self))
        (ih fun a ha => hc a (List.mem_cons_of_mem _ ha))

theorem encodeRule_width {P : Program} (hp : P.Fragment) {r : Rule}
    (hr : Cmd.rule r ∈ P) : (encodeRule r).WidthOk (encodeSig P) := by
  apply encodeActions_width hp r.actions
  intro a ha fk hk
  apply mem_program_ctors hr
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)

private theorem widthOk_vars (vs : List Var) (sig : Signature) :
    Expr.WidthOkList (vs.map Expr.var) sig := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih⟩

private theorem widthOk_set {es : List Expr} {sig : Signature} (h : Expr.WidthOkList es sig)
    (i : Nat) {e : Expr} (he : e.WidthOk sig) : Expr.WidthOkList (es.set i e) sig := by
  induction es generalizing i with
  | nil => trivial
  | cons a es ih =>
      cases i with
      | zero => exact ⟨he, h.2⟩
      | succ i => exact ⟨h.1, ih h.2 i⟩

private theorem rebuildVars_width (k : Nat) (sig : Signature) :
    Expr.WidthOkList (rebuildVars k) sig := by
  rw [rebuildVars_eq_map]
  exact widthOk_vars _ _

private theorem view_atom_width {P : Program} (hp : P.Fragment) {f : FnName} {k : Nat}
    (hk : (f, k) ∈ P.ctors) {es : List Expr}
    (hw : Expr.WidthOkList es (encodeSig P)) (hlen : es.length = k + 1) :
    (Action.expr (.app (viewName f) es)).WidthOk (encodeSig P) := by
  refine ⟨?_, hw⟩
  intro dc hd
  rw [(encodeSig_tables hp hk).2] at hd
  cases hd
  exact hlen

private theorem maintenance_width {P : Program} (hp : P.Fragment) :
    ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r → r.WidthOk (encodeSig P) := by
  intro c hc r hr
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain rfl := Cmd.rule.inj hr
    exact ⟨uf_atom_width hp trivial trivial, trivial⟩
  · obtain ⟨⟨f, k⟩, hk, hc⟩ := List.mem_flatMap.mp hc
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain rfl := Cmd.rule.inj hr
      exact ⟨view_atom_width hp hk
        (widthOkList_append (rebuildVars_width k _) ⟨trivial, trivial⟩)
        (by simp [rebuildVars]), trivial⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      obtain rfl := Cmd.rule.inj hr
      exact ⟨view_atom_width hp hk
        (widthOkList_append (widthOk_set (rebuildVars_width k _) i trivial) ⟨trivial, trivial⟩)
        (by simp [rebuildVars]), trivial⟩

/-- Copying a maintenance rule changes only its selected ruleset, not any column width. -/
theorem allMaintenance_width {P : Program} (hp : P.Fragment) {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) :
    r.WidthOk (encodeSig P) := by
  rcases List.mem_append.mp hc with hc | hc
  · exact maintenance_width hp c hc r hr
  · obtain ⟨R, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcbase, rfl⟩ := List.mem_map.mp hc
    unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact maintenance_width hp c hcbase s hs
    next => exact maintenance_width hp c hcbase r hr


/-- Widths constrain commands that write or register future writes. -/
def WritesWidth : Cmd → Signature → Prop
  | .action a, sig => a.WidthOk sig
  | .rule r, sig => r.WidthOk sig
  | _, _ => True

private theorem actions_width_mem {as : List Action} {sig : Signature}
    (h : Actions.WidthOk as sig) {a : Action} (ha : a ∈ as) : a.WidthOk sig := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.1
      · exact ih h.2 ha

theorem encodeCmd_writesWidth {P : Program} (hp : P.Fragment) {c : Cmd} (hc : c ∈ P)
    (i : Nat) : ∀ d ∈ encodeCmd i c, WritesWidth d.command (encodeSig P) := by
  intro d hd
  cases c with
  | action a =>
      simp only [encodeCmd, List.mem_append, List.mem_map, List.mem_singleton] at hd
      rcases hd with ⟨a', ha', rfl⟩ | rfl
      · exact actions_width_mem (encodeAction_width hp a (fun fk hk => mem_program_ctors hc hk))
          ha'
      · trivial
  | rule r =>
      obtain rfl := List.mem_singleton.mp hd
      exact encodeRule_width hp hc
  | decl _ _ => simp [encodeCmd] at hd
  | check _ =>
      obtain rfl := List.mem_singleton.mp hd
      trivial
  | run _ | saturate _ =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> trivial

theorem encodeCmds_writesWidth {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) (i : Nat) :
    ∀ c ∈ (encodeCmds pre i).map Command.command, WritesWidth c (encodeSig P) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  clear hc
  induction pre generalizing i with
  | nil => simp [encodeCmds] at hd
  | cons c cs ih =>
      rcases List.mem_append.mp hd with hd | hd
      · exact encodeCmd_writesWidth hp (hsub c List.mem_cons_self) i d hd
      · exact ih (fun c hc => hsub c (List.mem_cons_of_mem _ hc)) (i + 1) hd

private theorem sigBind_noDecl {c : Cmd} (h : NoDecl c) (sig : Signature) :
    c.sigBind sig = sig := by
  cases c <;> first | rfl | contradiction

/-- Fixed declarations and width-correct writes preserve declared historical rows and
well-sized stored rules. A successful check is the identity. -/
theorem programStep_widths {d e : Database} {p : Program} (h : ProgramStep d p e)
    (hn : ∀ c ∈ p, NoDecl c) (hwrites : ∀ c ∈ p, WritesWidth c d.sig)
    (hw : d.WF) (hdt : d.DeclaredTerms) (hr : d.RulesOk)
    (hml : d.sig.MergesLegal) (hmw : d.sig.MergesWidthOk) :
    e.DeclaredTerms ∧ e.RulesOk := by
  induction h with
  | nil => exact ⟨hdt, hr⟩
  | @cons d m e c cs hc hrest ih =>
      have hnc := hn c List.mem_cons_self
      have hcsig := sigBind_noDecl hnc d.sig
      have hmsig : m.sig = d.sig := hc.sig.trans hcsig
      have hwrite := hwrites c List.mem_cons_self
      have hmdt : m.DeclaredTerms := by
        cases c with
        | decl _ _ => contradiction
        | check q =>
            rw [(show QueryHolds d q ∧ m = d from hc).2]
            exact hdt
        | action a =>
            exact cmdStep_declaredTerms (c := .action a) hw hdt hr hwrite trivial hml hmw hc
        | rule r =>
            exact cmdStep_declaredTerms (c := .rule r) hw hdt hr hwrite trivial hml hmw hc
        | run R =>
            exact cmdStep_declaredTerms (c := .run R) hw hdt hr hwrite trivial hml hmw hc
        | saturate R =>
            exact cmdStep_declaredTerms (c := .saturate R) hw hdt hr hwrite trivial hml hmw hc
      have hmr : m.RulesOk := by
        intro r hmem
        rw [hmsig]
        rcases (hc.mem_rules_iff r).mp hmem with hmem | rfl
        · exact hr r hmem
        · exact hwrite
      exact ih (fun c hm => hn c (List.mem_cons_of_mem _ hm))
        (fun c hm => hmsig ▸ hwrites c (List.mem_cons_of_mem _ hm))
        (hc.wf hw) hmdt hmr (hmsig ▸ hml) (hmsig ▸ hmw)

private theorem programStep_append_inv {p q : Program} {d e : Database}
    (h : ProgramStep d (p ++ q) e) : ∃ m, ProgramStep d p m ∧ ProgramStep m q e := by
  induction p generalizing d with
  | nil => exact ⟨d, .nil, h⟩
  | cons c cs ih =>
      obtain ⟨m, hc, hrest⟩ := h.cons_inv
      obtain ⟨n, hp, hq⟩ := ih hrest
      exact ⟨n, .cons hc hp, hq⟩

/-- Every finite compiled-prefix execution has correctly sized historical entries and
rule heads. No interpreter invariant is assumed. -/
theorem prefix_widths {P pre : Program} (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {i : Nat} {d : Database}
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) :
    d.DeclaredTerms ∧ d.RulesOk := by
  rw [List.map_append] at ht
  obtain ⟨m, hm, hrest⟩ := programStep_append_inv ht
  have hsig : m.sig = encodeSig P := hm.sig
  have hmempty := (prelude_empty hm).2.1
  have hmdt : m.DeclaredTerms := by
    intro f as ha
    simp [hmempty] at ha
  have hmr : m.RulesOk := by
    intro r hr
    have hmem : Cmd.rule r ∈ (encodePrelude P).map Command.command := by
      simpa [Database.empty] using (hm.mem_rules_iff r).mp hr
    obtain ⟨c, hc, hcr⟩ := (rule_mem_prelude P r).mp hmem
    rw [hsig]
    exact allMaintenance_width hp hc hcr
  apply programStep_widths hrest (cmds_noDecl pre i)
    (fun c hc => hsig ▸ encodeCmds_writesWidth hp hsub i c hc)
    (hm.wf Database.WF.empty) hmdt hmr
  · rw [hsig]
    exact mergeShape_mergesLegal (encodeSig_mergeShape P)
  · rw [hsig]
    exact mergeShape_mergesWidthOk (encodeSig_mergeShape P) (encodeSig_ufName hp)


/-- Every structural runtime invariant follows from an actual compiled-prefix execution. -/
theorem prefix_runtime {P pre : Program} (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {i : Nat} {d : Database}
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) : Runtime d := by
  obtain ⟨hdt, hr⟩ := prefix_widths hp hsub ht
  have hsig := prefix_sig ht
  exact ⟨ht.wf Database.WF.empty, prefix_noUnions ht, hdt, hr,
    hsig ▸ encodeSig_mergeShape P, hsig ▸ encodeSig_ufName hp⟩

/-- In particular, the data-free prelude starts a valid target runtime. -/
theorem prelude_runtime {P : Program} (hp : P.Fragment) {d : Database}
    (ht : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) : Runtime d := by
  apply prefix_runtime (pre := []) (i := 0) hp (by simp)
  simpa [encodeCmds] using ht

end Egglog.Congruence.Abstract
