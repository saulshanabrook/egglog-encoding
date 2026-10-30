import EgglogSemantics.Proofs.Congruence.AbstractMerge
import EgglogSemantics.Proofs.Bindings

/-! Mathematical maintenance firings preserve source justifications. -/

namespace Egglog.Congruence.Abstract

/-- A diagonal match of a complete entry names that retained row. -/
theorem mem_terms_of_validQuerySubst_entry {d : Database} (hd : d.Diag)
    {q : Query} {σ : Env} (hσ : ValidQuerySubst d q σ)
    {f : FnName} {as vs : List Expr} (hp : Pattern.expr (.app f (as ++ vs)) ∈ q) :
    ∃ ts us, Expr.evalList d.sig as σ = some ts ∧ Expr.evalList d.sig vs σ = some us ∧
      Term.app f (ts ++ us) ∈ d.terms := by
  have hm := hσ.matches_of_mem hp
  cases hm using Matches.storedCases with
  | expr hw he hc =>
      obtain ⟨cols, hcols, heq⟩ := Expr.evalAtom_app_inv he
      subst heq
      have hheld := (congOn_eq_of_diag hd hc) ▸ hw
      rw [Expr.evalList_append_map] at hcols
      obtain ⟨ts, hts, hrest⟩ := Option.bind_eq_some_iff.mp hcols
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      exact ⟨ts, us, hts, hus, hheld⟩

/-- A singleton complete-atom head adds exactly its evaluated row. -/
theorem evalLocalActions_entry {d d' : Database} {σ : Env} {g : FnName}
    {args out : List Expr}
    (h : evalLocalActions d [.expr (.app g (args ++ out))] σ = some d') :
    ∃ es vs, Expr.evalList d.sig args (σ) = some es ∧
      Expr.evalList d.sig out (σ) = some vs ∧
      d'.terms ⊆ (d.addTerm (.app g (es ++ vs))).terms := by
  obtain ⟨mid, hmid, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [evalActions, evalAction] at hmid
  obtain ⟨post, hpost, heq⟩ := Option.bind_eq_some_iff.mp hmid
  obtain rfl := Option.some.inj heq
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hpost
  obtain ⟨cols, hcols, rfl⟩ := Expr.evalAtom_app_inv ht
  rw [Expr.evalList_append_map] at hcols
  obtain ⟨es, hes, hrest⟩ := Option.bind_eq_some_iff.mp hcols
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hrest
  refine ⟨es, vs, hes, hvs, ?_⟩
  exact (Database.terms_eq_of_eqs_eq rfl).subset

/-- Path compression only composes existing source equalities. -/
theorem pathCompressRule_soundTerms {src : Database} {d d' : Database} {σ : Env}
    (hr : d.Diag) (hsc : d.WF) (h : SoundTerms d src)
    (hσ : ValidQuerySubst d pathCompressRule.query σ)
    (hf : evalLocalActions d pathCompressRule.actions σ = some d') : SoundTerms d' src := by
  obtain ⟨ts₁, us₁, ha₁, hv₁, hm₁⟩ := mem_terms_of_validQuerySubst_entry hr hσ
    (vs := [Expr.var "@b"]) (f := ufName) (as := [Expr.var "@a"])
    (by simp [pathCompressRule])
  obtain ⟨a, hla, rfl⟩ := Expr.evalList_singleton ha₁
  obtain ⟨b, hlb, rfl⟩ := Expr.evalList_singleton hv₁
  obtain ⟨ts₂, us₂, ha₂, hv₂, hm₂⟩ := mem_terms_of_validQuerySubst_entry hr hσ
    (vs := [Expr.var "@c"]) (f := ufName) (as := [Expr.var "@b"])
    (by simp [pathCompressRule])
  obtain ⟨b', hlb', rfl⟩ := Expr.evalList_singleton ha₂
  obtain ⟨c, hlc, rfl⟩ := Expr.evalList_singleton hv₂
  obtain rfl : b = b' := Option.some.inj (hlb.symm.trans hlb')
  have hab := h.2 a b hm₁
  have hbc := h.2 b c hm₂
  have ham : a ∈ d.terms := Database.mem_terms_of_arg hsc hm₁ (by simp)
  have hcm : c ∈ d.terms := Database.mem_terms_of_arg hsc hm₂ (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := evalLocalActions_entry (g := ufName)
    (args := [.var "@a"]) (out := [.var "@c"]) hf
  obtain ⟨a', hla', rfl⟩ := Expr.evalList_singleton hesh
  obtain rfl : a = a' := Option.some.inj (hla.symm.trans hla')
  obtain ⟨c', hlc', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : c = c' := Option.some.inj (hlc.symm.trans hlc')
  exact (h.addUF hsc ham hcm (hab.trans hbc)).mono_terms hterms

/-- Propagating an output through UF preserves the original constructor witness. -/
theorem eclassRule_soundTerms {src : Database} {d d' : Database} {σ : Env} {f : FnName}
    {cs : List Expr}
    (hr : d.Diag) (hsc : d.WF) (h : SoundTerms d src)
    (hσ : ValidQuerySubst d
      [.expr (.app (viewName f) (cs ++ [.var "@e"])),
       .expr (.app ufName [.var "@e", .var "@x"])] σ)
    (hf : evalLocalActions d [.expr (.app (viewName f) (cs ++ [.var "@x"]))] σ = some d') :
    SoundTerms d' src := by
  obtain ⟨ts, us, hats, hvus, hmv⟩ := mem_terms_of_validQuerySubst_entry hr hσ
    (vs := [Expr.var "@e"]) (f := viewName f) (as := cs) (by simp)
  obtain ⟨e, hle, rfl⟩ := Expr.evalList_singleton hvus
  obtain ⟨ts₂, us₂, hats₂, hvus₂, hmu⟩ := mem_terms_of_validQuerySubst_entry hr hσ
    (vs := [Expr.var "@x"]) (f := ufName) (as := [Expr.var "@e"]) (by simp)
  obtain ⟨e', hle', rfl⟩ := Expr.evalList_singleton hats₂
  obtain ⟨x, hlx, rfl⟩ := Expr.evalList_singleton hvus₂
  obtain rfl : e = e' := Option.some.inj (hle.symm.trans hle')
  obtain ⟨as, ha, hal, hae⟩ := h.1 f ts e hmv
  have hex := h.2 e x hmu
  have hcol : ∀ z ∈ ts, z ∈ d.terms :=
    fun z hz => Database.mem_terms_of_arg hsc hmv (List.mem_append_left _ hz)
  have hxm : x ∈ d.terms := Database.mem_terms_of_arg hsc hmu (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := evalLocalActions_entry (g := viewName f)
    (args := cs) (out := [.var "@x"]) hf
  obtain rfl : esh = ts := Option.some.inj (hesh.symm.trans hats)
  obtain ⟨x', hlx', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : x = x' := Option.some.inj (hlx.symm.trans hlx')
  exact (h.addView hsc hcol hxm ⟨as, ha, hal, hae.trans hex⟩).mono_terms hterms

/-- Re-keying a child changes the represented key, while retaining the source witness
and its already justified output id. -/
theorem childRule_soundTerms {src : Database} {d d' : Database} {σ : Env} {f : FnName}
    {cs : List Expr} {v : Var} {i : Nat} (hi : cs[i]? = some (.var v))
    (hr : d.Diag) (hsc : d.WF) (h : SoundTerms d src)
    (hσ : ValidQuerySubst d
      [.expr (.app (viewName f) (cs ++ [.var "@e"])),
       .expr (.app ufName [.var v, .var "@x"])] σ)
    (hf : evalLocalActions d
      [.expr (.app (viewName f) (cs.set i (.var "@x") ++ [.var "@e"]))] σ = some d') :
    SoundTerms d' src := by
  obtain ⟨ts, us, hats, hvus, hmv⟩ := mem_terms_of_validQuerySubst_entry hr hσ
    (vs := [Expr.var "@e"]) (f := viewName f) (as := cs) (by simp)
  obtain ⟨e, hle, rfl⟩ := Expr.evalList_singleton hvus
  obtain ⟨c, hci, hlc⟩ := Expr.getElem?_of_evalList hats i hi
  obtain ⟨ts₂, us₂, hats₂, hvus₂, hmu⟩ := mem_terms_of_validQuerySubst_entry hr hσ
    (vs := [Expr.var "@x"]) (f := ufName) (as := [Expr.var v]) (by simp)
  obtain ⟨c', hlc', rfl⟩ := Expr.evalList_singleton hats₂
  obtain ⟨x, hlx, rfl⟩ := Expr.evalList_singleton hvus₂
  obtain rfl : c = c' := Option.some.inj (hlc.symm.trans hlc')
  obtain ⟨as, ha, hal, hae⟩ := h.1 f ts e hmv
  have hcx := h.2 c x hmu
  have hcol : ∀ z ∈ ts, z ∈ d.terms :=
    fun z hz => Database.mem_terms_of_arg hsc hmv (List.mem_append_left _ hz)
  have hem : e ∈ d.terms := Database.mem_terms_of_arg hsc hmv (by simp)
  have hxm : x ∈ d.terms := Database.mem_terms_of_arg hsc hmu (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := evalLocalActions_entry (g := viewName f)
    (args := cs.set i (.var "@x")) (out := [.var "@e"]) hf
  have hset := Expr.evalList_set hats i hlx
  obtain rfl : esh = ts.set i x := Option.some.inj (hesh.symm.trans hset)
  obtain ⟨e', hle', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : e = e' := Option.some.inj (hle.symm.trans hle')
  have hcol' : ∀ z ∈ ts.set i x, z ∈ d.terms := by
    intro z hz
    rcases mem_or_eq_of_mem_set hz with hz | rfl
    · exact hcol z hz
    · exact hxm
  exact (h.addView hsc hcol' hem ⟨as, ha, hal.setAt i hci hcx, hae⟩).mono_terms hterms

/-- Soundness depends on the query and actions, not the ruleset used to schedule them. -/
def RuleSound (src : Database) (r : Rule) : Prop :=
  ∀ {d d' : Database} {σ : Env}, d.Diag → d.WF →
    SoundTerms d src → ValidQuerySubst d r.query σ →
    evalLocalActions d r.actions σ = some d' → SoundTerms d' src

private def CommandSound (src : Database) (c : Command) : Prop :=
  ∀ r, c.command = .rule r → RuleSound src r

private theorem rebuildRules_sound (src : Database) (f : FnName) (arity : Nat) :
    ∀ c ∈ rebuildRules f arity, CommandSound src c := by
  intro c hc r hrule
  simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
  rcases hc with rfl | ⟨i, hi, rfl⟩
  · obtain rfl : eclassRule f arity = r := Cmd.rule.inj hrule
    exact eclassRule_soundTerms
  · obtain rfl : childRule f arity i = r := Cmd.rule.inj hrule
    have hget : (rebuildVars arity)[i]? = some (.var ("@c" ++ toString i)) := by
      simp [rebuildVars, List.mem_range.mp hi]
    intro d d' σ hr hsc hs hσ hf
    exact childRule_soundTerms hget hr hsc hs hσ hf

private theorem maintenanceRules_sound (src : Database) (P : Program) :
    ∀ c ∈ maintenanceRules P, CommandSound src c := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, arity⟩, _, hc⟩
  · intro r hrule
    obtain rfl : pathCompressRule = r := Cmd.rule.inj hrule
    exact pathCompressRule_soundTerms
  · exact rebuildRules_sound src f arity c hc

private theorem inRuleset_sound {src : Database} {c : Command}
    (h : CommandSound src c) (R : RulesetName) : CommandSound src (inRuleset R c) := by
  intro r hr
  unfold inRuleset at hr
  split at hr
  next s hs =>
    obtain rfl : { s with ruleset := R } = r := Cmd.rule.inj hr
    exact h s hs
  next => exact h r hr

/-- All generated maintenance rules, including copies in source saturation rulesets,
preserve the justification invariant. -/
theorem maintenance_soundTerms {src : Database} {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) :
    RuleSound src r := by
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenanceRules_sound src P c hc r hr
  · exact inRuleset_sound (maintenanceRules_sound src P c hc) R r hr


end Egglog.Congruence.Abstract
