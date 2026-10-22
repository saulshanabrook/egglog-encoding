import EgglogSemantics.Proofs.Congruence.State
import EgglogSemantics.Proofs.Entries

/-! Generated rebuilding rules preserve source justifications of view and UF entries. -/

namespace Egglog.Congruence

/-- Path compression only composes existing source equalities. -/
theorem pathCompressRule_soundTerms {src : Database} {d d' : FDatabase} {σ : Env}
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : SoundTerms d src)
    (hσ : σ ∈ matchQuery d pathCompressRule.query)
    (hf : execLocalActions d pathCompressRule.actions σ = some d') : SoundTerms d' src := by
  obtain ⟨ts₁, us₁, ha₁, hv₁, hm₁⟩ := mem_terms_of_mem_matchQuery_entry hr hidx hσ
    (vs := [Expr.var "@b"]) (f := ufName) (as := [Expr.var "@a"])
    (by simp [pathCompressRule])
  obtain ⟨a, hla, rfl⟩ := Expr.evalList_singleton ha₁
  obtain ⟨b, hlb, rfl⟩ := Expr.evalList_singleton hv₁
  obtain ⟨ts₂, us₂, ha₂, hv₂, hm₂⟩ := mem_terms_of_mem_matchQuery_entry hr hidx hσ
    (vs := [Expr.var "@c"]) (f := ufName) (as := [Expr.var "@b"])
    (by simp [pathCompressRule])
  obtain ⟨b', hlb', rfl⟩ := Expr.evalList_singleton ha₂
  obtain ⟨c, hlc, rfl⟩ := Expr.evalList_singleton hv₂
  obtain rfl : b = b' := Option.some.inj (hlb.symm.trans hlb')
  have hab := h.2 a b hm₁
  have hbc := h.2 b c hm₂
  have ham : a ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₁ (by simp)
  have hcm : c ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₂ (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := execLocalActions_entry (g := ufName)
    (args := [.var "@a"]) (out := [.var "@c"]) hf
  obtain ⟨a', hla', rfl⟩ := Expr.evalList_singleton hesh
  obtain rfl : a = a' := Option.some.inj ((Expr.eval_append_env _ hla).symm.trans hla')
  obtain ⟨c', hlc', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : c = c' := Option.some.inj ((Expr.eval_append_env _ hlc).symm.trans hlc')
  exact (h.addUF hsc ham hcm (hab.trans hbc)).mono_terms hterms

/-- Propagating an output through UF preserves the original constructor witness. -/
theorem eclassRule_soundTerms {src : Database} {d d' : FDatabase} {σ : Env} {f : FnName}
    {cs : List Expr}
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : SoundTerms d src)
    (hσ : σ ∈ matchQuery d
      [.expr (.app (viewName f) (cs ++ [.var "@e"])),
       .expr (.app ufName [.var "@e", .var "@x"])])
    (hf : execLocalActions d [.expr (.app (viewName f) (cs ++ [.var "@x"]))] σ = some d') :
    SoundTerms d' src := by
  obtain ⟨ts, us, hats, hvus, hmv⟩ := mem_terms_of_mem_matchQuery_entry hr hidx hσ
    (vs := [Expr.var "@e"]) (f := viewName f) (as := cs) (by simp)
  obtain ⟨e, hle, rfl⟩ := Expr.evalList_singleton hvus
  obtain ⟨ts₂, us₂, hats₂, hvus₂, hmu⟩ := mem_terms_of_mem_matchQuery_entry hr hidx hσ
    (vs := [Expr.var "@x"]) (f := ufName) (as := [Expr.var "@e"]) (by simp)
  obtain ⟨e', hle', rfl⟩ := Expr.evalList_singleton hats₂
  obtain ⟨x, hlx, rfl⟩ := Expr.evalList_singleton hvus₂
  obtain rfl : e = e' := Option.some.inj (hle.symm.trans hle')
  obtain ⟨as, ha, hal, hae⟩ := h.1 f ts e hmv
  have hex := h.2 e x hmu
  have hcol : ∀ z ∈ ts, z ∈ d.terms :=
    fun z hz => FDatabase.mem_terms_of_column hsc hmv (List.mem_append_left _ hz)
  have hxm : x ∈ d.terms := FDatabase.mem_terms_of_column hsc hmu (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := execLocalActions_entry (g := viewName f)
    (args := cs) (out := [.var "@x"]) hf
  obtain rfl : esh = ts := Option.some.inj (hesh.symm.trans (Expr.evalList_append_env _ hats))
  obtain ⟨x', hlx', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : x = x' := Option.some.inj ((Expr.eval_append_env _ hlx).symm.trans hlx')
  exact (h.addView hsc hcol hxm ⟨as, ha, hal, hae.trans hex⟩).mono_terms hterms

/-- Re-keying a child changes the represented key, while retaining the source witness
and its already justified output id. -/
theorem childRule_soundTerms {src : Database} {d d' : FDatabase} {σ : Env} {f : FnName}
    {cs : List Expr} {v : Var} {i : Nat} (hi : cs[i]? = some (.var v))
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : SoundTerms d src)
    (hσ : σ ∈ matchQuery d
      [.expr (.app (viewName f) (cs ++ [.var "@e"])),
       .expr (.app ufName [.var v, .var "@x"])])
    (hf : execLocalActions d
      [.expr (.app (viewName f) (cs.set i (.var "@x") ++ [.var "@e"]))] σ = some d') :
    SoundTerms d' src := by
  obtain ⟨ts, us, hats, hvus, hmv⟩ := mem_terms_of_mem_matchQuery_entry hr hidx hσ
    (vs := [Expr.var "@e"]) (f := viewName f) (as := cs) (by simp)
  obtain ⟨e, hle, rfl⟩ := Expr.evalList_singleton hvus
  obtain ⟨c, hci, hlc⟩ := Expr.getElem?_of_evalList hats i hi
  obtain ⟨ts₂, us₂, hats₂, hvus₂, hmu⟩ := mem_terms_of_mem_matchQuery_entry hr hidx hσ
    (vs := [Expr.var "@x"]) (f := ufName) (as := [Expr.var v]) (by simp)
  obtain ⟨c', hlc', rfl⟩ := Expr.evalList_singleton hats₂
  obtain ⟨x, hlx, rfl⟩ := Expr.evalList_singleton hvus₂
  obtain rfl : c = c' := Option.some.inj (hlc.symm.trans hlc')
  obtain ⟨as, ha, hal, hae⟩ := h.1 f ts e hmv
  have hcx := h.2 c x hmu
  have hcol : ∀ z ∈ ts, z ∈ d.terms :=
    fun z hz => FDatabase.mem_terms_of_column hsc hmv (List.mem_append_left _ hz)
  have hem : e ∈ d.terms := FDatabase.mem_terms_of_column hsc hmv (by simp)
  have hxm : x ∈ d.terms := FDatabase.mem_terms_of_column hsc hmu (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := execLocalActions_entry (g := viewName f)
    (args := cs.set i (.var "@x")) (out := [.var "@e"]) hf
  have hset := Expr.evalList_set (Expr.evalList_append_env (τ := d.env) _ hats) i
    (Expr.eval_append_env (τ := d.env) _ hlx)
  obtain rfl : esh = ts.set i x := Option.some.inj (hesh.symm.trans hset)
  obtain ⟨e', hle', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : e = e' := Option.some.inj ((Expr.eval_append_env _ hle).symm.trans hle')
  have hcol' : ∀ z ∈ ts.set i x, z ∈ d.terms := by
    intro z hz
    rcases mem_or_eq_of_mem_set hz with hz | rfl
    · exact hcol z hz
    · exact hxm
  exact (h.addView hsc hcol' hem ⟨as, ha, hal.setAt i hci hcx, hae⟩).mono_terms hterms

/-- Soundness depends on the query and actions, not the ruleset used to schedule them. -/
def RuleSound (src : Database) (r : Rule) : Prop :=
  ∀ {d d' : FDatabase} {σ : Env}, d.EqsRefl → d.IndexOk → d.SubtermClosed →
    SoundTerms d src → σ ∈ matchQuery d r.query →
    execLocalActions d r.actions σ = some d' → SoundTerms d' src

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
    intro d d' σ hr hidx hsc hs hσ hf
    exact childRule_soundTerms hget hr hidx hsc hs hσ hf

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

end Egglog.Congruence
