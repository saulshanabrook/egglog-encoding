import EgglogSemantics.Proofs.EnvTransform
import EgglogSemantics.Proofs.Congruence.Match
import EgglogSemantics.Proofs.Congruence.AbstractTransport
import EgglogSemantics.Proofs.Congruence.AbstractMaintenance

/-! A common target substitution reads every pattern of a source match. -/

namespace Egglog.Congruence.Abstract

/-- Each source binding is assigned one canonical target reading, shared by all uses. -/
def CanonicalReads (d : Database) (σ ρ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t → ∃ i, Env.lookup v ρ = some i ∧
    ViewRepr d t i ∧ Root d i

section Reading

variable {d : Database} {src : Database}
variable (h : Rebuilt d) (hs : EdgesSound d src) (hw : src.WF)
include h hs hw

/-- A single function on source values keeps repeated query variables consistent. -/
theorem exists_canonical_env {querySrc : Database} {σ : Env} (hv : ∀ b ∈ σ, b.2 ∈ querySrc.terms)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d t e) :
    ∃ ρ, CanonicalReads d σ ρ ∧ Env.dom ρ = Env.dom σ := by
  classical
  let w : Term → Term := fun t => if ht : t ∈ querySrc.terms then h.root (hex t ht).choose else t
  have hread : ∀ t ∈ querySrc.terms, ViewRepr d t (w t) ∧ Root d (w t) := by
    intro t ht
    simp only [w, dif_pos ht]
    exact ⟨h.normalize_view hs hw t (hex t ht).choose_spec,
      (h.root_spec _).2⟩
  refine ⟨Env.mapVals w σ, ?_, dom_mapVals w σ⟩
  intro v t ht
  have hm := hv (v, t) (Env.mem_of_lookup ht)
  exact ⟨w t, by rw [lookup_mapVals, ht]; rfl, hread t hm⟩

end Reading

mutual

/-- Evaluating the original syntax and representing the result gives a reading of
that syntax at the consistent target substitution. -/
theorem queryRead_of_eval_view {d : Database} {src : Database}
    (h : Rebuilt d) (hs : EdgesSound d src) (hw : src.WF) {sig : Signature} {σ ρ : Env}
    (hρ : CanonicalReads d σ ρ) :
    ∀ (e : Expr) {t i : Term}, e.OrderingFree →
      e.eval sig σ = some t → ViewRepr d t i →
      QueryRead d ρ e (h.root i)
  | .lit l, _, _, _, he, hv => by
      obtain rfl := Option.some.inj he
      cases hv
      rw [h.root_lit hs hw l]
      exact .lit
  | .var v, t, i, _, he, hv => by
      obtain ⟨j, hj, hvj, hrj⟩ := hρ v t he
      have heq : j = h.root i := by
        have hh := h.unique_view t hvj hv
        simpa only [h.root_eq hrj] using hh
      exact heq ▸ QueryRead.var hj
  | .min _ _, _, _, hp, _, _ => (Expr.not_orderingFree_min hp).elim
  | .ite _ _ _ _, _, _, hp, _, _ => (Expr.not_orderingFree_ite hp).elim
  | .app f args, t, i, hp, he, hv => by
      simp only [Expr.eval] at he
      split at he
      next hctor =>
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        cases hv with
        | @app _ _ es _ hl ho =>
            exact .app (queryReadList_of_eval_view h hs hw hρ args
              (Expr.orderingFree_app hp) hts hl) (h.out_normalized ho)
      next => cases he

@[inherit_doc queryRead_of_eval_view]
theorem queryReadList_of_eval_view {d : Database} {src : Database}
    (h : Rebuilt d) (hs : EdgesSound d src) (hw : src.WF) {sig : Signature} {σ ρ : Env}
    (hρ : CanonicalReads d σ ρ) :
    ∀ (es : List Expr) {ts is : List Term}, Expr.OrderingFreeList es →
      Expr.evalList sig es σ = some ts → ViewReprList d ts is →
      QueryReadList d ρ es (is.map h.root)
  | [], _, _, _, he, hv => by
      obtain rfl := Option.some.inj he
      cases hv
      exact .nil
  | e :: es, _, _, hp, he, hv => by
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      cases hv with
      | cons hv hvs =>
          exact .cons (queryRead_of_eval_view h hs hw hρ e
            (Expr.orderingFreeList_cons hp).1 ht hv)
            (queryReadList_of_eval_view h hs hw hρ es
              (Expr.orderingFreeList_cons hp).2 hts hvs)

end

/-- Original source matches produce query readings at the consistent substitution. -/
theorem patternRead_of_matches {d : Database} {src querySrc : Database}
    (h : Rebuilt d) (hs : EdgesSound d src) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hun : UnionsRead d querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d t e) {σ ρ : Env}
    (hρ : CanonicalReads d σ ρ) {p : Pattern}
    (hp : p.OrderingFree) (hm : Matches querySrc p σ) :
    PatternRead d ρ p := by
  cases p with
  | expr e =>
      obtain ⟨t, i, he, hv⟩ := view_of_matches_expr h hs hw hun hex hm
      rw [Expr.evalAtom_eq_eval hcs] at he
      exact .expr (queryRead_of_eval_view h hs hw hρ e hp he hv)
  | eq a b =>
      obtain ⟨ta, tb, i, ha, hb', hia, hib⟩ :=
        views_of_matches_eq h hs hw hun hex hm
      exact .eq (queryRead_of_eval_view h hs hw hρ a hp.1 ha hia)
        (queryRead_of_eval_view h hs hw hρ b hp.2 hb' hib)


mutual

/-- A variable appearing as a constructor argument receives a matchable value from a row. -/
theorem QueryRead.value_argVar {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    {ρ : Env} {v : Var} :
    ∀ {e : Expr} {i : Term}, QueryRead d ρ e i → Expr.ArgVar v e →
      ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.values
  | _, _, .lit, hv => absurd hv (by simp [Expr.ArgVar])
  | _, _, .var _, hv => absurd hv (by simp [Expr.ArgVar])
  | _, _, .app hl ho, hv => by
      have hcols := out_values hd hstore ho
      rcases hv with hv | hv
      · exact QueryReadList.value_memVar hl
          (fun j hj => hcols j (List.mem_append_left _ hj)) hv
      · exact QueryReadList.value_argVar hd hstore hl hv

/-- A direct variable column reads the value in that column. -/
theorem QueryReadList.value_memVar {d : Database} {ρ : Env} {v : Var} :
    ∀ {es : List Expr} {is : List Term}, QueryReadList d ρ es is →
      (∀ i ∈ is, i ∈ d.values) → Expr.var v ∈ es →
      ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.values
  | _, _, .nil, _, hv => absurd hv (by simp)
  | _, _, .cons he hl, hc, hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · cases he with
        | var hv => exact ⟨_, hv, hc _ List.mem_cons_self⟩
      · exact QueryReadList.value_memVar hl
          (fun j hj => hc j (List.mem_cons_of_mem _ hj)) hv

/-- Descend to the constructor occurrence that provides the variable's value. -/
theorem QueryReadList.value_argVar {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    {ρ : Env} {v : Var} :
    ∀ {es : List Expr} {is : List Term}, QueryReadList d ρ es is → Expr.ArgVarList v es →
      ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.values
  | _, _, .nil, hv => absurd hv (by simp [Expr.ArgVarList])
  | _, _, .cons he hl, hv =>
      hv.elim (QueryRead.value_argVar hd hstore he) (QueryReadList.value_argVar hd hstore hl)

end

theorem PatternRead.value_argVar {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    {ρ : Env} {v : Var} {p : Pattern}
    (h : PatternRead d ρ p) (hv : Pattern.ArgVar v p) :
    ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.values := by
  cases h with
  | expr he => exact QueryRead.value_argVar hd hstore he hv
  | eq ha hb =>
      exact hv.elim (QueryRead.value_argVar hd hstore ha) (QueryRead.value_argVar hd hstore hb)

/-- A nonliteral reading has an existing value, either from its binding or its parent row. -/
theorem QueryRead.output_value {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    {ρ : Env} {e : Expr} {i : Term}
    (h : QueryRead d ρ e i)
    (hv : ∀ v j, Env.lookup v ρ = some j → j ∈ d.values)
    (hn : ∀ l, e ≠ .lit l) : i ∈ d.values := by
  cases h with
  | lit => exact False.elim (hn _ rfl)
  | var hlk => exact hv _ _ hlk
  | app _ ho => exact out_values hd hstore ho _ (by simp)

/-- A complete source match has a consistent target substitution whose values can be
used in mathematical matching and whose original patterns read through view rows. -/
theorem exists_queryRead {d : Database} {src querySrc : Database}
    (h : Rebuilt d) (hd : d.Diag) (hstore : d.StoreOk) (hs : EdgesSound d src) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hun : UnionsRead d querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d t e) {σ : Env} {q : Query}
    (hp : ∀ p ∈ q, p.OrderingFree) (hk : Query.VarsKeyed q)
    (hm : ValidQuerySubst querySrc q σ) :
    ∃ ρ, CanonicalReads d σ ρ ∧ Env.dom ρ = Env.dom σ ∧
      (∀ p ∈ q, PatternRead d ρ p) ∧
      (∀ v j, Env.lookup v ρ = some j → j ∈ d.values) := by
  obtain ⟨ρ, hρ, hdom⟩ := exists_canonical_env h hs hw hm.mem_terms hex
  have hreads : ∀ p ∈ q, PatternRead d ρ p := fun p hmem =>
    patternRead_of_matches h hs hw hcs hun hex hρ
      (hp p hmem) (hm.matches_of_mem hmem)
  refine ⟨ρ, hρ, hdom, hreads, fun v j hj => ?_⟩
  have hvs : v ∈ Env.dom σ := hdom ▸ Env.mem_dom_of_mem (Env.mem_of_lookup hj)
  obtain ⟨p, hpm, hvp⟩ := hm.mem_dom_iff.mp hvs
  have hvq : v ∈ Query.vars q :=
    Query.mem_vars.mpr ⟨p, hpm, ((Pattern.mem_freeVars p).mp hvp).1⟩
  obtain ⟨a, ha, hva⟩ := hk v hvq
  obtain ⟨i, hi, him⟩ := PatternRead.value_argVar hd hstore (hreads a ha) hva
  exact (Option.some.inj (hi.symm.trans hj)) ▸ him

end Egglog.Congruence.Abstract
