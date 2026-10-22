import EgglogSemantics.Proofs.Congruence.QueryTransport

/-! Proof witnesses for reading original query expressions through live compiled rows.
These relations are erased proofs; the compiler does not store a flattening tree. -/

namespace Egglog.Congruence

mutual

inductive LiveQueryRead (d : FDatabase) (ρ : Env) : Expr → Term → Prop where
  | lit {l : Lit} : LiveQueryRead d ρ (.lit l) (.lit l)
  | var {v : Var} {i : Term} : Env.lookup v ρ = some i → LiveQueryRead d ρ (.var v) i
  | app {f : FnName} {args : List Expr} {is : List Term} {i : Term} :
      LiveQueryReadList d ρ args is → d.sig (viewName f) = some (tableDecl is.length) →
      (⟨viewName f, is, [i]⟩ : Row) ∈ d.rows →
      (∀ t ∈ is ++ [i], t ∈ d.valueTerms) → LiveQueryRead d ρ (.app f args) i

inductive LiveQueryReadList (d : FDatabase) (ρ : Env) : List Expr → List Term → Prop where
  | nil : LiveQueryReadList d ρ [] []
  | cons {e : Expr} {i : Term} {es : List Expr} {is : List Term} :
      LiveQueryRead d ρ e i → LiveQueryReadList d ρ es is →
      LiveQueryReadList d ρ (e :: es) (i :: is)

end

/-- Each source binding is assigned one canonical target reading, shared by all uses. -/
def Env.CanonicalReads (d : FDatabase) (σ ρ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t → ∃ i, Env.lookup v ρ = some i ∧
    ViewRepr d.toDatabase t i ∧ UFRowRoot d i

section Reading

variable {P : Program} {d : FDatabase} {src : Database}
variable (h : Rebuilt d) (htables : RebuildTables P d) (hs : SoundTerms d src)
variable (hb : src.TermsBuild) (hctors : src.CtorsIn P)
variable (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF)
include h htables hs hb hctors hc hw

/-- A single function on source values keeps repeated query variables consistent. -/
theorem exists_canonical_env {querySrc : Database} {σ : Env} (hv : ∀ b ∈ σ, b.2 ∈ querySrc.terms)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d.toDatabase t e) :
    ∃ ρ, Env.CanonicalReads d σ ρ ∧ Env.dom ρ = Env.dom σ := by
  classical
  let w : Term → Term := fun t => if ht : t ∈ querySrc.terms then h.root (hex t ht).choose else t
  have hread : ∀ t ∈ querySrc.terms, ViewRepr d.toDatabase t (w t) ∧ UFRowRoot d (w t) := by
    intro t ht
    simp only [w, dif_pos ht]
    exact ⟨h.normalize_view htables hs hb hctors hc hw t (hex t ht).choose_spec,
      (h.root_spec _).2⟩
  refine ⟨Env.mapVals w σ, ?_, dom_mapVals w σ⟩
  intro v t ht
  have hm := hv (v, t) (Env.mem_of_lookup ht)
  exact ⟨w t, by rw [lookup_mapVals, ht]; rfl, hread t hm⟩

end Reading

mutual

/-- Evaluating the original syntax and representing the result gives a live reading of
that syntax at the consistent target substitution. -/
theorem liveQueryRead_of_eval_view {P : Program} {d : FDatabase} {src : Database}
    (h : Rebuilt d) (htables : RebuildTables P d) (hs : SoundTerms d src)
    (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF) {sig : Signature} {σ ρ : Env}
    (hρ : Env.CanonicalReads d σ ρ) :
    ∀ (e : Expr) {t i : Term}, e.OrderingFree →
      e.eval sig σ = some t → ViewRepr d.toDatabase t i →
      LiveQueryRead d ρ e (h.root i)
  | .lit l, _, _, _, he, hv => by
      obtain rfl := Option.some.inj he
      cases hv
      rw [h.root_lit hs hw l]
      exact .lit
  | .var v, t, i, _, he, hv => by
      obtain ⟨j, hj, hvj, hrj⟩ := hρ v t he
      have heq : j = h.root i := by
        have hh := h.unique_view htables hs hb hctors hc t hvj hv
        simpa only [h.root_eq hrj] using hh
      exact heq ▸ LiveQueryRead.var hj
  | .min _ _, _, _, hp, _, _ => (Expr.not_orderingFree_min hp).elim
  | .ite _ _ _ _, _, _, hp, _, _ => (Expr.not_orderingFree_ite hp).elim
  | .app f args, t, i, hp, he, hv => by
      simp only [Expr.eval] at he
      split at he
      next hctor =>
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        cases hv with
        | @app _ _ es _ hl ho =>
            have hr := h.out_normalized htables hs hb hctors hc ho
            have hk := view_row_ctors h.inv h.noUnions hs hctors hr
            have hf := htables.view _ _ hk
            refine .app (liveQueryReadList_of_eval_view h htables hs hb hctors hc hw hρ args
              (Expr.orderingFree_app hp) hts hl) hf hr ?_
            exact viewRow_valueColumns h.noUnions.eqsRefl h.inv hs hb hc
              (by simp [Signature.mergeOf, hf, tableDecl]) hr
      next => cases he

@[inherit_doc liveQueryRead_of_eval_view]
theorem liveQueryReadList_of_eval_view {P : Program} {d : FDatabase} {src : Database}
    (h : Rebuilt d) (htables : RebuildTables P d) (hs : SoundTerms d src)
    (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF) {sig : Signature} {σ ρ : Env}
    (hρ : Env.CanonicalReads d σ ρ) :
    ∀ (es : List Expr) {ts is : List Term}, Expr.OrderingFreeList es →
      Expr.evalList sig es σ = some ts → ViewReprList d.toDatabase ts is →
      LiveQueryReadList d ρ es (is.map h.root)
  | [], _, _, _, he, hv => by
      obtain rfl := Option.some.inj he
      cases hv
      exact .nil
  | e :: es, _, _, hp, he, hv => by
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      cases hv with
      | cons hv hvs =>
          exact .cons (liveQueryRead_of_eval_view h htables hs hb hctors hc hw hρ e
            (Expr.orderingFreeList_cons hp).1 ht hv)
            (liveQueryReadList_of_eval_view h htables hs hb hctors hc hw hρ es
              (Expr.orderingFreeList_cons hp).2 hts hvs)

end

/-- Live readings of a source pattern. The equality's held-value check is supplied by
groundedness and the query's keyed-variable condition when constructing the final match. -/
inductive LivePatternRead (d : FDatabase) (ρ : Env) : Pattern → Prop where
  | expr {e : Expr} {i : Term} : LiveQueryRead d ρ e i → LivePatternRead d ρ (.expr e)
  | eq {a b : Expr} {i : Term} :
      LiveQueryRead d ρ a i → LiveQueryRead d ρ b i → LivePatternRead d ρ (.eq a b)

/-- Original source matches produce live query readings at the consistent substitution. -/
theorem livePatternRead_of_matches {P : Program} {d : FDatabase} {src querySrc : Database}
    (h : Rebuilt d) (htables : RebuildTables P d) (hs : SoundTerms d src)
    (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hun : UnionsRead d.toDatabase querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d.toDatabase t e) {σ ρ : Env}
    (hρ : Env.CanonicalReads d σ ρ) {p : Pattern}
    (hp : p.OrderingFree) (hm : Matches querySrc p σ) :
    LivePatternRead d ρ p := by
  cases p with
  | expr e =>
      obtain ⟨t, i, he, hv⟩ := view_of_matches_expr h htables hs hb hctors hc hw hun hex hm
      rw [Expr.evalAtom_eq_eval hcs] at he
      exact .expr (liveQueryRead_of_eval_view h htables hs hb hctors hc hw hρ e hp he hv)
  | eq a b =>
      obtain ⟨ta, tb, i, ha, hb', hia, hib⟩ :=
        views_of_matches_eq h htables hs hb hctors hc hw hun hex hm
      exact .eq (liveQueryRead_of_eval_view h htables hs hb hctors hc hw hρ a hp.1 ha hia)
        (liveQueryRead_of_eval_view h htables hs hb hctors hc hw hρ b hp.2 hb' hib)

mutual

/-- A variable appearing as a constructor argument receives a matchable value from a row. -/
theorem LiveQueryRead.value_argVar {d : FDatabase} {ρ : Env} {v : Var} :
    ∀ {e : Expr} {i : Term}, LiveQueryRead d ρ e i → Expr.ArgVar v e →
      ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.valueTerms
  | _, _, .lit, hv => absurd hv (by simp [Expr.ArgVar])
  | _, _, .var _, hv => absurd hv (by simp [Expr.ArgVar])
  | _, _, .app hl _ _ hcols, hv => by
      rcases hv with hv | hv
      · exact LiveQueryReadList.value_memVar hl
          (fun j hj => hcols j (List.mem_append_left _ hj)) hv
      · exact LiveQueryReadList.value_argVar hl hv

/-- A direct variable column reads the value in that column. -/
theorem LiveQueryReadList.value_memVar {d : FDatabase} {ρ : Env} {v : Var} :
    ∀ {es : List Expr} {is : List Term}, LiveQueryReadList d ρ es is →
      (∀ i ∈ is, i ∈ d.valueTerms) → Expr.var v ∈ es →
      ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.valueTerms
  | _, _, .nil, _, hv => absurd hv (by simp)
  | _, _, .cons he hl, hc, hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · cases he with
        | var hv => exact ⟨_, hv, hc _ List.mem_cons_self⟩
      · exact LiveQueryReadList.value_memVar hl
          (fun j hj => hc j (List.mem_cons_of_mem _ hj)) hv

/-- Descend to the constructor occurrence that provides the variable's value. -/
theorem LiveQueryReadList.value_argVar {d : FDatabase} {ρ : Env} {v : Var} :
    ∀ {es : List Expr} {is : List Term}, LiveQueryReadList d ρ es is → Expr.ArgVarList v es →
      ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.valueTerms
  | _, _, .nil, hv => absurd hv (by simp [Expr.ArgVarList])
  | _, _, .cons he hl, hv =>
      hv.elim (LiveQueryRead.value_argVar he) (LiveQueryReadList.value_argVar hl)

end

theorem LivePatternRead.value_argVar {d : FDatabase} {ρ : Env} {v : Var} {p : Pattern}
    (h : LivePatternRead d ρ p) (hv : Pattern.ArgVar v p) :
    ∃ j, Env.lookup v ρ = some j ∧ j ∈ d.valueTerms := by
  cases h with
  | expr he => exact he.value_argVar hv
  | eq ha hb => exact hv.elim (LiveQueryRead.value_argVar ha) (LiveQueryRead.value_argVar hb)

/-- A nonliteral reading has an existing value, either from its binding or its parent row. -/
theorem LiveQueryRead.output_value {d : FDatabase} {ρ : Env} {e : Expr} {i : Term}
    (h : LiveQueryRead d ρ e i)
    (hv : ∀ v j, Env.lookup v ρ = some j → j ∈ d.valueTerms)
    (hn : ∀ l, e ≠ .lit l) : i ∈ d.valueTerms := by
  cases h with
  | lit => exact False.elim (hn _ rfl)
  | var hlk => exact hv _ _ hlk
  | app _ _ _ hcols => exact hcols _ (by simp)

/-- A complete source match has a consistent target substitution whose values can be
assigned by the executable matcher and whose original patterns read through live rows. -/
theorem exists_live_query {P : Program} {d : FDatabase} {src querySrc : Database}
    (h : Rebuilt d) (htables : RebuildTables P d) (hs : SoundTerms d src)
    (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hun : UnionsRead d.toDatabase querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d.toDatabase t e) {σ : Env} {q : Query}
    (hp : ∀ p ∈ q, p.OrderingFree) (hk : Query.VarsKeyed q)
    (hm : ValidQuerySubst querySrc q σ) :
    ∃ ρ, Env.CanonicalReads d σ ρ ∧ Env.dom ρ = Env.dom σ ∧
      (∀ p ∈ q, LivePatternRead d ρ p) ∧
      (∀ v j, Env.lookup v ρ = some j → j ∈ d.valueTerms) := by
  obtain ⟨ρ, hρ, hdom⟩ := exists_canonical_env h htables hs hb hctors hc hw hm.mem_terms hex
  have hreads : ∀ p ∈ q, LivePatternRead d ρ p := fun p hmem =>
    livePatternRead_of_matches h htables hs hb hctors hc hw hcs hun hex hρ
      (hp p hmem) (hm.matches_of_mem hmem)
  refine ⟨ρ, hρ, hdom, hreads, fun v j hj => ?_⟩
  have hvs : v ∈ Env.dom σ := hdom ▸ Env.mem_dom_of_mem (Env.mem_of_lookup hj)
  obtain ⟨p, hpm, hvp⟩ := hm.mem_dom_iff.mp hvs
  have hvq : v ∈ Query.vars q :=
    Query.mem_vars.mpr ⟨p, hpm, ((Pattern.mem_freeVars p).mp hvp).1⟩
  obtain ⟨a, ha, hva⟩ := hk v hvq
  obtain ⟨i, hi, him⟩ := (hreads a ha).value_argVar hva
  exact (Option.some.inj (hi.symm.trans hj)) ▸ him

end Egglog.Congruence
