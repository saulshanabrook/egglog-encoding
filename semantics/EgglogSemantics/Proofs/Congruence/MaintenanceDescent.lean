import EgglogSemantics.Proofs.Congruence.Descent
import EgglogSemantics.Proofs.Congruence.MaintenanceHistory

/-! Rebuilding preserves descending UF edges: compression composes existing edges,
and view maintenance writes no new UF entry. -/

namespace Egglog.Congruence

/-- Path compression composes two descending recorded edges. -/
theorem pathCompressRule_ufTermsDescend {d d' : FDatabase} {σ : Env}
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : UFTermsDescend d)
    (hσ : σ ∈ matchQuery d pathCompressRule.query)
    (hf : execLocalActions d pathCompressRule.actions σ = some d') : UFTermsDescend d' := by
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
  have hac : c = a ∨ Term.blt c a = true :=
    UFReach.le h ((Relation.ReflTransGen.single hm₁ : UFReach d a b).trans (.single hm₂))
  have ham : a ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₁ (by simp)
  have hcm : c ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₂ (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := execLocalActions_entry (g := ufName)
    (args := [.var "@a"]) (out := [.var "@c"]) hf
  obtain ⟨a', hla', rfl⟩ := Expr.evalList_singleton hesh
  obtain rfl : a = a' := Option.some.inj ((Expr.eval_append_env _ hla).symm.trans hla')
  obtain ⟨c', hlc', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : c = c' := Option.some.inj ((Expr.eval_append_env _ hlc).symm.trans hlc')
  apply UFTermsDescend.mono_terms (ht := hterms)
  apply h.addAtom (f := ufName) (cols := [a, c]) hsc
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> assumption
  · intro x y he
    obtain ⟨rfl, rfl⟩ : a = x ∧ c = y := by simpa using he
    exact hac

/-- A variable-only head outside UF cannot introduce a new UF edge. -/
theorem execLocalActions_vars_ufTermsDescend {d d' : FDatabase} {q : Query} {σ : Env}
    {f : FnName} {cols : List Expr} (hf : f ≠ ufName)
    (hv : ∀ c ∈ cols, ∃ v, c = Expr.var v) (hi : d.Inv) (h : UFTermsDescend d)
    (hσ : σ ∈ matchQuery d q)
    (run : execLocalActions d [.expr (.app f cols)] σ = some d') : UFTermsDescend d' := by
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp run
  have hm' : execAction { d with env := σ ++ d.env } (.expr (.app f (cols ++ []))) =
      some m := by simpa [execActions] using hm
  obtain ⟨ts, vs, hts, hvs, rfl⟩ := execAction_entry hm'
  obtain rfl : vs = [] := (Option.some.inj hvs).symm
  have hcols := evalList_vars_held (hi.setEnvMatch hσ) cols hv hts
  exact h.addAtom (Egglog.FDatabase.SubtermClosed.of_wf hi.wf) (by simpa using hcols)
    (fun _ _ he => (hf (Term.app.inj he).1).elim)

/-- Every generated maintenance rule, including ruleset copies, preserves UF descent. -/
theorem maintenance_ufTermsDescend {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r)
    {d d' : FDatabase} {σ : Env} (hi : d.Inv) (hn : d.NoUnions) (h : UFTermsDescend d)
    (hσ : σ ∈ matchQuery d r.query) (run : execLocalActions d r.actions σ = some d') :
    UFTermsDescend d' := by
  obtain ⟨f, cols, ha, hv, hkind⟩ := maintenance_headShape hc hr
  rcases hkind with hf | ⟨hq, ha'⟩
  · rw [ha] at run
    exact execLocalActions_vars_ufTermsDescend hf hv hi h hσ run
  · rw [hq] at hσ
    rw [ha'] at run
    exact pathCompressRule_ufTermsDescend hn.eqsRefl hi.index
      (Egglog.FDatabase.SubtermClosed.of_wf hi.wf) h hσ run

end Egglog.Congruence
