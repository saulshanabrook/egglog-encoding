import EgglogSemantics.Proofs.Congruence.AbstractMaintenanceSound
import EgglogSemantics.Proofs.Congruence.MaintenanceSyntax

/-! Mathematical maintenance firings preserve weakly descending union-find edges. -/

namespace Egglog.Congruence.Abstract

/-- Path compression composes two descending recorded edges. -/
theorem pathCompressRule_descending {d d' : Database} {σ : Env}
    (hd : d.Diag) (hw : d.WF) (h : Descending d)
    (hσ : ValidQuerySubst d pathCompressRule.query σ)
    (hf : evalLocalActions d pathCompressRule.actions σ = some d') : Descending d' := by
  obtain ⟨ts₁, us₁, ha₁, hv₁, hm₁⟩ := mem_terms_of_validQuerySubst_entry hd hσ
    (vs := [Expr.var "@b"]) (f := ufName) (as := [Expr.var "@a"])
    (by simp [pathCompressRule])
  obtain ⟨a, hla, rfl⟩ := Expr.evalList_singleton ha₁
  obtain ⟨b, hlb, rfl⟩ := Expr.evalList_singleton hv₁
  obtain ⟨ts₂, us₂, ha₂, hv₂, hm₂⟩ := mem_terms_of_validQuerySubst_entry hd hσ
    (vs := [Expr.var "@c"]) (f := ufName) (as := [Expr.var "@b"])
    (by simp [pathCompressRule])
  obtain ⟨b', hlb', rfl⟩ := Expr.evalList_singleton ha₂
  obtain ⟨c, hlc, rfl⟩ := Expr.evalList_singleton hv₂
  obtain rfl : b = b' := Option.some.inj (hlb.symm.trans hlb')
  have hac : c = a ∨ Term.blt c a = true := by
    rcases h a b hm₁ with rfl | hab
    · exact h b c hm₂
    · rcases h b c hm₂ with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (Term.blt_trans c b a hbc hab)
  have ham : a ∈ d.terms := Database.mem_terms_of_arg hw hm₁ (by simp)
  have hcm : c ∈ d.terms := Database.mem_terms_of_arg hw hm₂ (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := evalLocalActions_entry (g := ufName)
    (args := [.var "@a"]) (out := [.var "@c"]) hf
  obtain ⟨a', hla', rfl⟩ := Expr.evalList_singleton hesh
  obtain rfl : a = a' := Option.some.inj (hla.symm.trans hla')
  obtain ⟨c', hlc', rfl⟩ := Expr.evalList_singleton hvsh
  obtain rfl : c = c' := Option.some.inj (hlc.symm.trans hlc')
  exact (h.addUF hw ham hcm hac).mono_terms hterms

/-- Bound variable columns remain held when a maintenance head rearranges them. -/
theorem evalList_vars_held {d : Database} {ρ : Env} (hv : ∀ b ∈ ρ, b.2 ∈ d.terms) :
    ∀ (cols : List Expr) {ts : List Term},
      (∀ c ∈ cols, ∃ v, c = Expr.var v) → Expr.evalList d.sig cols ρ = some ts →
      ∀ t ∈ ts, t ∈ d.terms
  | [], _, _, he => by obtain rfl := Option.some.inj he; simp
  | c :: cs, _, hvars, he => by
      obtain ⟨v, rfl⟩ := hvars c List.mem_cons_self
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv (v, x) (Env.mem_of_lookup ht)
      · exact evalList_vars_held hv cs
          (fun c hc => hvars c (List.mem_cons_of_mem _ hc)) hts x hx

/-- A flat non-UF head does not introduce a new UF row in its already-held columns. -/
theorem evalLocalActions_vars_descending {d d' : Database} {q : Query} {σ : Env}
    {f : FnName} {cols : List Expr} (hf : f ≠ ufName)
    (hvars : ∀ c ∈ cols, ∃ v, c = Expr.var v) (hw : d.WF) (h : Descending d)
    (hσ : ValidQuerySubst d q σ)
    (run : evalLocalActions d [.expr (.app f cols)] σ = some d') : Descending d' := by
  obtain ⟨ts, vs, hts, hvs, hterms⟩ := evalLocalActions_entry (args := cols) (out := [])
    (by simpa using run)
  obtain rfl : vs = [] := (Option.some.inj hvs).symm
  have hval : ∀ b ∈ σ, b.2 ∈ d.terms := hσ.mem_terms
  have hcols := evalList_vars_held hval cols hvars hts
  apply Descending.mono_terms hterms
  intro a b hm
  rw [Database.addTerm_terms] at hm
  rcases hm with hm | hm
  · exact h a b hm
  · apply h a b
    apply subterms_of_columns hw (by simpa using hcols) hm
    intro he
    exact hf (Term.app.inj he).1.symm

/-- All maintenance rules, including saturation copies, preserve descending links. -/
theorem maintenance_descending {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r)
    {d d' : Database} {σ : Env} (hd : d.Diag) (hw : d.WF) (h : Descending d)
    (hσ : ValidQuerySubst d r.query σ) (run : evalLocalActions d r.actions σ = some d') :
    Descending d' := by
  obtain ⟨f, cols, ha, hv, hkind⟩ := maintenance_headShape hc hr
  rcases hkind with hf | ⟨hq, ha'⟩
  · rw [ha] at run
    exact evalLocalActions_vars_descending hf hv hw h hσ run
  · rw [hq] at hσ
    rw [ha'] at run
    exact pathCompressRule_descending hd hw h hσ run

end Egglog.Congruence.Abstract
