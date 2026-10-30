import EgglogSemantics.Proofs.Congruence.HeadMatch
import EgglogSemantics.Proofs.Congruence.AbstractMaintenance

/-! Guarded head bindings reconstruct source matches at their current leader values. -/

namespace Egglog.Congruence

/-- Each leader guard reads two current UF rows at its bound values. -/
theorem leaderQuery_reads {d : Database} (hd : d.Diag) (hs : d.StoreOk)
    (huf : d.sig ufName = some (tableDecl 1)) {vs : List Var} {σ : Env}
    (hm : ∀ p ∈ leaderQuery vs, Matches d p σ) {v : Var} (hv : v ∈ vs) :
    ∃ a b, Env.lookup v σ = some a ∧ Env.lookup (leaderVar v) σ = some b ∧
      d.Out ufName [a] [b] ∧ d.Out ufName [b] [b] := by
  have hfirst : Matches d (.expr (.app ufName [.var v, .var (leaderVar v)])) σ :=
    hm _ (List.mem_flatMap.mpr ⟨v, hv, by simp⟩)
  have hlast : Matches d (.expr (.app ufName [.var (leaderVar v), .var (leaderVar v)])) σ :=
    hm _ (List.mem_flatMap.mpr ⟨v, hv, by simp⟩)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
    (Abstract.Matches.bound (v := v) hfirst (by rfl) (by simp [Pattern.vars, Expr.vars, Expr.varsList]))
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (Abstract.Matches.bound (v := leaderVar v) hlast (by rfl)
      (by simp [Pattern.vars, Expr.vars, Expr.varsList]))
  exact ⟨a, b, ha, hb, Live.uf_match_out hd hs huf ha hb hfirst,
    Live.uf_match_out hd hs huf hb hb hlast⟩

theorem sourceMatch_of_leaderQuery {src d : Database} (hb : src.TermsBuild) (hw : src.WF)
    (hs : ViewsSound d src) (he : EdgesSound d src) (hd : d.Diag) (hst : d.StoreOk)
    (_hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) (hdecl : ViewTables d)
    (huf : d.sig ufName = some (tableDecl 1)) {q : Query} {n : Nat} {σ : Env}
    (hof : ∀ p ∈ q, p.OrderingFree) (hg : ∀ p ∈ q, p.Grounded)
    (hk : Query.VarsKeyed q)
    (hm : ValidQuerySubst d ((encodeQuery q n).1 ++ leaderQuery q.vars) σ) :
    ∃ τ, ValidQuerySubst src q τ ∧ ∀ v ∈ q.vars, ∀ i,
      Env.lookup (leaderVar v) σ = some i → Env.lookup v (τ) = some i := by
  have hread := patternReads_of_encodeQuery_matches hd hst hdecl hof hk
    (hm.mem_values hst (encodeQuery_leader_safe q n hof))
    (fun _ hp => hm.matches_of_mem (List.mem_append_left _ hp))
  have hleaders := fun v (hv : v ∈ q.vars) => leaderQuery_reads hd hst huf
    (fun _ hp => hm.matches_of_mem (List.mem_append_right _ hp)) hv
  let g : Var → Term := fun v => idReading σ (leaderVar v)
  have hlink : ∀ v ∈ q.vars, ∀ i, Env.lookup v σ = some i → StoredCong src (g v) i := by
    intro v hv i hi
    obtain ⟨a, b, ha, hb, ho, _⟩ := hleaders v hv
    obtain rfl : a = i := Option.some.inj (ha.symm.trans hi)
    simpa only [g, idReading_eq hb] using (he _ _ ho).symm
  have hvalue : ∀ v ∈ q.vars, g v ∈ src.values := by
    intro v hv
    obtain ⟨a, b, ha, hleader, ho, _⟩ := hleaders v hv
    have hmem := (he _ _ ho).mem_right
    change idReading σ (leaderVar v) ∈ src.values
    rw [idReading_eq hleader]
    exact ⟨hmem, termsBuild_isValue hb hw hmem⟩
  obtain ⟨τ, hτ, _, hlookup⟩ := validQuerySubst_of_patternReads hb hs hvalue hlink
    (fun p hp => (hg p hp).groundedAt) hread
  exact ⟨τ, hτ, fun v hv i hi => by
    rw [hlookup v hv]
    simp only [g, idReading_eq hi]⟩

mutual

theorem eval_leader_eq {s₁ s₂ : Signature} {ρ₁ ρ₂ : Env} : ∀ e : Expr,
    (∀ f ∈ e.fns, s₁.IsCtor f ↔ s₂.IsCtor f) →
    (∀ v ∈ e.vars, Expr.eval s₁ (.var (leaderVar v)) ρ₁ = Expr.eval s₂ (.var v) ρ₂) →
    Expr.eval s₁ (leaderExpr e) ρ₁ = Expr.eval s₂ e ρ₂
  | .lit _, _, _ => rfl
  | .var v, _, hv => hv v (by simp [Expr.vars])
  | .app f args, hc, hv => by
      simp only [leaderExpr, Expr.eval]
      by_cases hf : s₁.IsCtor f
      · rw [if_pos hf, if_pos ((hc f (by simp [Expr.fns])).mp hf),
          evalList_leader_eq args (fun g hg => hc g (by simp [Expr.fns, hg]))
            (fun v hv' => hv v (by simpa [Expr.vars] using hv'))]
      · rw [if_neg hf, if_neg (fun hg => hf ((hc f (by simp [Expr.fns])).mpr hg))]
  | .min a b, hc, hv => by
      simp only [leaderExpr, Expr.eval]
      rw [eval_leader_eq a (fun f hf => hc f (by simp [Expr.fns, hf]))
        (fun v hv' => hv v (by simp [Expr.vars, hv'])),
        eval_leader_eq b (fun f hf => hc f (by simp [Expr.fns, hf]))
          (fun v hv' => hv v (by simp [Expr.vars, hv']))]
  | .ite lhs rhs yes no, hc, hv => by
      simp only [leaderExpr, Expr.eval]
      rw [evalList_leader_eq lhs
          (fun f hf => hc f (by simp [Expr.fns, hf]))
          (fun v hv' => hv v (by simp [Expr.vars, hv'])),
        evalList_leader_eq rhs
          (fun f hf => hc f (by simp [Expr.fns, hf]))
          (fun v hv' => hv v (by simp [Expr.vars, hv']))]
      simp only [eval_leader_eq yes
          (fun f hf => hc f (by simp [Expr.fns, hf]))
          (fun v hv' => hv v (by simp [Expr.vars, hv'])),
        eval_leader_eq no
          (fun f hf => hc f (by simp [Expr.fns, hf]))
          (fun v hv' => hv v (by simp [Expr.vars, hv']))]

theorem evalList_leader_eq {s₁ s₂ : Signature} {ρ₁ ρ₂ : Env} : ∀ es : List Expr,
    (∀ f ∈ Expr.fnsList es, s₁.IsCtor f ↔ s₂.IsCtor f) →
    (∀ v ∈ Expr.varsList es,
      Expr.eval s₁ (.var (leaderVar v)) ρ₁ = Expr.eval s₂ (.var v) ρ₂) →
    Expr.evalList s₁ (leaderArgs es) ρ₁ = Expr.evalList s₂ es ρ₂
  | [], _, _ => rfl
  | e :: es, hc, hv => by
      simp only [leaderArgs, Expr.evalList]
      rw [eval_leader_eq e (fun f hf => hc f (by simp [Expr.fnsList, hf]))
          (fun v hv' => hv v (by simp [Expr.varsList, hv'])),
        evalList_leader_eq es (fun f hf => hc f (by simp [Expr.fnsList, hf]))
          (fun v hv' => hv v (by simp [Expr.varsList, hv']))]

end

/-- Source heads use precisely the values selected by the compiled positive guards. -/
theorem sourceMatch_leader_evaluations {src d : Database} (hb : src.TermsBuild)
    (hw : src.WF) (hs : ViewsSound d src) (he : EdgesSound d src)
    (hd : d.Diag) (hst : d.StoreOk) (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms)
    (hdecl : ViewTables d) (huf : d.sig ufName = some (tableDecl 1))
    {q : Query} {n : Nat} {σ : Env}
    (hof : ∀ p ∈ q, p.OrderingFree) (hg : ∀ p ∈ q, p.Grounded)
    (hk : Query.VarsKeyed q)
    (hm : ValidQuerySubst d ((encodeQuery q n).1 ++ leaderQuery q.vars) σ) :
    ∃ τ, ValidQuerySubst src q τ ∧ ∀ e : Expr,
      (∀ f ∈ e.fns, d.sig.IsCtor f ↔ src.sig.IsCtor f) →
      (∀ v ∈ e.vars, v ∈ q.vars) →
      Expr.eval d.sig (leaderExpr e) σ = Expr.eval src.sig e τ := by
  obtain ⟨τ, hτ, hlookup⟩ := sourceMatch_of_leaderQuery hb hw hs he hd hst hsc hdecl huf
    hof hg hk hm
  refine ⟨τ, hτ, fun e hf hv => eval_leader_eq e hf fun v hve => ?_⟩
  obtain ⟨_, b, _, hl, _, _⟩ := leaderQuery_reads hd hst huf
    (fun _ hp => hm.matches_of_mem (List.mem_append_right _ hp)) (hv v hve)
  simp only [Expr.eval_var, hl, hlookup v (hv v hve) b hl]

end Egglog.Congruence
