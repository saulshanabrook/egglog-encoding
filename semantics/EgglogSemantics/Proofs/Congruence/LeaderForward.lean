import EgglogSemantics.Proofs.Congruence.AbstractForward
import EgglogSemantics.Proofs.Congruence.LeaderMatch

/-! Canonical source matches extend to the compiler's positive leader guards. -/

namespace Egglog.Congruence

theorem leaderVar_injective : Function.Injective leaderVar := by
  intro v w h
  have he := congrArg String.toList h
  simp only [leaderVar, String.toList_append] at he
  exact String.toList_inj.mp (List.append_cancel_left he)

theorem leaderVar_atPrefix (v : Var) : "@".isPrefixOf (leaderVar v) = true := by
  rw [leaderVar, String.isPrefixOf, String.startsWith_string_iff, String.toList_append]
  exact ⟨"leader:".toList ++ v.toList, rfl⟩

theorem leaderVar_ne_freshVar (v : Var) (n : Nat) : leaderVar v ≠ freshVar n := by
  intro he
  have ht := congrArg String.toList he
  simp [leaderVar, freshVar, String.toList_append] at ht

private def leaderBindings (vs : List Var) (g : Var → Term) : Env :=
  vs.map fun v => (leaderVar v, g v)

private theorem leaderBindings_lookup {vs : List Var} {g : Var → Term} {v : Var}
    (hv : v ∈ vs) : Env.lookup (leaderVar v) (leaderBindings vs g) = some (g v) := by
  induction vs with
  | nil => simp at hv
  | cons w ws ih =>
    by_cases he : v = w
    · subst w; simp [leaderBindings]
    · have hn : leaderVar v ≠ leaderVar w := fun h => he (leaderVar_injective h)
      have hv' : v ∈ ws := (List.mem_cons.mp hv).resolve_left he
      simpa [leaderBindings, hn] using ih hv'

private theorem lookup_values_append {d : Database} {ρ τ : Env}
    (hρ : ∀ v i, Env.lookup v ρ = some i → i ∈ d.values)
    (hτ : ∀ v i, Env.lookup v τ = some i → i ∈ d.values) :
    ∀ v i, Env.lookup v (ρ ++ τ) = some i → i ∈ d.values := by
  intro v i hi
  cases hv : Env.lookup v ρ with
  | none => rw [Env.lookup_append_of_none hv] at hi; exact hτ v i hi
  | some j =>
      rw [Env.lookup_append_of_some hv] at hi
      exact Option.some.inj hi ▸ hρ v j hv

namespace Abstract

/-- Both original and renamed variables bind the same canonical source reading. -/
def LeaderReads (d : Database) (σ ρ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t → ∃ i,
    Env.lookup (leaderVar v) ρ = some i ∧ ViewRepr d t i ∧ Root d i

/-- Rebuilt source readings supply a match of the flattened query and every leader guard. -/
theorem encodedRule_match_of_source {d src querySrc : Database}
    (h : Rebuilt d) (hd : d.Diag) (hstore : d.StoreOk) (hdecl : ViewDeclared d)
    (he : EdgesSound d src) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hun : UnionsRead d querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d t e)
    (hself : ∀ t ∈ querySrc.terms, ∀ i ∈ d.values, ViewRepr d t i → Root d i →
      d.Out ufName [i] [i]) {σ : Env} {q : Query}
    (hof : ∀ p ∈ q, p.OrderingFree) (hk : Query.VarsKeyed q)
    (hg : ∀ p ∈ q, p.Grounded) (hn : ∀ v ∈ q.vars, ¬ "@".isPrefixOf v = true)
    (hm : ValidQuerySubst querySrc q σ) (n : Nat) :
    ∃ ρ, ValidQuerySubst d ((encodeQuery q n).1 ++ leaderQuery q.vars) ρ ∧
      CanonicalReads d σ ρ ∧ LeaderReads d σ ρ := by
  obtain ⟨ρ₀, hρ₀, hdom, hreads, hv⟩ := exists_queryRead h hd hstore he hw hcs hun hex hof hk hm
  have hvars : ∀ v ∈ Env.dom σ, v ∈ q.vars := by
    intro v hv
    obtain ⟨p, hp, hfv⟩ := hm.mem_dom_iff.mp hv
    exact Query.mem_vars.mpr ⟨p, hp, (p.mem_freeVars.mp hfv).1⟩
  have hn₀ : ∀ b ∈ ρ₀, ¬ "@".isPrefixOf b.1 = true := by
    intro b hb
    exact hn b.1 (hvars b.1 (hdom ▸ Env.mem_dom_of_mem hb))
  have hbound : ∀ v ∈ q.vars, ∃ i, Env.lookup v ρ₀ = some i ∧
      i ∈ d.values ∧ d.Out ufName [i] [i] := by
    intro v hvq
    obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp hvq
    have hvσ : v ∈ Env.dom σ := hm.mem_dom_iff.mpr
      ⟨p, hp, p.mem_freeVars.mpr ⟨hvp, by simp⟩⟩
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (Env.lookup_isSome_iff_mem_dom.mpr hvσ)
    obtain ⟨i, hi, hrep, hr⟩ := hρ₀ v t ht
    exact ⟨i, hi, hv v i hi, hself t (hm.mem_terms (v, t) (Env.mem_of_lookup ht)) i (hv v i hi) hrep hr⟩
  let g := idReading ρ₀
  have hgval : ∀ v ∈ q.vars, g v ∈ d.values := by
    intro v hv
    obtain ⟨i, hi, hm, _⟩ := hbound v hv
    change idReading ρ₀ v ∈ d.values
    rw [idReading_eq hi]
    exact hm
  obtain ⟨fresh, hf, hp⟩ := freshEnv_of_query hd hstore hdecl hv q hreads hg n
  let ρ : Env := ρ₀ ++ (fresh ++ leaderBindings q.vars g)
  have hext : ∀ v i, Env.lookup v ρ₀ = some i → Env.lookup v ρ = some i :=
    fun _ _ hi => Env.lookup_append_of_some hi
  have hfresh : ∀ b ∈ fresh, Env.lookup b.1 ρ = some b.2 := by
    intro b hb
    obtain ⟨k, _, _, hk⟩ := hf.fresh b hb
    have hnone : Env.lookup b.1 ρ₀ = none := Env.lookup_eq_none_iff.mpr fun hmem => by
      obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hmem
      exact hn₀ (b.1, t) ht (hk ▸ atPrefix_freshVar k)
    rw [show ρ = ρ₀ ++ (fresh ++ leaderBindings q.vars g) from rfl,
      Env.lookup_append_of_none hnone,
      Env.lookup_append_of_some (Env.lookup_of_mem_nodup hb hf.nodup)]
  have hleader : ∀ v ∈ q.vars, Env.lookup (leaderVar v) ρ = some (g v) := by
    intro v hv
    have hnρ : Env.lookup (leaderVar v) ρ₀ = none := Env.lookup_eq_none_iff.mpr fun hmem => by
      obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hmem
      exact hn₀ (leaderVar v, t) ht (leaderVar_atPrefix v)
    have hnf : Env.lookup (leaderVar v) fresh = none := Env.lookup_eq_none_iff.mpr fun hmem => by
      obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hmem
      obtain ⟨k, _, _, heq⟩ := hf.fresh (leaderVar v, t) ht
      exact leaderVar_ne_freshVar v k heq
    rw [show ρ = ρ₀ ++ (fresh ++ leaderBindings q.vars g) from rfl,
      Env.lookup_append_of_none hnρ, Env.lookup_append_of_none hnf]
    exact leaderBindings_lookup hv
  have hval : ∀ v i, Env.lookup v ρ = some i → i ∈ d.values := by
    apply lookup_values_append hv
    apply lookup_values_append (fun v i hi => hf.valued (v, i) (Env.mem_of_lookup hi))
    intro v i hi
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp (Env.mem_of_lookup hi)
    have hgi : g w = i := congrArg Prod.snd heq
    exact hgi ▸ hgval w hw
  have hguard : ∀ p ∈ leaderQuery q.vars, Matches d p ρ := by
    intro p hp
    obtain ⟨v, hv, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨i, hi, hvi, hrow⟩ := hbound v hv
    have hgi : g v = i := idReading_eq hi
    have hl := hleader v hv
    rw [hgi] at hl
    rcases List.mem_cons.mp hp with rfl | hp
    · apply match_current (hrow.entry hd)
      simp [Expr.evalList, Expr.eval, hext v i hi, hl, Option.filter_some, hvi.2, Entry.columns]
    · obtain rfl := List.mem_singleton.mp hp
      apply match_current (hrow.entry hd)
      simp [Expr.evalList, Expr.eval, hl, Option.filter_some, hvi.2, Entry.columns]
  have hall : ∀ p ∈ (encodeQuery q n).1 ++ leaderQuery q.vars, Matches d p ρ := by
    intro p hp'
    exact (List.mem_append.mp hp').elim
      (fun hp' => (hp ρ hfresh hext p hp').holds) (hguard p)
  obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_matches (fun v hvq => by
    obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp hvq
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (Matches.bound (hall p hp) ((encodeQuery_leader_safe q n hof).2 p hp) hvp)
    exact ⟨i, hi, hval v i hi⟩) hall
  have hkeep : ∀ v ∈ q.vars, Env.lookup v τ = Env.lookup v ρ := by
    intro v hv
    obtain ⟨p, hp, ha⟩ := hk v hv
    exact hag v (Query.mem_vars_append.mpr (Or.inl
      (mem_vars_encodeQuery_of_argVar q n hof hp ha)))
  have hlkeep : ∀ v ∈ q.vars, Env.lookup (leaderVar v) τ = some (g v) := by
    intro v hv
    rw [hag _ (Query.mem_vars_append.mpr (Or.inr (Query.mem_vars.mpr
      ⟨.expr (.app ufName [.var (leaderVar v), .var (leaderVar v)]),
        List.mem_flatMap.mpr ⟨v, hv, by simp⟩,
        by simp [Pattern.vars, Expr.vars, Expr.varsList]⟩))), hleader v hv]
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro v t ht
    obtain ⟨i, hi, hr, hroot⟩ := hρ₀ v t ht
    refine ⟨i, ?_, hr, hroot⟩
    rw [hkeep v (hvars v (Env.mem_dom_of_mem (Env.mem_of_lookup ht)))]
    exact hext v i hi
  · intro v t ht
    obtain ⟨i, hi, hr, hroot⟩ := hρ₀ v t ht
    refine ⟨i, ?_, hr, hroot⟩
    rw [hlkeep v (hvars v (Env.mem_dom_of_mem (Env.mem_of_lookup ht)))]
    exact congrArg some (idReading_eq hi)

end Abstract
end Egglog.Congruence
