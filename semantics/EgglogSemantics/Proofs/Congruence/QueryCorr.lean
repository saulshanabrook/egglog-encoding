import EgglogSemantics.Proofs.Congruence.Complete
import EgglogSemantics.Proofs.Query

/-! The correspondence of query matches at a canonical state: a source match of a rule's
query extends to a match of the compiled query, and a match of the compiled query restricts
to a source match binding the same source variables. A disequality compares the ids of its
two sides, which at a canonical state are the representatives of the two source values. -/

namespace Egglog.Congruence

variable {sub : Bool}

variable {src d : Database}

/-- The conditions on a source query the correspondence uses: minima over variables,
scoped, over source names and source variables. -/
structure QueryOk (q : Query) : Prop where
  minOverVars : ∀ p ∈ q, p.MinOverVars
  shape : ∀ p ∈ q, p.Scoped
  names : ∀ p ∈ q, ∀ e ∈ p.exprs, SrcNames e
  vars : ∀ v ∈ Query.vars q, NotFresh v

theorem QueryOk.tail {p : Pattern} {ps : Query} (h : QueryOk (p :: ps)) : QueryOk ps where
  minOverVars := fun q hq => h.minOverVars q (by simp [hq])
  shape := fun q hq => h.shape q (by simp [hq])
  names := fun q hq => h.names q (by simp [hq])
  vars := fun v hv => h.vars v (by simp [hv])

theorem QueryOk.head_vars {p : Pattern} {ps : Query} (h : QueryOk (p :: ps)) :
    ∀ v ∈ p.vars, NotFresh v := fun v hv => h.vars v (by simp [hv])

/-! ### Completeness at the pattern and query level -/

/-- Both sides of a comparison: the flattening of the second continues the interval of the
first, every atom matches under the joint fresh bindings, and the two ids evaluate to the
representatives of the two source values. -/
theorem complete_sides (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {l r : Expr} (n : Nat)
    (hol : l.MinOverVars) (hor : r.MinOverVars) (hnl : SrcNames l) (hnr : SrcNames r)
    (hsl : ∀ v ∈ l.vars, NotFresh v) (hsr : ∀ v ∈ r.vars, NotFresh v) {σ : Env}
    (hσ : NoFreshDom σ) (hreps : ∀ b ∈ σ, b.2 ∈ src.reps) {t₁ t₂ : Term}
    (hl : Expr.Matches src σ l) (hr : Expr.Matches src σ r) (hev₁ : l.eval σ = some t₁)
    (hev₂ : r.eval σ = some t₂) {x₁ : Expr} {ps : Query} {next : Nat} {x₂ : Expr}
    {qs : Query} {last : Nat} (h₁ : encodeQueryExprWith {} l n = (x₁, ps, next))
    (h₂ : encodeQueryExprWith {} r next = (x₂, qs, last)) :
    ∃ ρ, Fresh n last ρ ∧ (∀ b ∈ ρ, b.2 ∈ d.terms) ∧ (∀ q ∈ ps ++ qs, Matches d q (σ ++ ρ)) ∧
      Expr.Matches d (σ ++ ρ) x₁ ∧ Expr.Matches d (σ ++ ρ) x₂ ∧
      x₁.eval (σ ++ ρ) = some (srep src t₁) ∧ x₂.eval (σ ++ ρ) = some (srep src t₂) := by
  obtain ⟨ρ₁, hfr₁, hval₁, hatoms₁, hx₁, t₁', hev₁', -, hxe₁⟩ :=
    complete_expr h hc hw l n hol hnl hsl hσ hreps hl
  obtain rfl : t₁ = t₁' := Option.some.inj (hev₁.symm.trans hev₁')
  rw [h₁] at hfr₁ hatoms₁ hx₁ hxe₁
  simp only at hfr₁ hatoms₁ hx₁ hxe₁
  obtain ⟨ρ₂, hfr₂, hval₂, hatoms₂, hx₂, t₂', hev₂', -, hxe₂⟩ :=
    complete_expr h hc hw r next hor hnr hsr hσ hreps hr
  obtain rfl : t₂ = t₂' := Option.some.inj (hev₂.symm.trans hev₂')
  rw [h₂] at hfr₂ hatoms₂ hx₂ hxe₂
  simp only at hfr₂ hatoms₂ hx₂ hxe₂
  have hn := flat_next_le l n
  have hm' := flat_next_le r next
  rw [h₁] at hn
  rw [h₂] at hm'
  simp only at hn hm'
  have hagree₁ : ∀ v, NotFresh v ∨ FreshIn n next v →
      Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) = Env.lookup v (σ ++ ρ₁) :=
    fun v hv => lookup_left hfr₂ (not_freshIn_right hv)
  have hagree₂ : ∀ v, NotFresh v ∨ FreshIn next last v →
      Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) = Env.lookup v (σ ++ ρ₂) :=
    fun v hv => lookup_right hfr₁ (not_freshIn_left hv)
  have hvars₁ : ∀ p ∈ ps, ∀ v ∈ p.vars, NotFresh v ∨ FreshIn n next v := by
    intro p hp v hv
    have := flat_vars_sub l n (v := v) (by rw [h₁]; exact Query.mem_vars.mpr ⟨p, hp, hv⟩)
    rw [h₁] at this
    rcases this with hv | hv
    · exact Or.inl (hsl v hv)
    · exact Or.inr hv
  have hvars₂ : ∀ p ∈ qs, ∀ v ∈ p.vars, NotFresh v ∨ FreshIn next last v := by
    intro p hp v hv
    have := flat_vars_sub r next (v := v) (by rw [h₂]; exact Query.mem_vars.mpr ⟨p, hp, hv⟩)
    rw [h₂] at this
    rcases this with hv | hv
    · exact Or.inl (hsr v hv)
    · exact Or.inr hv
  have hxvars₁ : ∀ v ∈ x₁.vars, NotFresh v ∨ FreshIn n next v := by
    intro v hv
    rcases flat_id_cases l n with ⟨hx, -, -⟩ | ⟨k, hx, hk₁, hk₂, -⟩
    · rw [h₁] at hx; simp only at hx
      rw [hx] at hv
      exact Or.inl (hsl v hv)
    · rw [h₁] at hx hk₂; simp only at hx hk₂
      rw [hx, Expr.vars_var, List.mem_singleton] at hv
      exact Or.inr ⟨k, hk₁, hk₂, hv⟩
  have hxvars₂ : ∀ v ∈ x₂.vars, NotFresh v ∨ FreshIn next last v := by
    intro v hv
    rcases flat_id_cases r next with ⟨hx, -, -⟩ | ⟨k, hx, hk₁, hk₂, -⟩
    · rw [h₂] at hx; simp only at hx
      rw [hx] at hv
      exact Or.inl (hsr v hv)
    · rw [h₂] at hx hk₂; simp only at hx hk₂
      rw [hx, Expr.vars_var, List.mem_singleton] at hv
      exact Or.inr ⟨k, hk₁, hk₂, hv⟩
  obtain ⟨hxe₁', hx₁'⟩ := Expr.Matches.of_agreeOn ⟨hxe₁, hx₁⟩
    fun v hv => (hagree₁ v (hxvars₁ v hv)).symm
  obtain ⟨hxe₂', hx₂'⟩ := Expr.Matches.of_agreeOn ⟨hxe₂, hx₂⟩
    fun v hv => (hagree₂ v (hxvars₂ v hv)).symm
  refine ⟨ρ₁ ++ ρ₂, hfr₁.append hfr₂ hn hm', ?_, ?_, hx₁', hx₂', hxe₁', hxe₂'⟩
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hval₁ b hb
    · exact hval₂ b hb
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact (hatoms₁ q hq).of_agreeOn fun v hv => (hagree₁ v (hvars₁ q hq v hv)).symm
    · exact (hatoms₂ q hq).of_agreeOn fun v hv => (hagree₂ v (hvars₂ q hq v hv)).symm

/-- The value of a matching source expression exists in the source. -/
theorem cong_self_of_matches {σ : Env} (hreps : ∀ b ∈ σ, b.2 ∈ src.reps) {e : Expr} {t : Term}
    (hm : Expr.Matches src σ e) (he : e.eval σ = some t) : Cong src t t :=
  Expr.Matches.eval_cong
    (fun v t hvt => Database.toCong (hreps (v, t) (Env.mem_of_lookup hvt)).1) ⟨he, hm⟩

theorem complete_pattern (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {p : Pattern} (n : Nat)
    (ho : p.MinOverVars) (hsc : p.Scoped) (hnames : ∀ e ∈ p.exprs, SrcNames e)
    (hsrc : ∀ v ∈ p.vars, NotFresh v) {σ : Env} (hσ : NoFreshDom σ)
    (hreps : ∀ b ∈ σ, b.2 ∈ src.reps) (hm : Matches src p σ) :
    ∃ ρ, Fresh n (encodePatternWith {} p n).2 ρ ∧ (∀ b ∈ ρ, b.2 ∈ d.terms) ∧
      ∀ q ∈ (encodePatternWith {} p n).1, Matches d q (σ ++ ρ) := by
  cases hm with
  | @atom e _ hl =>
    cases e with
    | app f args =>
      obtain ⟨ρ, hfr, hval, hatoms, -⟩ :=
        complete_expr h hc hw (.app f args) n ho (hnames _ (by simp [Pattern.exprs])) hsrc hσ
          hreps hl
      exact ⟨ρ, hfr, hval, hatoms⟩
    | lit _ => exact hsc.elim
    | var _ => exact hsc.elim
    | min _ _ => exact hsc.elim
  | @equal l r _ t₁ t₂ hl hr hev₁ hev₂ hcong =>
    obtain ⟨hol, hor⟩ := Pattern.minOverVars_eq ho
    have hsrc₁ : ∀ v ∈ l.vars, NotFresh v := fun v hv => hsrc v (by simp [Pattern.vars, hv])
    have hsrc₂ : ∀ v ∈ r.vars, NotFresh v := fun v hv => hsrc v (by simp [Pattern.vars, hv])
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    obtain ⟨ρ, hfr, hval, hatoms, hx₁, hx₂, hxe₁, hxe₂⟩ := complete_sides h hc hw n hol hor
      (hnames l (by simp [Pattern.exprs])) (hnames r (by simp [Pattern.exprs])) hsrc₁ hsrc₂ hσ
      hreps hl hr hev₁ hev₂ h₁ h₂
    rw [pattern_eq h₁ h₂]
    refine ⟨ρ, hfr, hval, ?_⟩
    simp only
    intro q hq
    rw [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hatoms q hq
    · refine matches_eq_iff.mpr ⟨srep src t₁, srep src t₂, hx₁, hx₂, hxe₁, hxe₂, ?_⟩
      rw [srep_eq_of_cong h.src_hasReps hcong]
      exact Database.toCong (h.src_mem_terms
        (srep_mem_terms h.src_hasReps (hcong.symm.trans hcong)))
  | @unequal l r _ t₁ t₂ hl hr hev₁ hev₂ hncong =>
    obtain ⟨hol, hor⟩ := Pattern.minOverVars_ne ho
    have hsrc₁ : ∀ v ∈ l.vars, NotFresh v := fun v hv => hsrc v (by simp [Pattern.vars, hv])
    have hsrc₂ : ∀ v ∈ r.vars, NotFresh v := fun v hv => hsrc v (by simp [Pattern.vars, hv])
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    obtain ⟨ρ, hfr, hval, hatoms, hx₁, hx₂, hxe₁, hxe₂⟩ := complete_sides h hc hw n hol hor
      (hnames l (by simp [Pattern.exprs])) (hnames r (by simp [Pattern.exprs])) hsrc₁ hsrc₂ hσ
      hreps hl hr hev₁ hev₂ h₁ h₂
    rw [pattern_ne h₁ h₂]
    refine ⟨ρ, hfr, hval, ?_⟩
    simp only
    intro q hq
    rw [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hatoms q hq
    · -- The two representatives are one term only if the source values are congruent.
      refine matches_ne_iff.mpr ⟨srep src t₁, srep src t₂, hx₁, hx₂, hxe₁, hxe₂,
        fun hcd => hncong ?_⟩
      have heq : srep src t₁ = srep src t₂ := hcd.eq_of_diag h.diag
      have hs₁ := (srep_spec h.src_hasReps (cong_self_of_matches hreps hl hev₁)).2
      have hs₂ := (srep_spec h.src_hasReps (cong_self_of_matches hreps hr hev₂)).2
      rw [← heq] at hs₂
      exact hs₁.trans hs₂.symm

theorem complete_query (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {q : Query} (n : Nat)
    (hq : QueryOk q) {σ : Env} (hσ : NoFreshDom σ) (hreps : ∀ b ∈ σ, b.2 ∈ src.reps)
    (hm : ∀ p ∈ q, Matches src p σ) :
    ∃ ρ, Fresh n (encodeQueryWith {} q n).2 ρ ∧ (∀ b ∈ ρ, b.2 ∈ d.terms) ∧
      ∀ p ∈ (encodeQueryWith {} q n).1, Matches d p (σ ++ ρ) := by
  induction q generalizing n with
  | nil => exact ⟨[], Fresh.nil n, by simp, by rw [query_nil]; simp⟩
  | cons p ps ih =>
    obtain ⟨ρ₁, hfr₁, hval₁, hatoms₁⟩ := complete_pattern h hc hw n (hq.minOverVars p (by simp))
      (hq.shape p (by simp)) (hq.names p (by simp)) hq.head_vars hσ hreps (hm p (by simp))
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rw [h₁] at hfr₁ hatoms₁
    simp only at hfr₁ hatoms₁
    obtain ⟨ρ₂, hfr₂, hval₂, hatoms₂⟩ := ih next hq.tail (fun p hp => hm p (by simp [hp]))
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    rw [h₂] at hfr₂ hatoms₂
    simp only at hfr₂ hatoms₂
    have hn := pattern_next_le p n
    have hm' := query_next_le ps next
    rw [h₁] at hn
    rw [h₂] at hm'
    simp only at hn hm'
    have hvars₁ : ∀ q ∈ qs, ∀ v ∈ q.vars, NotFresh v ∨ FreshIn n next v := by
      intro q hq' v hv
      have := (pattern_vars_iff (hq.shape p (by simp)) n (v := v)).mp
        (by rw [h₁]; exact Query.mem_vars.mpr ⟨q, hq', hv⟩)
      rw [h₁] at this
      rcases this with hv | hv
      · exact Or.inl (hq.head_vars v hv)
      · exact Or.inr hv
    have hvars₂ : ∀ q ∈ rest, ∀ v ∈ q.vars, NotFresh v ∨ FreshIn next last v := by
      intro q hq' v hv
      have := (query_vars_iff hq.tail.shape next (v := v)).mp
        (by rw [h₂]; exact Query.mem_vars.mpr ⟨q, hq', hv⟩)
      rw [h₂] at this
      rcases this with hv | hv
      · exact Or.inl (hq.tail.vars v hv)
      · exact Or.inr hv
    refine ⟨ρ₁ ++ ρ₂, ?_, ?_, ?_⟩
    · rw [query_cons h₁ h₂]
      exact hfr₁.append hfr₂ hn hm'
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hval₁ b hb
      · exact hval₂ b hb
    · rw [query_cons h₁ h₂]
      simp only
      intro q hq'
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact (hatoms₁ q hq').of_agreeOn fun v hv =>
          (lookup_left hfr₂ (not_freshIn_right (hvars₁ q hq' v hv))).symm
      · exact (hatoms₂ q hq').of_agreeOn fun v hv =>
          (lookup_right hfr₁ (not_freshIn_left (hvars₂ q hq' v hv))).symm

/-! ### Rule firings -/

/-- A source match of a rule's query extends to a match of the compiled query, agreeing on
the source variables. -/
theorem fire_complete (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {q : Query}
    (hq : QueryOk q) {σ : Env} (hm : QueryMatches src q σ) :
    ∃ σ', QueryMatches d (encodeQueryWith {} q 0).1 σ' ∧
      ∀ v ∈ Query.vars q, Env.lookup v σ' = Env.lookup v σ := by
  have hdom : ∀ v ∈ Env.dom σ, NotFresh v := fun v hv => hq.vars v (hm.1.1.mem_iff.mp hv)
  have hσ : NoFreshDom σ := noFreshDom_of_notFresh hdom
  obtain ⟨ρ, hfr, hval, hatoms⟩ := complete_query h hc hw 0 hq hσ hm.1.2 hm.2
  refine ⟨σ ++ ρ, ⟨⟨?_, ?_⟩, hatoms⟩, fun v hv => ?_⟩
  · have hnd : (Env.dom (σ ++ ρ)).Nodup := by
      rw [Env.dom_append]
      refine List.Nodup.append (hm.1.1.symm.nodup (Query.vars_nodup q)) hfr.nodup ?_
      intro v hv₁ hv₂
      obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hv₂
      obtain ⟨k, -, -, hk⟩ := hfr.fresh _ ht
      exact hdom v hv₁ k hk
    rw [List.perm_ext_iff_of_nodup hnd (Query.vars_nodup _)]
    intro v
    rw [query_vars_iff hq.shape 0, Env.dom_append, List.mem_append, hm.1.1.mem_iff]
    apply or_congr_right
    constructor
    · intro hv
      obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hv
      exact hfr.fresh _ ht
    · rintro ⟨k, hk₁, hk₂, rfl⟩
      exact hfr.complete k hk₁ hk₂
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact h.src_mem_reps (hm.1.2 b hb).1
    · exact mem_reps_of_diag h.diag (hval b hb)
  · exact lookup_src hfr (hq.vars v hv)

/-- The restriction of a substitution to a list of variables. -/
def restrict (vs : List Var) (σ : Env) : Env :=
  vs.filterMap fun v => (Env.lookup v σ).map (v, ·)

theorem mem_restrict {vs : List Var} {σ : Env} {b : Var × Term} (h : b ∈ restrict vs σ) :
    b.1 ∈ vs ∧ Env.lookup b.1 σ = some b.2 := by
  obtain ⟨v, hv, hb⟩ := List.mem_filterMap.mp h
  cases hlk : Env.lookup v σ with
  | none => rw [hlk] at hb; simp at hb
  | some t =>
    rw [hlk] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    exact ⟨hb ▸ hv, hb ▸ hlk⟩

theorem dom_restrict {vs : List Var} {σ : Env} (h : ∀ v ∈ vs, (Env.lookup v σ).isSome) :
    Env.dom (restrict vs σ) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h v (by simp))
    simp only [restrict, List.filterMap_cons, ht, Option.map_some, Env.dom, List.map_cons,
      List.cons.injEq, true_and]
    exact ih fun w hw => h w (by simp [hw])

theorem lookup_restrict {vs : List Var} {σ : Env} (hnd : vs.Nodup) {v : Var} (hv : v ∈ vs) :
    Env.lookup v (restrict vs σ) = Env.lookup v σ := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    rw [List.nodup_cons] at hnd
    cases hlk : Env.lookup w σ with
    | none =>
      simp only [restrict, List.filterMap_cons, hlk, Option.map_none]
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hlk]
        apply Env.lookup_eq_none_iff.mpr
        intro hmem
        obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hmem
        exact hnd.1 (mem_restrict ht).1
      · exact ih hnd.2 hv
    | some t =>
      simp only [restrict, List.filterMap_cons, hlk, Option.map_some, Env.lookup_cons]
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [hlk]
      · rw [if_neg (fun hc : v = w => hnd.1 (hc ▸ hv))]
        exact ih hnd.2 hv

/-- A match of the compiled query restricts to a source match that binds every source
variable to its root, a source representative. -/
theorem fire_sound (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {q : Query} (hq : QueryOk q)
    (hkeyed : Query.VarsKeyed q) {σ' : Env} (hm : QueryMatches d (encodeQueryWith {} q 0).1 σ') :
    QueryMatches src q (restrict (Query.vars q) σ') ∧
      ∀ v ∈ Query.vars q, Env.lookup v (restrict (Query.vars q) σ') = Env.lookup v σ' := by
  have hbound : ∀ v ∈ Query.vars q, (Env.lookup v σ').isSome := by
    intro v hv
    apply Env.lookup_isSome_iff_mem_dom.mpr
    exact hm.1.1.mem_iff.mpr ((query_vars_iff hq.shape 0).mpr (Or.inl hv))
  have hlook : ∀ v ∈ Query.vars q, Env.lookup v (restrict (Query.vars q) σ') = Env.lookup v σ' :=
    fun v hv => lookup_restrict (Query.vars_nodup q) hv
  -- Every source variable is read through a live edge, so it is bound to a root.
  have hroots : ∀ v t, v ∈ Query.vars q → Env.lookup v σ' = some t → t ∈ src.reps := by
    intro v t hv ht
    obtain ⟨p, hp, hpv⟩ := hkeyed v hv
    obtain ⟨a, ha⟩ := query_argVar_atom 0 hq.minOverVars hp hpv
    obtain ⟨a', t', ha', ht', hedge⟩ := matches_uf_var_var_iff.mp (hm.2 _ ha)
    obtain rfl : t = t' := Option.some.inj (ht.symm.trans ht')
    exact ((h.edge_iff_rep hc hw (h.key_of_edge hedge)).mp hedge).1
  have hval : ∀ b ∈ restrict (Query.vars q) σ', b.2 ∈ src.reps := by
    intro b hb
    obtain ⟨hv, hlk⟩ := mem_restrict hb
    exact hroots b.1 b.2 hv hlk
  refine ⟨⟨⟨by rw [dom_restrict hbound], hval⟩, ?_⟩, hlook⟩
  -- The canonical state reads every live edge to a representative.
  have hne : NeSound src d (restrict (Query.vars q) σ') σ' :=
    ⟨hw, fun k p he => ((h.edge_iff_rep hc hw (h.key_of_edge he)).mp he).1,
      fun v t hvt => hval (v, t) (Env.mem_of_lookup hvt),
      fun v t hvt => (hm.1.2 (v, t) (Env.mem_of_lookup hvt)).1⟩
  apply sound_query (h.reads hc hw) 0 hq.minOverVars hq.shape hq.names (Or.inr hne)
    (σ := restrict (Query.vars q) σ') (fun v hv => (hlook v hv).symm)
    (fun v t hvt => (hval (v, t) (Env.mem_of_lookup hvt)).1) hm.2

end Egglog.Congruence
