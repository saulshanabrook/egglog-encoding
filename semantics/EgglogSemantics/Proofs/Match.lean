import EgglogSemantics.Spec.Match
import EgglogSemantics.Proofs.Eval

/-- Every element of a `Forall₂`'s right list is related to one of the left's. -/
theorem List.Forall₂.exists_left {α β : Type*} {R : α → β → Prop} {as : List α}
    {bs : List β} (h : List.Forall₂ R as bs) {b : β} (hb : b ∈ bs) : ∃ a ∈ as, R a b := by
  induction h with
  | nil => simp at hb
  | @cons a b' as bs hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨a', ha', hR⟩ := ih hb
      exact ⟨a', by simp [ha'], hR⟩

namespace Egglog
namespace Expr
@[simp] theorem freeVars_lit {l : Lit} {σ : Env} : (Expr.lit l).freeVars σ = [] := rfl

@[simp] theorem freeVars_var {v : Var} {σ : Env} :
    (Expr.var v).freeVars σ = if (Env.lookup v σ).isSome then [] else [v] := rfl

@[simp] theorem freeVars_app {f : FnName} {args : List Expr} {σ : Env} :
    (Expr.app f args).freeVars σ = Expr.freeVarsList args σ := rfl

@[simp] theorem freeVarsList_nil {σ : Env} : Expr.freeVarsList [] σ = [] := rfl

@[simp] theorem freeVarsList_cons {e : Expr} {es : List Expr} {σ : Env} :
    Expr.freeVarsList (e :: es) σ = e.freeVars σ ∪ Expr.freeVarsList es σ := rfl

theorem freeVars_var_of_some {v : Var} {σ : Env} {t : Term} (h : Env.lookup v σ = some t) :
    (Expr.var v).freeVars σ = [] := by
  change (if (Env.lookup v σ).isSome then _ else _) = _
  rw [h]; rfl

theorem freeVars_var_of_none {v : Var} {σ : Env} (h : Env.lookup v σ = none) :
    (Expr.var v).freeVars σ = [v] := by
  change (if (Env.lookup v σ).isSome then _ else _) = _
  rw [h]; rfl

end Expr
theorem Query.mem_vars {v : Var} {q : Query} : v ∈ Query.vars q ↔ ∃ p ∈ q, v ∈ p.vars := by
  induction q with
  | nil => simp
  | cons p ps ih => simp only [vars_cons, List.mem_union_iff, List.mem_cons, ih]; aesop

mutual

/-- `freeVars` is `vars` minus the environment's domain. -/
theorem Expr.mem_freeVars {σ : Env} {v : Var} (e : Expr) :
    v ∈ e.freeVars σ ↔ v ∈ e.vars ∧ v ∉ Env.dom σ := by
  match e with
  | .lit _ => simp
  | .var w =>
    cases hlk : Env.lookup w σ with
    | some t =>
      have hw : w ∈ Env.dom σ := Env.lookup_isSome_iff_mem_dom.mp (by simp [hlk])
      rw [Expr.freeVars_var_of_some hlk, Expr.vars_var]
      constructor
      · intro h; simp at h
      · rintro ⟨hv, hvd⟩
        rw [List.mem_singleton] at hv
        subst hv
        exact absurd hw hvd
    | none =>
      have hw : w ∉ Env.dom σ := Env.lookup_eq_none_iff.mp hlk
      rw [Expr.freeVars_var_of_none hlk, Expr.vars_var]
      refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
      rw [List.mem_singleton] at h
      subst h
      exact hw
  | .app _ args => exact Expr.mem_freeVarsList args

theorem Expr.mem_freeVarsList {σ : Env} {v : Var} (es : List Expr) :
    v ∈ Expr.freeVarsList es σ ↔ v ∈ Expr.varsList es ∧ v ∉ Env.dom σ := by
  match es with
  | [] => simp
  | e :: es =>
    rw [Expr.freeVarsList_cons, Expr.varsList_cons, List.mem_union_iff, List.mem_union_iff,
      Expr.mem_freeVars e, Expr.mem_freeVarsList es]
    tauto

end

theorem Pattern.mem_freeVars {σ : Env} {v : Var} (p : Pattern) :
    v ∈ p.freeVars σ ↔ v ∈ p.vars ∧ v ∉ Env.dom σ := by
  cases p with
  | expr e => exact e.mem_freeVars
  | eq e₁ e₂ =>
    rw [Pattern.freeVars, Pattern.vars, List.mem_union_iff, List.mem_union_iff,
      Expr.mem_freeVars e₁, Expr.mem_freeVars e₂]
    tauto
  | values vs _ as =>
    rw [Pattern.freeVars, Pattern.vars, List.mem_union_iff, List.mem_union_iff,
      Expr.mem_freeVarsList vs, Expr.mem_freeVarsList as]
    tauto

/-- A free variable is by definition unbound, so a substitution over an expression's
free variables has a domain disjoint from the environment's. That is why appending
the two never fails, where `Env.Union2` can. -/
theorem Pattern.freeVars_lookup_eq_none {σ : Env} {v : Var} (p : Pattern)
    (h : v ∈ p.freeVars σ) : Env.lookup v σ = none :=
  Env.lookup_eq_none_iff.mpr (p.mem_freeVars.mp h).2

theorem Expr.freeVars_lookup_eq_none {σ : Env} {v : Var} (e : Expr)
    (h : v ∈ e.freeVars σ) : Env.lookup v σ = none :=
  Env.lookup_eq_none_iff.mpr (e.mem_freeVars.mp h).2

mutual

/-- `freeVars` never repeats a variable: it is built with `List.union`, which dedups. -/
theorem Expr.freeVars_nodup (e : Expr) (σ : Env) : (e.freeVars σ).Nodup := by
  match e with
  | .lit _ => simp
  | .var v =>
    cases hlk : Env.lookup v σ with
    | none => rw [Expr.freeVars_var_of_none hlk]; simp
    | some t => rw [Expr.freeVars_var_of_some hlk]; simp
  | .app _ args => exact Expr.freeVarsList_nodup args σ

theorem Expr.freeVarsList_nodup (es : List Expr) (σ : Env) :
    (Expr.freeVarsList es σ).Nodup := by
  match es with
  | [] => simp
  | e :: es => exact List.Nodup.union _ (Expr.freeVarsList_nodup es σ)

end

theorem Pattern.freeVars_nodup (p : Pattern) (σ : Env) : (p.freeVars σ).Nodup := by
  cases p with
  | expr e => exact e.freeVars_nodup σ
  | eq _ e₂ => exact List.Nodup.union _ (e₂.freeVars_nodup σ)
  | values _ _ as => exact List.Nodup.union _ (Expr.freeVarsList_nodup as σ)

namespace Env
/-- The union binds exactly what its operands bind: `Union2` appends, and only
constrains the terms. -/
theorem UnionAll.mem_iff {σs : List Env} {σ : Env} (h : UnionAll σs σ)
    {b : Var × Term} : b ∈ σ ↔ ∃ σ' ∈ σs, b ∈ σ' := by
  induction h with
  | nil => simp
  | single σ => simp
  | step hu _ ih =>
    rw [ih, hu.2]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨σ', rfl | hσ', hb⟩
      · rcases List.mem_append.mp hb with hb | hb
        · exact ⟨_, Or.inl rfl, hb⟩
        · exact ⟨_, Or.inr (Or.inl rfl), hb⟩
      · exact ⟨σ', Or.inr (Or.inr hσ'), hb⟩
    · rintro ⟨σ', rfl | rfl | hσ', hb⟩
      · exact ⟨_, Or.inl rfl, List.mem_append.mpr (Or.inl hb)⟩
      · exact ⟨_, Or.inl rfl, List.mem_append.mpr (Or.inr hb)⟩
      · exact ⟨σ', Or.inr hσ', hb⟩

/-- Anything true of every binding of every operand is true of the union's. -/
theorem UnionAll.forall_mem {P : Var × Term → Prop} {σs : List Env} {σ : Env}
    (h : UnionAll σs σ) (hs : ∀ σ' ∈ σs, ∀ b ∈ σ', P b) : ∀ b ∈ σ, P b := by
  intro b hb
  obtain ⟨σ', hσ', hb⟩ := h.mem_iff.mp hb
  exact hs σ' hσ' b hb

theorem UnionAll.mem_dom_iff {σs : List Env} {σ : Env} (h : UnionAll σs σ) {v : Var} :
    v ∈ dom σ ↔ ∃ σ' ∈ σs, v ∈ dom σ' := by
  simp only [Env.mem_dom_iff]
  constructor
  · rintro ⟨t, hb⟩
    obtain ⟨σ', hσ', hb⟩ := h.mem_iff.mp hb
    exact ⟨σ', hσ', t, hb⟩
  · rintro ⟨σ', hσ', t, hb⟩
    exact ⟨t, h.mem_iff.mpr ⟨σ', hσ', hb⟩⟩

/-- Every binding of `τ` is one `σ` also makes. The substitutions the enumerator restricts
out of a query substitution all refine it, which is what makes them pairwise compatible. -/
def Refines (τ σ : Env) : Prop := ∀ b ∈ τ, lookup b.1 σ = some b.2

theorem Refines.nil {σ : Env} : Refines [] σ := by simp [Refines]

theorem Refines.append {τ₁ τ₂ σ : Env} (h₁ : Refines τ₁ σ) (h₂ : Refines τ₂ σ) :
    Refines (τ₁ ++ τ₂) σ := fun b hb =>
  (List.mem_append.mp hb).elim (h₁ b) (h₂ b)

/-- Two substitutions refining a common one are compatible, so their union succeeds. -/
theorem Refines.union2 {τ₁ τ₂ σ : Env} (h₁ : Refines τ₁ σ) (h₂ : Refines τ₂ σ) :
    Union2 τ₁ τ₂ (τ₁ ++ τ₂) := by
  refine ⟨fun b hb t ht => ?_, rfl⟩
  have := h₂ (b.1, t) (mem_of_lookup ht)
  rw [h₁ b hb] at this
  exact (Option.some.injEq .. ▸ this : b.2 = t)

/-- A list of substitutions all refining `σ` has a union, which refines `σ` too. -/
theorem exists_unionAll {σ : Env} : ∀ σs : List Env, (∀ τ ∈ σs, Refines τ σ) →
    ∃ τ, UnionAll σs τ ∧ Refines τ σ
  | [], _ => ⟨[], .nil, Refines.nil⟩
  | [τ], h => ⟨τ, .single τ, h τ (by simp)⟩
  | τ₁ :: τ₂ :: rest, h => by
    have h₁ := h τ₁ (by simp)
    have h₂ := h τ₂ (by simp)
    obtain ⟨τ, hu, hr⟩ := exists_unionAll ((τ₁ ++ τ₂) :: rest) (by
      intro ρ hρ
      rcases List.mem_cons.mp hρ with rfl | hρ
      · exact h₁.append h₂
      · exact h ρ (by simp [hρ]))
    exact ⟨τ, .step (h₁.union2 h₂) hu, hr⟩
  termination_by σs => σs.length

theorem Refines.trans {ρ ρ' τ : Env} (h₁ : Refines ρ ρ') (h₂ : Refines ρ' τ) :
    Refines ρ τ := fun b hb => h₂ (b.1, b.2) (mem_of_lookup (h₁ b hb))

/-- A substitution binding no variable twice refines itself. This is the form of
"no duplicates" that survives being unioned, where `Nodup` does not: appending two
substitutions that share a variable duplicates it. -/
theorem Refines.self_of_nodup {σ : Env} (h : (dom σ).Nodup) : Refines σ σ :=
  fun _ hb => (lookup_eq_some_iff_mem h).mpr hb

theorem Refines.append_left {σ₁ σ₂ : Env} (h₁ : Refines σ₁ σ₁) : Refines σ₁ (σ₁ ++ σ₂) :=
  fun b hb => by rw [lookup_append_of_mem (mem_dom_of_mem hb)]; exact h₁ b hb

theorem Refines.append_right {σ₁ σ₂ : Env} (h₂ : Refines σ₂ σ₂)
    (hc : ∀ b ∈ σ₁, ∀ t, lookup b.1 σ₂ = some t → b.2 = t) : Refines σ₂ (σ₁ ++ σ₂) := by
  intro b hb
  by_cases hv : b.1 ∈ dom σ₁
  · rw [lookup_append_of_mem hv]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (lookup_isSome_iff_mem_dom.mpr hv)
    rw [hu]
    exact congrArg some (hc (b.1, u) (mem_of_lookup hu) b.2 (h₂ b hb))
  · rw [lookup_append_of_not_mem hv]
    exact h₂ b hb

/-- Every operand's bindings are reachable in the union.

The induction needs self-refinement rather than `Nodup`, since appending two substitutions
that share a variable duplicates it in the domain while leaving every lookup intact. -/
theorem UnionAll.refines_of_mem {σs : List Env} {τ : Env} (h : UnionAll σs τ) :
    (∀ ρ ∈ σs, Refines ρ ρ) → (∀ ρ ∈ σs, Refines ρ τ) ∧ Refines τ τ := by
  induction h with
  | nil => exact fun _ => ⟨by simp, Refines.nil⟩
  | single σ =>
    refine fun hsc => ⟨fun ρ hρ => ?_, hsc σ (by simp)⟩
    rw [List.mem_singleton] at hρ
    subst hρ
    exact hsc ρ (by simp)
  | @step σ₁ σ₂ σr σ σs hu _ ih =>
    intro hsc
    have h₁ := hsc σ₁ (by simp)
    have h₂ := hsc σ₂ (by simp)
    have hr₁ : Refines σ₁ σr := hu.2 ▸ Refines.append_left h₁
    have hr₂ : Refines σ₂ σr := hu.2 ▸ Refines.append_right h₂ hu.1
    have hsr : Refines σr σr := fun b hb =>
      (List.mem_append.mp (hu.2 ▸ hb : b ∈ σ₁ ++ σ₂)).elim (fun hb => hr₁ b hb)
        (fun hb => hr₂ b hb)
    obtain ⟨hall, hτ⟩ := ih (by
      intro ρ hρ
      rcases List.mem_cons.mp hρ with rfl | hρ
      · exact hsr
      · exact hsc ρ (by simp [hρ]))
    refine ⟨fun ρ hρ => ?_, hτ⟩
    rcases List.mem_cons.mp hρ with rfl | hρ
    · exact hr₁.trans (hall σr (by simp))
    rcases List.mem_cons.mp hρ with rfl | hρ
    · exact hr₂.trans (hall σr (by simp))
    · exact hall ρ (by simp [hρ])

/-- A substitution that refines `σ` and binds everything `σ` binds is indistinguishable
from it. -/
theorem agree_of_refines {τ σ : Env} (hr : Refines τ σ) (hd : dom σ ⊆ dom τ) :
    Agree τ σ := by
  intro v
  cases hlk : lookup v τ with
  | some t => exact (hr (v, t) (mem_of_lookup hlk)).symm
  | none =>
    rw [lookup_eq_none_iff] at hlk
    exact (lookup_eq_none_iff.mpr fun hc => hlk (hd hc)).symm

end Env
/-- Every element of a list is related to its image. -/
theorem List.forall₂_map_self {α β : Type*} {R : α → β → Prop} {f : α → β} {l : List α}
    (h : ∀ a ∈ l, R a (f a)) : List.Forall₂ R l (l.map f) := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

namespace ValidEnv
variable {vars : List Var} {db : Database} {σ : Env}

theorem mem_terms (h : ValidEnv vars db σ) : ∀ b ∈ σ, b.2 ∈ db.terms := h.2

theorem mem_dom_iff (h : ValidEnv vars db σ) {v : Var} : v ∈ Env.dom σ ↔ v ∈ vars :=
  h.1.mem_iff

/-- A substitution over variables the globals do not bind is compatible with the
globals, so unioning the two cannot fail. -/
theorem compatible (h : ValidEnv vars db σ)
    (hvars : ∀ v ∈ vars, Env.lookup v db.env = none) :
    ∀ b ∈ db.env, ∀ t, Env.lookup b.1 σ = some t → b.2 = t := by
  intro b hb t ht
  have hσ : b.1 ∈ Env.dom σ := Env.lookup_isSome_iff_mem_dom.mp (by simp [ht])
  exact absurd (Env.mem_dom_of_mem hb)
    (Env.lookup_eq_none_iff.mp (hvars b.1 (h.mem_dom_iff.mp hσ)))

theorem union2_env (h : ValidEnv vars db σ)
    (hvars : ∀ v ∈ vars, Env.lookup v db.env = none) :
    Env.Union2 db.env σ (db.env ++ σ) :=
  ⟨h.compatible hvars, rfl⟩

end ValidEnv
/-! ### Reading `CongOn` back as an `addTerm`

The two shapes `Matches` uses, unfolded to the `addTerm` chain every congruence lemma is
stated at. Both are `Iff.rfl`: `withOperands` at a list *literal* is a fold that reduces,
so `CongOn db [t]` and `CongOn db [t₁, t₂]` *are* `Cong (db.addTerm t)` and
`Cong ((db.addTerm t₁).addTerm t₂)`. -/

theorem congOn_singleton {db : Database} {t a b : Term} :
    CongOn db [t] a b ↔ Cong (db.addTerm t) a b := Iff.rfl

theorem congOn_pair {db : Database} {t₁ t₂ a b : Term} :
    CongOn db [t₁, t₂] a b ↔ Cong ((db.addTerm t₁).addTerm t₂) a b := Iff.rfl

/-! ### Matched substitutions

The e-matcher's API, on the one matching relation there is. `ValidEnv` per pattern,
unioned: `RuleResults.wf` needs it, because a firing runs its head in the caller's
environment extended by the substitution and that invariant asks that every value there be
a term the database already holds. -/
namespace ValidSubst
variable {db : Database} {p : Pattern} {σ : Env}

/-- The hypothesis `patternHolds_validSubst` adds is a consequence of its conclusion,
which is why requiring it costs nothing. Since the hoist it is the left conjunct. -/
theorem validEnv (h : ValidSubst db p σ) : ValidEnv (p.freeVars db.env) db σ := h.1

theorem mem_terms (h : ValidSubst db p σ) : ∀ b ∈ σ, b.2 ∈ db.terms :=
  h.validEnv.mem_terms

/-- Appending a matching substitution to the globals cannot fail. -/
theorem union2_env (h : ValidSubst db p σ) : Env.Union2 db.env σ (db.env ++ σ) :=
  h.validEnv.union2_env fun _ hv => p.freeVars_lookup_eq_none hv

/-- A matching substitution binds exactly the pattern's free variables. -/
theorem mem_dom_iff (h : ValidSubst db p σ) {v : Var} :
    v ∈ Env.dom σ ↔ v ∈ p.freeVars db.env :=
  h.validEnv.mem_dom_iff

end ValidSubst
/-- `ValidSubst` transfers along agreement, provided the new substitution has exactly the
pattern's free variables as its domain.

Agreement alone is not enough, because `ValidEnv` pins the domain — which is precisely why
an executable enumerator has to canonicalize rather than emit any agreeing representative. -/
theorem ValidSubst.of_agree {db : Database} {p : Pattern} {σ σ' : Env}
    (h : ValidSubst db p σ) (hag : Env.Agree σ σ')
    (hdom : Env.dom σ' = p.freeVars db.env) : ValidSubst db p σ' := by
  have hterms : ∀ b ∈ σ', b.2 ∈ db.terms := by
    intro b hb
    have hnd : (Env.dom σ').Nodup := hdom ▸ p.freeVars_nodup db.env
    have hlk : Env.lookup b.1 σ' = some b.2 := (Env.lookup_eq_some_iff_mem hnd).mpr hb
    rw [← hag b.1] at hlk
    exact h.mem_terms _ (Env.mem_of_lookup hlk)
  have hperm : (Env.dom σ').Perm (p.freeVars db.env) := hdom ▸ List.Perm.refl _
  have hev : ∀ e : Expr, e.eval db.sig (db.env ++ σ') = e.eval db.sig (db.env ++ σ) :=
    fun e => Expr.eval_agree (Env.Agree.append_left db.env hag.symm) e
  have hevl : ∀ es : List Expr,
      Expr.evalList db.sig es (db.env ++ σ') = Expr.evalList db.sig es (db.env ++ σ) :=
    fun es => Expr.evalList_agree (Env.Agree.append_left db.env hag.symm) es
  refine ⟨⟨hperm, hterms⟩, ?_⟩
  cases h.2 with
  | expr hwm he hc => exact .expr hwm (by rw [hev]; exact he) hc
  | eq hwm he₁ he₂ hc₁ hc₂ =>
    exact .eq hwm (by rw [hev]; exact he₁) (by rw [hev]; exact he₂) hc₁ hc₂
  | values hwm hts hus hc =>
    exact .values hwm (by rw [hevl]; exact hts) (by rw [hevl]; exact hus) hc

namespace ValidQuerySubst
variable {db : Database} {q : Query} {σ : Env}

/-- Every value a query substitution binds is a term the database holds — `ValidEnv` per
pattern, unioned. -/
theorem mem_terms (h : ValidQuerySubst db q σ) : ∀ b ∈ σ, b.2 ∈ db.terms := by
  obtain ⟨σs, hall, hu⟩ := h
  refine hu.forall_mem fun σ' hσ' b hb => ?_
  obtain ⟨p, _, hv⟩ := hall.exists_left hσ'
  exact hv.mem_terms b hb

/-- A query substitution binds exactly the query's free variables. -/
theorem mem_dom_iff (h : ValidQuerySubst db q σ) {v : Var} :
    v ∈ Env.dom σ ↔ ∃ p ∈ q, v ∈ p.freeVars db.env := by
  obtain ⟨σs, hall, hu⟩ := h
  rw [hu.mem_dom_iff]
  constructor
  · rintro ⟨σ', hσ', hv⟩
    obtain ⟨p, hp, hvs⟩ := hall.exists_left hσ'
    exact ⟨p, hp, hvs.mem_dom_iff.mp hv⟩
  · rintro ⟨p, hp, hv⟩
    obtain ⟨σ', hσ', hvs⟩ := hall.flip.exists_left hp
    exact ⟨σ', hσ', (ValidSubst.mem_dom_iff hvs).mpr hv⟩

/-- The empty query is satisfied by exactly the empty substitution: a rule with no
patterns fires once. -/
theorem nil_iff : ValidQuerySubst db [] σ ↔ σ = [] := by
  constructor
  · rintro ⟨σs, hall, hu⟩
    cases hall
    cases hu
    rfl
  · rintro rfl
    exact ⟨[], .nil, .nil⟩

end ValidQuerySubst
end Egglog
