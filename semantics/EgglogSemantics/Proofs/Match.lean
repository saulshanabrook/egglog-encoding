import EgglogSemantics.Spec.Match
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Proofs.SameMeaning
import EgglogSemantics.Proofs.SemanticCong

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

namespace Matches

/-- Stored witnesses recover the equivalent matching presentation used in compiler proofs. -/
theorem expr {db : Database} {e : Expr} {σ : Env} {w t : Term}
    (hw : w ∈ db.terms) (he : e.eval σ = some t)
    (hc : StoredCongOn db [t] w t) : Matches db (.expr e) σ := by
  apply Matches.atom he
  apply InferredFacts.congr_iff_infers.mpr
  have hc' : StoredCongOn db [t, t] w t := by
    simpa [StoredCongOn, Database.withOperands, Database.addTerms, Database.addTerm] using hc
  exact ⟨w, hw, hc', hc'.symm.trans hc'⟩

theorem eq {db : Database} {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term}
    (hw : w ∈ db.terms) (h₁ : e₁.eval σ = some t₁)
    (h₂ : e₂.eval σ = some t₂)
    (hc : StoredCongOn db [t₁, t₂] w t₁)
    (he : StoredCongOn db [t₁, t₂] t₁ t₂) : Matches db (.eq e₁ e₂) σ :=
  .equal h₁ h₂ (InferredFacts.congr_iff_infers.mpr ⟨w, hw, hc, he⟩)

@[elab_as_elim]
theorem storedCases {db : Database}
    {motive : (p : Pattern) → (σ : Env) → Matches db p σ → Prop}
    {p : Pattern} {σ : Env} (h : Matches db p σ)
    (expr : ∀ {e : Expr} {σ : Env} {w t : Term},
      (hw : w ∈ db.terms) → (he : e.eval σ = some t) →
      (hc : StoredCongOn db [t] w t) → motive (.expr e) σ (Matches.expr hw he hc))
    (eq : ∀ {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term}, (hw : w ∈ db.terms) →
      (h₁ : e₁.eval σ = some t₁) → (h₂ : e₂.eval σ = some t₂) →
      (hc : StoredCongOn db [t₁, t₂] w t₁) → (he : StoredCongOn db [t₁, t₂] t₁ t₂) →
      motive (.eq e₁ e₂) σ (Matches.eq hw h₁ h₂ hc he))
    (unequal : ∀ {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term},
      (h₁ : e₁.eval σ = some t₁) → (h₂ : e₂.eval σ = some t₂) →
      (hc₁ : Cong db t₁ t₁) → (hc₂ : Cong db t₂ t₂) → (hne : ¬ Cong db t₁ t₂) →
      motive (.ne e₁ e₂) σ (.unequal h₁ h₂ hc₁ hc₂ hne)) : motive p σ h := by
  cases h with
  | atom he hc =>
    obtain ⟨w, hw, hwt, _⟩ := InferredFacts.congr_iff_infers.mp hc
    exact expr hw he (by
      simpa [StoredCongOn, Database.withOperands, Database.addTerms, Database.addTerm] using hwt)
  | equal h₁ h₂ hc =>
    obtain ⟨w, hw, hwt, he⟩ := InferredFacts.congr_iff_infers.mp hc
    exact eq hw h₁ h₂ hwt he
  | unequal h₁ h₂ hc₁ hc₂ hne => exact unequal h₁ h₂ hc₁ hc₂ hne

end Matches

namespace Expr
@[simp] theorem mem_varsList_append {v : Var} (as bs : List Expr) :
    v ∈ Expr.varsList (as ++ bs) ↔ v ∈ Expr.varsList as ∨ v ∈ Expr.varsList bs := by
  induction as with
  | nil => simp [Expr.varsList]
  | cons e es ih => simp [Expr.varsList, ih, or_assoc]

@[simp] theorem freeVars_lit {l : Lit} {σ : Env} : (Expr.lit l).freeVars σ = [] := rfl

@[simp] theorem freeVars_var {v : Var} {σ : Env} :
    (Expr.var v).freeVars σ = if (Env.lookup v σ).isSome then [] else [v] := rfl

@[simp] theorem freeVars_app {f : FnName} {args : List Expr} {σ : Env} :
    (Expr.app f args).freeVars σ = Expr.freeVarsList args σ := rfl

@[simp] theorem freeVars_min {a b : Expr} {σ : Env} :
    (Expr.min a b).freeVars σ = a.freeVars σ ∪ b.freeVars σ := rfl

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
  | .min a b =>
    rw [Expr.freeVars_min, Expr.vars_min, List.mem_union_iff, List.mem_union_iff,
      Expr.mem_freeVars a, Expr.mem_freeVars b]
    tauto
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
  | eq e₁ e₂ | ne e₁ e₂ =>
    rw [Pattern.freeVars, Pattern.vars, List.mem_union_iff, List.mem_union_iff,
      Expr.mem_freeVars e₁, Expr.mem_freeVars e₂]
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
  | .min a b => exact List.Nodup.union _ (Expr.freeVars_nodup b σ)
theorem Expr.freeVarsList_nodup (es : List Expr) (σ : Env) :
    (Expr.freeVarsList es σ).Nodup := by
  match es with
  | [] => simp
  | e :: es => exact List.Nodup.union _ (Expr.freeVarsList_nodup es σ)

end

theorem Pattern.freeVars_nodup (p : Pattern) (σ : Env) : (p.freeVars σ).Nodup := by
  cases p with
  | expr e => exact e.freeVars_nodup σ
  | eq _ e₂ | ne _ e₂ => exact List.Nodup.union _ (e₂.freeVars_nodup σ)

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

end ValidEnv
/-! ### Reading `StoredCongOn` back as an `addTerm`

The two shapes `Matches` uses, unfolded to the `addTerm` chain every congruence lemma is
stated at. Both are `Iff.rfl`: `withOperands` at a list *literal* is a fold that reduces,
so `StoredCongOn db [t]` and `StoredCongOn db [t₁, t₂]` *are* `StoredCong (db.addTerm t)` and
`StoredCong ((db.addTerm t₁).addTerm t₂)`. -/

theorem congOn_singleton {db : Database} {t a b : Term} :
    StoredCongOn db [t] a b ↔ StoredCong (db.addTerm t) a b := Iff.rfl

theorem congOn_pair {db : Database} {t₁ t₂ a b : Term} :
    StoredCongOn db [t₁, t₂] a b ↔ StoredCong ((db.addTerm t₁).addTerm t₂) a b := Iff.rfl

/-! ### Matched substitutions

The e-matcher's API, on the one matching relation there is. `ValidEnv` per pattern,
unioned: `RuleResults.wf` needs it, because a firing runs its head in the caller's
environment extended by the substitution and that invariant asks that every value there be
a term the database already holds. -/
namespace ValidSubst
variable {db : Database} {p : Pattern} {σ : Env}

/-- The hypothesis `patternHolds_validSubst` adds is a consequence of its conclusion,
which is why requiring it costs nothing. Since the hoist it is the left conjunct. -/
theorem validEnv (h : ValidSubst db p σ) : ValidEnv (p.freeVars []) db σ := h.1

theorem mem_terms (h : ValidSubst db p σ) : ∀ b ∈ σ, b.2 ∈ db.terms :=
  h.validEnv.mem_terms

/-- A matching substitution binds exactly the pattern's free variables. -/
theorem mem_dom_iff (h : ValidSubst db p σ) {v : Var} :
    v ∈ Env.dom σ ↔ v ∈ p.freeVars [] :=
  h.validEnv.mem_dom_iff

end ValidSubst
/-- `ValidSubst` transfers along agreement, provided the new substitution has exactly the
pattern's free variables as its domain.

Agreement alone is not enough, because `ValidEnv` pins the domain — which is precisely why
an executable enumerator has to canonicalize rather than emit any agreeing representative. -/
theorem ValidSubst.of_agree {db : Database} {p : Pattern} {σ σ' : Env}
    (h : ValidSubst db p σ) (hag : Env.Agree σ σ')
    (hdom : Env.dom σ' = p.freeVars []) : ValidSubst db p σ' := by
  have hterms : ∀ b ∈ σ', b.2 ∈ db.terms := by
    intro b hb
    have hnd : (Env.dom σ').Nodup := hdom ▸ p.freeVars_nodup []
    have hlk : Env.lookup b.1 σ' = some b.2 := (Env.lookup_eq_some_iff_mem hnd).mpr hb
    rw [← hag b.1] at hlk
    exact h.mem_terms _ (Env.mem_of_lookup hlk)
  have hperm : (Env.dom σ').Perm (p.freeVars []) := hdom ▸ List.Perm.refl _
  have hev : ∀ e : Expr, e.eval σ' = e.eval σ :=
    fun e => Expr.eval_agree hag.symm e
  have heva : ∀ e : Expr, e.eval σ' = e.eval σ :=
    fun e => Expr.eval_agree hag.symm e
  refine ⟨⟨hperm, hterms⟩, ?_⟩
  cases h.2 using Matches.storedCases with
  | expr hwm he hc => exact .expr hwm (by rw [heva]; exact he) hc
  | eq hwm he₁ he₂ hc₁ hc₂ =>
    exact .eq hwm (by rw [hev]; exact he₁) (by rw [hev]; exact he₂) hc₁ hc₂
  | unequal he₁ he₂ hc₁ hc₂ hne =>
    exact .unequal (by rw [hev]; exact he₁) (by rw [hev]; exact he₂) hc₁ hc₂ hne

/-- **Matching transfers along agreement on the pattern's own variables.** `Matches` reads
the environment only through the `Expr.eval` of the pattern's expressions, so `Expr.vars` is
the whole of what it can see.

Unlike `ValidSubst.of_agree` there is no domain condition, because `Matches` alone says
nothing about a domain: the `ValidEnv` half of `ValidSubst` is what pins it, and this is
stated without it precisely so that a substitution *larger* than the pattern's free variables
— a whole query's union — can be substituted for one atom's own. -/
theorem Matches.of_agreeOn {db : Database} {p : Pattern} {σ σ' : Env} (h : Matches db p σ)
    (hag : ∀ v ∈ p.vars, Env.lookup v σ = Env.lookup v σ') :
    Matches db p σ' := by
  cases h using Matches.storedCases with
  | @expr e _ w t hwm he hc =>
    exact .expr hwm (by rw [Expr.eval_agreeOn e fun v hv => (hag v hv).symm]; exact he) hc
  | @eq e₁ e₂ _ w t₁ t₂ hwm he₁ he₂ hc₁ hc₂ =>
    refine .eq hwm ?_ ?_ hc₁ hc₂
    · rw [Expr.eval_agreeOn e₁ fun v hv =>
        (hag v (List.mem_union_iff.mpr (Or.inl hv))).symm]
      exact he₁
    · rw [Expr.eval_agreeOn e₂ fun v hv =>
        (hag v (List.mem_union_iff.mpr (Or.inr hv))).symm]
      exact he₂
  | @unequal e₁ e₂ _ t₁ t₂ he₁ he₂ hc₁ hc₂ hne =>
    refine .unequal ?_ ?_ hc₁ hc₂ hne
    · rw [Expr.eval_agreeOn e₁ fun v hv =>
        (hag v (List.mem_union_iff.mpr (Or.inl hv))).symm]
      exact he₁
    · rw [Expr.eval_agreeOn e₂ fun v hv =>
        (hag v (List.mem_union_iff.mpr (Or.inr hv))).symm]
      exact he₂


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
    v ∈ Env.dom σ ↔ ∃ p ∈ q, v ∈ p.freeVars [] := by
  obtain ⟨σs, hall, hu⟩ := h
  rw [hu.mem_dom_iff]
  constructor
  · rintro ⟨σ', hσ', hv⟩
    obtain ⟨p, hp, hvs⟩ := hall.exists_left hσ'
    exact ⟨p, hp, hvs.mem_dom_iff.mp hv⟩
  · rintro ⟨p, hp, hv⟩
    obtain ⟨σ', hσ', hvs⟩ := hall.flip.exists_left hp
    exact ⟨σ', hσ', (ValidSubst.mem_dom_iff hvs).mpr hv⟩

/-- **Every pattern of a satisfied query matches under the *joined* substitution.** The
per-pattern substitutions `ValidQuerySubst` quantifies over are an artefact of how the join is
stated; each of them binds exactly its own pattern's free variables and refines the union
(`Env.UnionAll.refines_of_mem`), so on the variables that pattern can see the union is
indistinguishable from it — `Matches.of_agreeOn`.

Only `Matches` survives, not `ValidSubst`: the union binds the *other* patterns' variables
too, so its domain is wrong for `ValidEnv`. -/
theorem matches_of_mem (h : ValidQuerySubst db q σ) {p : Pattern} (hp : p ∈ q) :
    Matches db p σ := by
  obtain ⟨σs, hall, hu⟩ := h
  obtain ⟨σp, hσp, hvs⟩ := hall.flip.exists_left hp
  have hsc : ∀ ρ ∈ σs, Env.Refines ρ ρ := by
    intro ρ hρ
    obtain ⟨p', -, hvs'⟩ := hall.exists_left hρ
    exact Env.Refines.self_of_nodup (hvs'.validEnv.1.symm.nodup (p'.freeVars_nodup _))
  have hrp : Env.Refines σp σ := (hu.refines_of_mem hsc).1 σp hσp
  refine hvs.2.of_agreeOn fun v hv => ?_
  have hfv : v ∈ p.freeVars [] := p.mem_freeVars.mpr ⟨hv, by simp⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (Env.lookup_isSome_iff_mem_dom.mpr ((ValidSubst.mem_dom_iff hvs).mpr hfv))
  rw [ht, hrp (v, t) (Env.mem_of_lookup ht)]

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
/-- `Query.vars` over a concatenation. -/
theorem Query.mem_vars_append {v : Var} {q₁ q₂ : Query} :
    v ∈ Query.vars (q₁ ++ q₂) ↔ v ∈ Query.vars q₁ ∨ v ∈ Query.vars q₂ := by
  rw [Query.mem_vars, Query.mem_vars, Query.mem_vars]
  constructor
  · rintro ⟨p, hp, hvp⟩
    exact (List.mem_append.mp hp).imp (fun h => ⟨p, h, hvp⟩) fun h => ⟨p, h, hvp⟩
  · rintro (⟨p, hp, hvp⟩ | ⟨p, hp, hvp⟩)
    · exact ⟨p, List.mem_append_left _ hp, hvp⟩
    · exact ⟨p, List.mem_append_right _ hp, hvp⟩


end Egglog
