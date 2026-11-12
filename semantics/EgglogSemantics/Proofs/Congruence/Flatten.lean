import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.Match
import EgglogSemantics.Proofs.Source.FreshBindings
import EgglogSemantics.Proofs.MatchValues
import EgglogSemantics.Proofs.Diagonal

/-! Equations and variable bounds for query flattening without views. Variables in emitted
atoms and ids come from the source expression or the consumed fresh-variable interval. -/

namespace Egglog.Congruence

/-- The fresh child variables of an application atom. -/
def freshArgs (next k : Nat) : List Expr :=
  (List.range k).map fun i => Expr.var (freshVar (next + i))

/-- `v` is a generated variable numbered in `[n, m)`. -/
def FreshIn (n m : Nat) (v : Var) : Prop := ∃ k, n ≤ k ∧ k < m ∧ v = freshVar k

theorem FreshIn.mono {n m n' m' : Nat} {v : Var} (h : FreshIn n m v) (hn : n' ≤ n) (hm : m ≤ m') :
    FreshIn n' m' v :=
  let ⟨k, h₁, h₂, h₃⟩ := h
  ⟨k, Nat.le_trans hn h₁, Nat.lt_of_lt_of_le h₂ hm, h₃⟩

/-- A source variable is not generated. -/
def NotFresh (v : Var) : Prop := ∀ k, v ≠ freshVar k

theorem notFresh_of_not_at {v : Var} (h : ¬ "@".isPrefixOf v) : NotFresh v := by
  intro k hk
  rw [hk] at h
  exact h (atPrefix_freshVar k)

/-! ### Equations of the flattening -/

theorem flat_lit (l : Lit) (n : Nat) : encodeQueryExprWith {} (.lit l) n = (.lit l, [], n) := rfl
theorem flat_var (v : Var) (n : Nat) : encodeQueryExprWith {} (.var v) n = (.var v, [], n) := rfl
theorem flat_min (a b : Expr) (n : Nat) :
    encodeQueryExprWith {} (.min a b) n = (.min a b, [], n) := rfl

theorem flat_app {f : FnName} {args : List Expr} {n : Nat} {xs : List Expr} {ps : Query}
    {next : Nat} (hr : encodeQueryArgsWith {} args n = (xs, ps, next)) :
    encodeQueryExprWith {} (.app f args) n =
      (Expr.var (freshVar (next + args.length)),
       ps ++ .expr (.app f (freshArgs next args.length)) ::
         ((freshArgs next args.length).zip xs).map (fun ax => .expr (ufRow ax.1 ax.2)) ++
         [.expr (ufRow (.app f (freshArgs next args.length))
           (.var (freshVar (next + args.length))))],
       next + args.length + 1) := by
  simp [encodeQueryExprWith, hr, freshArgs]

theorem flatArgs_nil (n : Nat) : encodeQueryArgsWith {} [] n = ([], [], n) := rfl

theorem flatArgs_cons {e : Expr} {es : List Expr} {n : Nat} {x : Expr} {ps : Query} {next : Nat}
    {xs : List Expr} {qs : Query} {last : Nat}
    (h₁ : encodeQueryExprWith {} e n = (x, ps, next))
    (h₂ : encodeQueryArgsWith {} es next = (xs, qs, last)) :
    encodeQueryArgsWith {} (e :: es) n = (x :: xs, ps ++ qs, last) := by
  simp [encodeQueryArgsWith, h₁, h₂]

theorem pattern_expr (e : Expr) (n : Nat) :
    encodePatternWith {} (.expr e) n = ((encodeQueryExprWith {} e n).2.1,
      (encodeQueryExprWith {} e n).2.2) := rfl

theorem pattern_eq {l r : Expr} {n : Nat} {x₁ : Expr} {ps : Query} {next : Nat} {x₂ : Expr}
    {qs : Query} {last : Nat} (h₁ : encodeQueryExprWith {} l n = (x₁, ps, next))
    (h₂ : encodeQueryExprWith {} r next = (x₂, qs, last)) :
    encodePatternWith {} (.eq l r) n = (ps ++ qs ++ [.eq x₁ x₂], last) := by
  simp [encodePatternWith, h₁, h₂]

theorem pattern_ne {l r : Expr} {n : Nat} {x₁ : Expr} {ps : Query} {next : Nat} {x₂ : Expr}
    {qs : Query} {last : Nat} (h₁ : encodeQueryExprWith {} l n = (x₁, ps, next))
    (h₂ : encodeQueryExprWith {} r next = (x₂, qs, last)) :
    encodePatternWith {} (.ne l r) n = (ps ++ qs ++ [.ne x₁ x₂], last) := by
  simp [encodePatternWith, h₁, h₂]

theorem query_nil (n : Nat) : encodeQueryWith {} [] n = ([], n) := rfl

theorem query_cons {p : Pattern} {ps : Query} {n : Nat} {qs : Query} {next : Nat} {rest : Query}
    {last : Nat} (h₁ : encodePatternWith {} p n = (qs, next))
    (h₂ : encodeQueryWith {} ps next = (rest, last)) :
    encodeQueryWith {} (p :: ps) n = (qs ++ rest, last) := by
  simp [encodeQueryWith, h₁, h₂]

/-! ### Fresh arguments -/

theorem freshArgs_length (next k : Nat) : (freshArgs next k).length = k := by simp [freshArgs]

theorem freshArgs_getElem {next k i : Nat} (hi : i < k) :
    (freshArgs next k)[i]'(by rw [freshArgs_length]; exact hi) = .var (freshVar (next + i)) := by
  simp [freshArgs]

theorem mem_freshArgs {next k : Nat} {e : Expr} :
    e ∈ freshArgs next k ↔ ∃ i, i < k ∧ e = .var (freshVar (next + i)) := by
  simp only [freshArgs, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem mem_varsList_freshArgs {next k : Nat} {v : Var} :
    v ∈ Expr.varsList (freshArgs next k) ↔ ∃ i, i < k ∧ v = freshVar (next + i) := by
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
    obtain ⟨i, hi, rfl⟩ := mem_freshArgs.mp he
    simp only [Expr.vars_var, List.mem_singleton] at hve
    exact ⟨i, hi, hve⟩
  · rintro ⟨i, hi, rfl⟩
    exact Expr.var_mem_varsList (mem_freshArgs.mpr ⟨i, hi, rfl⟩)

/-! ### The counter only grows -/

mutual

theorem flat_next_le : ∀ (e : Expr) (n : Nat), n ≤ (encodeQueryExprWith {} e n).2.2
  | .lit _, _ => Nat.le_refl _
  | .var _, _ => Nat.le_refl _
  | .min _ _, _ => Nat.le_refl _
  | .app f args, n => by
      rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      rw [flat_app hr]
      have := flatArgs_next_le args n
      rw [hr] at this
      simp only at this ⊢
      omega

theorem flatArgs_next_le : ∀ (es : List Expr) (n : Nat), n ≤ (encodeQueryArgsWith {} es n).2.2
  | [], _ => Nat.le_refl _
  | e :: es, n => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂]
      have hn := flat_next_le e n
      have hm := flatArgs_next_le es next
      rw [h₁] at hn
      rw [h₂] at hm
      simp only at hn hm ⊢
      omega

end

theorem pattern_next_le (p : Pattern) (n : Nat) : n ≤ (encodePatternWith {} p n).2 := by
  cases p with
  | expr e => exact flat_next_le e n
  | eq l r | ne l r =>
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    have hn := flat_next_le l n
    have hm := flat_next_le r next
    rw [h₁] at hn
    rw [h₂] at hm
    first
    | rw [pattern_eq h₁ h₂]
    | rw [pattern_ne h₁ h₂]
    simp only at hn hm ⊢
    omega

theorem query_next_le (q : Query) (n : Nat) : n ≤ (encodeQueryWith {} q n).2 := by
  induction q generalizing n with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    have hn := pattern_next_le p n
    have hm := ih next
    rw [h₁] at hn
    rw [h₂] at hm
    rw [query_cons h₁ h₂]
    simp only at hn hm ⊢
    omega

/-! ### The variables of the emitted atoms -/

/-- The variables of an id expression: the source variable itself, or a fresh variable of
the interval, which the atoms also mention. -/
theorem flat_id_cases (e : Expr) (n : Nat) :
    (encodeQueryExprWith {} e n).1 = e ∧ (encodeQueryExprWith {} e n).2.1 = [] ∧
      (encodeQueryExprWith {} e n).2.2 = n ∨
    ∃ k, (encodeQueryExprWith {} e n).1 = .var (freshVar k) ∧ n ≤ k ∧
      k < (encodeQueryExprWith {} e n).2.2 ∧
      freshVar k ∈ Query.vars (encodeQueryExprWith {} e n).2.1 := by
  cases e with
  | lit l => exact Or.inl ⟨rfl, rfl, rfl⟩
  | var v => exact Or.inl ⟨rfl, rfl, rfl⟩
  | min a b => exact Or.inl ⟨rfl, rfl, rfl⟩
  | app f args =>
    right
    rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
    have hle := flatArgs_next_le args n
    rw [hr] at hle
    simp only at hle
    rw [flat_app hr]
    refine ⟨next + args.length, rfl, by omega, by simp, ?_⟩
    rw [Query.mem_vars]
    refine ⟨.expr (ufRow (.app f (freshArgs next args.length))
      (.var (freshVar (next + args.length)))), by simp, ?_⟩
    simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]

mutual

/-- Every variable of the emitted atoms is a source variable of the expression or a fresh
variable of the consumed interval. -/
theorem flat_vars_sub : ∀ (e : Expr) (n : Nat) {v : Var},
    v ∈ Query.vars (encodeQueryExprWith {} e n).2.1 →
      v ∈ e.vars ∨ FreshIn n (encodeQueryExprWith {} e n).2.2 v
  | .lit _, _, _, hv => by rw [flat_lit] at hv; simp at hv
  | .var _, _, _, hv => by rw [flat_var] at hv; simp at hv
  | .min _ _, _, _, hv => by rw [flat_min] at hv; simp at hv
  | .app f args, n, v, hv => by
      rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hle := flatArgs_next_le args n
      rw [hr] at hle
      simp only at hle
      rw [flat_app hr] at hv ⊢
      simp only at hv ⊢
      rw [Query.mem_vars_append, Query.mem_vars_append] at hv
      rcases hv with (hv | hv) | hv
      · rcases flatArgs_vars_sub args n (by rw [hr]; exact hv) with hv | hv
        · exact Or.inl hv
        · rw [hr] at hv
          exact Or.inr (hv.mono (Nat.le_refl _) (by simp only; omega))
      · rw [Query.vars_cons, List.mem_union_iff] at hv
        rcases hv with hv | hv
        · rw [Pattern.vars, Expr.vars_app, mem_varsList_freshArgs] at hv
          obtain ⟨i, hi, rfl⟩ := hv
          exact Or.inr ⟨next + i, by omega, by omega, rfl⟩
        · rw [Query.mem_vars] at hv
          obtain ⟨p, hp, hv⟩ := hv
          obtain ⟨ax, hax, rfl⟩ := List.mem_map.mp hp
          obtain ⟨ha, hx⟩ := List.of_mem_zip hax
          obtain ⟨i, hi, hai⟩ := mem_freshArgs.mp ha
          simp only [Pattern.vars, ufRow, Expr.vars_app, Expr.varsList_cons, Expr.varsList_nil,
            List.mem_union_iff, List.not_mem_nil, or_false] at hv
          rcases hv with hv | hv
          · rw [hai, Expr.vars_var, List.mem_singleton] at hv
            exact Or.inr ⟨next + i, by omega, by omega, hv⟩
          · rcases flatArgs_ids_vars args n (by rw [hr]; exact hx) hv with hv | hv
            · exact Or.inl hv
            · rw [hr] at hv
              exact Or.inr (hv.mono (Nat.le_refl _) (by simp only; omega))
      · simp only [Query.vars_cons, Query.vars_nil, Pattern.vars, ufRow,
          Expr.vars_app, Expr.varsList_cons, Expr.varsList_nil, List.mem_union_iff,
          Expr.vars_var, List.mem_singleton, mem_varsList_freshArgs, List.not_mem_nil,
          or_false] at hv
        rcases hv with ⟨i, hi, rfl⟩ | rfl
        · exact Or.inr ⟨next + i, by omega, by omega, rfl⟩
        · exact Or.inr ⟨next + args.length, by omega, by omega, rfl⟩

theorem flatArgs_vars_sub : ∀ (es : List Expr) (n : Nat) {v : Var},
    v ∈ Query.vars (encodeQueryArgsWith {} es n).2.1 →
      v ∈ Expr.varsList es ∨ FreshIn n (encodeQueryArgsWith {} es n).2.2 v
  | [], _, _, hv => by rw [flatArgs_nil] at hv; simp at hv
  | e :: es, n, v, hv => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      have hn := flat_next_le e n
      have hm := flatArgs_next_le es next
      rw [h₁] at hn
      rw [h₂] at hm
      simp only at hn hm
      rw [flatArgs_cons h₁ h₂] at hv ⊢
      simp only at hv ⊢
      rw [Query.mem_vars_append] at hv
      rw [Expr.varsList_cons, List.mem_union_iff]
      rcases hv with hv | hv
      · rcases flat_vars_sub e n (by rw [h₁]; exact hv) with hv | hv
        · exact Or.inl (Or.inl hv)
        · rw [h₁] at hv
          exact Or.inr (hv.mono (Nat.le_refl _) (by simp only; omega))
      · rcases flatArgs_vars_sub es next (by rw [h₂]; exact hv) with hv | hv
        · exact Or.inl (Or.inr hv)
        · rw [h₂] at hv
          exact Or.inr (hv.mono hn (Nat.le_refl _))

/-- The variables of the ids of an argument list. -/
theorem flatArgs_ids_vars : ∀ (es : List Expr) (n : Nat) {x : Expr},
    x ∈ (encodeQueryArgsWith {} es n).1 → ∀ {v : Var}, v ∈ x.vars →
      v ∈ Expr.varsList es ∨ FreshIn n (encodeQueryArgsWith {} es n).2.2 v
  | [], _, _, hx, _, _ => by rw [flatArgs_nil] at hx; simp at hx
  | e :: es, n, x, hx, v, hv => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x₁, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      have hn := flat_next_le e n
      have hm := flatArgs_next_le es next
      rw [h₁] at hn
      rw [h₂] at hm
      simp only at hn hm
      rw [flatArgs_cons h₁ h₂] at hx ⊢
      simp only at hx ⊢
      rw [Expr.varsList_cons, List.mem_union_iff]
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases flat_id_cases e n with ⟨hx₁, -, -⟩ | ⟨k, hx₁, hk₁, hk₂, -⟩
        · rw [h₁] at hx₁
          simp only at hx₁
          rw [hx₁] at hv
          exact Or.inl (Or.inl hv)
        · rw [h₁] at hx₁ hk₂
          simp only at hx₁ hk₂
          rw [hx₁, Expr.vars_var, List.mem_singleton] at hv
          exact Or.inr ⟨k, hk₁, by omega, hv⟩
      · rcases flatArgs_ids_vars es next (by rw [h₂]; exact hx) hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · rw [h₂] at hv
          exact Or.inr (hv.mono hn (Nat.le_refl _))

end

mutual

/-- Every fresh variable of the consumed interval occurs in the atoms. -/
theorem flat_fresh_mem : ∀ (e : Expr) (n : Nat) {v : Var},
    FreshIn n (encodeQueryExprWith {} e n).2.2 v → v ∈ Query.vars (encodeQueryExprWith {} e n).2.1
  | .lit _, _, _, ⟨_, h₁, h₂, _⟩ => by rw [flat_lit] at h₂; simp at h₂; omega
  | .var _, _, _, ⟨_, h₁, h₂, _⟩ => by rw [flat_var] at h₂; simp at h₂; omega
  | .min _ _, _, _, ⟨_, h₁, h₂, _⟩ => by rw [flat_min] at h₂; simp at h₂; omega
  | .app f args, n, v, ⟨k, hk₁, hk₂, hvk⟩ => by
      subst hvk
      rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hle := flatArgs_next_le args n
      rw [hr] at hle
      simp only at hle
      rw [flat_app hr] at hk₂ ⊢
      simp only at hk₂ ⊢
      rw [Query.mem_vars_append, Query.mem_vars_append]
      by_cases hlt : k < next
      · have := flatArgs_fresh_mem args n ⟨k, hk₁, by rw [hr]; exact hlt, rfl⟩
        rw [hr] at this
        exact Or.inl (Or.inl this)
      · right
        simp only [Query.vars_cons, Query.vars_nil, Pattern.vars, ufRow,
          Expr.vars_app, Expr.varsList_cons, Expr.varsList_nil, List.mem_union_iff,
          Expr.vars_var, List.mem_singleton, mem_varsList_freshArgs, List.not_mem_nil, or_false]
        by_cases hk : k < next + args.length
        · exact Or.inl ⟨k - next, by omega, congrArg freshVar (by omega)⟩
        · exact Or.inr (congrArg freshVar (by omega))

theorem flatArgs_fresh_mem : ∀ (es : List Expr) (n : Nat) {v : Var},
    FreshIn n (encodeQueryArgsWith {} es n).2.2 v →
      v ∈ Query.vars (encodeQueryArgsWith {} es n).2.1
  | [], _, _, ⟨_, h₁, h₂, _⟩ => by rw [flatArgs_nil] at h₂; simp at h₂; omega
  | e :: es, n, v, ⟨k, hk₁, hk₂, hvk⟩ => by
      subst hvk
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂] at hk₂ ⊢
      simp only at hk₂ ⊢
      rw [Query.mem_vars_append]
      by_cases hlt : k < next
      · left
        have := flat_fresh_mem e n ⟨k, hk₁, by rw [h₁]; exact hlt, rfl⟩
        rw [h₁] at this
        exact this
      · right
        have := flatArgs_fresh_mem es next ⟨k, by omega, by rw [h₂]; exact hk₂, rfl⟩
        rw [h₂] at this
        exact this

end

theorem flatArgs_length : ∀ (es : List Expr) (n : Nat),
    (encodeQueryArgsWith {} es n).1.length = es.length
  | [], _ => rfl
  | e :: es, n => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂]
      have := flatArgs_length es next
      rw [h₂] at this
      simp only [List.length_cons] at this ⊢
      rw [this]

mutual

/-- A source variable of an expression occurs in its atoms or in its id. -/
theorem flat_vars_mem : ∀ (e : Expr) (n : Nat) {v : Var}, v ∈ e.vars →
    v ∈ Query.vars (encodeQueryExprWith {} e n).2.1 ∨ v ∈ (encodeQueryExprWith {} e n).1.vars
  | .lit _, _, _, hv => by simp at hv
  | .var _, _, _, hv => Or.inr hv
  | .min _ _, _, _, hv => Or.inr hv
  | .app f args, n, v, hv => by
      rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hlen := flatArgs_length args n
      rw [hr] at hlen
      simp only at hlen
      rw [flat_app hr]
      left
      simp only
      rw [Query.mem_vars_append, Query.mem_vars_append]
      rw [Expr.vars_app] at hv
      rcases flatArgs_vars_mem args n hv with hv | ⟨x, hx, hvx⟩
      · rw [hr] at hv
        exact Or.inl (Or.inl hv)
      · rw [hr] at hx
        simp only at hx
        left; right
        rw [Query.vars_cons, List.mem_union_iff]
        right
        rw [Query.mem_vars]
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hi' : i < args.length := hlen ▸ hi
        refine ⟨.expr (ufRow ((freshArgs next args.length)[i]'(by
          rw [freshArgs_length]; exact hi')) xs[i]), ?_, ?_⟩
        · refine List.mem_map.mpr ⟨((freshArgs next args.length)[i]'(by
            rw [freshArgs_length]; exact hi'), xs[i]), ?_, rfl⟩
          rw [List.mem_iff_getElem]
          refine ⟨i, by rw [List.length_zip, freshArgs_length, hlen, Nat.min_self]; exact hi', ?_⟩
          rw [List.getElem_zip]
        · simp only [Pattern.vars, ufRow, Expr.vars_app, Expr.varsList_cons, Expr.varsList_nil,
            List.mem_union_iff, List.not_mem_nil, or_false]
          exact Or.inr hvx

theorem flatArgs_vars_mem : ∀ (es : List Expr) (n : Nat) {v : Var}, v ∈ Expr.varsList es →
    v ∈ Query.vars (encodeQueryArgsWith {} es n).2.1 ∨
      ∃ x ∈ (encodeQueryArgsWith {} es n).1, v ∈ x.vars
  | [], _, _, hv => by simp at hv
  | e :: es, n, v, hv => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂]
      simp only
      rw [Query.mem_vars_append]
      rw [Expr.varsList_cons, List.mem_union_iff] at hv
      rcases hv with hv | hv
      · rcases flat_vars_mem e n hv with hv | hv
        · rw [h₁] at hv
          exact Or.inl (Or.inl hv)
        · rw [h₁] at hv
          exact Or.inr ⟨x, by simp, hv⟩
      · rcases flatArgs_vars_mem es next hv with hv | ⟨x', hx', hv⟩
        · rw [h₂] at hv
          exact Or.inl (Or.inr hv)
        · rw [h₂] at hx'
          exact Or.inr ⟨x', by simp [hx'], hv⟩

end

/-- An application's source variables all occur in its atoms. -/
theorem flat_app_vars_mem {f : FnName} {args : List Expr} {n : Nat} {v : Var}
    (hv : v ∈ (Expr.app f args).vars) :
    v ∈ Query.vars (encodeQueryExprWith {} (.app f args) n).2.1 := by
  rcases flat_vars_mem (.app f args) n hv with h | h
  · exact h
  · rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
    rw [flat_app hr] at h ⊢
    simp only [Expr.vars_var, List.mem_singleton] at h
    subst h
    simp only
    rw [Query.mem_vars_append, Query.mem_vars_append]
    right
    simp [Query.vars, Pattern.vars, ufRow, Expr.vars, Expr.varsList]

/-! ### Patterns and queries -/

/-- The variables of a compiled pattern: the pattern's own and the fresh ones of its
interval. A bare expression pattern must be an application for its variables to appear. -/
theorem pattern_vars_iff {p : Pattern} (hp : p.Scoped) (n : Nat) {v : Var} :
    v ∈ Query.vars (encodePatternWith {} p n).1 ↔
      v ∈ p.vars ∨ FreshIn n (encodePatternWith {} p n).2 v := by
  cases p with
  | expr e =>
    cases e with
    | app f args =>
      rw [pattern_expr]
      simp only [Pattern.vars]
      constructor
      · exact flat_vars_sub _ n
      · rintro (hv | hv)
        · exact flat_app_vars_mem hv
        · exact flat_fresh_mem _ n hv
    | lit _ => exact hp.elim
    | var _ => exact hp.elim
    | min _ _ => exact hp.elim
  | eq l r | ne l r =>
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    have hn := flat_next_le l n
    have hm := flat_next_le r next
    rw [h₁] at hn
    rw [h₂] at hm
    simp only at hn hm
    have hl := flat_vars_sub l n (v := v)
    have hr := flat_vars_sub r next (v := v)
    have hl' := flat_fresh_mem l n (v := v)
    have hr' := flat_fresh_mem r next (v := v)
    have hlm := flat_vars_mem l n (v := v)
    have hrm := flat_vars_mem r next (v := v)
    have hli := flat_id_cases l n
    have hri := flat_id_cases r next
    rw [h₁] at hl hl' hlm hli
    rw [h₂] at hr hr' hrm hri
    simp only at hl hr hl' hr' hlm hrm hli hri
    first
    | rw [pattern_eq h₁ h₂]
    | rw [pattern_ne h₁ h₂]
    simp only [Pattern.vars, Query.mem_vars_append, Query.vars_cons, Query.vars_nil,
      List.mem_union_iff, List.not_mem_nil, or_false]
    constructor
    · rintro ((hv | hv) | hv | hv)
      · rcases hl hv with hv | hv
        · exact Or.inl (Or.inl hv)
        · exact Or.inr (hv.mono (Nat.le_refl _) hm)
      · rcases hr hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr (hv.mono hn (Nat.le_refl _))
      · rcases hli with ⟨hx, -, -⟩ | ⟨k, hx, hk₁, hk₂, -⟩
        · rw [hx] at hv; exact Or.inl (Or.inl hv)
        · rw [hx, Expr.vars_var, List.mem_singleton] at hv
          exact Or.inr ⟨k, hk₁, by omega, hv⟩
      · rcases hri with ⟨hx, -, -⟩ | ⟨k, hx, hk₁, hk₂, -⟩
        · rw [hx] at hv; exact Or.inl (Or.inr hv)
        · rw [hx, Expr.vars_var, List.mem_singleton] at hv
          exact Or.inr ⟨k, by omega, hk₂, hv⟩
    · rintro ((hv | hv) | ⟨k, hk₁, hk₂, rfl⟩)
      · rcases hlm hv with hv | hv
        · exact Or.inl (Or.inl hv)
        · exact Or.inr (Or.inl hv)
      · rcases hrm hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr (Or.inr hv)
      · by_cases hlt : k < next
        · exact Or.inl (Or.inl (hl' ⟨k, hk₁, hlt, rfl⟩))
        · exact Or.inl (Or.inr (hr' ⟨k, by omega, hk₂, rfl⟩))

theorem query_vars_iff {q : Query} (hq : ∀ p ∈ q, p.Scoped) (n : Nat) {v : Var} :
    v ∈ Query.vars (encodeQueryWith {} q n).1 ↔
      v ∈ Query.vars q ∨ FreshIn n (encodeQueryWith {} q n).2 v := by
  induction q generalizing n with
  | nil =>
    rw [query_nil]
    simp only [Query.vars_nil, List.not_mem_nil, false_or, false_iff]
    rintro ⟨k, h₁, h₂, _⟩
    omega
  | cons p ps ih =>
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    have hn := pattern_next_le p n
    have hm := query_next_le ps next
    rw [h₁] at hn
    rw [h₂] at hm
    simp only at hn hm
    have hp := pattern_vars_iff (hq p (by simp)) n (v := v)
    have hps := ih (fun p hp => hq p (by simp [hp])) next
    rw [h₁] at hp
    rw [h₂] at hps
    simp only at hp hps
    rw [query_cons h₁ h₂]
    simp only [Query.mem_vars_append, Query.vars_cons, List.mem_union_iff, hp, hps]
    constructor
    · rintro ((hv | hv) | hv | hv)
      · exact Or.inl (Or.inl hv)
      · exact Or.inr (hv.mono (Nat.le_refl _) hm)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr (hv.mono hn (Nat.le_refl _))
    · rintro ((hv | hv) | ⟨k, hk₁, hk₂, rfl⟩)
      · exact Or.inl (Or.inl hv)
      · exact Or.inr (Or.inl hv)
      · by_cases hlt : k < next
        · exact Or.inl (Or.inr ⟨k, hk₁, hlt, rfl⟩)
        · exact Or.inr (Or.inr ⟨k, by omega, hk₂, rfl⟩)

/-! ### Keyed variables are read through an edge -/

theorem var_mem_flatArgs_ids : ∀ (es : List Expr) (n : Nat) {v : Var},
    Expr.var v ∈ es → Expr.var v ∈ (encodeQueryArgsWith {} es n).1
  | [], _, _, h => by simp at h
  | e :: es, n, v, h => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂]
      simp only [List.mem_cons]
      rcases List.mem_cons.mp h with rfl | h
      · rw [flat_var] at h₁
        exact Or.inl (Prod.mk.inj h₁).1
      · right
        have := var_mem_flatArgs_ids es next h
        rw [h₂] at this
        exact this

/-- An id of an argument list is read through a union-find atom of the application. -/
theorem id_atom_mem {f : FnName} {args : List Expr} {n : Nat} {x : Expr}
    (hx : x ∈ (encodeQueryArgsWith {} args n).1) :
    ∃ a, Pattern.expr (ufRow (.var a) x) ∈ (encodeQueryExprWith {} (.app f args) n).2.1 := by
  rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
  rw [hr] at hx
  simp only at hx
  have hlen := flatArgs_length args n
  rw [hr] at hlen
  simp only at hlen
  rw [flat_app hr]
  simp only
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < args.length := hlen ▸ hi
  refine ⟨freshVar (next + i), ?_⟩
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  refine List.mem_map.mpr ⟨((freshArgs next args.length)[i]'(by
    rw [freshArgs_length]; exact hi'), xs[i]), ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨i, by rw [List.length_zip, freshArgs_length, hlen, Nat.min_self]; exact hi', ?_⟩
    rw [List.getElem_zip]
  · rw [freshArgs_getElem hi']

mutual

/-- A keyed variable of an expression whose minima are over variables is the second
column of some union-find atom: a minimum keys no variable. -/
theorem argVar_atom : ∀ (e : Expr) (n : Nat) {v : Var}, e.MinOverVars → Expr.ArgVar v e →
    ∃ a, Pattern.expr (ufRow (.var a) (.var v)) ∈ (encodeQueryExprWith {} e n).2.1
  | .lit _, _, _, _, h => h.elim
  | .var _, _, _, _, h => h.elim
  | .min _ _, _, _, ho, h => by
      obtain ⟨ha, hb⟩ := Expr.minOverVars_min ho
      rcases h with h | h
      · exact (ha.not_argVar h).elim
      · exact (hb.not_argVar h).elim
  | .app f args, n, v, ho, h => by
      rcases h with h | h
      · exact id_atom_mem (var_mem_flatArgs_ids args n h)
      · obtain ⟨a, ha⟩ := argVarList_atom args n (Expr.minOverVars_app ho) h
        rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
        rw [hr] at ha
        rw [flat_app hr]
        simp only at ha ⊢
        exact ⟨a, List.mem_append_left _ (List.mem_append_left _ ha)⟩

theorem argVarList_atom : ∀ (es : List Expr) (n : Nat) {v : Var}, Expr.MinOverVarsList es →
    Expr.ArgVarList v es →
    ∃ a, Pattern.expr (ufRow (.var a) (.var v)) ∈ (encodeQueryArgsWith {} es n).2.1
  | [], _, _, _, h => h.elim
  | e :: es, n, v, ho, h => by
      obtain ⟨hoe, hoes⟩ := Expr.minOverVarsList_cons ho
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂]
      simp only [List.mem_append]
      rcases h with h | h
      · obtain ⟨a, ha⟩ := argVar_atom e n hoe h
        rw [h₁] at ha
        exact ⟨a, Or.inl ha⟩
      · obtain ⟨a, ha⟩ := argVarList_atom es next hoes h
        rw [h₂] at ha
        exact ⟨a, Or.inr ha⟩

end

theorem pattern_argVar_atom {p : Pattern} (n : Nat) (ho : p.MinOverVars) {v : Var}
    (h : Pattern.ArgVar v p) :
    ∃ a, Pattern.expr (ufRow (.var a) (.var v)) ∈ (encodePatternWith {} p n).1 := by
  cases p with
  | expr e => exact argVar_atom e n ho h
  | eq l r | ne l r =>
    obtain ⟨hol, hor⟩ := Bool.and_eq_true_iff.mp ho
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    first
    | rw [pattern_eq h₁ h₂]
    | rw [pattern_ne h₁ h₂]
    simp only [List.mem_append]
    rcases h with h | h
    · obtain ⟨a, ha⟩ := argVar_atom l n hol h
      rw [h₁] at ha
      exact ⟨a, Or.inl (Or.inl ha)⟩
    · obtain ⟨a, ha⟩ := argVar_atom r next hor h
      rw [h₂] at ha
      exact ⟨a, Or.inl (Or.inr ha)⟩

theorem query_argVar_atom {q : Query} (n : Nat) (ho : ∀ p ∈ q, p.MinOverVars) {v : Var}
    {p : Pattern} (hp : p ∈ q) (h : Pattern.ArgVar v p) :
    ∃ a, Pattern.expr (ufRow (.var a) (.var v)) ∈ (encodeQueryWith {} q n).1 := by
  induction q generalizing n with
  | nil => simp at hp
  | cons p' ps ih =>
    rcases h₁ : encodePatternWith {} p' n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    rw [query_cons h₁ h₂]
    simp only [List.mem_append]
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨a, ha⟩ := pattern_argVar_atom n (ho p (by simp)) h
      rw [h₁] at ha
      exact ⟨a, Or.inl ha⟩
    · obtain ⟨a, ha⟩ := ih next (fun p hp => ho p (by simp [hp])) hp
      rw [h₂] at ha
      exact ⟨a, Or.inr ha⟩

end Egglog.Congruence
