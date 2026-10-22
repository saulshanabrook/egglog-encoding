import EgglogSemantics.Proofs.Match

/-! Evaluating variables and constructing tuple substitutions. -/

namespace Egglog

theorem Env.dom_zip_subset : ∀ (vs : List Var) (as : List Term), Env.dom (vs.zip as) ⊆ vs
  | [], _ => by simp [Env.dom]
  | _ :: _, [] => by simp [Env.dom]
  | v :: vs, a :: as => by
      intro w hw
      rw [List.zip_cons_cons, Env.dom_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Env.dom_zip_subset vs as hw)

theorem Env.lookup_zip : ∀ (vs : List Var) (as : List Term), vs.length = as.length →
    vs.Nodup → ∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length),
      Env.lookup vs[i] (vs.zip as) = some as[i]
  | [], [], _, _, i, hi, _ => by simp at hi
  | v :: vs, a :: as, hlen, hnd, 0, _, _ => by
      rw [List.zip_cons_cons, Env.lookup_cons]
      simp
  | v :: vs, a :: as, hlen, hnd, i + 1, hi, hi' => by
      rw [List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi hi'
      have hne : vs[i] ≠ v := fun hc => hnd.1 (hc ▸ List.getElem_mem hi)
      rw [List.zip_cons_cons]
      simp only [List.getElem_cons_succ]
      rw [Env.lookup_cons, if_neg hne]
      exact Env.lookup_zip vs as (by simpa using hlen) hnd.2 i hi hi'

/-- **A list of variables evaluates to what the environment binds them to.** -/
theorem Expr.evalList_map_var : ∀ (vs : List Var) (as : List Term) (ρ : Env),
    vs.length = as.length →
    (∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length), Env.lookup vs[i] ρ = some as[i]) →
    Expr.evalList (vs.map Expr.var) ρ = some as
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | v :: vs, a :: as, ρ, hlen, h => by
      have h0 : Env.lookup v ρ = some a := h 0 (by simp) (by simp)
      have hrest : Expr.evalList (vs.map Expr.var) ρ = some as :=
        Expr.evalList_map_var vs as ρ (by simpa using hlen)
          (fun i hi hi' => h (i + 1) (by simpa using hi) (by simpa using hi'))
      have hev : Expr.eval (.var v) ρ = some a := h0
      rw [List.map_cons, Expr.evalList, hev, Option.bind_some, hrest]
      rfl

/-- Every free variable of a list of variable atoms is one of them. -/
theorem Expr.freeVarsList_map_var_subset : ∀ (vs : List Var) (σ : Env),
    Expr.freeVarsList (vs.map Expr.var) σ ⊆ vs
  | [], _ => by simp
  | v :: vs, σ => by
      intro w hw
      rw [List.map_cons, Expr.freeVarsList, List.mem_union_iff] at hw
      rcases hw with hw | hw
      · rw [Expr.freeVars] at hw
        split at hw
        · exact absurd hw (by simp)
        · rw [List.mem_singleton] at hw; exact hw ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Expr.freeVarsList_map_var_subset vs σ hw)

/-- And one the environment does not bind is free. -/
theorem Expr.mem_freeVarsList_map_var : ∀ (vs : List Var) (σ : Env) {v : Var}, v ∈ vs →
    Env.lookup v σ = none → v ∈ Expr.freeVarsList (vs.map Expr.var) σ
  | [], _, _, hv, _ => by simp at hv
  | w :: vs, σ, v, hv, hn => by
      rw [List.map_cons, Expr.freeVarsList, List.mem_union_iff]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Or.inl (by rw [Expr.freeVars, hn]; simp)
      · exact Or.inr (Expr.mem_freeVarsList_map_var vs σ hv' hn)

mutual

/-- Evaluating a constructor expression binds every variable it mentions. -/
theorem Expr.lookup_isSome_of_mem_vars {ρ : Env} {v : Var} :
    ∀ {e : Expr} {t : Term}, e.OrderingFree → Expr.eval e ρ = some t →
      v ∈ e.vars → (Env.lookup v ρ).isSome
  | .lit _, _, _, _, hv => by simp [Expr.vars] at hv
  | .var w, _, _, he, hv => by
      obtain rfl : v = w := by simpa [Expr.vars] using hv
      rw [Expr.eval_var] at he
      rw [he]; rfl
  | .app f args, t, ho, he, hv => by
      rw [Expr.vars] at hv
      have hl : ∃ ts, Expr.evalList args ρ = some ts := by
        rw [Expr.eval] at he
        obtain ⟨ts, hts, -⟩ := Option.map_eq_some_iff.mp he
        exact ⟨ts, hts⟩
      obtain ⟨ts, hts⟩ := hl
      exact Expr.lookup_isSome_of_mem_varsList ho hts hv
  | .min _ _, _, ho, _, _ => by simp [Expr.OrderingFree, Expr.hasMin] at ho

@[inherit_doc Expr.lookup_isSome_of_mem_vars]
theorem Expr.lookup_isSome_of_mem_varsList {ρ : Env} {v : Var} :
    ∀ {es : List Expr} {ts : List Term}, Expr.OrderingFreeList es →
      Expr.evalList es ρ = some ts → v ∈ Expr.varsList es → (Env.lookup v ρ).isSome
  | [], _, _, _, hv => by simp [Expr.varsList] at hv
  | e :: es, _, ho, he, hv => by
      have ho' : e.OrderingFree ∧ Expr.OrderingFreeList es := Bool.or_eq_false_iff.mp ho
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨t, ht, he'⟩ := he
      obtain ⟨us, hus, -⟩ := Option.map_eq_some_iff.mp he'
      rw [Expr.varsList, List.mem_union_iff] at hv
      exact hv.elim (fun h => Expr.lookup_isSome_of_mem_vars ho'.1 ht h)
        (fun h => Expr.lookup_isSome_of_mem_varsList ho'.2 hus h)

end


/-- Replacing one operand replaces one value: what a column rule's key expression is. -/
theorem Expr.evalList_set {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList es ρ = some ts →
      ∀ (i : Nat) {e : Expr} {t : Term}, e.eval ρ = some t →
        Expr.evalList (es.set i e) ρ = some (ts.set i t)
  | [], _, h, _, _, _, _ => by
      rw [Expr.evalList, Option.some.injEq] at h
      cases h
      simp
  | a :: as, _, h, 0, e, t, he => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      rw [List.set_cons_zero, List.set_cons_zero, Expr.evalList, he, Option.bind_some, hus]
      rfl
  | a :: as, _, h, i + 1, e, t, he => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      rw [List.set_cons_succ, List.set_cons_succ, Expr.evalList, hu, Option.bind_some,
        Expr.evalList_set hus i he]
      rfl

/-- The value at one position is that operand's. -/
theorem Expr.getElem?_of_evalList {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList es ρ = some ts →
      ∀ (i : Nat) {e : Expr}, es[i]? = some e →
        ∃ t, ts[i]? = some t ∧ e.eval ρ = some t
  | [], _, _, i, _, hi => by simp at hi
  | e :: es, _, h, 0, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain rfl : e = e' := by simpa using hi
      exact ⟨u, by simp, hu⟩
  | e :: es, _, h, i + 1, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hus i (by simpa using hi)
      exact ⟨t, by simpa using ht, hev⟩

/-- A one-element operand list. -/
theorem Expr.evalList_singleton {σ : Env} {e : Expr} {ts : List Term}
    (h : Expr.evalList [e] σ = some ts) : ∃ t, e.eval σ = some t ∧ ts = [t] := by
  rw [Expr.evalList] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
  rw [Expr.evalList, Option.map_some, Option.some.injEq] at h
  exact ⟨t, ht, h.symm⟩

/-- Evaluate a pair of operands. -/
theorem Expr.evalList_pair {σ : Env} {e₁ e₂ : Expr} {ts : List Term}
    (h : Expr.evalList [e₁, e₂] σ = some ts) :
    ∃ t₁ t₂, e₁.eval σ = some t₁ ∧ e₂.eval σ = some t₂ ∧ ts = [t₁, t₂] := by
  rw [Expr.evalList] at h
  obtain ⟨t₁, ht₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨t₂, ht₂, rfl⟩ := Expr.evalList_singleton hus
  exact ⟨t₁, t₂, ht₁, ht₂, rfl⟩

/-- One column of the right-hand list moved along a congruence. What the rebuild's column
rules do to a key, pointwise. -/
theorem StoredCongList.setAt {db : Database} {as cs : List Term} {c x : Term} (i : Nat)
    (h : StoredCongList db as cs) (hget : cs[i]? = some c) (hcx : StoredCong db c x) :
    StoredCongList db as (cs.set i x) := by
  rw [StoredCongList.forall₂] at h ⊢
  induction i generalizing as cs with
  | zero =>
    cases h with
    | nil => simp at hget
    | cons hab hl =>
      obtain rfl : _ = c := by simpa using hget
      simpa using List.Forall₂.cons (hab.trans hcx) hl
  | succ n ih =>
    cases h with
    | nil => simp at hget
    | cons hab hl => simpa using List.Forall₂.cons hab (ih hl (by simpa using hget))

/-- A member of a list one position was replaced in is a member or the replacement. -/
theorem mem_or_eq_of_mem_set {α : Type _} {l : List α} {i : Nat} {b a : α}
    (h : a ∈ l.set i b) : a ∈ l ∨ a = b := by
  induction l generalizing i with
  | nil => simp at h
  | cons c cs ih =>
    cases i with
    | zero =>
      rw [List.set_cons_zero, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem _ h)
    | succ j =>
      rw [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact (ih h).imp (List.mem_cons_of_mem _) id


end Egglog
