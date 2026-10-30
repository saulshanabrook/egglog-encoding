import EgglogSemantics.Proofs.Bindings
import EgglogSemantics.Proofs.NoUnions

/-! Substitution restriction, action blocks, and constructor-row reads.
Function-entry operations from the old module have been removed. -/

namespace Egglog

theorem lookup_append_of_refines {env ρ σ : Env} (hr : Env.Refines ρ σ) {v : Var} {t : Term}
    (h : Env.lookup v (env ++ ρ) = some t) : Env.lookup v (env ++ σ) = some t := by
  by_cases hv : v ∈ Env.dom env
  · rw [Env.lookup_append_of_mem hv]
    rw [Env.lookup_append_of_mem hv] at h
    exact h
  · rw [Env.lookup_append_of_not_mem hv]
    rw [Env.lookup_append_of_not_mem hv] at h
    exact hr (v, t) (Env.mem_of_lookup h)

mutual

/-- **An evaluation survives un-restricting the substitution.** `Expr.eval` reads the
environment only through `Env.lookup`, so what the pattern's own restriction pinned down the
whole match pins down too — which is what lets a query atom's reading be used at the
environment the *head* runs in. -/
theorem Expr.eval_of_refines {env ρ σ : Env} (hr : Env.Refines ρ σ) :
    ∀ (e : Expr) {t : Term}, e.eval (env ++ ρ) = some t → e.eval (env ++ σ) = some t
  | .lit _, _, h => h
  | .var _, _, h => by
      rw [Expr.eval] at h ⊢
      exact lookup_append_of_refines hr h
  | .app f args, _, h => by
      simp only [Expr.eval] at h ⊢
      obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
      rw [Expr.evalList_of_refines hr args hts]
      exact congrArg some hap
  | .min a b, _, h => by
      rw [Expr.eval_min] at h ⊢
      obtain ⟨x, hx, hmap⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rw [Expr.eval_of_refines hr a hx, Option.bind_some, Expr.eval_of_refines hr b hy,
        Option.map_some]

@[inherit_doc Expr.eval_of_refines]
theorem Expr.evalList_of_refines {env ρ σ : Env} (hr : Env.Refines ρ σ) :
    ∀ (es : List Expr) {ts : List Term},
      Expr.evalList es (env ++ ρ) = some ts → Expr.evalList es (env ++ σ) = some ts
  | [], _, h => h
  | e :: es, _, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [Expr.eval_of_refines hr e ht, Expr.evalList_of_refines hr es hts]
      exact congrArg some hcons

end

/-- Every pattern of a matched query holds, at its own restriction of the substitution. -/
theorem patternHolds_of_mem_matchQuery {d : FDatabase} {q : Query} {σ : Env}
    (h : σ ∈ matchQuery d q) {p : Pattern} (hp : p ∈ q) :
    patternHolds d p (Env.canon (p.freeVars []) σ) = true := by
  rw [matchQuery, List.mem_filter] at h
  exact List.all_eq_true.mp h.2 p hp

theorem execActions_append {σ : Env} {as bs : List Action} : ∀ {d e : FDatabase},
    execActions σ d (as ++ bs) = some e →
      ∃ m, execActions σ d as = some m ∧ execActions σ m bs = some e := by
  induction as with
  | nil => intro d e h; exact ⟨d, rfl, h⟩
  | cons a as ih =>
    intro d e h
    cases hv : execAction σ d a with
    | none => rw [List.cons_append, execActions, hv] at h; simp at h
    | some d' =>
      rw [List.cons_append, execActions, hv, Option.bind_some] at h
      obtain ⟨m, hm, hme⟩ := ih h
      exact ⟨m, by rw [execActions, hv, Option.bind_some]; exact hm, hme⟩


/-- Evaluating a concatenation, in the direction that *builds* one. `Expr.evalList_append` is
the elimination. -/
theorem Expr.evalList_append_eq {σ : Env} :
    ∀ {es fs : List Expr} {as bs : List Term},
      Expr.evalList es σ = some as → Expr.evalList fs σ = some bs →
        Expr.evalList (es ++ fs) σ = some (as ++ bs) := by
  intro es
  induction es with
  | nil =>
      intro fs as bs h₁ h₂
      obtain rfl : as = [] := (Option.some.inj h₁).symm
      simpa using h₂
  | cons e es ih =>
      intro fs as bs h₁ h₂
      rw [Expr.evalList] at h₁
      obtain ⟨t, ht, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h₁
      simp only [List.cons_append, Expr.evalList, ht, Option.bind_some, ih hus h₂,
        Option.map_some]

/-- Running a concatenation of action blocks, in the direction that *builds* one.
`execActions_append` is the elimination. -/
theorem execActions_append_eq {σ : Env} {as bs : List Action} : ∀ {d m e : FDatabase},
    execActions σ d as = some m → execActions σ m bs = some e →
      execActions σ d (as ++ bs) = some e := by
  induction as with
  | nil =>
      intro d m e h₁ h₂
      obtain rfl : d = m := Option.some.inj h₁
      simpa using h₂
  | cons a as ih =>
      intro d m e h₁ h₂
      rw [execActions] at h₁
      obtain ⟨d₁, hd₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      rw [List.cons_append, execActions, hd₁, Option.bind_some]
      exact ih h₁ h₂

theorem mem_zip_self {α : Type _} : ∀ {xs : List α} {q : α × α},
    q ∈ xs.zip xs → q.1 = q.2 ∧ q.1 ∈ xs
  | [], _, h => by simp at h
  | x :: xs, q, h => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨rfl, List.mem_cons_self⟩
      · exact ⟨(mem_zip_self h).1, List.mem_cons_of_mem _ (mem_zip_self h).2⟩

theorem congrKeys_self {cl : Finset (Term × Term)} {as : List Term}
    (h : ∀ a ∈ as, (a, a) ∈ cl) : FDatabase.congrTuple cl as as = true := by
  simp only [FDatabase.congrTuple, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, decide_eq_true_eq]
  intro q hq
  obtain ⟨heq, hmem⟩ := mem_zip_self hq
  rw [show q = (q.1, q.1) from Prod.ext rfl heq.symm]
  exact h q.1 hmem


/-- Evaluated columns build an atom at any name. -/
theorem execAction_atom_of_eval {σ : Env} {d : FDatabase} {f : FnName} {cols : List Expr}
    {ts : List Term} (hev : Expr.evalList cols σ = some ts) :
    execAction σ d (.expr (.app f cols)) = some (d.addTerm (.app f ts)) := by
  simp [execAction, Expr.eval, hev]

/-- A row and its held columns make its atom match. -/
theorem patternHolds_entry_of_mem_rows {d : FDatabase} (hc : d.SubtermClosed)
    {as : List Expr} {f : FnName} {σ : Env} {ts : List Term}
    (he : Expr.evalList as σ = some ts) (hr : (⟨f, ts⟩ : Row) ∈ d.rows)
    (ht : ∀ t ∈ ts, t ∈ d.terms) : patternHolds d (.expr (.app f as)) σ = true := by
  have hh : d.holdsAll ts = true := by
    simp only [FDatabase.holdsAll, List.all_eq_true, decide_eq_true_eq]
    exact fun t ht' s hs => hc t (ht t ht') s hs
  simp only [patternHolds, Expr.eval, he, Option.map_some, hh, if_true,
    FDatabase.hasCtorRow, List.any_eq_true]
  refine ⟨⟨f, ts⟩, hr, ?_⟩
  simp only [beq_self_eq_true, Bool.true_and]
  exact congrKeys_self (fun t h => (FDatabase.mem_closureF_iff hc (ht t h) (ht t h)).mpr
    (Database.toCong ((FDatabase.mem_toDatabase_terms hc).mpr (ht t h))))

/-- Diagonality is unnecessary once index soundness is stated explicitly. -/
theorem matches_of_patternHolds {d : FDatabase} (he : d.Closed) (_hr : d.EqsRefl)
    (hi : d.IndexOk) {p : Pattern} {σ : Env} (h : patternHolds d p σ = true) :
    Matches d.toDatabase p σ := patternHolds_matches he hi h

theorem validQuerySubst_of_mem_matchQuery_diag {d : FDatabase} (he : d.Closed)
    (_hr : d.EqsRefl) (hi : d.IndexOk) {q : Query} {σ : Env} (h : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ :=
  validQuerySubst_of_mem_matchQuery he hi h

end Egglog
