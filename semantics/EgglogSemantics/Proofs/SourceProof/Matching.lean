import EgglogSemantics.SourceProof.Checker
import EgglogSemantics.Proofs.SourceProof.Actions
import EgglogSemantics.Proofs.Query

namespace Egglog.SourceProof

/-- A monotone query head consumes one claim and leaves the remaining query to match. -/
private theorem premisesMatch_cons {σ : Env} {p : Pattern} {ps : Query} {cs : List Claim}
    (hm : p.monotoneB = true) (h : premisesMatch σ (p :: ps) cs = true) :
    ∃ c cs', cs = c :: cs' ∧ premisesMatch σ [p] [c] = true ∧
      premisesMatch σ ps cs' = true := by
  cases p <;> cases cs <;> simp_all [premisesMatch, Pattern.monotoneB]

theorem premiseMatches_sound {db : Database} {σ : Env} {p : Pattern} {c : Claim}
    (hX : db.subsumed = ∅) (ho : p.OrderingFree) (hm : p.monotoneB = true)
    (hc : c.Holds db) (h : premisesMatch σ [p] [c] = true) : Matches db p σ := by
  cases p with
  | expr e =>
      simp only [premisesMatch, Bool.and_true, Bool.and_eq_true_iff, beq_iff_eq] at h
      exact .atom (Expr.Matches.of_eval hX (Expr.minOverVars_of_orderingFree e ho) h.1
        (hc.trans hc.symm).toCong).2
  | eq a b =>
      simp only [premisesMatch, Bool.and_true, Bool.and_eq_true_iff, beq_iff_eq] at h
      exact .equal
        (Expr.Matches.of_eval hX (Expr.minOverVars_of_orderingFree a ho.1) h.1
          (hc.trans hc.symm).toCong).2
        (Expr.Matches.of_eval hX (Expr.minOverVars_of_orderingFree b ho.2) h.2
          (hc.symm.trans hc).toCong).2 h.1 h.2 hc.toCong
  | ne _ _ => simp [Pattern.monotoneB] at hm

theorem premisesMatch_sound {db : Database} {σ : Env} {q : Query} {cs : List Claim}
    (hX : db.subsumed = ∅) (ho : ∀ p ∈ q, p.OrderingFree)
    (hm : ∀ p ∈ q, p.monotoneB = true)
    (hc : ∀ c ∈ cs, c.Holds db) (h : premisesMatch σ q cs = true) :
    ∀ p ∈ q, Matches db p σ := by
  induction q generalizing cs with
  | nil => simp
  | cons p ps ih =>
      obtain ⟨c, cs, rfl, hp, hps⟩ := premisesMatch_cons (hm p (by simp)) h
      intro p' hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact premiseMatches_sound hX (ho p' (by simp)) (hm p' (by simp))
          (hc c (by simp)) hp
      · exact ih (fun p hp => ho p (by simp [hp])) (fun p hp => hm p (by simp [hp]))
          (fun c hc' => hc c (by simp [hc'])) hps p' hp'

mutual

/-- Every variable value occurs in the instance of an ordering-free expression. -/
theorem eval_lookup_subterm {σ : Env} {v : Var} {s : Term}
    (hv : Env.lookup v σ = some s) :
    ∀ {e : Expr} {t : Term}, e.OrderingFree → e.eval σ = some t →
      v ∈ e.vars → s ∈ t.subterms
  | .lit _, _, _, _, hmem => by simp at hmem
  | .var w, _, _, he, hmem => by
      obtain rfl : v = w := by simpa using hmem
      rw [Expr.eval_var, hv, Option.some.injEq] at he
      exact he ▸ Term.self_mem_subterms s
  | .app _ _, _, ho, he, hmem => by
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨t, ht, hsub⟩ := evalList_lookup_subterm hv ho hts hmem
      exact Term.IsSubterm.arg ht hsub
  | .min _ _, _, ho, _, _ => by simp [Expr.OrderingFree, Expr.hasMin] at ho

/-- A variable value occurs in one of the evaluated arguments that mention it. -/
theorem evalList_lookup_subterm {σ : Env} {v : Var} {s : Term}
    (hv : Env.lookup v σ = some s) :
    ∀ {es : List Expr} {ts : List Term}, Expr.OrderingFreeList es →
      Expr.evalList es σ = some ts → v ∈ Expr.varsList es →
      ∃ t ∈ ts, s ∈ t.subterms
  | [], _, _, _, hmem => by simp at hmem
  | e :: es, _, ho, he, hmem => by
      have ho' : e.OrderingFree ∧ Expr.OrderingFreeList es := Bool.or_eq_false_iff.mp ho
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      rcases List.mem_union_iff.mp hmem with hmem | hmem
      · exact ⟨t, by simp, eval_lookup_subterm hv ho'.1 ht hmem⟩
      · obtain ⟨u, hu, hsub⟩ := evalList_lookup_subterm hv ho'.2 hts hmem
        exact ⟨u, List.mem_cons_of_mem _ hu, hsub⟩

end

/-- A matched pattern supports its variable values on one of the claim's sides. -/
theorem premiseMatches_lookup_subterm {σ : Env} {p : Pattern} {c : Claim}
    (ho : p.OrderingFree) (hm : p.monotoneB = true) (h : premisesMatch σ [p] [c] = true)
    {v : Var} {s : Term} (hv : v ∈ p.vars) (hs : Env.lookup v σ = some s) :
    s ∈ c.lhs.subterms ∨ s ∈ c.rhs.subterms := by
  cases p with
  | expr e =>
      simp only [premisesMatch, Bool.and_true, Bool.and_eq_true_iff, beq_iff_eq] at h
      exact Or.inl (eval_lookup_subterm hs ho h.1 hv)
  | eq a b =>
      simp only [premisesMatch, Bool.and_true, Bool.and_eq_true_iff, beq_iff_eq] at h
      rcases List.mem_union_iff.mp hv with hv | hv
      · exact Or.inl (eval_lookup_subterm hs ho.1 h.1 hv)
      · exact Or.inr (eval_lookup_subterm hs ho.2 h.2 hv)
  | ne _ _ => simp [Pattern.monotoneB] at hm

/-- Matching supported claims suffices to support every query substitution value. -/
theorem premisesMatch_values {db : Database} (hw : db.WF) {σ : Env}
    {q : Query} {cs : List Claim} (ho : ∀ p ∈ q, p.OrderingFree)
    (hm : ∀ p ∈ q, p.monotoneB = true)
    (hc : ∀ c ∈ cs, c.Holds db) (hdom : (Env.dom σ).Perm q.vars)
    (h : premisesMatch σ q cs = true) : ∀ b ∈ σ, b.2 ∈ db.terms := by
  have hvar : ∀ v ∈ q.vars, ∀ s, Env.lookup v σ = some s → s ∈ db.terms := by
    clear hdom
    induction q generalizing cs with
    | nil => simp
    | cons p ps ih =>
        obtain ⟨c, cs, rfl, hp, hps⟩ := premisesMatch_cons (hm p (by simp)) h
        intro v hv s hs
        rcases List.mem_union_iff.mp hv with hv | hv
        · rcases premiseMatches_lookup_subterm (ho p (by simp)) (hm p (by simp))
            hp hv hs with hl | hr
          · exact hw.subtermClosed _ (eqsInTerms_free (hc c (by simp))).1 hl
          · exact hw.subtermClosed _ (eqsInTerms_free (hc c (by simp))).2 hr
        · exact ih (fun p hp => ho p (by simp [hp]))
            (fun p hp => hm p (by simp [hp]))
            (fun c hc' => hc c (by simp [hc'])) hps v hv s hs
  intro b hb
  exact hvar b.1 (hdom.mem_iff.mp (Env.mem_dom_of_mem hb)) b.2
    ((Env.lookup_eq_some_iff_mem (hdom.symm.nodup q.vars_nodup)).mpr hb)

end Egglog.SourceProof
