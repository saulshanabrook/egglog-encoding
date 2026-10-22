import EgglogSemantics.Proofs.Bindings
import EgglogSemantics.Proofs.Entries

/-! Constructing executable query matches from valued substitutions. -/

namespace Egglog

/-- **`matchQuery` completeness, in general form.** A substitution the enumerator will offer is
`Env.canon`-shaped at `Query.freeVars`' own order and drawn from `FDatabase.terms`; the
per-atom check then reads it restricted to that atom, and the two restrictions compose. -/
theorem mem_matchQuery_of_lookup {d : FDatabase} {q : Query} {τ : Env}
    (hdef : ∀ v ∈ Query.freeVars q [], (Env.lookup v τ).isSome = true)
    (hval : ∀ v ∈ Query.freeVars q [], ∀ t, Env.lookup v τ = some t → t ∈ d.terms)
    (hp : ∀ p ∈ q, patternHolds d p (Env.canon (p.freeVars []) τ) = true) :
    Env.canon (Query.freeVars q []) τ ∈ matchQuery d q := by
  rw [matchQuery, List.mem_filter]
  refine ⟨mem_assignments.mpr ⟨Env.dom_canon hdef, fun b hb => ?_⟩, List.all_eq_true.mpr ?_⟩
  · obtain ⟨hmem, hlk⟩ := Env.mem_canon hb
    exact hval b.1 hmem b.2 hlk
  · intro p hpq
    rw [Env.canon_canon (Query.freeVars_subset hpq) (Query.freeVars_nodup q [])]
    exact hp p hpq


/-- A constructor atom answered by an indexed row with held arguments. -/
def EntryRead (d : FDatabase) (τ : Env) (p : Pattern) : Prop :=
  ∃ f as ts, p = .expr (.app f as) ∧ Expr.evalList as τ = some ts ∧
    (⟨f, ts⟩ : Row) ∈ d.rows ∧ ∀ t ∈ ts, t ∈ d.terms

theorem EntryRead.bound {d : FDatabase} {τ : Env} {p : Pattern} (h : EntryRead d τ p)
    {v : Var} (hv : v ∈ p.freeVars []) : (Env.lookup v τ).isSome := by
  obtain ⟨f, as, ts, rfl, he, _, _⟩ := h
  exact Expr.evalList_bound he ((Pattern.mem_freeVars _).mp hv).1

theorem EntryRead.holds {d : FDatabase} (hc : d.SubtermClosed) {τ : Env} {p : Pattern}
    (h : EntryRead d τ p) : patternHolds d p (Env.canon (p.freeVars []) τ) = true := by
  obtain ⟨f, as, ts, rfl, he, hr, ht⟩ := h
  apply patternHolds_entry_of_mem_rows hc ?_ hr ht
  rw [Expr.evalList_agreeOn as (fun v hv => Env.lookup_canon
    (Pattern.freeVars_nodup _ []) ((Pattern.mem_freeVars (.expr (.app f as))).mpr ⟨hv, by simp⟩))]
  exact he

theorem mem_matchQuery_of_entryReads {d : FDatabase} (hc : d.SubtermClosed)
    {τ : Env} {q : Query} (hv : ∀ b ∈ τ, b.2 ∈ d.terms) (h : ∀ p ∈ q, EntryRead d τ p) :
    Env.canon (Query.freeVars q []) τ ∈ matchQuery d q := by
  apply mem_matchQuery_of_lookup
  · intro v hm
    obtain ⟨p, hp, hpm⟩ := Query.mem_freeVars.mp hm
    exact (h p hp).bound hpm
  · intro v _ t ht
    exact hv (v, t) (Env.mem_of_lookup ht)
  · exact fun p hp => (h p hp).holds hc

theorem Query.freeVars_of_atom {q : Query} {f : FnName} {cols : List Expr} {v : Var}
    (hp : Pattern.expr (.app f cols) ∈ q) (hv : v ∈ Expr.varsList cols) :
    v ∈ Query.freeVars q [] :=
  Query.freeVars_subset hp ((Pattern.mem_freeVars _).mpr ⟨hv, by simp⟩)

theorem Expr.evalList_canon_query {q : Query} {es : List Expr}
    {τ : Env} {ts : List Term} (he : Expr.evalList es τ = some ts)
    (hv : ∀ v ∈ Expr.varsList es, v ∈ Query.freeVars q []) :
    Expr.evalList es (Env.canon (Query.freeVars q []) τ) = some ts := by
  rw [Expr.evalList_agreeOn es (fun v hm => Env.lookup_canon
    (Query.freeVars_nodup q []) (hv v hm))]
  exact he

/-- A singleton head records its evaluated application. -/
theorem execLocalActions_atom_of_eval {d : FDatabase} {f : FnName} {cols : List Expr}
    {ts : List Term} {σ : Env} (he : Expr.evalList cols σ = some ts) :
    ∃ d', execActions σ d [.expr (.app f cols)] = some d' ∧ Term.app f ts ∈ d'.terms := by
  refine ⟨d.addTerm (.app f ts), ?_, FDatabase.self_mem_addTerm _ _⟩
  simp [execActions, execAction_atom_of_eval he]

end Egglog
