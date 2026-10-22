import EgglogSemantics.Proofs.Match

/-! Keyed, order-free queries and held bindings. -/

namespace Egglog

/-- Every query variable is witnessed below an application, without a discarded computation arm. -/
def Query.Safe (q : Query) : Prop := q.VarsKeyed ∧ ∀ p ∈ q, p.OrderingFree


theorem Expr.var_mem_varsList {v : Var} :
    ∀ {es : List Expr}, Expr.var v ∈ es → v ∈ Expr.varsList es
  | [], h => by simp at h
  | e :: es, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp [Expr.varsList, Expr.vars]
      · exact List.mem_union_iff.mpr (Or.inr (Expr.var_mem_varsList h))

mutual

theorem Expr.argVar_mem_vars {v : Var} : ∀ {e : Expr}, e.ArgVar v → v ∈ e.vars
  | .lit _, h => h.elim
  | .var _, h => h.elim
  | .app _ _, h => h.elim Expr.var_mem_varsList Expr.argVarList_mem_vars
  | .min _ _, h => h.elim
      (fun h => List.mem_union_iff.mpr (Or.inl (Expr.argVar_mem_vars h)))
      (fun h => List.mem_union_iff.mpr (Or.inr (Expr.argVar_mem_vars h)))

theorem Expr.argVarList_mem_vars {v : Var} :
    ∀ {es : List Expr}, Expr.ArgVarList v es → v ∈ Expr.varsList es
  | [], h => h.elim
  | _ :: _, h => h.elim
      (fun h => List.mem_union_iff.mpr (Or.inl (Expr.argVar_mem_vars h)))
      (fun h => List.mem_union_iff.mpr (Or.inr (Expr.argVarList_mem_vars h)))

end

/-- Every binding of a joined match is held; no separate value sort is needed. -/
theorem ValidQuerySubst.mem_values {db : Database} {q : Query} {σ : Env}
    (h : ValidQuerySubst db q σ) : ∀ b ∈ σ, b.2 ∈ db.terms := h.mem_terms

end Egglog
