import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.Congruence.Flatten

/-! Source variables remain present in flattened queries. -/

namespace Egglog.Congruence

/-- **A `.var` argument survives the flattening as the read's own key column.** -/
theorem mem_varsList_encodeQueryArgs_of_mem : ∀ (es : List Expr) (n : Nat) {v : Var},
    Expr.var v ∈ es → v ∈ Expr.varsList (encodeQueryArgs es n).1
  | [], _, _, h => absurd h (by simp)
  | e :: es, n, v, h => by
      have hsplit : (encodeQueryArgs (e :: es) n).1
          = (encodeQueryExpr e n).1 :: (encodeQueryArgs es (encodeQueryExpr e n).2.2).1 := rfl
      rw [hsplit, Expr.varsList, List.mem_union_iff]
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inl (by
          rw [show (encodeQueryExpr (Expr.var v) n).1 = Expr.var v from rfl, Expr.vars]
          exact List.mem_cons_self)
      · exact Or.inr (mem_varsList_encodeQueryArgs_of_mem es _ h')

mutual

/-- **And so a variable at an argument position is one the emitted reads mention**, in an
ordering-free expression: a `min` emits no read. -/
theorem mem_vars_encodeQueryExpr_of_argVar : ∀ (e : Expr) (n : Nat) {v : Var},
    e.OrderingFree → Expr.ArgVar v e → v ∈ Query.vars (encodeQueryExpr e n).2.1
  | .lit _, _, _, _, h => absurd h id
  | .var _, _, _, _, h => absurd h id
  | .min _ _, _, _, hof, _ => (Expr.not_orderingFree_min hof).elim
  | .ite _ _ _ _, _, _, hof, _ => (Expr.not_orderingFree_ite hof).elim
  | .app f args, n, v, hof, h => by
      have hsplit : (encodeQueryExpr (.app f args) n).2.1
          = (encodeQueryArgs args n).2.1
            ++ [Pattern.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
              [Expr.var (freshVar (encodeQueryArgs args n).2.2)]))] := rfl
      rw [hsplit, Query.mem_vars_append]
      rcases (h : Expr.var v ∈ args ∨ Expr.ArgVarList v args) with hv | hv
      · refine Or.inr (Query.mem_vars.mpr ⟨_, List.mem_cons_self, ?_⟩)
        rw [Pattern.vars, Expr.vars, Expr.mem_varsList_append]
        exact Or.inl (mem_varsList_encodeQueryArgs_of_mem args n hv)
      · exact Or.inl (mem_vars_encodeQueryArgs_of_argVarList args n
          (Expr.orderingFree_app hof) hv)

@[inherit_doc mem_vars_encodeQueryExpr_of_argVar]
theorem mem_vars_encodeQueryArgs_of_argVarList : ∀ (es : List Expr) (n : Nat) {v : Var},
    Expr.OrderingFreeList es → Expr.ArgVarList v es →
      v ∈ Query.vars (encodeQueryArgs es n).2.1
  | [], _, _, _, h => absurd h id
  | e :: es, n, v, hof, h => by
      have hsplit : (encodeQueryArgs (e :: es) n).2.1
          = (encodeQueryExpr e n).2.1
            ++ (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.1 := rfl
      rw [hsplit, Query.mem_vars_append]
      rcases (h : Expr.ArgVar v e ∨ Expr.ArgVarList v es) with hv | hv
      · exact Or.inl (mem_vars_encodeQueryExpr_of_argVar e n
          (Expr.orderingFreeList_cons hof).1 hv)
      · exact Or.inr (mem_vars_encodeQueryArgs_of_argVarList es _
          (Expr.orderingFreeList_cons hof).2 hv)

end

@[inherit_doc mem_vars_encodeQueryExpr_of_argVar]
theorem mem_vars_encodePattern_of_argVar : ∀ (p : Pattern) (n : Nat) {v : Var},
    p.OrderingFree → Pattern.ArgVar v p → v ∈ Query.vars (encodePattern p n).1
  | .expr e, n, _, hof, h => mem_vars_encodeQueryExpr_of_argVar e n hof h
  | .eq e₁ e₂, n, v, hof, h => by
      have hsplit : (encodePattern (.eq e₁ e₂) n).1
          = ((encodeQueryExpr e₁ n).2.1
              ++ (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).2.1)
            ++ [Pattern.eq (encodeQueryExpr e₁ n).1
                 (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1] := rfl
      rw [hsplit, Query.mem_vars_append]
      refine Or.inl (Query.mem_vars_append.mpr ?_)
      rcases (h : Expr.ArgVar v e₁ ∨ Expr.ArgVar v e₂) with hv | hv
      · exact Or.inl (mem_vars_encodeQueryExpr_of_argVar e₁ n hof.1 hv)
      · exact Or.inr (mem_vars_encodeQueryExpr_of_argVar e₂ _ hof.2 hv)

@[inherit_doc mem_vars_encodeQueryExpr_of_argVar]
theorem mem_vars_encodeQuery_of_argVar : ∀ (q : Query) (n : Nat) {v : Var} {p : Pattern},
    (∀ p ∈ q, p.OrderingFree) → p ∈ q → Pattern.ArgVar v p →
      v ∈ Query.vars (encodeQuery q n).1
  | [], _, _, _, _, hp, _ => absurd hp (by simp)
  | p :: ps, n, _, p', hof, hp, h => by
      have hsplit : (encodeQuery (p :: ps) n).1
          = (encodePattern p n).1 ++ (encodeQuery ps (encodePattern p n).2).1 := rfl
      rw [hsplit, Query.mem_vars_append]
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact Or.inl (mem_vars_encodePattern_of_argVar p' n (hof p' List.mem_cons_self) h)
      · exact Or.inr (mem_vars_encodeQuery_of_argVar ps _
          (fun p'' hp'' => hof p'' (List.mem_cons_of_mem _ hp'')) hp' h)

end Egglog.Congruence
