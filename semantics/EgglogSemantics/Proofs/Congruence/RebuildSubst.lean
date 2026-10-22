import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.Source.RebuildVars

/-! Substitutions for the generated output and child propagation rules. -/

namespace Egglog.Congruence

theorem rebuildVars_eq_map (k : Nat) : rebuildVars k = (rebuildVarNames k).map Expr.var := by
  rw [rebuildVars, rebuildVarNames, List.map_map]; rfl

/-- A row's key columns and the two ids used by either rebuilding rule. -/
def rebuildSubst (cs : List Term) (e x : Term) : Env :=
  ("@e", e) :: ("@x", x) :: (rebuildVarNames cs.length).zip cs

@[simp] theorem rebuildSubst_e (cs : List Term) (e x : Term) :
    Env.lookup "@e" (rebuildSubst cs e x) = some e := by
  simp [rebuildSubst, Env.lookup_cons]

@[simp] theorem rebuildSubst_x (cs : List Term) (e x : Term) :
    Env.lookup "@x" (rebuildSubst cs e x) = some x := by
  simp [rebuildSubst, Env.lookup_cons]

theorem rebuildSubst_key {cs : List Term} {e x : Term} (i : Nat) (hi : i < cs.length) :
    Env.lookup ("@c" ++ toString i) (rebuildSubst cs e x) = some cs[i] := by
  have hv : "@c" ++ toString i ∈ rebuildVarNames cs.length := by
    rw [← getElem_rebuildVarNames hi]; exact List.getElem_mem _
  have hne : "@c" ++ toString i ≠ "@e" := by
    intro heq; rw [heq] at hv
    exact not_mem_rebuildVarNames (c := 'e') (by decide) (by decide) _ hv
  have hnx : "@c" ++ toString i ≠ "@x" := by
    intro heq; rw [heq] at hv
    exact not_mem_rebuildVarNames (c := 'x') (by decide) (by decide) _ hv
  simp only [rebuildSubst, Env.lookup_cons, if_neg hne, if_neg hnx]
  rw [← getElem_rebuildVarNames hi]
  exact Env.lookup_zip _ _ (length_rebuildVarNames _) (rebuildVarNames_nodup _) i
    (by simpa only [length_rebuildVarNames] using hi) hi

theorem eval_rebuildVars {sig : Signature} (cs : List Term) (e x : Term)
    (hvalues : ∀ c ∈ cs, c.IsValue sig) :
    Expr.evalList sig (rebuildVars cs.length) (rebuildSubst cs e x) = some cs := by
  rw [rebuildVars_eq_map]
  apply Expr.evalList_map_var _ _ _ (length_rebuildVarNames _) ?_ hvalues
  intro i hi hi'
  rw [getElem_rebuildVarNames hi']
  exact rebuildSubst_key i hi'

end Egglog.Congruence
