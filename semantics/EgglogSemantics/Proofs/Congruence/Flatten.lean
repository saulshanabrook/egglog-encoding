import EgglogSemantics.Congruence.Encode

/-! The flattening pass emits only flat entry atoms and equalities of leaves. -/

namespace Egglog.Congruence

/-- An id expression usable as one column of a flat query. A `min` is neither a leaf nor
flattened: the source domain contains none. -/
def Leaf : Expr → Prop
  | .lit _ | .var _ => True
  | .app _ _ | .min _ _ | .ite _ _ _ _ => False

/-- Complete entry atoms have only leaf columns; equalities compare leaves. -/
def FlatPattern : Pattern → Prop
  | .expr (.app _ es) => ∀ e ∈ es, Leaf e
  | .expr _ => False
  | .eq a b => Leaf a ∧ Leaf b

mutual

/-- The returned id is a leaf and all emitted atoms are flat, for an ordering-free
expression. -/
theorem encodeQueryExpr_flat : ∀ (e : Expr) (n : Nat), e.OrderingFree →
    Leaf (encodeQueryExpr e n).1 ∧ ∀ p ∈ (encodeQueryExpr e n).2.1, FlatPattern p
  | .lit _, _, _ | .var _, _, _ => ⟨trivial, by simp [encodeQueryExpr]⟩
  | .min _ _, _, ho => by simp [Expr.OrderingFree, Expr.hasMin] at ho
  | .ite _ _ _ _, _, ho => by simp [Expr.OrderingFree, Expr.hasMin] at ho
  | .app f es, n, ho => by
      obtain ⟨hids, hps⟩ := encodeQueryArgs_flat es n
        (by simpa [Expr.OrderingFree, Expr.OrderingFreeList, Expr.hasMin] using ho)
      refine ⟨trivial, ?_⟩
      intro p hp
      change p ∈ (encodeQueryArgs es n).2.1 ++ [_] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hps p hp
      · obtain rfl := List.mem_singleton.mp hp
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hids e he
        · obtain rfl := List.mem_singleton.mp he
          trivial

/-- Argument ids and their emitted atoms satisfy the same invariant. -/
theorem encodeQueryArgs_flat : ∀ (es : List Expr) (n : Nat), Expr.OrderingFreeList es →
    (∀ e ∈ (encodeQueryArgs es n).1, Leaf e) ∧
      ∀ p ∈ (encodeQueryArgs es n).2.1, FlatPattern p
  | [], _, _ => ⟨by simp [encodeQueryArgs], by simp [encodeQueryArgs]⟩
  | e :: es, n, ho => by
      have ho' : e.OrderingFree ∧ Expr.OrderingFreeList es := by
        simpa [Expr.OrderingFreeList, Expr.OrderingFree, Expr.hasMinList] using ho
      obtain ⟨he, hp⟩ := encodeQueryExpr_flat e n ho'.1
      obtain ⟨hes, hps⟩ := encodeQueryArgs_flat es (encodeQueryExpr e n).2.2 ho'.2
      constructor
      · intro x hx
        change x ∈ (encodeQueryExpr e n).1 :: _ at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he
        · exact hes x hx
      · intro p h
        change p ∈ (encodeQueryExpr e n).2.1 ++ _ at h
        rcases List.mem_append.mp h with h | h
        · exact hp p h
        · exact hps p h

end

theorem encodePattern_flat (p : Pattern) (n : Nat) (ho : p.OrderingFree) :
    ∀ q ∈ (encodePattern p n).1, FlatPattern q := by
  cases p with
  | expr e => exact (encodeQueryExpr_flat e n ho).2
  | eq a b =>
      obtain ⟨ha, hpa⟩ := encodeQueryExpr_flat a n ho.1
      obtain ⟨hb, hpb⟩ := encodeQueryExpr_flat b (encodeQueryExpr a n).2.2 ho.2
      intro q hq
      change q ∈ (_ ++ _) ++ [_] at hq
      rcases List.mem_append.mp hq with hq | hq
      · rcases List.mem_append.mp hq with hq | hq
        · exact hpa q hq
        · exact hpb q hq
      · obtain rfl := List.mem_singleton.mp hq
        exact ⟨ha, hb⟩

/-- Every ordering-free source query compiles to flat atoms, independent of the other
source-domain assumptions. -/
theorem encodeQuery_flat (q : Query) (n : Nat) (ho : ∀ p ∈ q, p.OrderingFree) :
    ∀ p ∈ (encodeQuery q n).1, FlatPattern p := by
  induction q generalizing n with
  | nil => simp [encodeQuery]
  | cons p ps ih =>
      intro q hq
      change q ∈ (encodePattern p n).1 ++ _ at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact encodePattern_flat p n (ho p List.mem_cons_self) q hq
      · exact ih (encodePattern p n).2 (fun p' hp' => ho p' (List.mem_cons_of_mem _ hp')) q hq

mutual

/-- Exactly one fresh id per application occurrence of an ordering-free expression. This
fixes the recursion's premise positions without retaining any extra flattening metadata. -/
theorem encodeQueryExpr_next : ∀ (e : Expr) (n : Nat), e.OrderingFree →
    (encodeQueryExpr e n).2.2 = n + e.ctors.length
  | .lit _, _, _ | .var _, _, _ => rfl
  | .min _ _, _, ho => by simp [Expr.OrderingFree, Expr.hasMin] at ho
  | .ite _ _ _ _, _, ho => by simp [Expr.OrderingFree, Expr.hasMin] at ho
  | .app _ es, n, ho => by
      change (encodeQueryArgs es n).2.2 + 1 = _
      rw [encodeQueryArgs_next es n
        (by simpa [Expr.OrderingFree, Expr.OrderingFreeList, Expr.hasMin] using ho)]
      simp only [Expr.ctors, List.length_cons]
      omega

@[inherit_doc encodeQueryExpr_next]
theorem encodeQueryArgs_next : ∀ (es : List Expr) (n : Nat), Expr.OrderingFreeList es →
    (encodeQueryArgs es n).2.2 = n + (Expr.ctorsList es).length
  | [], _, _ => rfl
  | e :: es, n, ho => by
      have ho' : e.OrderingFree ∧ Expr.OrderingFreeList es := by
        simpa [Expr.OrderingFreeList, Expr.OrderingFree, Expr.hasMinList] using ho
      change (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.2 = _
      rw [encodeQueryArgs_next es _ ho'.2, encodeQueryExpr_next e n ho'.1]
      simp [Expr.ctorsList, Nat.add_assoc]

end

mutual

/-- The variable supply never runs backwards, whatever the expression: a `min` consumes
nothing, and an application consumes its arguments' ids and then one more. -/
theorem le_encodeQueryExpr_next : ∀ (e : Expr) (n : Nat), n ≤ (encodeQueryExpr e n).2.2
  | .lit _, _ | .var _, _ | .min _ _, _ | .ite _ _ _ _, _ => Nat.le_refl _
  | .app _ es, n => by
      change n ≤ (encodeQueryArgs es n).2.2 + 1
      exact Nat.le_succ_of_le (le_encodeQueryArgs_next es n)

@[inherit_doc le_encodeQueryExpr_next]
theorem le_encodeQueryArgs_next : ∀ (es : List Expr) (n : Nat), n ≤ (encodeQueryArgs es n).2.2
  | [], _ => Nat.le_refl _
  | e :: es, n => by
      change n ≤ (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.2
      exact (le_encodeQueryExpr_next e n).trans (le_encodeQueryArgs_next es _)

end

end Egglog.Congruence
