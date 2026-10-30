import EgglogSemantics.Proofs.Congruence.Flatten
import EgglogSemantics.Proofs.Congruence.MetadataSyntax
import EgglogSemantics.Proofs.MatchValues
import EgglogSemantics.Proofs.Source.Execution
import EgglogSemantics.Proofs.Congruence.QueryVars

/-! Generated queries bind every variable through a constructor or table column. -/

namespace Egglog.Congruence

private def KeyedIn (q : Query) (v : Var) : Prop := ∃ p ∈ q, p.ArgVar v

private theorem KeyedIn.mono {q q' : Query} {v : Var} (h : KeyedIn q v)
    (hh : q ⊆ q') : KeyedIn q' v := by
  obtain ⟨p, hp, hv⟩ := h
  exact ⟨p, hh hp, hv⟩

private theorem Leaf.orderingFree {e : Expr} (h : Leaf e) : e.OrderingFree := by
  cases e <;> first | rfl | contradiction

private theorem leaves_orderingFree {es : List Expr} (h : ∀ e ∈ es, Leaf e) :
    Expr.OrderingFreeList es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      exact Bool.or_eq_false_iff.mpr ⟨(h e List.mem_cons_self).orderingFree,
        ih (fun e he => h e (List.mem_cons_of_mem _ he))⟩

private theorem leaf_var_member {es : List Expr} {v : Var}
    (h : ∀ e ∈ es, Leaf e) (hv : v ∈ Expr.varsList es) : Expr.var v ∈ es := by
  induction es with
  | nil => simp [Expr.varsList] at hv
  | cons e es ih =>
      rcases List.mem_union_iff.mp hv with hv | hv
      · have he := h e List.mem_cons_self
        cases e with
        | lit => simp [Expr.vars] at hv
        | var w => obtain rfl := List.mem_singleton.mp hv; exact List.mem_cons_self
        | app | min | ite => contradiction
      · exact List.mem_cons_of_mem _ (ih (fun e he => h e (List.mem_cons_of_mem _ he)) hv)

private theorem flatAtom_safe {f : FnName} {es : List Expr} (h : ∀ e ∈ es, Leaf e) :
    (∀ v ∈ (Pattern.expr (.app f es)).vars, (Pattern.expr (.app f es)).ArgVar v) ∧
      (Pattern.expr (.app f es)).OrderingFree :=
  ⟨fun _ hv => Or.inl (leaf_var_member h hv), leaves_orderingFree h⟩

private theorem flatAtoms_safe {q : Query}
    (h : ∀ p ∈ q, ∃ f es, p = .expr (.app f es) ∧ ∀ e ∈ es, Leaf e) : q.Safe := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨p, hp, hv⟩ := Query.mem_vars.mp hv
    obtain ⟨f, es, rfl, he⟩ := h p hp
    exact ⟨_, hp, (flatAtom_safe he).1 v hv⟩
  · intro p hp
    obtain ⟨f, es, rfl, he⟩ := h p hp
    exact (flatAtom_safe he).2

theorem FlatPattern.orderingFree {p : Pattern} (h : FlatPattern p) :
    p.OrderingFree := by
  cases p with
  | expr e =>
      cases e with
      | app f es => exact leaves_orderingFree h
      | lit | var | min | ite => contradiction
  | eq a b => exact ⟨h.1.orderingFree, h.2.orderingFree⟩

mutual

private theorem encodeQueryExpr_atoms : ∀ (e : Expr) (n : Nat),
    ∀ p ∈ (encodeQueryExpr e n).2.1, ∃ f es, p = .expr (.app f es)
  | .lit _, _, _, h | .var _, _, _, h | .min _ _, _, _, h | .ite _ _ _ _, _, _, h => by simp [encodeQueryExpr] at h
  | .app f es, n, p, h => by
      change p ∈ (encodeQueryArgs es n).2.1 ++ [_] at h
      rcases List.mem_append.mp h with h | h
      · exact encodeQueryArgs_atoms es n p h
      · obtain rfl := List.mem_singleton.mp h; exact ⟨_, _, rfl⟩

private theorem encodeQueryArgs_atoms : ∀ (es : List Expr) (n : Nat),
    ∀ p ∈ (encodeQueryArgs es n).2.1, ∃ f es, p = .expr (.app f es)
  | [], _, _, h => by simp [encodeQueryArgs] at h
  | e :: es, n, p, h => by
      change p ∈ (encodeQueryExpr e n).2.1 ++ _ at h
      rcases List.mem_append.mp h with h | h
      · exact encodeQueryExpr_atoms e n p h
      · exact encodeQueryArgs_atoms es _ p h

end

private theorem encodeQueryExpr_keyed (e : Expr) (n : Nat) (ho : e.OrderingFree) :
    (encodeQueryExpr e n).2.1.VarsKeyed := by
  apply (flatAtoms_safe ?_).1
  intro p hp
  obtain ⟨f, es, rfl⟩ := encodeQueryExpr_atoms e n p hp
  exact ⟨f, es, rfl, (encodeQueryExpr_flat e n ho).2 _ hp⟩

private theorem returned_var_covered (e : Expr) (n : Nat) (ho : e.OrderingFree)
    {v : Var} (hv : v ∈ (encodeQueryExpr e n).1.vars) :
    v ∈ e.vars ∨ KeyedIn (encodeQueryExpr e n).2.1 v := by
  cases e with
  | lit => simp [encodeQueryExpr] at hv
  | var => exact Or.inl hv
  | min | ite => simp [Expr.OrderingFree, Expr.hasMin] at ho
  | app f es =>
      obtain rfl : v = freshVar (encodeQueryArgs es n).2.2 := List.mem_singleton.mp hv
      refine Or.inr ⟨_, List.mem_append_right _ List.mem_cons_self, Or.inl ?_⟩
      exact List.mem_append_right _ List.mem_cons_self

private theorem encodePattern_covered (p : Pattern) (n : Nat) (ho : p.OrderingFree)
    {v : Var} (hv : v ∈ (encodePattern p n).1.vars) :
    v ∈ p.vars ∨ KeyedIn (encodePattern p n).1 v := by
  cases p with
  | expr e => exact Or.inr (encodeQueryExpr_keyed e n ho v hv)
  | eq a b =>
      change v ∈ Query.vars ((_ ++ _) ++ [_]) at hv
      rcases Query.mem_vars_append.mp hv with hv | hv
      · rcases Query.mem_vars_append.mp hv with hv | hv
        · exact Or.inr (KeyedIn.mono (encodeQueryExpr_keyed a n ho.1 v hv)
            (fun _ hp => List.mem_append_left _ (List.mem_append_left _ hp)))
        · exact Or.inr (KeyedIn.mono (encodeQueryExpr_keyed b _ ho.2 v hv)
            (fun _ hp => List.mem_append_left _ (List.mem_append_right _ hp)))
      · obtain ⟨p, hp, hv⟩ := Query.mem_vars.mp hv
        obtain rfl := List.mem_singleton.mp hp
        rcases List.mem_union_iff.mp hv with hv | hv
        · rcases returned_var_covered a n ho.1 hv with hv | hv
          · exact Or.inl (List.mem_union_iff.mpr (Or.inl hv))
          · exact Or.inr (hv.mono
              (fun _ hp => List.mem_append_left _ (List.mem_append_left _ hp)))
        · rcases returned_var_covered b _ ho.2 hv with hv | hv
          · exact Or.inl (List.mem_union_iff.mpr (Or.inr hv))
          · exact Or.inr (hv.mono
              (fun _ hp => List.mem_append_left _ (List.mem_append_right _ hp)))

private theorem encodeQuery_covered (q : Query) (n : Nat)
    (ho : ∀ p ∈ q, p.OrderingFree) {v : Var} (hv : v ∈ (encodeQuery q n).1.vars) :
    v ∈ q.vars ∨ KeyedIn (encodeQuery q n).1 v := by
  induction q generalizing n with
  | nil => simp [encodeQuery] at hv
  | cons p ps ih =>
      change v ∈ Query.vars ((encodePattern p n).1 ++ _) at hv
      rcases Query.mem_vars_append.mp hv with hv | hv
      · rcases encodePattern_covered p n (ho p List.mem_cons_self) hv with hv | hv
        · exact Or.inl (List.mem_union_iff.mpr (Or.inl hv))
        · exact Or.inr (hv.mono (fun _ hp => List.mem_append_left _ hp))
      · rcases ih _ (fun p hp => ho p (List.mem_cons_of_mem _ hp)) hv with hv | hv
        · exact Or.inl (List.mem_union_iff.mpr (Or.inr hv))
        · exact Or.inr (hv.mono (fun _ hp => List.mem_append_right _ hp))

private theorem encoded_pattern_keyed {p : Pattern} {v : Var} (n : Nat)
    (ho : p.OrderingFree) (hv : p.ArgVar v) : KeyedIn (encodePattern p n).1 v := by
  cases p with
  | expr e =>
      exact encodeQueryExpr_keyed e n ho v
        (mem_vars_encodeQueryExpr_of_argVar e n ho hv)
  | eq a b =>
      rcases hv with hv | hv
      · exact KeyedIn.mono (encodeQueryExpr_keyed a n ho.1 v
          (mem_vars_encodeQueryExpr_of_argVar a n ho.1 hv))
          (fun _ hp => List.mem_append_left _ (List.mem_append_left _ hp))
      · exact KeyedIn.mono (encodeQueryExpr_keyed b _ ho.2 v
          (mem_vars_encodeQueryExpr_of_argVar b _ ho.2 hv))
          (fun _ hp => List.mem_append_left _ (List.mem_append_right _ hp))

private theorem encoded_query_keyed {q : Query} {p : Pattern} {v : Var} (n : Nat)
    (ho : ∀ p ∈ q, p.OrderingFree) (hp : p ∈ q) (hv : p.ArgVar v) :
    KeyedIn (encodeQuery q n).1 v := by
  induction q generalizing n with
  | nil => simp at hp
  | cons a q ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (encoded_pattern_keyed n (ho p List.mem_cons_self) hv).mono
          (fun _ hh => List.mem_append_left _ hh)
      · exact (ih _ (fun p hp => ho p (List.mem_cons_of_mem _ hp)) hp).mono
          (fun _ hh => List.mem_append_right _ hh)

theorem encodeQuery_safe (q : Query) (n : Nat)
    (ho : ∀ p ∈ q, p.OrderingFree) (hk : q.VarsKeyed) : (encodeQuery q n).1.Safe := by
  refine ⟨?_, fun p hp => (encodeQuery_flat q n ho p hp).orderingFree⟩
  intro v hv
  rcases encodeQuery_covered q n ho hv with hv | hv
  · obtain ⟨p, hp, hv⟩ := hk v hv
    exact encoded_query_keyed n ho hp hv
  · exact hv

private theorem leaderQuery_safe (vs : List Var) : (leaderQuery vs).Safe := by
  apply flatAtoms_safe
  intro p hp
  obtain ⟨v, _, hp⟩ := List.mem_flatMap.mp hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨_, _, rfl, by simp [Leaf]⟩
  · obtain rfl := List.mem_singleton.mp hp
    exact ⟨_, _, rfl, by simp [Leaf]⟩

private theorem keyedIn_leaderQuery {vs : List Var} {v : Var} (hv : v ∈ vs) :
    KeyedIn (leaderQuery vs) v :=
  ⟨_, List.mem_flatMap.mpr ⟨v, hv, List.mem_cons_self⟩, Or.inl List.mem_cons_self⟩

theorem encodeQuery_leader_safe (q : Query) (n : Nat)
    (ho : ∀ p ∈ q, p.OrderingFree) :
    ((encodeQuery q n).1 ++ leaderQuery q.vars).Safe := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rcases Query.mem_vars_append.mp hv with hv | hv
    · rcases encodeQuery_covered q n ho hv with hv | hv
      · exact (keyedIn_leaderQuery hv).mono (fun _ hp => List.mem_append_right _ hp)
      · exact hv.mono (fun _ hp => List.mem_append_left _ hp)
    · exact KeyedIn.mono ((leaderQuery_safe _).1 v hv) (fun _ hp => List.mem_append_right _ hp)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact (encodeQuery_flat _ _ ho p hp).orderingFree
    · exact (leaderQuery_safe _).2 p hp

theorem encodeRule_querySafe (r : Rule) (ho : ∀ p ∈ r.query, p.OrderingFree) :
    (encodeRule r).query.Safe := encodeQuery_leader_safe r.query 0 ho

private theorem rebuildVars_leaf (k : Nat) : ∀ e ∈ rebuildVars k, Leaf e := by
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  trivial

private theorem maintenance_querySafe (P : Program) :
    ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r → r.query.Safe := by
  intro c hc r hr
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain rfl := Cmd.rule.inj hr
    apply flatAtoms_safe
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl, by simp [Leaf]⟩
    · obtain rfl := List.mem_singleton.mp hp
      exact ⟨_, _, rfl, by simp [Leaf]⟩
  · obtain ⟨⟨f, k⟩, _, hc⟩ := List.mem_flatMap.mp hc
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain rfl := Cmd.rule.inj hr
      apply flatAtoms_safe
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · refine ⟨_, _, rfl, ?_⟩
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact rebuildVars_leaf k e he
        · obtain rfl := List.mem_singleton.mp he; trivial
      · obtain rfl := List.mem_singleton.mp hp
        exact ⟨_, _, rfl, by simp [Leaf]⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      obtain rfl := Cmd.rule.inj hr
      apply flatAtoms_safe
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · refine ⟨_, _, rfl, ?_⟩
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact rebuildVars_leaf k e he
        · obtain rfl := List.mem_singleton.mp he; trivial
      · obtain rfl := List.mem_singleton.mp hp
        exact ⟨_, _, rfl, by simp [Leaf]⟩

private theorem allMaintenance_querySafe (P : Program) :
    ∀ c ∈ allMaintenanceRules P, ∀ r, c.command = .rule r → r.query.Safe := by
  intro c hc r hr
  rcases List.mem_append.mp hc with hc | hc
  · exact maintenance_querySafe P c hc r hr
  · obtain ⟨R, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcbase, rfl⟩ := List.mem_map.mp hc
    unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact maintenance_querySafe P c hcbase s hs
    next => exact maintenance_querySafe P c hcbase r hr

theorem prelude_querySafe (P : Program) :
    ∀ r, Cmd.rule r ∈ (encodePrelude P).map Command.command → r.query.Safe := by
  intro r hr
  obtain ⟨c, hc, he⟩ := (rule_mem_prelude P r).mp hr
  exact allMaintenance_querySafe P c hc r he

theorem encodeCmds_querySafe {pre : Program} (ho : pre.OrderingFree) (i : Nat) :
    ∀ r, Cmd.rule r ∈ (encodeCmds pre i).map Command.command → r.query.Safe := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := (rule_mem_encodeCmds pre i r).mp hr
  exact encodeRule_querySafe s (Program.OrderingFree.of_mem ho hs).1

theorem encode_querySafe {P : Program} (hp : P.Fragment) :
    ∀ r, Cmd.rule r ∈ encode P → r.query.Safe := by
  intro r hr
  rw [encode, compile, List.map_append] at hr
  exact (List.mem_append.mp hr).elim (prelude_querySafe P r) (encodeCmds_querySafe hp.noMin 0 r)

end Egglog.Congruence
