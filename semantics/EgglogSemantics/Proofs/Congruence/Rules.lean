import EgglogSemantics.Proofs.Congruence.Atoms
import EgglogSemantics.Proofs.Presentation
import EgglogSemantics.Proofs.Writes

/-! The maintenance rules of the view-free encoding: the rebuild is one saturation of the
list `maintenance sub P`, and a firing of each rule is characterized by the live edges, node
rows and markers it matched and the rows it writes and marks. -/

namespace Egglog.Congruence

variable {sub : Bool}

/-- The maintenance rules without their origins. -/
def maintenance (sub : Bool) (P : Program) : List Rule := (maintenanceRules sub P).map Prod.fst

theorem rebuild_eq (P : Program) : (rebuildWith { subsumption := sub } P).1 = .saturate (.run (maintenance sub P)) := by
  simp only [rebuildWith, maintenanceGroups, maintenance, maintenanceRules]
  have hrekey : ∀ fk : FnName × Nat, rekeyRules { subsumption := sub } fk.1 fk.2 = [] := fun _ => rfl
  have hmerge : ∀ fk : FnName × Nat, mergeRules { subsumption := sub } fk.1 fk.2 = rebuildRules sub fk.1 fk.2 :=
    fun _ => rfl
  have h0 : P.ctors.flatMap (fun _ => ([] : List (Rule × RuleOrigin))) = [] :=
    List.flatMap_eq_nil_iff.mpr fun _ _ => rfl
  simp only [hrekey, hmerge, h0, Bool.false_eq_true, ↓reduceIte,
    List.flatten_filter_not_isEmpty, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.nil_append, List.cons_append, List.map_cons]

theorem mem_rebuildRules {f : FnName} {n : Nat} {ro : Rule × RuleOrigin} :
    ro ∈ rebuildRules sub f n ↔
      (n ≠ 0 ∧ ro = (congruenceRule sub f n, .rebuild (.congruence f))) ∨
        (sub = true ∧ ro = (subsumeRule f n, .rebuild (.subsume f))) := by
  cases sub <;> by_cases hn : n = 0 <;> simp [rebuildRules, hn]

theorem mem_maintenance {P : Program} {r : Rule} :
    r ∈ maintenance sub P ↔ r = pathCompressRule ∨ r = ufCollideRule ∨
      (∃ fk ∈ P.ctors, fk.2 ≠ 0 ∧ r = congruenceRule sub fk.1 fk.2) ∨
      ∃ fk ∈ P.ctors, sub = true ∧ r = subsumeRule fk.1 fk.2 := by
  simp only [maintenance, maintenanceRules, List.map_cons, List.mem_cons, List.map_flatMap,
    List.mem_flatMap, List.mem_map]
  apply or_congr_right
  apply or_congr_right
  constructor
  · rintro ⟨fk, hfk, ro, hro, rfl⟩
    rcases mem_rebuildRules.mp hro with ⟨hne, rfl⟩ | ⟨hon, rfl⟩
    · exact Or.inl ⟨fk, hfk, hne, rfl⟩
    · exact Or.inr ⟨fk, hfk, hon, rfl⟩
  · rintro (⟨fk, hfk, hne, rfl⟩ | ⟨fk, hfk, hon, rfl⟩)
    · exact ⟨fk, hfk, _, mem_rebuildRules.mpr (Or.inl ⟨hne, rfl⟩), rfl⟩
    · exact ⟨fk, hfk, _, mem_rebuildRules.mpr (Or.inr ⟨hon, rfl⟩), rfl⟩

/-! ### Path compression -/

theorem compress_inv {d : Database} {σ : Env} (hq : QueryMatches d pathCompressRule.query σ) :
    ∃ a b c, Env.lookup "@a" σ = some a ∧ Env.lookup "@b" σ = some b ∧
      Env.lookup "@c" σ = some c ∧ Edge d a b ∧ Edge d b c ∧ ¬ Cong d b c := by
  have h₁ := hq.2 (.expr (ufRow (.var "@a") (.var "@b"))) (by simp [pathCompressRule])
  have h₂ := hq.2 (.expr (ufRow (.var "@b") (.var "@c"))) (by simp [pathCompressRule])
  have h₃ := hq.2 (.ne (.var "@b") (.var "@c")) (by simp [pathCompressRule])
  obtain ⟨a, b, ha, hb, hab⟩ := matches_uf_var_var_iff.mp h₁
  obtain ⟨b', c, hb', hc, hbc⟩ := matches_uf_var_var_iff.mp h₂
  obtain ⟨b'', c', hb'', hc', hne⟩ := matches_ne_var_var_iff.mp h₃
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : b = b'' := Option.some.inj (hb.symm.trans hb'')
  obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
  exact ⟨a, b, c, ha, hb, hc, hab, hbc, hne⟩

theorem compress_writes {σ : Env} {a b c : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : Env.lookup "@c" σ = some c) :
    Action.writes σ pathCompressRule.actions =
      some ({(ufRowT a b, ufRowT a b)} ∪ ({(ufRowT a c, ufRowT a c)} ∪ ∅)) := by
  simp [pathCompressRule, Action.writes, Action.write, subsumeUf, ufRow, Expr.eval,
    Expr.evalList, ha, hb, hc]

theorem compress_marks {σ : Env} {a b : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : (Env.lookup "@c" σ).isSome) :
    Action.marks σ pathCompressRule.actions = some ({ufRowT a b} ∪ (∅ ∪ ∅)) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
  simp [pathCompressRule, Action.marks, Action.mark, Action.write, subsumeUf, ufRow, Expr.eval,
    Expr.evalList, ha, hb, hc]

/-! ### Collisions -/

theorem collide_query : ufCollideRule.query =
    [.expr (ufRow (.var "@a") (.var "@b")), .expr (ufRow (.var "@a") (.var "@c")),
     .eq (.var "@b") (.min (.var "@b") (.var "@c")), .ne (.var "@b") (.var "@c")] := rfl

theorem collide_actions : ufCollideRule.actions =
    [subsumeUf (.var "@a") (.var "@c"), .expr (ufRow (.var "@c") (.var "@b"))] := rfl

theorem collide_inv {d : Database} (hd : d.Diag) {σ : Env}
    (hq : QueryMatches d ufCollideRule.query σ) :
    ∃ a b c, Env.lookup "@a" σ = some a ∧ Env.lookup "@b" σ = some b ∧
      Env.lookup "@c" σ = some c ∧ Edge d a b ∧ Edge d a c ∧ b = Term.least b c ∧ ¬ Cong d b c := by
  have h₁ := hq.2 (.expr (ufRow (.var "@a") (.var "@b"))) (by rw [collide_query]; simp)
  have h₂ := hq.2 (.expr (ufRow (.var "@a") (.var "@c"))) (by rw [collide_query]; simp)
  have h₃ := hq.2 (.eq (.var "@b") (.min (.var "@b") (.var "@c"))) (by rw [collide_query]; simp)
  have h₄ := hq.2 (.ne (.var "@b") (.var "@c")) (by rw [collide_query]; simp)
  obtain ⟨a, b, ha, hb, hab⟩ := matches_uf_var_var_iff.mp h₁
  obtain ⟨a', c, ha', hc, hac⟩ := matches_uf_var_var_iff.mp h₂
  obtain ⟨b', c', hb', hc', _, hmin⟩ := (matches_eq_min_iff hd).mp h₃
  obtain ⟨b'', c'', hb'', hc'', hne⟩ := matches_ne_var_var_iff.mp h₄
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
  obtain rfl : b = b'' := Option.some.inj (hb.symm.trans hb'')
  obtain rfl : c = c'' := Option.some.inj (hc.symm.trans hc'')
  exact ⟨a, b, c, ha, hb, hc, hab, hac, hmin, hne⟩

theorem collide_writes {σ : Env} {a b c : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : Env.lookup "@c" σ = some c) :
    Action.writes σ ufCollideRule.actions =
      some ({(ufRowT a c, ufRowT a c)} ∪ ({(ufRowT c b, ufRowT c b)} ∪ ∅)) := by
  rw [collide_actions]
  simp [Action.writes, Action.write, subsumeUf, ufRow, Expr.eval, Expr.evalList, ha, hb, hc]

theorem collide_marks {σ : Env} {a b c : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : Env.lookup "@c" σ = some c) :
    Action.marks σ ufCollideRule.actions = some ({ufRowT a c} ∪ (∅ ∪ ∅)) := by
  rw [collide_actions]
  simp [Action.marks, Action.mark, Action.write, subsumeUf, ufRow, Expr.eval, Expr.evalList,
    ha, hb, hc]

/-! ### The column variables -/

theorem congruenceVars_length (stem : String) (n : Nat) : (congruenceVars stem n).length = n := by
  simp [congruenceVars]

theorem congruenceVars_getElem (stem : String) {n i : Nat} (hi : i < n) :
    (congruenceVars stem n)[i]'(by rw [congruenceVars_length]; exact hi) =
      .var ("@" ++ stem ++ toString i) := by
  simp [congruenceVars]

theorem congruenceVars_getElem? (stem : String) {n i : Nat} (hi : i < n) :
    (congruenceVars stem n)[i]? = some (.var ("@" ++ stem ++ toString i)) := by
  rw [List.getElem?_eq_getElem (by rw [congruenceVars_length]; exact hi),
    congruenceVars_getElem stem hi]

/-- The value of a column variable from the evaluated list. -/
theorem congruence_lookup {σ : Env} {stem : String} {n : Nat} {ts : List Term}
    (hts : Expr.evalList (congruenceVars stem n) σ = some ts) {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ stem ++ toString i) σ = ts[i]? := by
  obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hts i (congruenceVars_getElem? stem hi)
  rw [ht]
  exact hev

/-- The edge atoms of the congruence and subsumption rules, one pair per column. -/
def edgeAtoms (n : Nat) : Query :=
  (((congruenceVars "a" n).zip (congruenceVars "b" n)).zip (congruenceVars "r" n)).flatMap
    fun abr => [.expr (ufRow abr.1.1 abr.2), .expr (ufRow abr.1.2 abr.2)]

theorem edge_atoms_mem {n i : Nat} (hi : i < n) :
    Pattern.expr (ufRow (.var ("@" ++ "a" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        edgeAtoms n ∧
      Pattern.expr (ufRow (.var ("@" ++ "b" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        edgeAtoms n := by
  have hlen : i < (((congruenceVars "a" n).zip (congruenceVars "b" n)).zip
      (congruenceVars "r" n)).length := by
    simp [congruenceVars_length, hi]
  have hmem : ((Expr.var ("@" ++ "a" ++ toString i), Expr.var ("@" ++ "b" ++ toString i)),
      Expr.var ("@" ++ "r" ++ toString i)) ∈
      ((congruenceVars "a" n).zip (congruenceVars "b" n)).zip (congruenceVars "r" n) := by
    rw [List.mem_iff_getElem]
    refine ⟨i, hlen, ?_⟩
    rw [List.getElem_zip, List.getElem_zip, congruenceVars_getElem "a" hi,
      congruenceVars_getElem "b" hi, congruenceVars_getElem "r" hi]
  exact ⟨List.mem_flatMap.mpr ⟨_, hmem, by simp⟩, List.mem_flatMap.mpr ⟨_, hmem, by simp⟩⟩

/-- A member of the edge atoms is an edge between a column variable and its parent. -/
theorem mem_edgeAtoms {n : Nat} {p : Pattern} (hp : p ∈ edgeAtoms n) :
    ∃ i, i < n ∧ (p = .expr (ufRow (.var ("@" ++ "a" ++ toString i))
      (.var ("@" ++ "r" ++ toString i))) ∨
      p = .expr (ufRow (.var ("@" ++ "b" ++ toString i)) (.var ("@" ++ "r" ++ toString i)))) := by
  obtain ⟨abr, habr, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp habr
  simp only [List.length_zip, congruenceVars_length, Nat.min_self] at hi
  rw [List.getElem_zip, List.getElem_zip, congruenceVars_getElem "a" hi,
    congruenceVars_getElem "b" hi, congruenceVars_getElem "r" hi] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  exact ⟨i, hi, hp⟩

/-- The matched edges of the column groups. -/
theorem edges_of_matches {d : Database} {σ : Env} {n : Nat} {rs : List Term}
    (hrs : Expr.evalList (congruenceVars "r" n) σ = some rs) (stem : String) {ts : List Term}
    (hts : Expr.evalList (congruenceVars stem n) σ = some ts)
    (hm : ∀ i, i < n → Matches d (.expr (ufRow (.var ("@" ++ stem ++ toString i))
      (.var ("@" ++ "r" ++ toString i)))) σ) :
    List.Forall₂ (Edge d) ts rs := by
  have hlen : ts.length = n := by rw [Expr.evalList_length hts, congruenceVars_length]
  have hlenR : rs.length = n := by rw [Expr.evalList_length hrs, congruenceVars_length]
  rw [List.forall₂_iff_get]
  refine ⟨by rw [hlen, hlenR], fun i h₁ h₂ => ?_⟩
  have hi : i < n := hlen ▸ h₁
  obtain ⟨u, r, hu, hr, hur⟩ := matches_uf_var_var_iff.mp (hm i hi)
  have hu' := congruence_lookup hts hi
  have hr' := congruence_lookup hrs hi
  rw [hu, List.getElem?_eq_getElem h₁] at hu'
  rw [hr, List.getElem?_eq_getElem h₂] at hr'
  simp only [List.get_eq_getElem]
  rw [← Option.some.inj hu', ← Option.some.inj hr']
  exact hur

/-- The parents are bound when every column's edge atom is in the query. -/
theorem parents_eval {d : Database} {σ : Env} {q : Query} {n : Nat}
    (hq : QueryMatches d q σ) (hatoms : ∀ i, i < n →
      Pattern.expr (ufRow (.var ("@" ++ "a" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈ q) :
    ∃ rs, Expr.evalList (congruenceVars "r" n) σ = some rs := by
  apply Expr.evalList_isSome
  intro v hv
  obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  rw [congruenceVars_length] at hi
  rw [congruenceVars_getElem "r" hi] at hve
  simp only [Expr.vars_var, List.mem_singleton] at hve
  subst hve
  apply hq.1.1.mem_iff.mpr
  rw [Query.mem_vars]
  refine ⟨_, hatoms i hi, ?_⟩
  simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]

theorem evalList_append {σ : Env} {xs ys : List Expr} {ts : List Term}
    (h : Expr.evalList (xs ++ ys) σ = some ts) :
    ∃ ts₁ ts₂, Expr.evalList xs σ = some ts₁ ∧ Expr.evalList ys σ = some ts₂ ∧
      ts = ts₁ ++ ts₂ := by
  induction xs generalizing ts with
  | nil => exact ⟨[], ts, rfl, h, rfl⟩
  | cons x xs ih =>
    rw [List.cons_append, Expr.evalList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, hrest⟩ := h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
    obtain ⟨ts₁, ts₂, h₁, h₂, rfl⟩ := ih hus
    exact ⟨t :: ts₁, ts₂, by rw [Expr.evalList_cons, ht, Option.bind_some, h₁, Option.map_some],
      h₂, rfl⟩

/-- A held node atom is the node row of its children. -/
theorem node_atom_inv {d : Database} (hs : Shape d) {f : FnName} {ts : List Term}
    (h : Term.app (nodeName f) ts ∈ d.terms) :
    ∃ as, ts = as ++ [Term.app f as] ∧ Node d f as := by
  rcases hs.mem_terms_iff.mp h with ⟨k, p, _, heq⟩ | ⟨g, bs, hn, heq⟩ | ⟨g, bs, _, heq⟩ |
    ⟨k, hk, hsub⟩
  · exact ((nodeName_ne_ufName f) (Term.app.inj heq).1).elim
  · have h' := Term.app.inj heq
    obtain rfl := nodeName_inj h'.1
    exact ⟨bs, h'.2, hn⟩
  · exact ((subName_ne_nodeName g f) (Term.app.inj heq).1.symm).elim
  · exact (not_sourceName_nodeName f
      (Term.SourceShaped.head (hs.subterm_sourceShaped hk hsub))).elim

/-- A held marker atom is a marker. -/
theorem marker_atom_inv {d : Database} (hs : Shape d) {f : FnName} {ts : List Term}
    (h : Term.app (subName f) ts ∈ d.terms) : Marker d f ts := by
  rcases hs.mem_terms_iff.mp h with ⟨k, p, _, heq⟩ | ⟨g, bs, _, heq⟩ | ⟨g, bs, hm, heq⟩ |
    ⟨k, hk, hsub⟩
  · exact ((subName_ne_ufName f) (Term.app.inj heq).1).elim
  · exact ((subName_ne_nodeName f g) (Term.app.inj heq).1).elim
  · obtain ⟨rfl, rfl⟩ := subRowT_inj heq
    exact hm
  · exact (not_sourceName_subName f
      (Term.SourceShaped.head (hs.subterm_sourceShaped hk hsub))).elim

/-! ### Congruence -/

theorem congruence_query_node (f : FnName) (n : Nat) : (congruenceRule true f n).query =
    [.expr (nodeAtom f (congruenceVars "a" n) (.var "@k")),
     .expr (nodeAtom f (congruenceVars "b" n) (.var "@l"))] ++ edgeAtoms n ++
      [.expr (ufRow (.var "@k") (.var "@y")), .expr (ufRow (.var "@l") (.var "@z")),
       .eq (.var "@y") (.min (.var "@y") (.var "@z")), .ne (.var "@y") (.var "@z")] := rfl

theorem congruence_query_plain (f : FnName) (n : Nat) : (congruenceRule false f n).query =
    [.expr (.app f (congruenceVars "a" n)), .expr (.app f (congruenceVars "b" n))] ++
      (((congruenceVars "a" n).zip (congruenceVars "b" n)).zip (congruenceVars "r" n)).flatMap
        (fun abr => [.expr (ufRow abr.1.1 abr.2), .expr (ufRow abr.1.2 abr.2)]) ++
      [.expr (ufRow (.app f (congruenceVars "a" n)) (.var "@y")),
       .expr (ufRow (.app f (congruenceVars "b" n)) (.var "@z")),
       .eq (.var "@y") (.min (.var "@y") (.var "@z")), .ne (.var "@y") (.var "@z")] := rfl

theorem congruence_actions (f : FnName) (n : Nat) :
    (congruenceRule sub f n).actions = [.expr (ufRow (.var "@z") (.var "@y"))] := rfl

theorem congruence_edge_atoms_mem {f : FnName} {n i : Nat} (hi : i < n) :
    Pattern.expr (ufRow (.var ("@" ++ "a" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        (congruenceRule sub f n).query ∧
      Pattern.expr (ufRow (.var ("@" ++ "b" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        (congruenceRule sub f n).query := by
  cases sub <;> first | rw [congruence_query_plain] | rw [congruence_query_node]
  all_goals exact ⟨List.mem_append_left _ (List.mem_append_right _ (edge_atoms_mem hi).1),
    List.mem_append_left _ (List.mem_append_right _ (edge_atoms_mem hi).2)⟩

/-- A node atom over the column variables of a group matches a node row of the group's
values, which it binds the id variable to. -/
theorem node_atom_matches {d : Database} (hd : d.Diag) (hs : Shape d) {σ : Env} {f : FnName}
    {stem : String} {n : Nat} {v : Var}
    (hm : Matches d (.expr (nodeAtom f (congruenceVars stem n) (.var v))) σ) :
    ∃ ts, Expr.evalList (congruenceVars stem n) σ = some ts ∧
      Env.lookup v σ = some (Term.app f ts) ∧ Node d f ts := by
  obtain ⟨us, _, hus, hlive⟩ := matches_app_iff.mp hm
  obtain ⟨ts, ks, hts, hk, rfl⟩ := evalList_append hus
  obtain ⟨k, hk', rfl⟩ := Expr.evalList_singleton hk
  obtain ⟨as, heq, hn⟩ := node_atom_inv hs ((Cong.iff_eq_and_mem_of_diag hd).mp hlive.1).2
  obtain ⟨rfl, hk⟩ := List.append_inj' heq (by simp [Expr.evalList_length hts])
  simp only [List.cons.injEq, and_true] at hk
  subst hk
  exact ⟨ts, hts, hk', hn⟩

theorem congruence_inv_node {d : Database} (hd : d.Diag) (hs : Shape d) {σ : Env} {f : FnName}
    {n : Nat} (hq : QueryMatches d (congruenceRule true f n).query σ) :
    ∃ as bs rs y z, Expr.evalList (congruenceVars "a" n) σ = some as ∧
      Expr.evalList (congruenceVars "b" n) σ = some bs ∧
      Expr.evalList (congruenceVars "r" n) σ = some rs ∧
      Env.lookup "@k" σ = some (Term.app f as) ∧ Env.lookup "@l" σ = some (Term.app f bs) ∧
      Env.lookup "@y" σ = some y ∧ Env.lookup "@z" σ = some z ∧
      Node d f as ∧ Node d f bs ∧
      List.Forall₂ (Edge d) as rs ∧ List.Forall₂ (Edge d) bs rs ∧
      Edge d (.app f as) y ∧ Edge d (.app f bs) z ∧ y = Term.least y z ∧ ¬ Cong d y z := by
  have hm := hq.2
  rw [congruence_query_node] at hm
  have hA := hm (.expr (nodeAtom f (congruenceVars "a" n) (.var "@k"))) (by simp)
  have hB := hm (.expr (nodeAtom f (congruenceVars "b" n) (.var "@l"))) (by simp)
  have hY := hm (.expr (ufRow (.var "@k") (.var "@y"))) (by simp)
  have hZ := hm (.expr (ufRow (.var "@l") (.var "@z"))) (by simp)
  have hmin := hm (.eq (.var "@y") (.min (.var "@y") (.var "@z"))) (by simp)
  have hne := hm (.ne (.var "@y") (.var "@z")) (by simp)
  obtain ⟨as, has, hk, hna⟩ := node_atom_matches hd hs hA
  obtain ⟨bs, hbs, hl, hnb⟩ := node_atom_matches hd hs hB
  obtain ⟨ka, y, hk', hy, hey⟩ := matches_uf_var_var_iff.mp hY
  obtain ⟨lb, z, hl', hz, hez⟩ := matches_uf_var_var_iff.mp hZ
  obtain ⟨y', z', hy', hz', _, hyz⟩ := (matches_eq_min_iff hd).mp hmin
  obtain ⟨y'', z'', hy'', hz'', hnyz⟩ := matches_ne_var_var_iff.mp hne
  obtain rfl : ka = Term.app f as := Option.some.inj (hk'.symm.trans hk)
  obtain rfl : lb = Term.app f bs := Option.some.inj (hl'.symm.trans hl)
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : y = y'' := Option.some.inj (hy.symm.trans hy'')
  obtain rfl : z = z'' := Option.some.inj (hz.symm.trans hz'')
  obtain ⟨rs, hrs⟩ := parents_eval hq fun i hi => (congruence_edge_atoms_mem hi).1
  refine ⟨as, bs, rs, y, z, has, hbs, hrs, hk, hl, hy, hz, hna, hnb, ?_, ?_, hey, hez, hyz, hnyz⟩
  · exact edges_of_matches hrs "a" has fun i hi => hq.2 _ (congruence_edge_atoms_mem hi).1
  · exact edges_of_matches hrs "b" hbs fun i hi => hq.2 _ (congruence_edge_atoms_mem hi).2

theorem congruence_inv_plain {d : Database} (hd : d.Diag) {σ : Env} {f : FnName} {n : Nat}
    (hq : QueryMatches d (congruenceRule false f n).query σ) :
    ∃ as bs rs y z, Expr.evalList (congruenceVars "a" n) σ = some as ∧
      Expr.evalList (congruenceVars "b" n) σ = some bs ∧
      Expr.evalList (congruenceVars "r" n) σ = some rs ∧
      Env.lookup "@y" σ = some y ∧ Env.lookup "@z" σ = some z ∧
      Term.app f as ∈ d.live ∧ Term.app f bs ∈ d.live ∧
      List.Forall₂ (Edge d) as rs ∧ List.Forall₂ (Edge d) bs rs ∧
      Edge d (.app f as) y ∧ Edge d (.app f bs) z ∧ y = Term.least y z ∧ ¬ Cong d y z := by
  have hm := hq.2
  rw [congruence_query_plain] at hm
  have hA := hm (.expr (.app f (congruenceVars "a" n))) (by simp)
  have hB := hm (.expr (.app f (congruenceVars "b" n))) (by simp)
  have hY := hm (.expr (ufRow (.app f (congruenceVars "a" n)) (.var "@y"))) (by simp)
  have hZ := hm (.expr (ufRow (.app f (congruenceVars "b" n)) (.var "@z"))) (by simp)
  have hmin := hm (.eq (.var "@y") (.min (.var "@y") (.var "@z"))) (by simp)
  have hne := hm (.ne (.var "@y") (.var "@z")) (by simp)
  obtain ⟨as, _, has, hliveA⟩ := matches_app_iff.mp hA
  obtain ⟨bs, _, hbs, hliveB⟩ := matches_app_iff.mp hB
  obtain ⟨ta, y, _, _, hta, hy, hey⟩ := matches_uf_iff.mp hY
  obtain ⟨tb, z, _, _, htb, hz, hez⟩ := matches_uf_iff.mp hZ
  obtain ⟨y', z', hy', hz', _, hyz⟩ := (matches_eq_min_iff hd).mp hmin
  obtain ⟨y'', z'', hy'', hz'', hnyz⟩ := matches_ne_var_var_iff.mp hne
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : y = y'' := Option.some.inj (hy.symm.trans hy'')
  obtain rfl : z = z'' := Option.some.inj (hz.symm.trans hz'')
  obtain rfl : ta = Term.app f as := by
    rw [Expr.eval_app_ctor, has] at hta
    exact (Option.some.inj hta).symm
  obtain rfl : tb = Term.app f bs := by
    rw [Expr.eval_app_ctor, hbs] at htb
    exact (Option.some.inj htb).symm
  -- The column variables are all bound, so the parents evaluate.
  have hdom : ∀ v ∈ Expr.varsList (congruenceVars "r" n), v ∈ Env.dom σ := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    rw [congruenceVars_length] at hi
    rw [congruenceVars_getElem "r" hi] at hve
    simp only [Expr.vars_var, List.mem_singleton] at hve
    subst hve
    apply hq.1.1.mem_iff.mpr
    rw [Query.mem_vars]
    refine ⟨_, (congruence_edge_atoms_mem (f := f) hi).1, ?_⟩
    simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]
  obtain ⟨rs, hrs⟩ := Expr.evalList_isSome (congruenceVars "r" n) hdom
  have hlenA : as.length = n := by rw [Expr.evalList_length has, congruenceVars_length]
  have hlenB : bs.length = n := by rw [Expr.evalList_length hbs, congruenceVars_length]
  have hlenR : rs.length = n := by rw [Expr.evalList_length hrs, congruenceVars_length]
  have edges : ∀ (stem : String) (ts : List Term),
      Expr.evalList (congruenceVars stem n) σ = some ts →
      (∀ i, i < n → Pattern.expr (ufRow (.var ("@" ++ stem ++ toString i))
        (.var ("@" ++ "r" ++ toString i))) ∈ (congruenceRule false f n).query) →
      List.Forall₂ (Edge d) ts rs := by
    intro stem ts hts hatoms
    have hlen : ts.length = n := by rw [Expr.evalList_length hts, congruenceVars_length]
    rw [List.forall₂_iff_get]
    refine ⟨by rw [hlen, hlenR], fun i h₁ h₂ => ?_⟩
    have hi : i < n := hlen ▸ h₁
    obtain ⟨u, r, hu, hr, hur⟩ := matches_uf_var_var_iff.mp (hq.2 _ (hatoms i hi))
    have hu' := congruence_lookup hts hi
    have hr' := congruence_lookup hrs hi
    rw [hu, List.getElem?_eq_getElem h₁] at hu'
    rw [hr, List.getElem?_eq_getElem h₂] at hr'
    simp only [List.get_eq_getElem]
    rw [← Option.some.inj hu', ← Option.some.inj hr']
    exact hur
  refine ⟨as, bs, rs, y, z, has, hbs, hrs, hy, hz, hliveA, hliveB, ?_, ?_, hey, hez, hyz, hnyz⟩
  · exact edges "a" as has fun i hi => (congruence_edge_atoms_mem hi).1
  · exact edges "b" bs hbs fun i hi => (congruence_edge_atoms_mem hi).2

/-- Both node reads produce the same child edges and output edges. -/
theorem congruence_inv {d : Database} (hd : d.Diag) (hs : Shape d) {σ : Env} {f : FnName}
    {n : Nat} (hq : QueryMatches d (congruenceRule sub f n).query σ) :
    ∃ as bs rs y z, Expr.evalList (congruenceVars "a" n) σ = some as ∧
      Expr.evalList (congruenceVars "b" n) σ = some bs ∧
      Expr.evalList (congruenceVars "r" n) σ = some rs ∧
      Env.lookup "@y" σ = some y ∧ Env.lookup "@z" σ = some z ∧
      List.Forall₂ (Edge d) as rs ∧ List.Forall₂ (Edge d) bs rs ∧
      Edge d (.app f as) y ∧ Edge d (.app f bs) z ∧ y = Term.least y z ∧ ¬ Cong d y z := by
  cases sub with
  | false =>
    obtain ⟨as, bs, rs, y, z, ha, hb, hr, hy, hz, _, _, rest⟩ := congruence_inv_plain hd hq
    exact ⟨as, bs, rs, y, z, ha, hb, hr, hy, hz, rest⟩
  | true =>
    obtain ⟨as, bs, rs, y, z, ha, hb, hr, _, _, hy, hz, _, _, rest⟩ :=
      congruence_inv_node hd hs hq
    exact ⟨as, bs, rs, y, z, ha, hb, hr, hy, hz, rest⟩

theorem congruence_writes {σ : Env} {f : FnName} {n : Nat} {y z : Term}
    (hy : Env.lookup "@y" σ = some y) (hz : Env.lookup "@z" σ = some z) :
    Action.writes σ (congruenceRule sub f n).actions = some ({(ufRowT z y, ufRowT z y)} ∪ ∅) := by
  rw [congruence_actions]
  simp [Action.writes, Action.write, ufRow, Expr.eval, Expr.evalList, hy, hz]

theorem congruence_marks {σ : Env} {f : FnName} {n : Nat} {y z : Term}
    (hy : Env.lookup "@y" σ = some y) (hz : Env.lookup "@z" σ = some z) :
    Action.marks σ (congruenceRule sub f n).actions = some (∅ ∪ ∅) := by
  rw [congruence_actions]
  simp [Action.marks, Action.mark, Action.write, ufRow, Expr.eval, Expr.evalList, hy, hz]

/-! ### Subsumption -/

theorem subsume_query (f : FnName) (n : Nat) : (subsumeRule f n).query =
    [.expr (subRow f (congruenceVars "a" n)), .expr (.app f (congruenceVars "b" n))] ++
      edgeAtoms n := rfl

theorem subsume_actions (f : FnName) (n : Nat) :
    (subsumeRule f n).actions = [.subsume f (congruenceVars "b" n)] := rfl

theorem subsume_edge_atoms_mem {f : FnName} {n i : Nat} (hi : i < n) :
    Pattern.expr (ufRow (.var ("@" ++ "a" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        (subsumeRule f n).query ∧
      Pattern.expr (ufRow (.var ("@" ++ "b" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        (subsumeRule f n).query := by
  rw [subsume_query]
  exact ⟨List.mem_append_right _ (edge_atoms_mem hi).1,
    List.mem_append_right _ (edge_atoms_mem hi).2⟩

theorem subsume_inv {d : Database} (hd : d.Diag) (hs : Shape d) {σ : Env} {f : FnName} {n : Nat}
    (hq : QueryMatches d (subsumeRule f n).query σ) :
    ∃ as bs rs, Expr.evalList (congruenceVars "a" n) σ = some as ∧
      Expr.evalList (congruenceVars "b" n) σ = some bs ∧
      Expr.evalList (congruenceVars "r" n) σ = some rs ∧
      Marker d f as ∧ Term.app f bs ∈ d.live ∧
      List.Forall₂ (Edge d) as rs ∧ List.Forall₂ (Edge d) bs rs := by
  have hm := hq.2
  rw [subsume_query] at hm
  have hA := hm (.expr (subRow f (congruenceVars "a" n))) (by simp)
  have hB := hm (.expr (.app f (congruenceVars "b" n))) (by simp)
  obtain ⟨as, _, has, hliveA⟩ := matches_app_iff.mp hA
  obtain ⟨bs, _, hbs, hliveB⟩ := matches_app_iff.mp hB
  obtain ⟨rs, hrs⟩ := parents_eval hq fun i hi => (subsume_edge_atoms_mem hi).1
  refine ⟨as, bs, rs, has, hbs, hrs,
    marker_atom_inv hs ((Cong.iff_eq_and_mem_of_diag hd).mp hliveA.1).2, hliveB, ?_, ?_⟩
  · exact edges_of_matches hrs "a" has fun i hi => hq.2 _ (subsume_edge_atoms_mem hi).1
  · exact edges_of_matches hrs "b" hbs fun i hi => hq.2 _ (subsume_edge_atoms_mem hi).2

theorem subsume_writes {σ : Env} {f : FnName} {n : Nat} {bs : List Term}
    (hbs : Expr.evalList (congruenceVars "b" n) σ = some bs) :
    Action.writes σ (subsumeRule f n).actions =
      some ({(Term.app f bs, Term.app f bs)} ∪ ∅) := by
  rw [subsume_actions]
  simp [Action.writes, Action.write, hbs]

theorem subsume_marks {σ : Env} {f : FnName} {n : Nat} {bs : List Term}
    (hbs : Expr.evalList (congruenceVars "b" n) σ = some bs) :
    Action.marks σ (subsumeRule f n).actions = some ({Term.app f bs} ∪ ∅) := by
  rw [subsume_actions]
  simp [Action.marks, Action.mark, hbs]

end Egglog.Congruence
