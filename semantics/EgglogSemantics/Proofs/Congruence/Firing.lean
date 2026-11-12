import EgglogSemantics.Proofs.Congruence.Invariant
import EgglogSemantics.Proofs.Congruence.Rules
import EgglogSemantics.Proofs.Source.RebuildVars
import EgglogSemantics.Proofs.Query

/-! Firing the maintenance rules: from live edges, node rows and markers that a rule's query
describes, the substitution the rule matches. Used to show that a rebuild fixpoint is
canonical. -/

namespace Egglog.Congruence

variable {sub : Bool}

/-! ### Path compression and collisions -/

/-- The substitution of the two union-find rules. -/
def ufEnv (a b c : Term) : Env := [("@a", a), ("@b", b), ("@c", c)]

theorem ufEnv_lookup_a (a b c : Term) : Env.lookup "@a" (ufEnv a b c) = some a := rfl
theorem ufEnv_lookup_b (a b c : Term) : Env.lookup "@b" (ufEnv a b c) = some b := rfl
theorem ufEnv_lookup_c (a b c : Term) : Env.lookup "@c" (ufEnv a b c) = some c := rfl

theorem ufEnv_mem {a b c : Term} {x : Var × Term} (h : x ∈ ufEnv a b c) :
    x.2 = a ∨ x.2 = b ∨ x.2 = c := by
  simp only [ufEnv, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

theorem compress_fire {d : Database} (hd : d.Diag) {a b c : Term} (hab : Edge d a b)
    (hbc : Edge d b c) (hne : b ≠ c) (ha : a ∈ d.terms) (hb : b ∈ d.terms) (hc : c ∈ d.terms) :
    QueryMatches d pathCompressRule.query (ufEnv a b c) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, fun p hp => ?_⟩
  · change (["@a", "@b", "@c"] : List Var).Perm (Query.vars pathCompressRule.query)
    decide
  · rw [hd.reps_eq_terms]
    rcases ufEnv_mem hx with h | h | h <;> rw [h] <;> assumption
  · simp only [pathCompressRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact matches_uf_var_var_iff.mpr ⟨a, b, rfl, rfl, hab⟩
    · exact matches_uf_var_var_iff.mpr ⟨b, c, rfl, rfl, hbc⟩
    · exact matches_ne_var_var_iff.mpr ⟨b, c, rfl, rfl, not_cong_of_ne hd hne⟩

theorem collide_fire {d : Database} (hd : d.Diag) {a b c : Term} (hab : Edge d a b)
    (hac : Edge d a c) (hmin : b = Term.least b c) (hne : b ≠ c)
    (ha : a ∈ d.terms) (hb : b ∈ d.terms) (hc : c ∈ d.terms) :
    QueryMatches d ufCollideRule.query (ufEnv a b c) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, fun p hp => ?_⟩
  · change (["@a", "@b", "@c"] : List Var).Perm (Query.vars ufCollideRule.query)
    decide
  · rw [hd.reps_eq_terms]
    rcases ufEnv_mem hx with h | h | h <;> rw [h] <;> assumption
  · rw [collide_query] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact matches_uf_var_var_iff.mpr ⟨a, b, rfl, rfl, hab⟩
    · exact matches_uf_var_var_iff.mpr ⟨a, c, rfl, rfl, hac⟩
    · exact (matches_eq_min_iff hd).mpr ⟨b, c, rfl, rfl, hb, hmin⟩
    · exact matches_ne_var_var_iff.mpr ⟨b, c, rfl, rfl, not_cong_of_ne hd hne⟩

/-! ### The column groups -/

/-- The variable names of one column group of the congruence and subsumption rules. -/
def congNames (stem : String) (n : Nat) : List Var :=
  (List.range n).map fun i => "@" ++ stem ++ toString i

theorem congruenceVars_eq_map (stem : String) (n : Nat) :
    congruenceVars stem n = (congNames stem n).map Expr.var := by
  simp [congruenceVars, congNames]

theorem congNames_length (stem : String) (n : Nat) : (congNames stem n).length = n := by
  simp [congNames]

theorem congNames_getElem (stem : String) {n i : Nat} (hi : i < n) :
    (congNames stem n)[i]'(by rw [congNames_length]; exact hi) = "@" ++ stem ++ toString i := by
  simp [congNames]

theorem mem_congNames {stem : String} {n : Nat} {v : Var} :
    v ∈ congNames stem n ↔ ∃ i, i < n ∧ v = "@" ++ stem ++ toString i := by
  simp only [congNames, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem congName_toList (stem : String) (i : Nat) :
    ("@" ++ stem ++ toString i).toList = '@' :: (stem.toList ++ (toString i).toList) := by
  rw [String.toList_append, String.toList_append, show ("@").toList = ['@'] from by decide]
  rfl

theorem congName_inj {stem : String} {i j : Nat}
    (h : "@" ++ stem ++ toString i = "@" ++ stem ++ toString j) : i = j := by
  have h2 := congrArg String.toList h
  rw [congName_toList, congName_toList] at h2
  exact toString_nat_inj (String.toList_inj.mp (List.append_cancel_left (List.cons.inj h2).2))

theorem congNames_nodup (stem : String) (n : Nat) : (congNames stem n).Nodup := by
  refine (List.nodup_map_iff_inj_on List.nodup_range).mpr fun i _ j _ h => congName_inj h

/-- Column groups with different stems share no name. -/
theorem congName_ne_of_stem {s s' : String} {c c' : Char} (hs : s.toList = [c])
    (hs' : s'.toList = [c']) (hne : c ≠ c') (i j : Nat) :
    "@" ++ s ++ toString i ≠ "@" ++ s' ++ toString j := by
  intro h
  have h2 := congrArg String.toList h
  rw [congName_toList, congName_toList, hs, hs'] at h2
  exact hne (List.cons.inj (List.cons.inj h2).2).1

/-- A two-character generated name is in no column group. -/
theorem short_ne_congName {w : String} {c₂ : Char} (hw : w.toList = ['@', c₂]) {s : String}
    {c : Char} (hs : s.toList = [c]) (hne : c₂ ≠ c) (i : Nat) : w ≠ "@" ++ s ++ toString i := by
  intro h
  have h2 := congrArg String.toList h
  rw [congName_toList, hs, hw] at h2
  exact hne (List.cons.inj (List.cons.inj h2).2).1

theorem not_mem_congNames_of_stem {s s' : String} {c c' : Char} (hs : s.toList = [c])
    (hs' : s'.toList = [c']) (hne : c ≠ c') {n i : Nat} :
    "@" ++ s ++ toString i ∉ congNames s' n := by
  rw [mem_congNames]
  rintro ⟨j, _, hj⟩
  exact congName_ne_of_stem hs hs' hne i j hj

theorem short_not_mem_congNames {w : String} {c₂ : Char} (hw : w.toList = ['@', c₂]) {s : String}
    {c : Char} (hs : s.toList = [c]) (hne : c₂ ≠ c) {n : Nat} : w ∉ congNames s n := by
  rw [mem_congNames]
  rintro ⟨j, _, hj⟩
  exact short_ne_congName hw hs hne j hj

theorem toList_a : ("a" : String).toList = ['a'] := by decide
theorem toList_b : ("b" : String).toList = ['b'] := by decide
theorem toList_r : ("r" : String).toList = ['r'] := by decide
theorem toList_k : ("@k" : String).toList = ['@', 'k'] := by decide
theorem toList_l : ("@l" : String).toList = ['@', 'l'] := by decide
theorem toList_y : ("@y" : String).toList = ['@', 'y'] := by decide
theorem toList_z : ("@z" : String).toList = ['@', 'z'] := by decide

theorem lookup_zip_eq_none {vs : List Var} {ts : List Term} {v : Var} (hv : v ∉ vs) :
    Env.lookup v (vs.zip ts) = none :=
  Env.lookup_eq_none_iff.mpr fun h => hv (Env.dom_zip_subset vs ts h)

theorem lookup_zip_congNames {stem : String} {n : Nat} {ts : List Term} (hlen : ts.length = n)
    {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ stem ++ toString i) ((congNames stem n).zip ts) =
      some (ts[i]'(by rw [hlen]; exact hi)) := by
  have := Env.lookup_zip (congNames stem n) ts (by rw [congNames_length, hlen])
    (congNames_nodup stem n) i (by rw [congNames_length]; exact hi) (by rw [hlen]; exact hi)
  rwa [congNames_getElem stem hi] at this

/-- The variables of a column group's atoms. -/
theorem mem_varsList_congruenceVars {stem : String} {n : Nat} {v : Var} :
    v ∈ Expr.varsList (congruenceVars stem n) ↔ v ∈ congNames stem n := by
  rw [congruenceVars_eq_map]
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
    simp only [Expr.vars_var, List.mem_singleton] at hve
    exact hve ▸ hw
  · exact fun hv => Expr.var_mem_varsList (List.mem_map_of_mem hv)

theorem Expr.mem_varsList_append {v : Var} : ∀ {xs ys : List Expr},
    v ∈ Expr.varsList (xs ++ ys) ↔ v ∈ Expr.varsList xs ∨ v ∈ Expr.varsList ys
  | [], _ => by simp
  | x :: xs, ys => by
      rw [List.cons_append, Expr.varsList_cons, Expr.varsList_cons, List.mem_union_iff,
        List.mem_union_iff, Expr.mem_varsList_append, or_assoc]

/-- The variables of the edge atoms. -/
theorem mem_vars_edgeAtoms {n : Nat} {v : Var} :
    v ∈ Query.vars (edgeAtoms n) ↔
      v ∈ congNames "a" n ∨ v ∈ congNames "b" n ∨ v ∈ congNames "r" n := by
  rw [Query.mem_vars]
  constructor
  · rintro ⟨p, hp, hv⟩
    obtain ⟨i, hi, rfl | rfl⟩ := mem_edgeAtoms hp
    · simp only [Pattern.vars, ufRow, Expr.vars_app, Expr.varsList_cons, Expr.varsList_nil,
        List.mem_union_iff, Expr.vars_var, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Or.inl (mem_congNames.mpr ⟨i, hi, rfl⟩)
      · exact Or.inr (Or.inr (mem_congNames.mpr ⟨i, hi, rfl⟩))
    · simp only [Pattern.vars, ufRow, Expr.vars_app, Expr.varsList_cons, Expr.varsList_nil,
        List.mem_union_iff, Expr.vars_var, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Or.inr (Or.inl (mem_congNames.mpr ⟨i, hi, rfl⟩))
      · exact Or.inr (Or.inr (mem_congNames.mpr ⟨i, hi, rfl⟩))
  · rintro (hv | hv | hv)
    · obtain ⟨i, hi, rfl⟩ := mem_congNames.mp hv
      exact ⟨_, (edge_atoms_mem hi).1, by simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]⟩
    · obtain ⟨i, hi, rfl⟩ := mem_congNames.mp hv
      exact ⟨_, (edge_atoms_mem hi).2, by simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]⟩
    · obtain ⟨i, hi, rfl⟩ := mem_congNames.mp hv
      exact ⟨_, (edge_atoms_mem hi).1, by simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]⟩

/-- A column group evaluates to its values under a substitution that binds them. -/
theorem evalList_congruenceVars {σ : Env} {stem : String} {n : Nat} {ts : List Term}
    (hlen : ts.length = n)
    (hlook : ∀ i (hi : i < n), Env.lookup ("@" ++ stem ++ toString i) σ =
      some (ts[i]'(by rw [hlen]; exact hi))) :
    Expr.evalList (congruenceVars stem n) σ = some ts := by
  rw [congruenceVars_eq_map]
  apply Expr.evalList_map_var _ _ _ (by rw [congNames_length, hlen])
  intro i hi hi'
  rw [congNames_length] at hi
  rw [congNames_getElem stem hi]
  exact hlook i hi

theorem matchesList_congruenceVars {d : Database} {σ : Env} {stem : String} {n : Nat}
    {ts : List Term} (hts : Expr.evalList (congruenceVars stem n) σ = some ts) :
    Expr.MatchesList d σ (congruenceVars stem n) := by
  rw [congruenceVars_eq_map]
  apply matchesList_map_var
  intro v hv
  rw [congruenceVars_eq_map] at hts
  exact Expr.lookup_isSome_of_mem_evalList hts (List.mem_map_of_mem hv)

theorem evalList_append_of {σ : Env} {xs ys : List Expr} {ts us : List Term}
    (h₁ : Expr.evalList xs σ = some ts) (h₂ : Expr.evalList ys σ = some us) :
    Expr.evalList (xs ++ ys) σ = some (ts ++ us) := by
  induction xs generalizing ts with
  | nil =>
    rw [Expr.evalList_nil, Option.some.injEq] at h₁
    subst h₁
    simpa using h₂
  | cons x xs ih =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h₁
    obtain ⟨t, ht, hrest⟩ := h₁
    obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp hrest
    rw [List.cons_append, Expr.evalList_cons, ht, Option.bind_some, ih hts', Option.map_some,
      List.cons_append]

/-- A node atom over a column group matches the node row of the group's values. -/
theorem node_atom_fire {src d : Database} (h : Rel sub src d) {σ : Env} {f : FnName}
    {stem : String} {n : Nat} {as : List Term} {v : Var}
    (has : Expr.evalList (congruenceVars stem n) σ = some as)
    (hv : Env.lookup v σ = some (Term.app f as)) (hn : Node d f as) :
    Matches d (.expr (nodeAtom f (congruenceVars stem n) (.var v))) σ := by
  unfold nodeAtom
  refine matches_app_iff.mpr ⟨as ++ [Term.app f as], ?_, ?_, h.node_live hn⟩
  · have hmap : congruenceVars stem n ++ [Expr.var v] = (congNames stem n ++ [v]).map Expr.var := by
      rw [congruenceVars_eq_map, List.map_append, List.map_singleton]
    rw [hmap]
    apply matchesList_map_var
    intro w hw
    rw [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · rw [congruenceVars_eq_map] at has
      exact Expr.lookup_isSome_of_mem_evalList has (List.mem_map_of_mem hw)
    · rw [hv]; rfl
  · exact evalList_append_of has (by simp [Expr.evalList, hv])

/-! ### The congruence rule -/

/-- The substitution of the congruence rule: the two nodes' children, the parents, the two
nodes and their roots. -/
def congEnv (as bs rs : List Term) (k l y z : Term) (n : Nat) : Env :=
  (congNames "a" n).zip as ++ ((congNames "b" n).zip bs ++
    ((congNames "r" n).zip rs ++ [("@k", k), ("@l", l), ("@y", y), ("@z", z)]))

section

variable {as bs rs : List Term} {k l y z : Term} {n : Nat}
  (hla : as.length = n) (hlb : bs.length = n) (hlr : rs.length = n)
include hla hlb hlr

omit hlb hlr in
theorem congEnv_lookup_a {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "a" ++ toString i) (congEnv as bs rs k l y z n) =
      some (as[i]'(by rw [hla]; exact hi)) :=
  Env.lookup_append_of_some (lookup_zip_congNames hla hi)

omit hla hlr in
theorem congEnv_lookup_b {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "b" ++ toString i) (congEnv as bs rs k l y z n) =
      some (bs[i]'(by rw [hlb]; exact hi)) := by
  unfold congEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_b toList_a (by decide)))]
  exact Env.lookup_append_of_some (lookup_zip_congNames hlb hi)

omit hla hlb in
theorem congEnv_lookup_r {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "r" ++ toString i) (congEnv as bs rs k l y z n) =
      some (rs[i]'(by rw [hlr]; exact hi)) := by
  unfold congEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_b (by decide)))]
  exact Env.lookup_append_of_some (lookup_zip_congNames hlr hi)

omit hla hlb hlr in
theorem congEnv_lookup_short {w : Var} {c : Char} (hw : w.toList = ['@', c]) (ha : c ≠ 'a')
    (hb : c ≠ 'b') (hr : c ≠ 'r') :
    Env.lookup w (congEnv as bs rs k l y z n) =
      Env.lookup w [("@k", k), ("@l", l), ("@y", y), ("@z", z)] := by
  unfold congEnv
  rw [Env.lookup_append_of_none (lookup_zip_eq_none (short_not_mem_congNames hw toList_a ha)),
    Env.lookup_append_of_none (lookup_zip_eq_none (short_not_mem_congNames hw toList_b hb)),
    Env.lookup_append_of_none (lookup_zip_eq_none (short_not_mem_congNames hw toList_r hr))]

omit hla hlb hlr in
theorem congEnv_lookup_k : Env.lookup "@k" (congEnv as bs rs k l y z n) = some k := by
  rw [congEnv_lookup_short toList_k (by decide) (by decide) (by decide)]; rfl

omit hla hlb hlr in
theorem congEnv_lookup_l : Env.lookup "@l" (congEnv as bs rs k l y z n) = some l := by
  rw [congEnv_lookup_short toList_l (by decide) (by decide) (by decide)]; rfl

omit hla hlb hlr in
theorem congEnv_lookup_y : Env.lookup "@y" (congEnv as bs rs k l y z n) = some y := by
  rw [congEnv_lookup_short toList_y (by decide) (by decide) (by decide)]; rfl

omit hla hlb hlr in
theorem congEnv_lookup_z : Env.lookup "@z" (congEnv as bs rs k l y z n) = some z := by
  rw [congEnv_lookup_short toList_z (by decide) (by decide) (by decide)]; rfl

theorem congEnv_dom : Env.dom (congEnv as bs rs k l y z n) =
    congNames "a" n ++ (congNames "b" n ++ (congNames "r" n ++ ["@k", "@l", "@y", "@z"])) := by
  unfold congEnv Env.dom
  rw [List.map_append, List.map_append, List.map_append, List.map_fst_zip, List.map_fst_zip,
    List.map_fst_zip]
  · rfl
  all_goals rw [congNames_length]; omega

theorem congEnv_dom_nodup : (Env.dom (congEnv as bs rs k l y z n)).Nodup := by
  rw [congEnv_dom hla hlb hlr]
  have disj : ∀ {s s' : String} {c c' : Char}, s.toList = [c] → s'.toList = [c'] → c ≠ c' →
      List.Disjoint (congNames s n) (congNames s' n) := by
    intro s s' c c' hs hs' hne v hv hv'
    obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
    exact not_mem_congNames_of_stem hs hs' hne hv'
  have hshort : (["@k", "@l", "@y", "@z"] : List Var).Nodup := by decide
  have hnot : ∀ {s : String} {c : Char}, s.toList = [c] → c ≠ 'k' → c ≠ 'l' → c ≠ 'y' →
      c ≠ 'z' → ∀ v ∈ congNames s n, v ∉ (["@k", "@l", "@y", "@z"] : List Var) := by
    intro s c hs hk hl hy hz v hv hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl | rfl
    · exact short_not_mem_congNames toList_k hs (Ne.symm hk) hv
    · exact short_not_mem_congNames toList_l hs (Ne.symm hl) hv
    · exact short_not_mem_congNames toList_y hs (Ne.symm hy) hv
    · exact short_not_mem_congNames toList_z hs (Ne.symm hz) hv
  refine List.Nodup.append (congNames_nodup _ _) (List.Nodup.append (congNames_nodup _ _)
    (List.Nodup.append (congNames_nodup _ _) hshort ?_) ?_) ?_
  · exact hnot toList_r (by decide) (by decide) (by decide) (by decide)
  · intro v hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_b toList_r (by decide) hv hv'
    · exact hnot toList_b (by decide) (by decide) (by decide) (by decide) v hv hv'
  · intro v hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_a toList_b (by decide) hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_a toList_r (by decide) hv hv'
    · exact hnot toList_a (by decide) (by decide) (by decide) (by decide) v hv hv'

omit hla hlb hlr in
theorem congEnv_mem_values {x : Var × Term} (hx : x ∈ congEnv as bs rs k l y z n) :
    x.2 ∈ as ∨ x.2 ∈ bs ∨ x.2 ∈ rs ∨ x.2 = k ∨ x.2 = l ∨ x.2 = y ∨ x.2 = z := by
  unfold congEnv at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | rfl | rfl | rfl | rfl
  · exact Or.inl (List.of_mem_zip hx).2
  · exact Or.inr (Or.inl (List.of_mem_zip hx).2)
  · exact Or.inr (Or.inr (Or.inl (List.of_mem_zip hx).2))
  · simp
  · simp
  · simp
  · simp

end

/-- The variables of the congruence rule's query. -/
theorem mem_congruence_vars_node {f : FnName} {n : Nat} {v : Var} :
    v ∈ Query.vars (congruenceRule true f n).query ↔
      v ∈ congNames "a" n ∨ v ∈ congNames "b" n ∨ v ∈ congNames "r" n ∨
        v = "@k" ∨ v = "@l" ∨ v = "@y" ∨ v = "@z" := by
  rw [congruence_query_node, Query.mem_vars_append, Query.mem_vars_append, mem_vars_edgeAtoms]
  simp only [Query.vars_cons, Query.vars_nil, Pattern.vars, nodeAtom, ufRow, Expr.vars_app,
    Expr.mem_varsList_append, mem_varsList_congruenceVars, Expr.varsList_cons, Expr.varsList_nil,
    List.mem_union_iff, Expr.vars_var, List.mem_singleton, List.not_mem_nil, or_false,
    Expr.vars_min]
  tauto

/-- The congruence rule fires on two nodes with the same live child parents. -/
theorem congruence_fire_node {src d : Database} (h : Rel sub src d) {f : FnName} {as bs rs : List Term}
    {y z : Term} (hna : Node d f as) (hnb : Node d f bs)
    (hra : List.Forall₂ (Edge d) as rs) (hrb : List.Forall₂ (Edge d) bs rs)
    (hey : Edge d (.app f as) y) (hez : Edge d (.app f bs) z) (hmin : y = Term.least y z)
    (hne : y ≠ z) :
    QueryMatches d (congruenceRule true f as.length).query
      (congEnv as bs rs (.app f as) (.app f bs) y z as.length) := by
  set n := as.length with hn
  have hlen_a : as.length = n := rfl
  have hlen_r : rs.length = n := hra.length_eq.symm
  have hlen_b : bs.length = n := hrb.length_eq.trans hlen_r
  have hterms : ∀ x ∈ congEnv as bs rs (.app f as) (.app f bs) y z n, x.2 ∈ d.terms := by
    intro x hx
    rcases congEnv_mem_values hx with hx | hx | hx | hx | hx | hx | hx
    · obtain ⟨r, _, he⟩ := hra.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨r, _, he⟩ := hrb.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨a, _, he⟩ := hra.exists_left hx
      exact Keys.subset_terms d (h.parent_of_edge he)
    · rw [hx]; exact Keys.subset_terms d (h.key_of_edge hey)
    · rw [hx]; exact Keys.subset_terms d (h.key_of_edge hez)
    · rw [hx]; exact Keys.subset_terms d (h.parent_of_edge hey)
    · rw [hx]; exact Keys.subset_terms d (h.parent_of_edge hez)
  have evalA := evalList_congruenceVars (σ := congEnv as bs rs (.app f as) (.app f bs) y z n)
    hlen_a fun i hi => congEnv_lookup_a hlen_a hi
  have evalB := evalList_congruenceVars (σ := congEnv as bs rs (.app f as) (.app f bs) y z n)
    hlen_b fun i hi => congEnv_lookup_b hlen_b hi
  refine ⟨⟨?_, fun x hx => mem_reps_of_diag h.diag (hterms x hx)⟩, fun p hp => ?_⟩
  · rw [List.perm_ext_iff_of_nodup (congEnv_dom_nodup hlen_a hlen_b hlen_r) (Query.vars_nodup _)]
    intro v
    rw [congEnv_dom hlen_a hlen_b hlen_r, mem_congruence_vars_node]
    simp
  · rw [congruence_query_node] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | hp) | rfl | rfl | rfl | rfl
    · exact node_atom_fire h evalA congEnv_lookup_k hna
    · exact node_atom_fire h evalB congEnv_lookup_l hnb
    · obtain ⟨i, hi, rfl | rfl⟩ := mem_edgeAtoms hp
      · exact matches_uf_var_var_iff.mpr ⟨_, _, congEnv_lookup_a hlen_a hi,
          congEnv_lookup_r hlen_r hi, (List.forall₂_iff_get.mp hra).2 i _ _⟩
      · exact matches_uf_var_var_iff.mpr ⟨_, _, congEnv_lookup_b hlen_b hi,
          congEnv_lookup_r hlen_r hi, (List.forall₂_iff_get.mp hrb).2 i _ _⟩
    · exact matches_uf_var_var_iff.mpr ⟨_, _, congEnv_lookup_k, congEnv_lookup_y, hey⟩
    · exact matches_uf_var_var_iff.mpr ⟨_, _, congEnv_lookup_l, congEnv_lookup_z, hez⟩
    · exact (matches_eq_min_iff h.diag).mpr ⟨y, z, congEnv_lookup_y, congEnv_lookup_z,
        Keys.subset_terms d (h.parent_of_edge hey), hmin⟩
    · exact matches_ne_var_var_iff.mpr ⟨y, z, congEnv_lookup_y, congEnv_lookup_z,
        not_cong_of_ne h.diag hne⟩

def plainCongEnv (as bs rs : List Term) (y z : Term) (n : Nat) : Env :=
  (congNames "a" n).zip as ++ ((congNames "b" n).zip bs ++
    ((congNames "r" n).zip rs ++ [("@y", y), ("@z", z)]))

section

variable {as bs rs : List Term} {y z : Term} {n : Nat}
  (hla : as.length = n) (hlb : bs.length = n) (hlr : rs.length = n)
include hla hlb hlr

omit hlb hlr in
theorem plainCongEnv_lookup_a {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "a" ++ toString i) (plainCongEnv as bs rs y z n) =
      some (as[i]'(by rw [hla]; exact hi)) :=
  Env.lookup_append_of_some (lookup_zip_congNames hla hi)

omit hla hlr in
theorem plainCongEnv_lookup_b {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "b" ++ toString i) (plainCongEnv as bs rs y z n) =
      some (bs[i]'(by rw [hlb]; exact hi)) := by
  unfold plainCongEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_b toList_a (by decide)))]
  exact Env.lookup_append_of_some (lookup_zip_congNames hlb hi)

omit hla hlb in
theorem plainCongEnv_lookup_r {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "r" ++ toString i) (plainCongEnv as bs rs y z n) =
      some (rs[i]'(by rw [hlr]; exact hi)) := by
  unfold plainCongEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_b (by decide)))]
  exact Env.lookup_append_of_some (lookup_zip_congNames hlr hi)

omit hla hlb hlr in
theorem plainCongEnv_lookup_y : Env.lookup "@y" (plainCongEnv as bs rs y z n) = some y := by
  unfold plainCongEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_y toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_y toList_b (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_y toList_r (by decide)))]
  rfl

omit hla hlb hlr in
theorem plainCongEnv_lookup_z : Env.lookup "@z" (plainCongEnv as bs rs y z n) = some z := by
  unfold plainCongEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_z toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_z toList_b (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_z toList_r (by decide)))]
  rfl

theorem plainCongEnv_dom : Env.dom (plainCongEnv as bs rs y z n) =
    congNames "a" n ++ (congNames "b" n ++ (congNames "r" n ++ ["@y", "@z"])) := by
  unfold plainCongEnv Env.dom
  rw [List.map_append, List.map_append, List.map_append, List.map_fst_zip, List.map_fst_zip,
    List.map_fst_zip]
  · rfl
  all_goals rw [congNames_length]; omega

theorem plainCongEnv_dom_nodup : (Env.dom (plainCongEnv as bs rs y z n)).Nodup := by
  rw [plainCongEnv_dom hla hlb hlr]
  have disj : ∀ {s s' : String} {c c' : Char}, s.toList = [c] → s'.toList = [c'] → c ≠ c' →
      List.Disjoint (congNames s n) (congNames s' n) := by
    intro s s' c c' hs hs' hne v hv hv'
    obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
    exact not_mem_congNames_of_stem hs hs' hne hv'
  have hyz : (["@y", "@z"] : List Var).Nodup := by decide
  refine List.Nodup.append (congNames_nodup _ _) (List.Nodup.append (congNames_nodup _ _)
    (List.Nodup.append (congNames_nodup _ _) hyz ?_) ?_) ?_
  · intro v hv hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl
    · exact short_not_mem_congNames toList_y toList_r (by decide) hv
    · exact short_not_mem_congNames toList_z toList_r (by decide) hv
  · intro v hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_b toList_r (by decide) hv hv'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with rfl | rfl
      · exact short_not_mem_congNames toList_y toList_b (by decide) hv
      · exact short_not_mem_congNames toList_z toList_b (by decide) hv
  · intro v hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_a toList_b (by decide) hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_a toList_r (by decide) hv hv'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with rfl | rfl
      · exact short_not_mem_congNames toList_y toList_a (by decide) hv
      · exact short_not_mem_congNames toList_z toList_a (by decide) hv

omit hla hlb hlr in
theorem plainCongEnv_mem_values {x : Var × Term} (hx : x ∈ plainCongEnv as bs rs y z n) :
    x.2 ∈ as ∨ x.2 ∈ bs ∨ x.2 ∈ rs ∨ x.2 = y ∨ x.2 = z := by
  unfold plainCongEnv at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | rfl | rfl
  · exact Or.inl (List.of_mem_zip hx).2
  · exact Or.inr (Or.inl (List.of_mem_zip hx).2)
  · exact Or.inr (Or.inr (Or.inl (List.of_mem_zip hx).2))
  · simp
  · simp

end

/-- The variables of the congruence rule's query. -/
theorem mem_congruence_vars_plain {f : FnName} {n : Nat} {v : Var} :
    v ∈ Query.vars (congruenceRule false f n).query ↔
      v ∈ congNames "a" n ∨ v ∈ congNames "b" n ∨ v ∈ congNames "r" n ∨
        v = "@y" ∨ v = "@z" := by
  change v ∈ Query.vars ([.expr (.app f (congruenceVars "a" n)),
    .expr (.app f (congruenceVars "b" n))] ++ edgeAtoms n ++ _) ↔ _
  rw [Query.mem_vars_append, Query.mem_vars_append, mem_vars_edgeAtoms]
  simp only [Bool.false_eq_true, ↓reduceIte, Query.vars_cons, Query.vars_nil, Pattern.vars, ufRow, Expr.vars_app,
    mem_varsList_congruenceVars, Expr.varsList_cons, Expr.varsList_nil,
    List.mem_union_iff, Expr.vars_var, List.mem_singleton, List.not_mem_nil, or_false,
    Expr.vars_min]
  tauto

/-- The congruence rule fires on two live applications with the same live child parents. -/
theorem congruence_fire_plain {src d : Database} (h : Rel sub src d) {f : FnName} {as bs rs : List Term}
    {y z : Term} (hla : Term.app f as ∈ d.live) (hlb : Term.app f bs ∈ d.live)
    (hra : List.Forall₂ (Edge d) as rs) (hrb : List.Forall₂ (Edge d) bs rs)
    (hey : Edge d (.app f as) y) (hez : Edge d (.app f bs) z) (hmin : y = Term.least y z)
    (hne : y ≠ z) :
    QueryMatches d (congruenceRule false f as.length).query (plainCongEnv as bs rs y z as.length) := by
  set n := as.length with hn
  have hlen_a : as.length = n := rfl
  have hlen_r : rs.length = n := hra.length_eq.symm
  have hlen_b : bs.length = n := hrb.length_eq.trans hlen_r
  have hterms : ∀ x ∈ plainCongEnv as bs rs y z n, x.2 ∈ d.terms := by
    intro x hx
    rcases plainCongEnv_mem_values hx with hx | hx | hx | hx | hx
    · obtain ⟨r, _, he⟩ := hra.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨r, _, he⟩ := hrb.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨a, _, he⟩ := hra.exists_left hx
      exact Keys.subset_terms d (h.parent_of_edge he)
    · rw [hx]; exact Keys.subset_terms d (h.parent_of_edge hey)
    · rw [hx]; exact Keys.subset_terms d (h.parent_of_edge hez)
  have hsome : ∀ stem (ts : List Term) (hlen : ts.length = n),
      (∀ i (hi : i < n), Env.lookup ("@" ++ stem ++ toString i) (plainCongEnv as bs rs y z n) =
        some (ts[i]'(by rw [hlen]; exact hi))) →
      Expr.evalList (congruenceVars stem n) (plainCongEnv as bs rs y z n) = some ts := by
    intro stem ts hlen hlook
    rw [congruenceVars_eq_map]
    apply Expr.evalList_map_var _ _ _ (by rw [congNames_length, hlen])
    intro i hi hi'
    rw [congNames_length] at hi
    rw [congNames_getElem stem hi]
    exact hlook i hi
  have evalA := hsome "a" as hlen_a fun i hi => plainCongEnv_lookup_a hlen_a hi
  have evalB := hsome "b" bs hlen_b fun i hi => plainCongEnv_lookup_b hlen_b hi
  have evalR := hsome "r" rs hlen_r fun i hi => plainCongEnv_lookup_r hlen_r hi
  have matchesVars : ∀ stem (ts : List Term),
      Expr.evalList (congruenceVars stem n) (plainCongEnv as bs rs y z n) = some ts →
      Expr.MatchesList d (plainCongEnv as bs rs y z n) (congruenceVars stem n) := by
    intro stem ts hts
    rw [congruenceVars_eq_map]
    apply matchesList_map_var
    intro v hv
    rw [congruenceVars_eq_map] at hts
    exact Expr.lookup_isSome_of_mem_evalList hts (List.mem_map_of_mem hv)
  refine ⟨⟨?_, fun x hx => mem_reps_of_diag h.diag (hterms x hx)⟩, fun p hp => ?_⟩
  · rw [List.perm_ext_iff_of_nodup (plainCongEnv_dom_nodup hlen_a hlen_b hlen_r) (Query.vars_nodup _)]
    intro v
    rw [plainCongEnv_dom hlen_a hlen_b hlen_r, mem_congruence_vars_plain]
    simp
  · rw [congruence_query_plain] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap] at hp
    rcases hp with ((rfl | rfl) | ⟨abr, habr, hp⟩) | rfl | rfl | rfl | rfl
    · exact matches_app_iff.mpr ⟨as, matchesVars "a" as evalA, evalA, hla⟩
    · exact matches_app_iff.mpr ⟨bs, matchesVars "b" bs evalB, evalB, hlb⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp habr
      simp only [List.length_zip, congruenceVars_length, Nat.min_self] at hi
      rw [List.getElem_zip, List.getElem_zip, congruenceVars_getElem "a" hi,
        congruenceVars_getElem "b" hi, congruenceVars_getElem "r" hi] at hp
      have hedge_a : Edge d (as[i]'(by rw [hlen_a]; exact hi)) (rs[i]'(by rw [hlen_r]; exact hi)) :=
        (List.forall₂_iff_get.mp hra).2 i _ _
      have hedge_b : Edge d (bs[i]'(by rw [hlen_b]; exact hi)) (rs[i]'(by rw [hlen_r]; exact hi)) :=
        (List.forall₂_iff_get.mp hrb).2 i _ _
      simp only at hp
      rcases hp with rfl | rfl
      · exact matches_uf_var_var_iff.mpr ⟨_, _, plainCongEnv_lookup_a hlen_a hi,
          plainCongEnv_lookup_r hlen_r hi, hedge_a⟩
      · exact matches_uf_var_var_iff.mpr ⟨_, _, plainCongEnv_lookup_b hlen_b hi,
          plainCongEnv_lookup_r hlen_r hi, hedge_b⟩
    · refine matches_uf_iff.mpr ⟨.app f as, y, .app (matchesVars "a" as evalA) evalA hla,
        .var plainCongEnv_lookup_y, ?_, plainCongEnv_lookup_y, hey⟩
      rw [Expr.eval_app_ctor, evalA]; rfl
    · refine matches_uf_iff.mpr ⟨.app f bs, z, .app (matchesVars "b" bs evalB) evalB hlb,
        .var plainCongEnv_lookup_z, ?_, plainCongEnv_lookup_z, hez⟩
      rw [Expr.eval_app_ctor, evalB]; rfl
    · exact (matches_eq_min_iff h.diag).mpr ⟨y, z, plainCongEnv_lookup_y, plainCongEnv_lookup_z,
        Keys.subset_terms d (h.parent_of_edge hey), hmin⟩
    · exact matches_ne_var_var_iff.mpr ⟨y, z, plainCongEnv_lookup_y, plainCongEnv_lookup_z,
        not_cong_of_ne h.diag hne⟩

/-- All congruence-query variables belong to the three column groups or output ids. -/
theorem congruence_vars_subset {f : FnName} {n : Nat} {v : Var}
    (hv : v ∈ Query.vars (congruenceRule sub f n).query) :
    v ∈ congNames "a" n ∨ v ∈ congNames "b" n ∨ v ∈ congNames "r" n ∨
      v = "@k" ∨ v = "@l" ∨ v = "@y" ∨ v = "@z" := by
  cases sub with
  | false => have := mem_congruence_vars_plain.mp hv; tauto
  | true => exact mem_congruence_vars_node.mp hv

/-- Either representation of nodes supplies a congruence firing. -/
theorem congruence_fire {src d : Database} (h : Rel sub src d) {f : FnName}
    {as bs rs : List Term} {y z : Term}
    (hra : List.Forall₂ (Edge d) as rs) (hrb : List.Forall₂ (Edge d) bs rs)
    (hey : Edge d (.app f as) y) (hez : Edge d (.app f bs) z)
    (hmin : y = Term.least y z) (hne : y ≠ z) :
    ∃ σ, QueryMatches d (congruenceRule sub f as.length).query σ ∧
      Env.lookup "@y" σ = some y ∧ Env.lookup "@z" σ = some z := by
  cases sub with
  | false =>
    exact ⟨_, congruence_fire_plain h (h.plain_live rfl (h.key_of_edge hey))
      (h.plain_live rfl (h.key_of_edge hez)) hra hrb hey hez hmin hne,
      plainCongEnv_lookup_y, plainCongEnv_lookup_z⟩
  | true =>
    exact ⟨_, congruence_fire_node h (h.nodes f as (h.key_of_edge hey) rfl)
      (h.nodes f bs (h.key_of_edge hez) rfl) hra hrb hey hez hmin hne,
      congEnv_lookup_y, congEnv_lookup_z⟩

/-! ### The subsumption rule -/

/-- The substitution of the subsumption rule: the marked spelling's children, the live
application's children, and the parents. -/
def subEnv (as bs rs : List Term) (n : Nat) : Env :=
  (congNames "a" n).zip as ++ ((congNames "b" n).zip bs ++ (congNames "r" n).zip rs)

section

variable {as bs rs : List Term} {n : Nat}
  (hla : as.length = n) (hlb : bs.length = n) (hlr : rs.length = n)
include hla hlb hlr

omit hlb hlr in
theorem subEnv_lookup_a {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "a" ++ toString i) (subEnv as bs rs n) =
      some (as[i]'(by rw [hla]; exact hi)) :=
  Env.lookup_append_of_some (lookup_zip_congNames hla hi)

omit hla hlr in
theorem subEnv_lookup_b {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "b" ++ toString i) (subEnv as bs rs n) =
      some (bs[i]'(by rw [hlb]; exact hi)) := by
  unfold subEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_b toList_a (by decide)))]
  exact Env.lookup_append_of_some (lookup_zip_congNames hlb hi)

omit hla hlb in
theorem subEnv_lookup_r {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "r" ++ toString i) (subEnv as bs rs n) =
      some (rs[i]'(by rw [hlr]; exact hi)) := by
  unfold subEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_b (by decide)))]
  exact lookup_zip_congNames hlr hi

theorem subEnv_dom : Env.dom (subEnv as bs rs n) =
    congNames "a" n ++ (congNames "b" n ++ congNames "r" n) := by
  unfold subEnv Env.dom
  rw [List.map_append, List.map_append, List.map_fst_zip, List.map_fst_zip, List.map_fst_zip]
  all_goals rw [congNames_length]; omega

theorem subEnv_dom_nodup : (Env.dom (subEnv as bs rs n)).Nodup := by
  rw [subEnv_dom hla hlb hlr]
  have disj : ∀ {s s' : String} {c c' : Char}, s.toList = [c] → s'.toList = [c'] → c ≠ c' →
      List.Disjoint (congNames s n) (congNames s' n) := by
    intro s s' c c' hs hs' hne v hv hv'
    obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
    exact not_mem_congNames_of_stem hs hs' hne hv'
  refine List.Nodup.append (congNames_nodup _ _)
    (List.Nodup.append (congNames_nodup _ _) (congNames_nodup _ _)
      (disj toList_b toList_r (by decide))) ?_
  intro v hv hv'
  rcases List.mem_append.mp hv' with hv' | hv'
  · exact disj toList_a toList_b (by decide) hv hv'
  · exact disj toList_a toList_r (by decide) hv hv'

omit hla hlb hlr in
theorem subEnv_mem_values {x : Var × Term} (hx : x ∈ subEnv as bs rs n) :
    x.2 ∈ as ∨ x.2 ∈ bs ∨ x.2 ∈ rs := by
  unfold subEnv at hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx | hx
  · exact Or.inl (List.of_mem_zip hx).2
  · exact Or.inr (Or.inl (List.of_mem_zip hx).2)
  · exact Or.inr (Or.inr (List.of_mem_zip hx).2)

end

/-- The variables of the subsumption rule's query. -/
theorem mem_subsume_vars {f : FnName} {n : Nat} {v : Var} :
    v ∈ Query.vars (subsumeRule f n).query ↔
      v ∈ congNames "a" n ∨ v ∈ congNames "b" n ∨ v ∈ congNames "r" n := by
  rw [subsume_query, Query.mem_vars_append, mem_vars_edgeAtoms]
  simp only [Query.vars_cons, Query.vars_nil, Pattern.vars, subRow, Expr.vars_app,
    mem_varsList_congruenceVars, List.mem_union_iff, List.not_mem_nil, or_false]
  tauto

/-- The subsumption rule fires on a marker and a live application with the same live child
parents. -/
theorem subsume_fire {src d : Database} (h : Rel sub src d) {f : FnName} {as bs rs : List Term}
    (hm : Marker d f as) (hl : Term.app f bs ∈ d.live)
    (hra : List.Forall₂ (Edge d) as rs) (hrb : List.Forall₂ (Edge d) bs rs) :
    QueryMatches d (subsumeRule f as.length).query (subEnv as bs rs as.length) := by
  set n := as.length with hn
  have hlen_a : as.length = n := rfl
  have hlen_r : rs.length = n := hra.length_eq.symm
  have hlen_b : bs.length = n := hrb.length_eq.trans hlen_r
  have hterms : ∀ x ∈ subEnv as bs rs n, x.2 ∈ d.terms := by
    intro x hx
    rcases subEnv_mem_values hx with hx | hx | hx
    · obtain ⟨r, _, he⟩ := hra.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨r, _, he⟩ := hrb.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨a, _, he⟩ := hra.exists_left hx
      exact Keys.subset_terms d (h.parent_of_edge he)
  have evalA := evalList_congruenceVars (σ := subEnv as bs rs n) hlen_a
    fun i hi => subEnv_lookup_a hlen_a hi
  have evalB := evalList_congruenceVars (σ := subEnv as bs rs n) hlen_b
    fun i hi => subEnv_lookup_b hlen_b hi
  refine ⟨⟨?_, fun x hx => mem_reps_of_diag h.diag (hterms x hx)⟩, fun p hp => ?_⟩
  · rw [List.perm_ext_iff_of_nodup (subEnv_dom_nodup hlen_a hlen_b hlen_r) (Query.vars_nodup _)]
    intro v
    rw [subEnv_dom hlen_a hlen_b hlen_r, mem_subsume_vars]
    simp
  · rw [subsume_query] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl) | hp
    · exact matches_app_iff.mpr ⟨as, matchesList_congruenceVars evalA, evalA, h.marker_live hm⟩
    · exact matches_app_iff.mpr ⟨bs, matchesList_congruenceVars evalB, evalB, hl⟩
    · obtain ⟨i, hi, rfl | rfl⟩ := mem_edgeAtoms hp
      · exact matches_uf_var_var_iff.mpr ⟨_, _, subEnv_lookup_a hlen_a hi,
          subEnv_lookup_r hlen_r hi, (List.forall₂_iff_get.mp hra).2 i _ _⟩
      · exact matches_uf_var_var_iff.mpr ⟨_, _, subEnv_lookup_b hlen_b hi,
          subEnv_lookup_r hlen_r hi, (List.forall₂_iff_get.mp hrb).2 i _ _⟩

end Egglog.Congruence
