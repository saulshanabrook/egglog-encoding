import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Proofs.Provenance.Round
import EgglogSemantics.Proofs.Congruence.Flatten
import EgglogSemantics.Proofs.Congruence.Writes
import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Proofs.Congruence.Rules
import EgglogSemantics.Proofs.Congruence.Firing
import EgglogSemantics.Proofs.Congruence.Simulate

/-! The congruence compiler's output satisfies `Instrumentable`: it is union-free, its
names avoid the log prefix, and every query or check variable is an argument of an
application pattern. This supplies the premise for `ExtlogTheorems.passes_compose`. -/

namespace Egglog.Provenance

variable {sub : Bool}

open Congruence

/-! ### Names outside the log namespace -/

theorem firePrefix_toList : firePrefix.toList = ['@', 'f', 'i', 'r', 'e', ':'] := by decide

/-- A name that starts with `@` and a character other than `f`. -/
theorem dataName_of_second {s : String} {c : Char} {rest : List Char}
    (hs : s.toList = '@' :: c :: rest) (hc : c ≠ 'f') : DataName s := by
  change firePrefix.isPrefixOf s = false
  rw [Bool.eq_false_iff]
  intro h
  rw [String.isPrefixOf, String.startsWith_string_iff, firePrefix_toList, hs] at h
  obtain ⟨t, ht⟩ := h
  rw [List.cons_append, List.cons_append] at ht
  exact hc (List.cons.inj (List.cons.inj ht).2).1.symm

/-- A source name, which avoids `@`. -/
theorem dataName_of_not_at {s : String} (h : ¬ "@".isPrefixOf s) : DataName s := by
  change firePrefix.isPrefixOf s = false
  rw [Bool.eq_false_iff]
  intro hp
  apply h
  rw [String.isPrefixOf, String.startsWith_string_iff] at hp ⊢
  refine List.IsPrefix.trans ?_ hp
  rw [show ("@").toList = ['@'] from by decide, firePrefix_toList]
  exact ⟨_, rfl⟩

theorem dataName_ufName : DataName ufName := by decide

theorem dataName_nodeName (f : FnName) : DataName (nodeName f) :=
  dataName_of_second (by
    rw [nodeName, String.toList_append,
      show ("@Node").toList = ['@', 'N', 'o', 'd', 'e'] from by decide]
    rfl) (by decide)

theorem dataName_subName (f : FnName) : DataName (subName f) :=
  dataName_of_second (by
    rw [subName, String.toList_append,
      show ("@Sub").toList = ['@', 'S', 'u', 'b'] from by decide]
    rfl) (by decide)

theorem dataName_freshVar (k : Nat) : DataName (freshVar k) :=
  dataName_of_second (by
    rw [freshVar, String.toList_append, show ("@v").toList = ['@', 'v'] from by decide]
    rfl) (by decide)

theorem dataName_congName {stem : String} {c : Char} (hs : stem.toList = [c]) (hc : c ≠ 'f')
    (i : Nat) : DataName ("@" ++ stem ++ toString i) :=
  dataName_of_second (by
    rw [String.toList_append, String.toList_append, show ("@").toList = ['@'] from by decide, hs]
    rfl) hc

/-! ### Union-freedom -/

theorem actions_unionFree_mem : ∀ {as : List Action}, Actions.UnionFree as →
    ∀ a ∈ as, a.UnionFree
  | [], _, _, h => by simp at h
  | b :: bs, h, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.1
      · exact actions_unionFree_mem h.2 a ha

theorem unionFree_of_unionFree {Q : Program} (h : Q.UnionFree) : unionFree Q = true := by
  rw [unionFree, List.all_eq_true]
  intro r hr
  rw [List.all_eq_true]
  intro a ha
  have := actions_unionFree_mem (h r hr) a ha
  cases a <;> simp [Action.UnionFree] at this ⊢

/-! ### Constructors of the compiled program -/

theorem mem_ufRow_ctors {a b : Expr} {fk : FnName × Nat} :
    fk ∈ (ufRow a b).ctors ↔ fk = (ufName, 2) ∨ fk ∈ a.ctors ∨ fk ∈ b.ctors := by
  simp [ufRow, Expr.ctors, Expr.ctorsList]

theorem ctorsList_eq_nil_of_vars : ∀ {es : List Expr}, (∀ e ∈ es, ∃ v, e = Expr.var v) →
    Expr.ctorsList es = []
  | [], _ => rfl
  | e :: es, h => by
      obtain ⟨v, rfl⟩ := h e List.mem_cons_self
      rw [Expr.ctorsList, Expr.ctors, List.nil_append]
      exact ctorsList_eq_nil_of_vars fun e' he' => h e' (List.mem_cons_of_mem _ he')

theorem ctorsList_freshArgs (next k : Nat) : Expr.ctorsList (freshArgs next k) = [] :=
  ctorsList_eq_nil_of_vars fun e he => by
    obtain ⟨i, _, rfl⟩ := mem_freshArgs.mp he
    exact ⟨_, rfl⟩

theorem ctorsList_congruenceVars (stem : String) (n : Nat) :
    Expr.ctorsList (congruenceVars stem n) = [] :=
  ctorsList_eq_nil_of_vars fun e he => by
    rw [congruenceVars_eq_map] at he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact ⟨v, rfl⟩

theorem ctorsList_append (as bs : List Expr) :
    Expr.ctorsList (as ++ bs) = Expr.ctorsList as ++ Expr.ctorsList bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [Expr.ctorsList, ih, List.append_assoc]

mutual

/-- Flattened atoms use source constructors and names outside the log namespace; the id
applies only source constructors. -/
theorem flat_ctors : ∀ (e : Expr) (n : Nat),
    (∀ p ∈ (encodeQueryExprWith {} e n).2.1, ∀ fk ∈ p.ctors, fk ∈ e.ctors ∨ DataName fk.1) ∧
      ∀ fk ∈ (encodeQueryExprWith {} e n).1.ctors, fk ∈ e.ctors
  | .lit _, _ => by rw [flat_lit]; exact ⟨by simp, fun _ h => h⟩
  | .var _, _ => by rw [flat_var]; exact ⟨by simp, fun _ h => h⟩
  | .min _ _, _ => by rw [flat_min]; exact ⟨by simp, fun _ h => h⟩
  | .app f args, n => by
      rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have ih := flatArgs_ctors args n
      rw [hr] at ih
      simp only at ih
      rw [flat_app hr]
      refine ⟨?_, by simp [Expr.ctors]⟩
      intro p hp fk hfk
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hp
      rcases hp with (hp | rfl | ⟨ax, hax, rfl⟩) | rfl
      · rcases ih.1 p hp fk hfk with h | h
        · exact Or.inl (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · rw [Pattern.ctors, Expr.ctors, ctorsList_freshArgs, freshArgs_length,
          List.mem_singleton] at hfk
        subst hfk
        exact Or.inl (by rw [Expr.ctors]; exact List.mem_cons_self)
      · obtain ⟨ha, hx⟩ := List.of_mem_zip hax
        rw [Pattern.ctors, mem_ufRow_ctors] at hfk
        rcases hfk with rfl | hfk | hfk
        · exact Or.inr dataName_ufName
        · obtain ⟨i, _, hax⟩ := mem_freshArgs.mp ha
          rw [hax] at hfk
          simp [Expr.ctors] at hfk
        · exact Or.inl (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ (ih.2 ax.2 hx fk hfk))
      · rw [Pattern.ctors, mem_ufRow_ctors] at hfk
        rcases hfk with rfl | hfk | hfk
        · exact Or.inr dataName_ufName
        · rw [Expr.ctors, ctorsList_freshArgs, freshArgs_length, List.mem_singleton] at hfk
          subst hfk
          exact Or.inl (by rw [Expr.ctors]; exact List.mem_cons_self)
        · simp [Expr.ctors] at hfk

theorem flatArgs_ctors : ∀ (es : List Expr) (n : Nat),
    (∀ p ∈ (encodeQueryArgsWith {} es n).2.1, ∀ fk ∈ p.ctors,
      fk ∈ Expr.ctorsList es ∨ DataName fk.1) ∧
      ∀ x ∈ (encodeQueryArgsWith {} es n).1, ∀ fk ∈ x.ctors, fk ∈ Expr.ctorsList es
  | [], _ => by rw [flatArgs_nil]; exact ⟨by simp, by simp⟩
  | e :: es, n => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      have ih₁ := flat_ctors e n
      have ih₂ := flatArgs_ctors es next
      rw [h₁] at ih₁
      rw [h₂] at ih₂
      simp only at ih₁ ih₂
      rw [flatArgs_cons h₁ h₂]
      constructor
      · intro p hp fk hfk
        rcases List.mem_append.mp hp with hp | hp
        · exact (ih₁.1 p hp fk hfk).imp_left fun h => by
            rw [Expr.ctorsList]; exact List.mem_append_left _ h
        · exact (ih₂.1 p hp fk hfk).imp_left fun h => by
            rw [Expr.ctorsList]; exact List.mem_append_right _ h
      · intro y hy fk hfk
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [Expr.ctorsList]; exact List.mem_append_left _ (ih₁.2 fk hfk)
        · rw [Expr.ctorsList]; exact List.mem_append_right _ (ih₂.2 y hy fk hfk)

end

theorem pattern_ctors (p : Pattern) (n : Nat) :
    ∀ q ∈ (encodePatternWith {} p n).1, ∀ fk ∈ q.ctors, fk ∈ p.ctors ∨ DataName fk.1 := by
  cases p with
  | expr e => rw [pattern_expr]; exact (flat_ctors e n).1
  | eq l r | ne l r =>
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    have hl := flat_ctors l n
    have hr := flat_ctors r next
    rw [h₁] at hl
    rw [h₂] at hr
    simp only at hl hr
    first
    | rw [pattern_eq h₁ h₂]
    | rw [pattern_ne h₁ h₂]
    intro q hq fk hfk
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | rfl
    · exact (hl.1 q hq fk hfk).imp_left (List.mem_append_left _)
    · exact (hr.1 q hq fk hfk).imp_left (List.mem_append_right _)
    · rcases List.mem_append.mp hfk with hfk | hfk
      · exact Or.inl (List.mem_append_left _ (hl.2 fk hfk))
      · exact Or.inl (List.mem_append_right _ (hr.2 fk hfk))

theorem query_ctors (q : Query) (n : Nat) :
    ∀ p' ∈ (encodeQueryWith {} q n).1, ∀ fk ∈ p'.ctors,
      fk ∈ q.flatMap Pattern.ctors ∨ DataName fk.1 := by
  induction q generalizing n with
  | nil => rw [query_nil]; simp
  | cons p ps ih =>
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    have hp := pattern_ctors p n
    have hps := ih next
    rw [h₁] at hp
    rw [h₂] at hps
    simp only at hp hps
    rw [query_cons h₁ h₂]
    intro p' hp' fk hfk
    rcases List.mem_append.mp hp' with hp' | hp'
    · exact (hp p' hp' fk hfk).imp_left fun h => List.mem_flatMap.mpr ⟨p, List.mem_cons_self, h⟩
    · refine (hps p' hp' fk hfk).imp_left fun h => ?_
      obtain ⟨p'', hp'', h⟩ := List.mem_flatMap.mp h
      exact List.mem_flatMap.mpr ⟨p'', List.mem_cons_of_mem _ hp'', h⟩

theorem build_min (a b : Expr) :
    encodeBuildWith { subsumption := sub } (.min a b) = encodeBuildWith { subsumption := sub } a ++ encodeBuildWith { subsumption := sub } b := rfl

mutual

/-- A compiled build uses source constructors and generated names outside the log namespace. -/
theorem build_ctors : ∀ (e : Expr), ∀ a ∈ encodeBuildWith { subsumption := sub } e, ∀ fk ∈ a.ctors,
    fk ∈ e.ctors ∨ DataName fk.1
  | .lit l, a, ha, fk, hfk => by
      rw [build_lit, List.mem_singleton] at ha
      subst ha
      rw [Action.ctors, mem_ufRow_ctors] at hfk
      rcases hfk with rfl | hfk | hfk
      · exact Or.inr dataName_ufName
      · exact Or.inl hfk
      · exact Or.inl hfk
  | .var v, a, ha, fk, hfk => by
      rw [build_var, List.mem_singleton] at ha
      subst ha
      rw [Action.ctors, mem_ufRow_ctors] at hfk
      rcases hfk with rfl | hfk | hfk
      · exact Or.inr dataName_ufName
      · exact Or.inl hfk
      · exact Or.inl hfk
  | .min a b, c, hc, fk, hfk => by
      rw [build_min, List.mem_append] at hc
      rcases hc with hc | hc
      · exact (build_ctors a c hc fk hfk).imp_left fun h => by
          rw [Expr.ctors]; exact List.mem_append_left _ h
      · exact (build_ctors b c hc fk hfk).imp_left fun h => by
          rw [Expr.ctors]; exact List.mem_append_right _ h
  | .app f args, c, hc, fk, hfk => by
      rw [build_app, List.mem_append] at hc
      have hc : c ∈ encodeBuildArgsWith { subsumption := sub } args ∨
          c = .expr (nodeRow f args) ∨ c = .expr (ufRow (.app f args) (.app f args)) := by
        cases sub <;> simp_all <;> tauto
      rcases hc with hc | rfl | rfl
      · exact (buildArgs_ctors args c hc fk hfk).imp_left fun h => by
          rw [Expr.ctors]; exact List.mem_cons_of_mem _ h
      · simp only [Action.ctors, nodeRow, nodeAtom, Expr.ctors, ctorsList_append,
          Expr.ctorsList, List.append_nil, List.mem_cons, List.mem_append] at hfk
        rcases hfk with rfl | hfk | rfl | hfk
        · exact Or.inr (dataName_nodeName f)
        · exact Or.inl (List.mem_cons_of_mem _ hfk)
        · exact Or.inl List.mem_cons_self
        · exact Or.inl (List.mem_cons_of_mem _ hfk)
      · rw [Action.ctors, mem_ufRow_ctors] at hfk
        rcases hfk with rfl | hfk | hfk
        · exact Or.inr dataName_ufName
        · exact Or.inl hfk
        · exact Or.inl hfk

theorem buildArgs_ctors : ∀ (es : List Expr), ∀ a ∈ encodeBuildArgsWith { subsumption := sub } es, ∀ fk ∈ a.ctors,
    fk ∈ Expr.ctorsList es ∨ DataName fk.1
  | [], a, ha, _, _ => by rw [buildArgs_nil] at ha; simp at ha
  | e :: es, a, ha, fk, hfk => by
      rw [buildArgs_cons, List.mem_append] at ha
      rcases ha with ha | ha
      · exact (build_ctors e a ha fk hfk).imp_left fun h => by
          rw [Expr.ctorsList]; exact List.mem_append_left _ h
      · exact (buildArgs_ctors es a ha fk hfk).imp_left fun h => by
          rw [Expr.ctorsList]; exact List.mem_append_right _ h

end

theorem action_ctors (a : Action) : ∀ b ∈ encodeActionWith { subsumption := sub } a, ∀ fk ∈ b.ctors,
    fk ∈ a.ctors ∨ DataName fk.1 := by
  cases a with
  | expr e => exact build_ctors e
  | union a b =>
    intro c hc fk hfk
    simp only [encodeActionWith, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with (hc | hc) | rfl | rfl
    · exact (build_ctors a c hc fk hfk).imp_left (List.mem_append_left _)
    · exact (build_ctors b c hc fk hfk).imp_left (List.mem_append_right _)
    · rw [Action.ctors, mem_ufRow_ctors] at hfk
      rcases hfk with rfl | hfk | hfk
      · exact Or.inr dataName_ufName
      · exact Or.inl (List.mem_append_left _ hfk)
      · exact Or.inl hfk
    · rw [Action.ctors, mem_ufRow_ctors] at hfk
      rcases hfk with rfl | hfk | hfk
      · exact Or.inr dataName_ufName
      · exact Or.inl (List.mem_append_right _ hfk)
      · exact Or.inl hfk
  | subsume f es =>
    intro c hc fk hfk
    have hc : c ∈ encodeBuildWith { subsumption := sub } (.app f es) ∨
        c = .subsume f es ∨ c = .expr (subRow f es) := by
      cases sub <;> simp_all [encodeActionWith] <;> tauto
    rcases hc with hc | rfl | rfl
    · exact build_ctors (.app f es) c hc fk hfk
    · exact Or.inl hfk
    · simp only [Action.ctors, subRow, Expr.ctors, List.mem_cons] at hfk
      rcases hfk with rfl | hfk
      · exact Or.inr (dataName_subName f)
      · exact Or.inl (List.mem_cons_of_mem _ hfk)

theorem rule_ctors (r : Rule) :
    ∀ fk ∈ (encodeRuleWith { subsumption := sub } r).ctors, fk ∈ r.ctors ∨ DataName fk.1 := by
  intro fk hfk
  rw [Rule.ctors, List.mem_append] at hfk
  rcases hfk with hfk | hfk
  · obtain ⟨p', hp', hfk⟩ := List.mem_flatMap.mp hfk
    exact (query_ctors r.query 0 p' hp' fk hfk).imp_left (List.mem_append_left _)
  · obtain ⟨b, hb, hfk⟩ := List.mem_flatMap.mp hfk
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    exact (action_ctors a b hb fk hfk).imp_left fun h =>
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, h⟩)

theorem ctors_ufRow_vars (v w : Var) : (ufRow (.var v) (.var w)).ctors = [(ufName, 2)] := rfl

/-- Child-parent atoms mention only the union-find constructor. -/
theorem edgeAtoms_ctors {n : Nat} {p : Pattern} (hp : p ∈ edgeAtoms n) :
    ∀ fk ∈ p.ctors, fk = (ufName, 2) := by
  obtain ⟨abr, habr, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨hab, hr⟩ := List.of_mem_zip habr
  obtain ⟨ha, hb⟩ := List.of_mem_zip hab
  rw [congruenceVars_eq_map] at ha hb hr
  obtain ⟨wa, _, hwa⟩ := List.mem_map.mp ha
  obtain ⟨wb, _, hwb⟩ := List.mem_map.mp hb
  obtain ⟨wr, _, hwr⟩ := List.mem_map.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp [Pattern.ctors, ← hwa, ← hwr, ctors_ufRow_vars]
  · simp [Pattern.ctors, ← hwb, ← hwr, ctors_ufRow_vars]

/-- Maintenance mentions source constructors and names outside the log namespace. -/
theorem maintenance_ctors {P : Program} {r : Rule} (hr : r ∈ maintenance sub P) :
    ∀ fk ∈ r.ctors, fk ∈ P.ctors ∨ DataName fk.1 := by
  rcases mem_maintenance.mp hr with rfl | rfl | ⟨fk', hfk', _, rfl⟩ | ⟨fk', hfk', _, rfl⟩
  · intro fk hfk
    have : fk = (ufName, 2) := by revert fk; decide
    subst fk
    exact Or.inr dataName_ufName
  · intro fk hfk
    have : fk = (ufName, 2) := by revert fk; decide
    subst fk
    exact Or.inr dataName_ufName
  · cases sub with
    | false =>
        intro fk hfk
        rw [Rule.ctors, List.mem_append] at hfk
        rcases hfk with hfk | hfk
        · obtain ⟨p, hp, hfk⟩ := List.mem_flatMap.mp hfk
          rw [congruence_query_plain] at hp
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            List.mem_flatMap] at hp
          rcases hp with ((rfl | rfl) | ⟨abr, habr, hp⟩) | rfl | rfl | rfl | rfl
          · rw [Pattern.ctors, Expr.ctors, ctorsList_congruenceVars, congruenceVars_length,
              List.mem_singleton] at hfk
            exact Or.inl (hfk ▸ hfk')
          · rw [Pattern.ctors, Expr.ctors, ctorsList_congruenceVars, congruenceVars_length,
              List.mem_singleton] at hfk
            exact Or.inl (hfk ▸ hfk')
          · obtain ⟨hab, hr'⟩ := List.of_mem_zip habr
            obtain ⟨ha, hb⟩ := List.of_mem_zip hab
            rw [congruenceVars_eq_map] at ha hb hr'
            obtain ⟨wa, _, hwa⟩ := List.mem_map.mp ha
            obtain ⟨wb, _, hwb⟩ := List.mem_map.mp hb
            obtain ⟨wr, _, hwr⟩ := List.mem_map.mp hr'
            rcases hp with rfl | rfl
            · rw [Pattern.ctors, ← hwa, ← hwr, ctors_ufRow_vars, List.mem_singleton] at hfk
              exact Or.inr (by subst fk; exact dataName_ufName)
            · rw [Pattern.ctors, ← hwb, ← hwr, ctors_ufRow_vars, List.mem_singleton] at hfk
              exact Or.inr (by subst fk; exact dataName_ufName)
          · rw [Pattern.ctors, mem_ufRow_ctors] at hfk
            rcases hfk with rfl | hfk | hfk
            · exact Or.inr dataName_ufName
            · rw [Expr.ctors, ctorsList_congruenceVars, congruenceVars_length,
                List.mem_singleton] at hfk
              exact Or.inl (hfk ▸ hfk')
            · simp [Expr.ctors] at hfk
          · rw [Pattern.ctors, mem_ufRow_ctors] at hfk
            rcases hfk with rfl | hfk | hfk
            · exact Or.inr dataName_ufName
            · rw [Expr.ctors, ctorsList_congruenceVars, congruenceVars_length,
                List.mem_singleton] at hfk
              exact Or.inl (hfk ▸ hfk')
            · simp [Expr.ctors] at hfk
          · simp [Pattern.ctors, Expr.ctors] at hfk
          · simp [Pattern.ctors, Expr.ctors] at hfk
        · rw [congruence_actions] at hfk
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Action.ctors,
            ctors_ufRow_vars, List.mem_singleton] at hfk
          exact Or.inr (by subst fk; exact dataName_ufName)
    | true =>
        intro fk hfk
        simp only [Rule.ctors, congruence_query_node, congruence_actions, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, Pattern.ctors,
          Action.ctors, nodeAtom, Expr.ctors, ctorsList_append, ctorsList_congruenceVars,
          Expr.ctorsList, List.nil_append, ufRow, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hfk
        simp only [or_assoc] at hfk
        rcases hfk with rfl | rfl | hfk | rfl | rfl | rfl
        · exact Or.inr (dataName_nodeName _)
        · exact Or.inr (dataName_nodeName _)
        · obtain ⟨p, hp, hfk⟩ := List.mem_flatMap.mp hfk
          obtain rfl := edgeAtoms_ctors hp fk hfk
          exact Or.inr dataName_ufName
        · exact Or.inr dataName_ufName
        · exact Or.inr dataName_ufName
        · exact Or.inr dataName_ufName
  · intro fk hfk
    simp only [Rule.ctors, subsume_query, subsume_actions, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, Pattern.ctors,
      Action.ctors, subRow, Expr.ctors, ctorsList_congruenceVars, congruenceVars_length,
      List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hfk
    simp only [or_assoc] at hfk
    rcases hfk with rfl | rfl | hfk | rfl
    · exact Or.inr (dataName_subName _)
    · exact Or.inl hfk'
    · obtain ⟨p, hp, hfk⟩ := List.mem_flatMap.mp hfk
      obtain rfl := edgeAtoms_ctors hp fk hfk
      exact Or.inr dataName_ufName
    · exact Or.inl hfk'

/-! ### Variables of the compiled program -/

theorem mem_ufRow_vars {a b : Expr} {v : Var} :
    v ∈ (ufRow a b).vars ↔ v ∈ a.vars ∨ v ∈ b.vars := by
  simp [ufRow, Expr.varsList]

/-- A variable of a compiled source rule is one of the rule's or a fresh variable. -/
theorem rule_vars (r : Rule) (hsc : ∀ p ∈ r.query, p.Scoped) :
    ∀ v ∈ (encodeRuleWith { subsumption := sub } r).vars, v ∈ r.vars ∨ ∃ k, v = freshVar k := by
  intro v hv
  rw [Rule.vars, List.mem_union_iff] at hv
  rcases hv with hv | hv
  · rcases (query_vars_iff hsc 0).mp hv with hv | ⟨k, _, _, rfl⟩
    · exact Or.inl (List.mem_union_iff.mpr (Or.inl hv))
    · exact Or.inr ⟨k, rfl⟩
  · obtain ⟨b, hb, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    exact Or.inl (List.mem_union_iff.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨a, ha, action_vars a b hb v hv⟩)))

/-- The variables of a maintenance rule are generated, outside the log namespace. -/
theorem maintenance_vars {P : Program} {r : Rule} (hr : r ∈ maintenance sub P) :
    ∀ v ∈ r.vars, DataName v := by
  rcases mem_maintenance.mp hr with rfl | rfl | ⟨fk, _, _, rfl⟩ | ⟨fk, _, _, rfl⟩
  · decide
  · decide
  · intro v hv
    rw [Rule.vars, List.mem_union_iff] at hv
    rcases hv with hv | hv
    · rcases congruence_vars_subset hv with hv | hv | hv | rfl | rfl | rfl | rfl
      · obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
        exact dataName_congName (c := 'a') (by decide) (by decide) i
      · obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
        exact dataName_congName (c := 'b') (by decide) (by decide) i
      · obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
        exact dataName_congName (c := 'r') (by decide) (by decide) i
      · decide
      · decide
      · decide
      · decide
    · rw [congruence_actions] at hv
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Action.vars,
        mem_ufRow_vars, Expr.vars_var, List.mem_singleton] at hv
      rcases hv with rfl | rfl <;> decide

  · intro v hv
    rw [Rule.vars, List.mem_union_iff] at hv
    have hg : ∀ stem, stem = "a" ∨ stem = "b" ∨ stem = "r" →
        v ∈ congNames stem fk.2 → DataName v := by
      intro stem hs hv
      obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
      rcases hs with rfl | rfl | rfl
      · exact dataName_congName (c := 'a') (by decide) (by decide) i
      · exact dataName_congName (c := 'b') (by decide) (by decide) i
      · exact dataName_congName (c := 'r') (by decide) (by decide) i
    rcases hv with hv | hv
    · rcases mem_subsume_vars.mp hv with hv | hv | hv
      · exact hg "a" (by simp) hv
      · exact hg "b" (by simp) hv
      · exact hg "r" (by simp) hv
    · rw [subsume_actions] at hv
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Action.vars, Expr.vars_app,
        mem_varsList_congruenceVars] at hv
      exact hg "b" (by simp) hv

/-! ### Keyed variables of the compiled queries -/

mutual

/-- Every fresh variable of the consumed interval is an argument of an emitted atom. -/
theorem flat_fresh_argVar : ∀ (e : Expr) (n : Nat) {v : Var},
    FreshIn n (encodeQueryExprWith {} e n).2.2 v →
      ∃ p ∈ (encodeQueryExprWith {} e n).2.1, Pattern.ArgVar v p
  | .lit _, _, _, ⟨_, h₁, h₂, _⟩ => by rw [flat_lit] at h₂; simp at h₂; omega
  | .var _, _, _, ⟨_, h₁, h₂, _⟩ => by rw [flat_var] at h₂; simp at h₂; omega
  | .min _ _, _, _, ⟨_, h₁, h₂, _⟩ => by rw [flat_min] at h₂; simp at h₂; omega
  | .app f args, n, v, ⟨k, hk₁, hk₂, hvk⟩ => by
      subst hvk
      rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hle := flatArgs_next_le args n
      rw [hr] at hle
      simp only at hle
      rw [flat_app hr] at hk₂ ⊢
      simp only at hk₂ ⊢
      by_cases hlt : k < next
      · obtain ⟨p, hp, hvp⟩ := flatArgs_fresh_argVar args n ⟨k, hk₁, by rw [hr]; exact hlt, rfl⟩
        rw [hr] at hp
        exact ⟨p, List.mem_append_left _ (List.mem_append_left _ hp), hvp⟩
      · by_cases hk : k < next + args.length
        · refine ⟨.expr (.app f (freshArgs next args.length)), by simp, ?_⟩
          simp only [Pattern.ArgVar, Expr.ArgVar]
          exact Or.inl (mem_freshArgs.mpr ⟨k - next, by omega, by rw [Nat.add_sub_cancel' (by omega)]⟩)
        · refine ⟨.expr (ufRow (.app f (freshArgs next args.length))
            (.var (freshVar (next + args.length)))), by simp, ?_⟩
          obtain rfl : k = next + args.length := by omega
          simp [Pattern.ArgVar, Expr.ArgVar, ufRow]

theorem flatArgs_fresh_argVar : ∀ (es : List Expr) (n : Nat) {v : Var},
    FreshIn n (encodeQueryArgsWith {} es n).2.2 v →
      ∃ p ∈ (encodeQueryArgsWith {} es n).2.1, Pattern.ArgVar v p
  | [], _, _, ⟨_, h₁, h₂, _⟩ => by rw [flatArgs_nil] at h₂; simp at h₂; omega
  | e :: es, n, v, ⟨k, hk₁, hk₂, hvk⟩ => by
      subst hvk
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂] at hk₂ ⊢
      simp only at hk₂ ⊢
      by_cases hlt : k < next
      · obtain ⟨p, hp, hvp⟩ := flat_fresh_argVar e n ⟨k, hk₁, by rw [h₁]; exact hlt, rfl⟩
        rw [h₁] at hp
        exact ⟨p, List.mem_append_left _ hp, hvp⟩
      · obtain ⟨p, hp, hvp⟩ :=
          flatArgs_fresh_argVar es next ⟨k, by omega, by rw [h₂]; exact hk₂, rfl⟩
        rw [h₂] at hp
        exact ⟨p, List.mem_append_right _ hp, hvp⟩

end

theorem pattern_fresh_argVar (p : Pattern) (n : Nat) {v : Var}
    (h : FreshIn n (encodePatternWith {} p n).2 v) :
    ∃ q ∈ (encodePatternWith {} p n).1, Pattern.ArgVar v q := by
  cases p with
  | expr e => rw [pattern_expr] at h ⊢; exact flat_fresh_argVar e n h
  | eq l r | ne l r =>
    obtain ⟨k, hk₁, hk₂, rfl⟩ := h
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    have hn := flat_next_le l n
    rw [h₁] at hn
    simp only at hn
    first
    | rw [pattern_eq h₁ h₂] at hk₂ ⊢
    | rw [pattern_ne h₁ h₂] at hk₂ ⊢
    simp only at hk₂ ⊢
    by_cases hlt : k < next
    · obtain ⟨q, hq, hvq⟩ := flat_fresh_argVar l n ⟨k, hk₁, by rw [h₁]; exact hlt, rfl⟩
      rw [h₁] at hq
      exact ⟨q, List.mem_append_left _ (List.mem_append_left _ hq), hvq⟩
    · obtain ⟨q, hq, hvq⟩ := flat_fresh_argVar r next ⟨k, by omega, by rw [h₂]; exact hk₂, rfl⟩
      rw [h₂] at hq
      exact ⟨q, List.mem_append_left _ (List.mem_append_right _ hq), hvq⟩

theorem query_fresh_argVar (q : Query) (n : Nat) {v : Var}
    (h : FreshIn n (encodeQueryWith {} q n).2 v) :
    ∃ p ∈ (encodeQueryWith {} q n).1, Pattern.ArgVar v p := by
  induction q generalizing n with
  | nil =>
    obtain ⟨k, hk₁, hk₂, _⟩ := h
    rw [query_nil] at hk₂
    simp at hk₂
    omega
  | cons p ps ih =>
    obtain ⟨k, hk₁, hk₂, rfl⟩ := h
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    rw [query_cons h₁ h₂] at hk₂ ⊢
    simp only at hk₂ ⊢
    by_cases hlt : k < next
    · obtain ⟨q, hq, hvq⟩ := pattern_fresh_argVar p n ⟨k, hk₁, by rw [h₁]; exact hlt, rfl⟩
      rw [h₁] at hq
      exact ⟨q, List.mem_append_left _ hq, hvq⟩
    · obtain ⟨q, hq, hvq⟩ := ih next ⟨k, by omega, by rw [h₂]; exact hk₂, rfl⟩
      rw [h₂] at hq
      exact ⟨q, List.mem_append_right _ hq, hvq⟩

/-- Every variable of a compiled query is an argument of an application pattern. -/
theorem keyed_encodeQuery {q : Query} (hsc : ∀ p ∈ q, p.Scoped) (ho : ∀ p ∈ q, p.MinOverVars)
    (hk : Query.VarsKeyed q) (n : Nat) : Query.VarsKeyed (encodeQueryWith {} q n).1 := by
  intro v hv
  rcases (query_vars_iff hsc n).mp hv with hv | hv
  · obtain ⟨p, hp, hvp⟩ := hk v hv
    obtain ⟨a, ha⟩ := query_argVar_atom n ho hp hvp
    refine ⟨_, ha, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]
  · exact query_fresh_argVar q n hv

/-- Every variable of the congruence rule is an argument of an application pattern. -/
theorem congruence_keyed_node (f : FnName) (n : Nat) : Query.VarsKeyed (congruenceRule true f n).query := by
  intro v hv
  rcases mem_congruence_vars_node.mp hv with hv | hv | hv | rfl | rfl | rfl | rfl
  · refine ⟨.expr (nodeAtom f (congruenceVars "a" n) (.var "@k")),
      by rw [congruence_query_node]; simp, ?_⟩
    simp only [Pattern.ArgVar, nodeAtom, Expr.ArgVar]
    exact Or.inl (List.mem_append_left _ (by rw [congruenceVars_eq_map]; exact List.mem_map_of_mem hv))
  · refine ⟨.expr (nodeAtom f (congruenceVars "b" n) (.var "@l")),
      by rw [congruence_query_node]; simp, ?_⟩
    simp only [Pattern.ArgVar, nodeAtom, Expr.ArgVar]
    exact Or.inl (List.mem_append_left _ (by rw [congruenceVars_eq_map]; exact List.mem_map_of_mem hv))
  · obtain ⟨i, hi, rfl⟩ := mem_congNames.mp hv
    refine ⟨_, (congruence_edge_atoms_mem (f := f) hi).1, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]
  · refine ⟨.expr (ufRow (.var "@k") (.var "@y")), by rw [congruence_query_node]; simp, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]
  · refine ⟨.expr (ufRow (.var "@l") (.var "@z")), by rw [congruence_query_node]; simp, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]
  · refine ⟨.expr (ufRow (.var "@k") (.var "@y")), by rw [congruence_query_node]; simp, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]
  · refine ⟨.expr (ufRow (.var "@l") (.var "@z")), by rw [congruence_query_node]; simp, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]

theorem congruence_keyed_plain (f : FnName) (n : Nat) : Query.VarsKeyed (congruenceRule false f n).query := by
  intro v hv
  rcases mem_congruence_vars_plain.mp hv with hv | hv | hv | rfl | rfl
  · refine ⟨.expr (.app f (congruenceVars "a" n)), by rw [congruence_query_plain]; simp, ?_⟩
    simp only [Pattern.ArgVar, Expr.ArgVar]
    exact Or.inl (by rw [congruenceVars_eq_map]; exact List.mem_map_of_mem hv)
  · refine ⟨.expr (.app f (congruenceVars "b" n)), by rw [congruence_query_plain]; simp, ?_⟩
    simp only [Pattern.ArgVar, Expr.ArgVar]
    exact Or.inl (by rw [congruenceVars_eq_map]; exact List.mem_map_of_mem hv)
  · obtain ⟨i, hi, rfl⟩ := mem_congNames.mp hv
    refine ⟨_, (congruence_edge_atoms_mem (f := f) hi).1, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]
  · refine ⟨.expr (ufRow (.app f (congruenceVars "a" n)) (.var "@y")),
      by rw [congruence_query_plain]; simp, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]
  · refine ⟨.expr (ufRow (.app f (congruenceVars "b" n)) (.var "@z")),
      by rw [congruence_query_plain]; simp, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]

theorem congruence_keyed (f : FnName) (n : Nat) :
    Query.VarsKeyed (congruenceRule sub f n).query := by
  cases sub
  · exact congruence_keyed_plain f n
  · exact congruence_keyed_node f n

/-- Every subsumption-query variable is an argument of an atom. -/
theorem subsume_keyed (f : FnName) (n : Nat) : Query.VarsKeyed (subsumeRule f n).query := by
  intro v hv
  rcases mem_subsume_vars.mp hv with hv | hv | hv
  · refine ⟨.expr (subRow f (congruenceVars "a" n)), by rw [subsume_query]; simp, ?_⟩
    simp only [Pattern.ArgVar, subRow, Expr.ArgVar]
    exact Or.inl (by rw [congruenceVars_eq_map]; exact List.mem_map_of_mem hv)
  · refine ⟨.expr (.app f (congruenceVars "b" n)), by rw [subsume_query]; simp, ?_⟩
    simp only [Pattern.ArgVar, Expr.ArgVar]
    exact Or.inl (by rw [congruenceVars_eq_map]; exact List.mem_map_of_mem hv)
  · obtain ⟨i, hi, rfl⟩ := mem_congNames.mp hv
    refine ⟨_, List.mem_append_right _ (edge_atoms_mem hi).1, ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar, ufRow]

/-! ### The compiled program -/

/-- A rule of the compiled program compiles a source rule or maintains the union-find. -/
theorem mem_rules_encS {P : Program} : ∀ {S : Schedule} {r' : Rule}, r' ∈ (encS P S).rules →
    (∃ r ∈ S.rules, r' = encodeRuleWith { subsumption := !P.schedule.subsumeFreeB } r) ∨ r' ∈ maintenance (!P.schedule.subsumeFreeB) P
  | .run rs, r', h => by
      simp only [encS, Schedule.rules, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact Or.inl ⟨r, hr, rfl⟩
      · exact Or.inr h
  | .saturate S, r', h => mem_rules_encS (S := S) h
  | .seq S₁ S₂, r', h => by
      simp only [encS, Schedule.rules, List.mem_append] at h
      rcases h with h | h
      · rcases mem_rules_encS h with ⟨r, hr, rfl⟩ | h
        · exact Or.inl ⟨r, List.mem_append_left _ hr, rfl⟩
        · exact Or.inr h
      · rcases mem_rules_encS h with ⟨r, hr, rfl⟩ | h
        · exact Or.inl ⟨r, List.mem_append_right _ hr, rfl⟩
        · exact Or.inr h

theorem compiled_rules {P : Program} {r' : Rule} (hr : r' ∈ (Congruence.encode P).rules) :
    (∃ r ∈ P.rules, r' = encodeRuleWith { subsumption := !P.schedule.subsumeFreeB } r) ∨ r' ∈ maintenance (!P.schedule.subsumeFreeB) P := by
  rw [Program.rules, encode_schedule] at hr
  exact mem_rules_encS hr

variable {P : Program}

theorem compiled_ctors : ∀ fk ∈ (Congruence.encode P).ctors, fk ∈ P.ctors ∨ DataName fk.1 := by
  intro fk hfk
  rw [Program.ctors, List.mem_dedup, List.mem_append] at hfk
  rcases hfk with hfk | hfk
  · rw [Schedule.ctors] at hfk
    obtain ⟨r', hr', hfk⟩ := List.mem_flatMap.mp hfk
    rcases compiled_rules hr' with ⟨r, hr, rfl⟩ | hr'
    · exact (rule_ctors r fk hfk).imp_left fun h =>
        mem_program_ctors (S := P.schedule) (fun _ h => h) (List.mem_flatMap.mpr ⟨r, hr, h⟩)
    · exact maintenance_ctors hr' fk hfk
  · rw [encode_check] at hfk
    obtain ⟨p', hp', hfk⟩ := List.mem_flatMap.mp hfk
    refine (query_ctors P.check 0 p' hp' fk hfk).imp_left fun h => ?_
    rw [Program.ctors, List.mem_dedup]
    exact List.mem_append_right _ h

theorem source_var_dataName (hP : P.Fragment) {v : Var} (hv : v ∈ P.vars) : DataName v :=
  dataName_of_not_at (hP.noAt v (List.mem_append_right _ hv))

theorem compiled_vars (hP : P.Fragment) : ∀ v ∈ (Congruence.encode P).vars, DataName v := by
  intro v hv
  rw [Program.vars, List.mem_dedup, List.mem_append] at hv
  rcases hv with hv | hv
  · rw [Schedule.vars] at hv
    obtain ⟨r', hr', hv⟩ := List.mem_flatMap.mp hv
    rcases compiled_rules hr' with ⟨r, hr, rfl⟩ | hr'
    · have hsc : ∀ p ∈ r.query, p.Scoped := fun p hp => ((hP.queryEncodable.1 r hr).1 p hp).2
      rcases rule_vars r hsc v hv with hv | ⟨k, rfl⟩
      · apply source_var_dataName hP
        rw [Program.vars, List.mem_dedup]
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, hv⟩)
      · exact dataName_freshVar k
    · exact maintenance_vars hr' v hv
  · rw [encode_check] at hv
    rcases (query_vars_iff (fun p hp => (hP.queryEncodable.2.1 p hp).2) 0).mp hv with
      hv | ⟨k, _, _, rfl⟩
    · apply source_var_dataName hP
      rw [Program.vars, List.mem_dedup]
      exact List.mem_append_right _ hv
    · exact dataName_freshVar k

theorem compiled_keyed (hP : P.Fragment) :
    ∀ r' ∈ (Congruence.encode P).rules, Query.VarsKeyed r'.query := by
  intro r' hr'
  rcases compiled_rules hr' with ⟨r, hr, rfl⟩ | hr'
  · exact keyed_encodeQuery (fun p hp => ((hP.queryEncodable.1 r hr).1 p hp).2)
      (rule_minOverVars hP hr).1 (hP.queryEncodable.1 r hr).2 0
  · rcases mem_maintenance.mp hr' with rfl | rfl | ⟨fk, _, _, rfl⟩ | ⟨fk, _, _, rfl⟩
    · decide
    · decide
    · exact congruence_keyed fk.1 fk.2
    · exact subsume_keyed fk.1 fk.2

theorem compiled_check_keyed (hP : P.Fragment) : Query.VarsKeyed (Congruence.encode P).check := by
  rw [encode_check]
  exact keyed_encodeQuery (fun p hp => (hP.queryEncodable.2.1 p hp).2) (check_minOverVars hP)
    hP.queryEncodable.2.2 0

/-- The congruence compiler's output satisfies the instrumentation premise. -/
theorem encode_instrumentable (P : Program) (_hW : P.WellFormed) (hP : P.Fragment) :
    Instrumentable (Congruence.encode P) where
  ok := by
    rw [programOk, Bool.and_eq_true]
    refine ⟨unionFree_of_unionFree (encode_unionFree P), ?_⟩
    rw [List.all_eq_true]
    intro f hf
    have hd : DataName f := by
      rw [Program.names, List.mem_append] at hf
      rcases hf with hf | hf
      · obtain ⟨fk, hfk, rfl⟩ := List.mem_map.mp hf
        rcases compiled_ctors fk hfk with h | h
        · exact dataName_of_not_at (hP.noAt _ (List.mem_append_left _ (List.mem_map_of_mem h)))
        · exact h
      · exact compiled_vars hP f hf
    simpa using hd
  keyedRules := compiled_keyed hP
  keyedCheck := compiled_check_keyed hP

end Egglog.Provenance
