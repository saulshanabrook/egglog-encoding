import EgglogSemantics.Proofs.Congruence.Vocab
import EgglogSemantics.Proofs.Congruence.Round
import EgglogSemantics.Proofs.Schedule
import EgglogSemantics.Proofs.SourceSubsume

/-! The source side of the simulation: the invariants of a state reached by rounds of the
program, the rule conditions the fragment supplies, and that source heads never get
stuck. -/

namespace Egglog.Congruence

/-- The invariants of a source state reached by rounds of `P`. -/
structure SrcInv (P : Program) (x : Database) : Prop where
  wf : x.WF
  marksExist : x.MarksExist
  finite : x.eqs.Finite
  ctors : x.CtorsIn P
  vocab : ∀ t ∈ x.terms, Term.VocabIn P t
  litFree : P.schedule.litFreeB = true → x.LitFree

variable {P : Program}

theorem SrcInv.empty (P : Program) : SrcInv P Database.empty where
  wf := Database.WF.empty
  marksExist := by intro t ht; cases ht
  finite := Set.finite_empty
  ctors := Database.empty_ctorsIn
  vocab := by intro _ ht; simp at ht
  litFree := fun _ => Database.empty_litFree

theorem SrcInv.hasReps {x : Database} (h : SrcInv P x) : x.HasReps :=
  Database.hasReps_of_finite h.finite

theorem SrcInv.avoids (hP : P.Fragment) {x : Database} (h : SrcInv P x) :
    ∀ t ∈ x.terms, t.SourceShaped :=
  fun _ ht => sourceShaped_of_ctorsIn hP (h.ctors.term h.wf ht)

/-! ### Rounds of the program -/

/-- `y` is reached from `x` by rounds of the program's rules. -/
def Rounds (P : Program) : Database → Database → Prop :=
  Relation.ReflTransGen fun a b => ∃ R : List Rule, (∀ r ∈ R, r ∈ P.rules) ∧ b = RunRules R a

theorem Rounds.refl (x : Database) : Rounds P x x := Relation.ReflTransGen.refl

theorem Rounds.trans {x y z : Database} (h₁ : Rounds P x y) (h₂ : Rounds P y z) : Rounds P x z :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Rounds.single {x : Database} {R : List Rule} (hR : ∀ r ∈ R, r ∈ P.rules) :
    Rounds P x (RunRules R x) :=
  Relation.ReflTransGen.single ⟨R, hR, rfl⟩

theorem Rounds.eqs_subset {x y : Database} (h : Rounds P x y) : x.eqs ⊆ y.eqs := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hbc ih =>
    obtain ⟨R, _, rfl⟩ := hbc
    exact ih.trans (by rw [RunRules.eq_pair]; exact Set.subset_union_left)

theorem Rounds.terms_subset {x y : Database} (h : Rounds P x y) : x.terms ⊆ y.terms :=
  fun _ ht => Database.mem_terms_of_eqs h.eqs_subset ht

theorem Rounds.cong {x y : Database} (h : Rounds P x y) {a b : Term} (hc : Cong x a b) :
    Cong y a b := Cong.mono_eqs h.eqs_subset hc

theorem Reach.rounds {S : Schedule} (hS : S.rules ⊆ P.rules) {x y : Database}
    (h : Reach x S y) : Rounds P x y := by
  induction h with
  | @run _ rs => exact Rounds.single fun r hr => hS hr
  | seq _ _ ih₁ ih₂ =>
    exact (ih₁ fun r hr => hS (List.mem_append_left _ hr)).trans
      (ih₂ fun r hr => hS (List.mem_append_right _ hr))
  | fixpoint _ _ ih => exact ih hS
  | again _ _ _ ih₁ ih₂ => exact (ih₁ hS).trans (ih₂ hS)

/-! ### Preservation -/

theorem SrcInv.runRules (hP : P.Fragment) {x : Database} (h : SrcInv P x) {R : List Rule}
    (hR : ∀ r ∈ R, r ∈ P.rules) : SrcInv P (RunRules R x) where
  wf := RunRules.wf h.wf
  marksExist := RunRules.marksExist h.marksExist
  finite := RunRules.finite_eqs h.finite R
  ctors := (Database.CtorsInState.runRules h.wf ⟨h.ctors⟩
    (Schedule.CtorsIn.of_domain hP (c := .run R) hR)).terms
  vocab := RunRules.vocab h.wf hR h.vocab
  litFree := fun hl => (Database.NoLits.runRules h.wf ⟨h.litFree hl⟩
    (Schedule.NoLits.of_domain hP hl (S := .run R) hR)).terms

theorem SrcInv.rounds (hP : P.Fragment) {x y : Database} (h : SrcInv P x) (hr : Rounds P x y) :
    SrcInv P y := by
  induction hr with
  | refl => exact h
  | tail _ hbc ih =>
    obtain ⟨R, hR, rfl⟩ := hbc
    exact ih.runRules hP hR

theorem SrcInv.reach (hP : P.Fragment) {S : Schedule} (hS : S.rules ⊆ P.rules) {x y : Database}
    (h : SrcInv P x) (hr : Reach x S y) : SrcInv P y :=
  h.rounds hP (Reach.rounds hS hr)

/-! ### The rule conditions -/

theorem srcNames_of_ctors (hP : P.Fragment) {e : Expr} (hc : ∀ fk ∈ e.ctors, fk ∈ P.ctors) :
    SrcNames e := by
  intro g hg heq
  obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg
  exact noAt_of_mem_ctors hP (hc _ hk) heq

theorem notFresh_of_mem_vars (hP : P.Fragment) {v : Var} (hv : v ∈ P.vars) : NotFresh v :=
  notFresh_of_not_at (hP.noAt v (List.mem_append_right _ hv))

/-- The constructors of a side of a pattern are constructors of the pattern. -/
theorem Pattern.ctors_of_mem_exprs {p : Pattern} {e : Expr} (he : e ∈ p.exprs) :
    ∀ fk ∈ e.ctors, fk ∈ p.ctors := by
  cases p with
  | expr e' =>
    simp only [Pattern.exprs, List.mem_singleton] at he
    subst he
    exact fun _ hk => hk
  | eq a b | ne a b =>
    simp only [Pattern.exprs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact fun _ hk => List.mem_append_left _ hk
    · exact fun _ hk => List.mem_append_right _ hk

theorem pattern_names {q : Query} (hq : ∀ fk ∈ q.flatMap Pattern.ctors, fk ∈ P.ctors)
    (hP : P.Fragment) : ∀ p ∈ q, ∀ e ∈ p.exprs, SrcNames e := by
  intro p hp e he
  apply srcNames_of_ctors hP
  intro fk hk
  apply hq
  exact List.mem_flatMap.mpr ⟨p, hp, Pattern.ctors_of_mem_exprs he fk hk⟩

/-- Every minimum of a rule is over query variables. -/
theorem rule_minOverVars (hP : P.Fragment) {r : Rule} (hr : r ∈ P.rules) :
    (∀ p ∈ r.query, p.MinOverVars) ∧ Actions.MinOverVars r.actions := by
  rcases hP.ordering with hO | ⟨_, hM⟩
  · exact Rule.minOverVars_of_orderingFree (hO.1 r hr)
  · exact Rule.minOverVars_of_minOverVarsB
      (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hM).1 r hr)

/-- Every minimum of the final check is over query variables. -/
theorem check_minOverVars (hP : P.Fragment) : ∀ p ∈ P.check, p.MinOverVars := by
  rcases hP.ordering with hO | ⟨_, hM⟩
  · exact fun p hp => Pattern.minOverVars_of_orderingFree p (hO.2 p hp)
  · exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp hM).2

/-- Every rule of a fragment program satisfies the round correspondence's conditions. -/
theorem ruleOk_of_fragment (hP : P.Fragment) {r : Rule} (hr : r ∈ P.rules) : RuleOk (!P.schedule.subsumeFreeB) r := by
  have henc : r.query.Encodable := hP.queryEncodable.1 r hr
  obtain ⟨hoq, hoa⟩ := rule_minOverVars hP hr
  refine ⟨⟨hoq, fun p hp => (henc.1 p hp).2, pattern_names ?_ hP, fun v hv => ?_⟩, henc.2,
    hP.headsScoped r hr, hoa, ?_⟩
  · intro fk hk
    apply mem_program_ctors (S := P.schedule) (fun r hr => hr)
    exact List.mem_flatMap.mpr ⟨r, hr, List.mem_append_left _ hk⟩
  · apply notFresh_of_mem_vars hP
    unfold Program.vars
    rw [List.mem_dedup]
    apply List.mem_append_left
    unfold Schedule.vars
    exact List.mem_flatMap.mpr ⟨r, hr, List.mem_union_iff.mpr (Or.inl hv)⟩
  · intro a ha f es heq
    subst a
    constructor
    · apply noAt_of_mem_ctors hP (fk := (f, es.length))
      apply mem_program_ctors (S := P.schedule) (fun _ h => h)
      exact List.mem_flatMap.mpr ⟨r, hr, List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.subsume f es, ha, List.mem_cons_self⟩)⟩
    · cases hs : P.schedule.subsumeFreeB with
      | false => rfl
      | true =>
        have hr' := List.all_eq_true.mp hs r hr
        have ha' := List.all_eq_true.mp hr' (.subsume f es) ha
        simp [Action.monotoneB] at ha'

/-- The final check satisfies the query conditions. -/
theorem queryOk_check (hP : P.Fragment) : QueryOk P.check where
  minOverVars := check_minOverVars hP
  shape := fun p hp => (hP.queryEncodable.2.1 p hp).2
  names := pattern_names (by
    intro fk hk
    unfold Program.ctors
    rw [List.mem_dedup]
    exact List.mem_append_right _ hk) hP
  vars := by
    intro v hv
    apply notFresh_of_mem_vars hP
    unfold Program.vars
    rw [List.mem_dedup]
    exact List.mem_append_right _ hv

theorem check_keyed (hP : P.Fragment) : Query.VarsKeyed P.check := hP.queryEncodable.2.2

/-! ### Source heads never get stuck -/

theorem Expr.isApp_of_isAppB {e : Expr} (h : e.isAppB = true) : e.IsApp := by
  cases e <;> simp [Expr.isAppB, Expr.IsApp] at h ⊢

theorem source_writes_some (hP : P.Fragment) {x : Database} (hx : SrcInv P x) {r : Rule}
    (hr : r ∈ P.rules) {σ : Env} (hσ : QueryMatches x r.query σ) :
    ∃ W, Action.writes σ r.actions = some W := by
  have hm : Scope.Models (Query.vars r.query) σ := fun v => hσ.1.1.mem_iff.symm
  have hsc : Actions.Scoped r.actions (Query.vars r.query) := hP.headsScoped r hr
  have hu : ∀ a ∈ r.actions, a.UnionSafe σ := by
    intro a ha e₁ e₂ hae t₁ t₂ ht₁ ht₂
    rcases hP.noLitUnion with happ | hlit
    · have h₁ : a.unionAppsB = true :=
        List.all_eq_true.mp (List.all_eq_true.mp happ r hr) _ ha
      subst hae
      simp only [Action.unionAppsB, Bool.and_eq_true] at h₁
      rintro (h | h)
      · exact Expr.not_isLit_of_isApp (Expr.isApp_of_isAppB h₁.1) ht₁ h
      · exact Expr.not_isLit_of_isApp (Expr.isApp_of_isAppB h₁.2) ht₂ h
    · have hfree : x.LitFree := hx.litFree hlit
      have hvals : ∀ v t, Env.lookup v σ = some t → Term.LitFree t := fun v t hv =>
        hfree.term hx.wf (hσ.1.mem_terms (v, t) (Env.mem_of_lookup hv))
      have h₁ : a.litFreeB = true :=
        List.all_eq_true.mp (List.all_eq_true.mp hlit r hr) _ ha
      subst hae
      simp only [Action.litFreeB, Bool.and_eq_true] at h₁
      rintro (h | h)
      · exact Expr.eval_litFree hvals e₁ h₁.1 ht₁ t₁ (Term.self_mem_subterms _) h
      · exact Expr.eval_litFree hvals e₂ h₁.2 ht₂ t₂ (Term.self_mem_subterms _) h
  obtain ⟨db', hdb'⟩ := evalActions_isSome_of_scoped (db := x) hm hsc hu
  rw [evalActions_eq_writes_marks, Option.bind_eq_some_iff] at hdb'
  obtain ⟨W, hW, _⟩ := hdb'
  exact ⟨W, hW⟩

/-! ### Rounds respect meaning -/

/-- Rounds of ordering-free rules respect meaning. A rule that takes a minimum does not: the
minimum compares representatives, which two states of one meaning need not share. -/
theorem round_sameMeaning (hP : P.Fragment) (hO : P.schedule.OrderingFree) {x y : Database}
    (hx : SrcInv P x) (hy : SrcInv P y) (hm : x.SameMeaning y) {R : List Rule}
    (hR : ∀ r ∈ R, r ∈ P.rules) : (RunRules R x).SameMeaning (RunRules R y) :=
  SourceMeaning.round_sameMeaning_subsume hx.wf hy.wf hm hx.marksExist hy.marksExist
    hx.hasReps hy.hasReps (fun r hr => hO r (hR r hr))
    (fun r hr σ hσ => source_writes_some hP hx (hR r hr) hσ)
    (fun r hr σ hσ => source_writes_some hP hy (hR r hr) hσ)

/-- A finite source run from a state of the same meaning reaches a state of the same
meaning. -/
theorem reach_transport (hP : P.Fragment) (hO : P.schedule.OrderingFree) {S : Schedule}
    (hS : S.rules ⊆ P.rules) {x y e : Database} (hx : SrcInv P x) (hy : SrcInv P y)
    (hm : x.SameMeaning y) (hr : Reach x S e) : ∃ e', Reach y S e' ∧ e.SameMeaning e' :=
  Reach.transport (I := SrcInv P) (good := fun r => r ∈ P.rules)
    (fun _ _ hg hd => hd.runRules hP hg)
    (fun _ _ _ hg hd he hm => round_sameMeaning hP hO hd he hm hg)
    hr (fun _ hr => hS hr) hx hy hm

/-- Stored marks only grow along rounds. -/
theorem Rounds.marks_subset {x y : Database} (h : Rounds P x y) : x.subsumed ⊆ y.subsumed := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hbc ih =>
    obtain ⟨R, _, rfl⟩ := hbc
    exact ih.trans (SourceMeaning.round_contains _ _).subsumed

/-- A state between two equivalent states has the same congruence and live rows. -/
theorem sameMeaning_of_between {x z y : Database} (hxz : Rounds P x z) (hzy : Rounds P z y)
    (hxy : x.SameMeaning y) : x.SameMeaning z := by
  have hc : ∀ a b, Cong x a b ↔ Cong z a b := fun a b =>
    ⟨hxz.cong, fun h => (hxy.congr a b).mpr (hzy.cong h)⟩
  refine ⟨hc, fun t => ?_⟩
  constructor
  · intro ht
    refine ⟨(hc _ _).mp ht.1, ?_⟩
    rintro ⟨u, hu, hs⟩
    exact ((hxy.live t).mp ht).2 ⟨u, hzy.marks_subset hu, hs.mono (fun _ _ h => hzy.cong h)⟩
  · intro ht
    refine ⟨(hc _ _).mpr ht.1, ?_⟩
    rintro ⟨u, hu, hs⟩
    exact ht.2 ⟨u, hxz.marks_subset hu, hs.mono (fun _ _ h => hxz.cong h)⟩

/-! ### Bounded terms around a stable state -/

/-- From a state, the rounds of the program that keep its meaning build terms of bounded
size: every representative is bounded by a representative of the state. -/
theorem terms_bounded (hP : P.Fragment) (hO : P.schedule.OrderingFree) {x₀ : Database}
    (hx₀ : SrcInv P x₀) :
    ∃ M, ∀ x, Rounds P x₀ x → x.SameMeaning x₀ → ∀ t ∈ x.terms, t.nodeSize ≤ M := by
  have hfin : x₀.terms.Finite := Database.finite_terms hx₀.finite
  obtain ⟨N, hN⟩ := (hfin.image Term.nodeSize).bddAbove
  have hN' : ∀ t ∈ x₀.terms, t.nodeSize ≤ N := fun t ht => hN ⟨t, ht, rfl⟩
  refine ⟨max N (P.headSize * (N + 1)), fun x hr => ?_⟩
  induction hr with
  | refl => exact fun _ t ht => Nat.le_trans (hN' t ht) (Nat.le_max_left _ _)
  | @tail z y _ hzy ih =>
    intro hm
    obtain ⟨R, hR, rfl⟩ := hzy
    have hz : z.SameMeaning x₀ := by
      refine (sameMeaning_of_between (x := x₀) (z := z) (y := RunRules R z) ?_ (Rounds.single hR)
        hm.symm).symm
      assumption
    have hz' : SrcInv P z := hx₀.rounds hP (by assumption)
    apply RunRules.nodeSize_le hR (fun r hr => (hO r (hR r hr)).2)
      (reps_nodeSize_le hx₀.hasReps hz (Rounds.terms_subset (by assumption)) hN')
      (Nat.le_max_right _ _) (ih hz)

end Egglog.Congruence
