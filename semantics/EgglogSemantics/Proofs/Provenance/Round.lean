import EgglogSemantics.Proofs.Provenance.Match
import EgglogSemantics.Proofs.Presentation
import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.Source.Ctors
import EgglogSemantics.Proofs.Schedule

/-! One round of the instrumented rules against the instrumented state: it writes the
original round's rows, one log row per firing, and subsumes the original round's rows. The
relation between an original state and its instrumented state is preserved. -/

namespace Egglog.Provenance

/-! ### The premise on the original program -/

theorem programOk_unionFree {P : Program} (h : programOk P = true) : unionFree P = true :=
  (Bool.and_eq_true_iff.mp h).1

theorem programOk_names {P : Program} (h : programOk P = true) : ∀ f ∈ P.names, DataName f := by
  intro f hf
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 f hf
  simpa using this

theorem programOk_ctors {P : Program} (h : programOk P = true) :
    ∀ fk ∈ P.ctors, DataName fk.1 := fun fk hfk =>
  programOk_names h fk.1 (List.mem_append_left _ (List.mem_map_of_mem hfk))

theorem Actions.unionFree_of_all : ∀ {as : List Action},
    (as.all fun a => match a with | .union _ _ => false | _ => true) = true →
      Actions.UnionFree as
  | [], _ => trivial
  | a :: as, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      refine ⟨?_, Actions.unionFree_of_all h.2⟩
      cases a <;> simp [Action.UnionFree] at h ⊢

theorem Rule.unionFree_of_mem {P : Program} (h : unionFree P = true) {r : Rule}
    (hr : r ∈ P.rules) : r.UnionFree :=
  Actions.unionFree_of_all (List.all_eq_true.mp h r hr)

theorem programOk_rule_unionFree {P : Program} (h : programOk P = true) {r : Rule}
    (hr : r ∈ P.rules) : r.UnionFree :=
  Rule.unionFree_of_mem (programOk_unionFree h) hr

/-- A constructor of a rule's query is a constructor of the program. -/
theorem query_ctors_mem {P : Program} {r : Rule} (hr : r ∈ P.rules) {p : Pattern}
    (hp : p ∈ r.query) {fk : FnName × Nat} (hfk : fk ∈ p.ctors) : fk ∈ P.ctors :=
  mem_program_ctors (S := P.schedule) (fun _ h => h) (List.mem_flatMap.mpr ⟨r, hr,
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, hfk⟩)⟩)

/-- A constructor of the check is a constructor of the program. -/
theorem check_ctors_mem {P : Program} {p : Pattern} (hp : p ∈ P.check) {fk : FnName × Nat}
    (hfk : fk ∈ p.ctors) : fk ∈ P.ctors := by
  rw [Program.ctors, List.mem_dedup]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hfk⟩)

/-- A constructor of a rule's head is a constructor of the program. -/
theorem action_ctorsIn {P : Program} {r : Rule} (hr : r ∈ P.rules) {a : Action}
    (ha : a ∈ r.actions) : a.CtorsIn P := fun _ hk =>
  mem_program_ctors (S := P.schedule) (fun _ h => h) (List.mem_flatMap.mpr ⟨r, hr,
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)⟩)

theorem logFreeQuery_of_mem {P : Program} (h : programOk P = true) {r : Rule}
    (hr : r ∈ P.rules) : LogFreeQuery r.query :=
  fun _ hp fk hfk => programOk_ctors h fk (query_ctors_mem hr hp hfk)

theorem logFreeQuery_check {P : Program} (h : programOk P = true) : LogFreeQuery P.check :=
  fun _ hp fk hfk => programOk_ctors h fk (check_ctors_mem hp hfk)

/-! ### The original side -/

/-- A state the original program reaches: good, finite, and every application it holds
is one of the program's constructors. -/
structure Inv (P : Program) (d : Database) : Prop where
  good : Good d
  finite : d.eqs.Finite
  ctors : d.CtorsIn P

namespace Inv

variable {P : Program} {d e : Database}

theorem noLog (hP : programOk P = true) (h : Inv P d) : ∀ t ∈ d.terms, ¬ IsLog t := by
  intro t ht
  cases t with
  | lit l => exact not_isLog_lit l
  | app f ts => exact not_isLog_app (programOk_ctors hP _ (h.ctors f ts ht))

theorem terms_finite (h : Inv P d) : d.terms.Finite := Database.finite_terms h.finite

theorem empty : Inv P Database.empty where
  good := Good.empty
  finite := Set.finite_empty
  ctors := Database.empty_ctorsIn

theorem runRules (hP : programOk P = true) (h : Inv P d) {R : List Rule}
    (hR : ∀ r ∈ R, r ∈ P.rules) : Inv P (RunRules R d) where
  good := h.good.runRules fun r hr => programOk_rule_unionFree hP (hR r hr)
  finite := RunRules.finite_eqs h.finite R
  ctors := (Database.CtorsInState.runRules h.good.wf ⟨h.ctors⟩
    fun r hr _ ha => action_ctorsIn (hR r hr) ha).terms

theorem reach (hP : programOk P = true) {S : Schedule} (hS : S.rules ⊆ P.rules) (h : Inv P d)
    (hr : Reach d S e) : Inv P e :=
  Reach.preserves (I := Inv P) (good := fun r => r ∈ P.rules)
    (fun _ _ hg hd => hd.runRules hP hg) hr (fun _ h => hS h) h

/-- A round from two states of one meaning reaches two states of one meaning. -/
theorem round_sameMeaning (hP : programOk P = true) (hd : Inv P d) (he : Inv P e)
    (hm : d.SameMeaning e) {R : List Rule} (hR : ∀ r ∈ R, r ∈ P.rules) :
    (RunRules R d).SameMeaning (RunRules R e) := by
  obtain ⟨ht, hs⟩ := (hd.good.sameMeaning_iff he.good).mp hm
  obtain ⟨ht', hs'⟩ := hd.good.round_same he.good ht hs R
  exact (hd.runRules hP hR).good.sameMeaning_of (he.runRules hP hR).good ht' hs'

/-- A finite run from a state of the same meaning reaches a state of the same meaning. -/
theorem reach_transport (hP : programOk P = true) {S : Schedule} (hS : S.rules ⊆ P.rules)
    {x y e : Database} (hx : Inv P x) (hy : Inv P y) (hm : x.SameMeaning y)
    (hr : Reach x S e) : ∃ e', Reach y S e' ∧ e.SameMeaning e' :=
  Reach.transport (I := Inv P) (good := fun r => r ∈ P.rules)
    (fun _ _ hg hd => hd.runRules hP hg) (fun _ _ _ hg hd he hm => hd.round_sameMeaning hP he hm hg)
    hr (fun _ h => hS h) hx hy hm

end Inv

/-! ### The relation -/

/-- The instrumented state `d'` of the original state `d`: the same subsumed rows, the
original's equations, and otherwise only log rows whose columns the original holds. -/
structure Rel (P : Program) (d d' : Database) : Prop where
  inv : Inv P d
  subsumed : d'.subsumed = d.subsumed
  eqs : d.eqs ⊆ d'.eqs
  log : ∀ q ∈ d'.eqs, q ∈ d.eqs ∨ ∃ f ts, q = (.app f ts, .app f ts) ∧
    firePrefix.isPrefixOf f = true ∧ ∀ t ∈ ts, t ∈ d.terms

namespace Rel

variable {P : Program} {d d' : Database} (h : Rel P d d')
include h

theorem diag' : d'.Diag := by
  intro q hq
  rcases h.log q hq with hq | ⟨f, ts, rfl, _, _⟩
  · exact h.inv.good.diag q hq
  · rfl

theorem terms_sub : d.terms ⊆ d'.terms := fun _ ht => Database.mem_terms_of_eqs h.eqs ht

theorem good' : Good d' where
  diag := h.diag'
  marks := by
    intro t ht
    rw [h.subsumed] at ht
    exact ⟨(h.inv.good.marks t ht).1, h.terms_sub (h.inv.good.marks t ht).2⟩

/-- A held term of the instrumented state is a term of the original or a log row. -/
theorem mem_terms {t : Term} (ht : t ∈ d'.terms) : t ∈ d.terms ∨ (IsLog t ∧ (t, t) ∈ d'.eqs) := by
  obtain ⟨q, hq, ht⟩ := ht
  rcases h.log q hq with hq' | ⟨f, ts, rfl, hf, hts⟩
  · exact Or.inl ⟨q, hq', ht⟩
  · have hsub : t ∈ (Term.app f ts).subterms := ht.elim id id
    rw [Term.subterms_app] at hsub
    rcases Set.mem_insert_iff.mp hsub with rfl | hsub
    · exact Or.inr ⟨isLog_app_iff.mpr hf, hq⟩
    · obtain ⟨u, hu, hs⟩ := Set.mem_iUnion₂.mp hsub
      exact Or.inl (Database.subtermClosed d u (hts u hu) hs)

theorem mem_terms_of_not_log {t : Term} (ht : t ∈ d'.terms) (hl : ¬ IsLog t) : t ∈ d.terms :=
  (h.mem_terms ht).elim id fun hl' => (hl hl'.1).elim

theorem log_mem_eqs (hP : programOk P = true) {t : Term} (hl : IsLog t) (ht : t ∈ d'.terms) :
    (t, t) ∈ d'.eqs :=
  (h.mem_terms ht).elim (fun ht => (h.inv.noLog hP t ht hl).elim) And.right

theorem shadow (hP : programOk P = true) : Shadow d d' where
  good := h.inv.good
  good' := h.good'
  subsumed := h.subsumed
  terms := fun _ hl => ⟨fun ht => h.mem_terms_of_not_log ht hl, fun ht => h.terms_sub ht⟩
  noLog := h.inv.noLog hP

/-- The original's terms are the instrumented state's data terms. -/
theorem terms_eq (hP : programOk P = true) : d.terms = {t ∈ d'.terms | ¬ IsLog t} := by
  ext t
  exact ⟨fun ht => ⟨h.terms_sub ht, h.inv.noLog hP t ht⟩, fun ht => h.mem_terms_of_not_log ht.1 ht.2⟩

/-- Erasing the log from the instrumented state gives back the original. -/
theorem eraseLog (hP : programOk P = true) : d'.eraseLog = d := by
  apply Database.ext
  · ext q
    rw [Database.mem_eraseLog_eqs]
    constructor
    · rintro ⟨hq, hl⟩
      rcases h.log q hq with hq | ⟨f, ts, rfl, hf, _⟩
      · exact hq
      · exact (hl (isLog_app_iff.mpr hf)).elim
    · intro hq
      exact ⟨h.eqs hq, h.inv.noLog hP q.1 ⟨q, hq, Or.inl (Term.self_mem_subterms _)⟩⟩
  · exact h.subsumed

end Rel

theorem Rel.empty (P : Program) : Rel P Database.empty Database.empty where
  inv := Inv.empty
  subsumed := rfl
  eqs := subset_rfl
  log := fun _ hq => Or.inl hq

/-- Two instrumented states of one meaning have originals of one meaning. -/
theorem Rel.sameMeaning_of_inst {P : Program} (hP : programOk P = true) {x y d' e' : Database}
    (hx : Rel P x d') (hy : Rel P y e') (h : d'.SameMeaning e') : x.SameMeaning y := by
  obtain ⟨ht, hs⟩ := (hx.good'.sameMeaning_iff hy.good').mp h
  apply hx.inv.good.sameMeaning_of hy.inv.good
  · rw [hx.terms_eq hP, hy.terms_eq hP, ht]
  · rw [← hx.subsumed, ← hy.subsumed, hs]

/-! ### Instrumented rules -/

/-- `R'` instruments `R`: the rules of `R` with their log actions, under some indices. -/
structure InstrRules (R R' : List Rule) : Prop where
  orig : ∀ r' ∈ R', ∃ r ∈ R, ∃ j, r' = encodeRule j r
  inst : ∀ r ∈ R, ∃ j, encodeRule j r ∈ R'

@[simp] theorem encodeRule_query (k : Nat) (r : Rule) : (encodeRule k r).query = r.query := rfl

@[simp] theorem encodeRule_actions (k : Nat) (r : Rule) :
    (encodeRule k r).actions = r.actions ++ [fireAction k r] := rfl

theorem exists_of_mem_evalList {σ : Env} : ∀ {es : List Expr} {ts : List Term},
    Expr.evalList es σ = some ts → ∀ {t : Term}, t ∈ ts → ∃ e ∈ es, e.eval σ = some t
  | [], _, h, _, ht => by cases Option.some.inj h; simp at ht
  | e :: es, ts, h, t, ht => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, h⟩ := h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨e, List.mem_cons_self, hu⟩
      · obtain ⟨e', he', hev⟩ := exists_of_mem_evalList hus ht
        exact ⟨e', List.mem_cons_of_mem _ he', hev⟩

theorem mem_of_mem_varsList_map_var {vs : List Var} {v : Var}
    (h : v ∈ Expr.varsList (vs.map Expr.var)) : v ∈ vs := by
  obtain ⟨e, he, hv⟩ := Expr.mem_varsList h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
  rw [Expr.vars_var, List.mem_singleton] at hv
  exact hv ▸ hw

/-- The log action of a rule writes its log row under any substitution that binds the
query's variables, each column a bound value, and subsumes nothing. -/
theorem fireAction_write {r : Rule} {σ : Env} (hσ : ∀ v ∈ r.query.vars, v ∈ Env.dom σ)
    (k : Nat) : ∃ ts, (∀ t ∈ ts, ∃ v, Env.lookup v σ = some t) ∧
      (fireAction k r).write σ = some {(.app (fireName k) ts, .app (fireName k) ts)} ∧
      (fireAction k r).mark σ = some ∅ := by
  obtain ⟨ts, hts⟩ := Expr.evalList_isSome (r.query.vars.map Expr.var)
    fun v hv => hσ v (mem_of_mem_varsList_map_var hv)
  refine ⟨ts, fun t ht => ?_, ?_, ?_⟩
  · obtain ⟨e, he, hev⟩ := exists_of_mem_evalList hts ht
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact ⟨v, hev⟩
  · simp [fireAction, Action.write, hts]
  · simp [fireAction, Action.mark, Action.write, hts]

theorem Action.marks_singleton (σ : Env) (a : Action) : Action.marks σ [a] = a.mark σ := by
  cases h : a.mark σ <;> simp [Action.marks, h]

theorem Action.marks_append (σ : Env) (as bs : List Action) :
    Action.marks σ (as ++ bs) =
      (Action.marks σ as).bind fun A => (Action.marks σ bs).map fun B => A ∪ B := by
  induction as with
  | nil => simp [Action.marks]
  | cons a as ih =>
    simp only [List.cons_append, Action.marks, ih]
    cases a.mark σ <;> cases Action.marks σ as <;> cases Action.marks σ bs <;>
      simp [Set.union_assoc]

/-- The writes and marks of an instrumented head: the original's, plus the log row. -/
theorem encodeRule_writes_marks {r : Rule} {σ : Env} (hσ : ∀ v ∈ r.query.vars, v ∈ Env.dom σ)
    (k : Nat) : ∃ ts, (∀ t ∈ ts, ∃ v, Env.lookup v σ = some t) ∧
      Action.writes σ (encodeRule k r).actions =
        (Action.writes σ r.actions).map
          (fun W => W ∪ {(.app (fireName k) ts, .app (fireName k) ts)}) ∧
      Action.marks σ (encodeRule k r).actions = (Action.marks σ r.actions).map (fun X => X ∪ ∅) := by
  obtain ⟨ts, hts, hw, hx⟩ := fireAction_write hσ k
  refine ⟨ts, hts, ?_, ?_⟩
  · rw [encodeRule_actions, Action.writes_append, Action.writes_singleton, hw]
    cases Action.writes σ r.actions <;> rfl
  · rw [encodeRule_actions, Action.marks_append, Action.marks_singleton, hx]
    cases Action.marks σ r.actions <;> rfl

/-! ### The round -/

/-- A round of the instrumented rules against the instrumented state is related to the
round of the original rules against the original state. -/
theorem run_rel {P : Program} (hP : programOk P = true) {R R' : List Rule}
    (hR : ∀ r ∈ R, r ∈ P.rules) (hK : ∀ r ∈ R, Query.VarsKeyed r.query) (hI : InstrRules R R')
    {d d' : Database} (h : Rel P d d') : Rel P (RunRules R d) (RunRules R' d') := by
  have hsh : Shadow d d' := h.shadow hP
  have hmatch : ∀ r ∈ R, ∀ σ, QueryMatches d' r.query σ ↔ QueryMatches d r.query σ :=
    fun r hr σ => queryMatches_iff hsh (hK r hr) (logFreeQuery_of_mem hP (hR r hr))
  have hdom : ∀ {r : Rule} {σ : Env}, QueryMatches d r.query σ → ∀ v ∈ r.query.vars, v ∈ Env.dom σ :=
    fun hm v hv => hm.1.1.mem_iff.mpr hv
  -- The marks are the original's.
  have hmarks : RunMarks R' d' = RunMarks R d := by
    ext t
    constructor
    · rintro ⟨X, ⟨r', hr', σ, hσ, hX⟩, ht⟩
      obtain ⟨r, hr, j, rfl⟩ := hI.orig r' hr'
      rw [encodeRule_query] at hσ
      have hσ' := (hmatch r hr σ).mp hσ
      obtain ⟨_, _, _, hx⟩ := encodeRule_writes_marks (hdom hσ') j
      rw [hx] at hX
      obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.mp hX
      exact ⟨Y, ⟨r, hr, σ, hσ', hY⟩, by simpa using ht⟩
    · rintro ⟨X, ⟨r, hr, σ, hσ, hX⟩, ht⟩
      obtain ⟨j, hj⟩ := hI.inst r hr
      obtain ⟨_, _, _, hx⟩ := encodeRule_writes_marks (hdom hσ) j
      refine ⟨X ∪ ∅, ⟨encodeRule j r, hj, σ, (hmatch r hr σ).mpr hσ, ?_⟩, Or.inl ht⟩
      rw [hx, hX]
      rfl
  -- The writes are the original's and the log rows of the firings.
  have hW₁ : RunWrites R d ⊆ RunWrites R' d' := by
    rintro p ⟨W, ⟨r, hr, σ, hσ, hW⟩, hp⟩
    obtain ⟨j, hj⟩ := hI.inst r hr
    obtain ⟨ts, _, hw, _⟩ := encodeRule_writes_marks (hdom hσ) j
    refine ⟨W ∪ {(.app (fireName j) ts, .app (fireName j) ts)},
      ⟨encodeRule j r, hj, σ, (hmatch r hr σ).mpr hσ, ?_⟩, Or.inl hp⟩
    rw [hw, hW]
    rfl
  have hW₂ : ∀ p ∈ RunWrites R' d', p ∈ RunWrites R d ∨ ∃ f ts, p = (.app f ts, .app f ts) ∧
      firePrefix.isPrefixOf f = true ∧ ∀ t ∈ ts, t ∈ d.terms := by
    rintro p ⟨W', ⟨r', hr', σ, hσ, hW'⟩, hp⟩
    obtain ⟨r, hr, j, rfl⟩ := hI.orig r' hr'
    rw [encodeRule_query] at hσ
    have hσ' := (hmatch r hr σ).mp hσ
    obtain ⟨ts, hts, hw, _⟩ := encodeRule_writes_marks (hdom hσ') j
    rw [hw] at hW'
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.mp hW'
    rcases hp with hp | hp
    · exact Or.inl ⟨W, ⟨r, hr, σ, hσ', hW⟩, hp⟩
    · refine Or.inr ⟨fireName j, ts, hp, isPrefixOf_fireName j, fun t ht => ?_⟩
      obtain ⟨v, hv⟩ := hts t ht
      exact hσ'.1.mem_terms (v, t) (Env.mem_of_lookup hv)
  refine ⟨h.inv.runRules hP hR, ?_, ?_, ?_⟩
  · rw [RunRules.eq_pair R d, RunRules.eq_pair R' d']
    change d'.subsumed ∪ RunMarks R' d' = d.subsumed ∪ RunMarks R d
    rw [h.subsumed, hmarks]
  · rw [RunRules.eq_pair R d, RunRules.eq_pair R' d']
    change d.eqs ∪ RunWrites R d ⊆ d'.eqs ∪ RunWrites R' d'
    exact Set.union_subset_union h.eqs hW₁
  · intro q hq
    have hq' : q ∈ d'.eqs ∪ RunWrites R' d' := by rw [RunRules.eq_pair] at hq; exact hq
    have hterms := RunRules.terms_subset R d
    rcases hq' with hq' | hq'
    · rcases h.log q hq' with hq' | ⟨f, ts, rfl, hf, hts⟩
      · exact Or.inl (RunRules.eqs_subset R d hq')
      · exact Or.inr ⟨f, ts, rfl, hf, fun t ht => hterms (hts t ht)⟩
    · rcases hW₂ q hq' with hq' | ⟨f, ts, rfl, hf, hts⟩
      · exact Or.inl (by rw [RunRules.eq_pair]; exact Or.inr hq')
      · exact Or.inr ⟨f, ts, rfl, hf, fun t ht => hterms (hts t ht)⟩

end Egglog.Provenance
