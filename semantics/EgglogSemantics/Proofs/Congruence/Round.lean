import EgglogSemantics.Proofs.Congruence.Writes
import EgglogSemantics.Proofs.Congruence.QueryCorr
import EgglogSemantics.Proofs.Congruence.Invariant

/-! A source run and its compiled run preserve the simulation relation: the firings
correspond through the query correspondence, and the compiled rows and marks of each firing
stand to its source writes and marks as the relation requires. -/

namespace Egglog.Congruence

variable {sub : Bool}

/-! ### Compiled heads -/

theorem encodeAction_expr (e : Expr) : encodeActionWith { subsumption := sub } (.expr e) = encodeBuildWith { subsumption := sub } e := rfl

theorem encodeAction_union (a b : Expr) : encodeActionWith { subsumption := sub } (.union a b) =
    encodeBuildWith { subsumption := sub } a ++ encodeBuildWith { subsumption := sub } b ++
      [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))] := rfl

theorem encodeAction_subsume (f : FnName) (es : List Expr) :
    encodeActionWith { subsumption := sub } (.subsume f es) =
      encodeBuildWith { subsumption := sub } (.app f es) ++
        ([.subsume f es] ++ (if sub then [.expr (subRow f es)] else [])) := by
  simp [encodeActionWith, List.append_assoc]

theorem encodeActions_nil : encodeActionsWith { subsumption := sub } [] = [] := rfl

theorem encodeActions_cons (a : Action) (as : List Action) :
    encodeActionsWith { subsumption := sub } (a :: as) = encodeActionWith { subsumption := sub } a ++ encodeActionsWith { subsumption := sub } as := by
  simp [encodeActionsWith]

/-- Compiled builds only write rows. -/
theorem encodeBuild_subsumeFree : ∀ e : Expr, Actions.SubsumeFree (encodeBuildWith { subsumption := sub } e)
  | .lit _ => by
      rw [build_lit]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; trivial
  | .var _ => by
      rw [build_var]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; trivial
  | .min a b => by
      intro x hx
      simp only [encodeBuildWith, List.mem_append] at hx
      rcases hx with hx | hx
      · exact encodeBuild_subsumeFree a x hx
      · exact encodeBuild_subsumeFree b x hx
  | .app f args => by
      rw [build_app]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact encodeBuildArgs_subsumeFree args x hx
      · have hx : x = .expr (nodeRow f args) ∨
            x = .expr (ufRow (.app f args) (.app f args)) := by
          cases sub <;> simp_all
        rcases hx with rfl | rfl <;> trivial
where
  encodeBuildArgs_subsumeFree : ∀ es : List Expr, Actions.SubsumeFree (encodeBuildArgsWith { subsumption := sub } es)
    | [] => by intro a ha; simp [buildArgs_nil] at ha
    | e :: es => by
        rw [buildArgs_cons]
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact encodeBuild_subsumeFree e x hx
        · exact encodeBuildArgs_subsumeFree es x hx

/-! ### Marks of action lists -/

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

/-- The marks of a compiled head are the marks of the source head. -/
theorem encodeAction_marks {σ : Env} {a : Action} {X Y : Set Term}
    (hX : Action.marks σ (encodeActionWith { subsumption := sub } a) = some X) (hY : a.mark σ = some Y) : X = Y := by
  cases a with
  | expr e =>
    rw [encodeAction_expr] at hX
    rw [Action.marks_eq_empty (encodeBuild_subsumeFree e) hX]
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hY
    rfl
  | union a b =>
    have hsf : Actions.SubsumeFree (encodeActionWith { subsumption := sub } (.union a b)) := by
      rw [encodeAction_union]
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | rfl | rfl
      · exact encodeBuild_subsumeFree a x hx
      · exact encodeBuild_subsumeFree b x hx
      · trivial
      · trivial
    rw [Action.marks_eq_empty hsf hX]
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hY
    rfl
  | subsume f es =>
    rw [encodeAction_subsume, Action.marks_append, Option.bind_eq_some_iff] at hX
    obtain ⟨A, hA, hX⟩ := hX
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp hX
    rw [Action.marks_eq_empty (encodeBuild_subsumeFree _) hA]
    simp only [Action.mark] at hY
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hY
    cases sub <;> simp_all [Action.marks, Action.mark, Action.write, hts, subRow,
      Expr.eval_app_ctor]

theorem encodeActions_marks {σ : Env} : ∀ {as : List Action} {X Y : Set Term},
    Action.marks σ (encodeActionsWith { subsumption := sub } as) = some X → Action.marks σ as = some Y → X = Y
  | [], X, Y, hX, hY => by
      rw [encodeActions_nil] at hX
      exact (Option.some.inj hX).symm.trans (Option.some.inj hY)
  | a :: as, X, Y, hX, hY => by
      rw [encodeActions_cons, Action.marks_append, Option.bind_eq_some_iff] at hX
      obtain ⟨A, hA, hX⟩ := hX
      obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp hX
      rw [Action.marks, Option.bind_eq_some_iff] at hY
      obtain ⟨A', hA', hY⟩ := hY
      obtain ⟨B', hB', rfl⟩ := Option.map_eq_some_iff.mp hY
      rw [encodeAction_marks hA hA', encodeActions_marks hB hB']

/-! ### Writes and marks depend only on the head's variables -/

/-- A write reads the environment only at the action's variables. -/
theorem Action.write_agreeOn {σ τ : Env} (a : Action)
    (h : ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) : a.write σ = a.write τ := by
  cases a with
  | expr e => simp only [Action.write, Expr.eval_agreeOn e h]
  | union a b =>
    simp only [Action.write, Expr.eval_agreeOn a (fun v hv => h v (by simp [Action.vars, hv])),
      Expr.eval_agreeOn b (fun v hv => h v (by simp [Action.vars, hv]))]
  | subsume f es =>
    simp only [Action.write, Expr.evalList_agreeOn es (by simpa [Action.vars] using h)]

theorem Action.mark_agreeOn {σ τ : Env} (a : Action)
    (h : ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) : a.mark σ = a.mark τ := by
  cases a with
  | expr e => simp only [Action.mark, Action.write_agreeOn _ h]
  | union a b => simp only [Action.mark, Action.write_agreeOn _ h]
  | subsume f es =>
    simp only [Action.mark, Expr.evalList_agreeOn es (by simpa [Action.vars] using h)]

theorem Action.writes_agreeOn {σ τ : Env} (as : List Action)
    (h : ∀ a ∈ as, ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) :
    Action.writes σ as = Action.writes τ as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [Action.writes, Action.write_agreeOn a (h a (by simp)),
      ih fun a ha => h a (by simp [ha])]

theorem Action.marks_agreeOn {σ τ : Env} (as : List Action)
    (h : ∀ a ∈ as, ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) :
    Action.marks σ as = Action.marks τ as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [Action.marks, Action.mark_agreeOn a (h a (by simp)),
      ih fun a ha => h a (by simp [ha])]

theorem mem_ufRow_vars {a b : Expr} {v : Var} :
    v ∈ (ufRow a b).vars ↔ v ∈ a.vars ∨ v ∈ b.vars := by
  simp [ufRow, Expr.varsList]

theorem build_min (a b : Expr) :
    encodeBuildWith { subsumption := sub } (.min a b) = encodeBuildWith { subsumption := sub } a ++ encodeBuildWith { subsumption := sub } b := rfl

mutual

/-- A compiled construction mentions only the expression's variables. -/
theorem build_vars : ∀ (e : Expr), ∀ a ∈ encodeBuildWith { subsumption := sub } e, ∀ v ∈ a.vars, v ∈ e.vars
  | .lit l, a, ha, v, hv => by
      rw [build_lit, List.mem_singleton] at ha
      subst ha
      rw [Action.vars, mem_ufRow_vars] at hv
      exact hv.elim id id
  | .var w, a, ha, v, hv => by
      rw [build_var, List.mem_singleton] at ha
      subst ha
      rw [Action.vars, mem_ufRow_vars] at hv
      exact hv.elim id id
  | .min a b, c, hc, v, hv => by
      rw [build_min, List.mem_append] at hc
      rw [Expr.vars_min, List.mem_union_iff]
      rcases hc with hc | hc
      · exact Or.inl (build_vars a c hc v hv)
      · exact Or.inr (build_vars b c hc v hv)
  | .app f args, c, hc, v, hv => by
      rw [build_app, List.mem_append] at hc
      have hc : c ∈ encodeBuildArgsWith { subsumption := sub } args ∨
          c = .expr (nodeRow f args) ∨ c = .expr (ufRow (.app f args) (.app f args)) := by
        cases sub <;> simp_all <;> tauto
      rcases hc with hc | rfl | rfl
      · exact buildArgs_vars args c hc v hv
      · obtain ⟨e, he, hv⟩ := Expr.mem_varsList hv
        rcases List.mem_append.mp he with he | he
        · exact var_mem_varsList_of_mem he hv
        · obtain rfl := List.mem_singleton.mp he
          exact hv
      · rw [Action.vars, mem_ufRow_vars] at hv
        exact hv.elim id id

theorem buildArgs_vars : ∀ (es : List Expr), ∀ a ∈ encodeBuildArgsWith { subsumption := sub } es, ∀ v ∈ a.vars,
    v ∈ Expr.varsList es
  | [], a, ha, _, _ => by rw [buildArgs_nil] at ha; simp at ha
  | e :: es, a, ha, v, hv => by
      rw [buildArgs_cons, List.mem_append] at ha
      rw [Expr.varsList_cons, List.mem_union_iff]
      rcases ha with ha | ha
      · exact Or.inl (build_vars e a ha v hv)
      · exact Or.inr (buildArgs_vars es a ha v hv)

end

theorem action_vars (a : Action) : ∀ b ∈ encodeActionWith { subsumption := sub } a, ∀ v ∈ b.vars, v ∈ a.vars := by
  cases a with
  | expr e => exact build_vars e
  | union a b =>
    intro c hc v hv
    simp only [encodeActionWith, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rw [Action.vars, List.mem_union_iff]
    rcases hc with (hc | hc) | rfl | rfl
    · exact Or.inl (build_vars a c hc v hv)
    · exact Or.inr (build_vars b c hc v hv)
    · rw [Action.vars, mem_ufRow_vars, Expr.vars_min, List.mem_union_iff] at hv
      exact hv.elim Or.inl id
    · rw [Action.vars, mem_ufRow_vars, Expr.vars_min, List.mem_union_iff] at hv
      exact hv.elim Or.inr id
  | subsume f es =>
    intro c hc v hv
    rw [encodeAction_subsume, List.mem_append] at hc
    have hc : c ∈ encodeBuildWith { subsumption := sub } (.app f es) ∨
        c = .subsume f es ∨ c = .expr (subRow f es) := by
      cases sub <;> simp_all <;> tauto
    rcases hc with hc | rfl | rfl
    · exact build_vars _ c hc v hv
    · exact hv
    · simpa [Action.vars, subRow] using hv

theorem actions_vars (as : List Action) :
    ∀ b ∈ encodeActionsWith { subsumption := sub } as, ∀ v ∈ b.vars, ∃ a ∈ as, v ∈ a.vars := by
  induction as with
  | nil => intro b hb; rw [encodeActions_nil] at hb; simp at hb
  | cons a as ih =>
    intro b hb v hv
    rw [encodeActions_cons, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ⟨a, by simp, action_vars a b hb v hv⟩
    · obtain ⟨a', ha', hv'⟩ := ih b hb v hv
      exact ⟨a', by simp [ha'], hv'⟩

theorem actions_writes_agreeOn {σ τ : Env} (as : List Action)
    (h : ∀ a ∈ as, ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) :
    Action.writes σ (encodeActionsWith { subsumption := sub } as) = Action.writes τ (encodeActionsWith { subsumption := sub } as) := by
  apply Action.writes_agreeOn
  intro b hb v hv
  obtain ⟨a, ha, hv'⟩ := actions_vars as b hb v hv
  exact h a ha v hv'

theorem actions_marks_agreeOn {σ τ : Env} (as : List Action)
    (h : ∀ a ∈ as, ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) :
    Action.marks σ (encodeActionsWith { subsumption := sub } as) = Action.marks τ (encodeActionsWith { subsumption := sub } as) := by
  apply Action.marks_agreeOn
  intro b hb v hv
  obtain ⟨a, ha, hv'⟩ := actions_vars as b hb v hv
  exact h a ha v hv'

/-- A scoped action mentions only variables of the scope. -/
theorem Action.vars_subset_of_scoped {a : Action} {Γ : Scope} (h : a.Scoped Γ) :
    ∀ v ∈ a.vars, v ∈ Γ := by
  cases a with
  | expr e => exact h.2
  | union a b =>
    intro v hv
    rw [Action.vars, List.mem_union_iff] at hv
    exact hv.elim (h.1 v) (h.2 v)
  | subsume f es => exact h

theorem Actions.vars_subset_of_scoped : ∀ {as : List Action} {Γ : Scope},
    Actions.Scoped as Γ → ∀ a ∈ as, ∀ v ∈ a.vars, v ∈ Γ
  | [], _, _ => by simp
  | a :: as, Γ, h => by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Action.vars_subset_of_scoped h.1
      · exact Actions.vars_subset_of_scoped h.2 b hb

/-! ### The compiled rows of a head against its source writes -/

/-- How the compiled rows `V'` and marks `M` of a head stand to its source writes `V` and
marks `M`: every compiled row is a union-find row between terms congruent and held once
`V` is asserted and the bindings are held, going down the term order, with its endpoints'
self-loops; or the node row of a term whose self-loop is written; or the marker, or the
self-pair, of a marked spelling. Every source write is derivable from the rows; every
subterm of a source write is a self-loop, with its node row when enabled, or lies
inside a binding; and every mark is an application whose marker, self-loop and source
self-pair are written. The bindings matter for a `min`: the compiled head writes the
self-loop of the operand it does not choose, which is a bound representative. -/
structure HeadWrites (sub : Bool) (σ : Env) (V V' : Set (Term × Term)) (M : Set Term) : Prop where
  shape : ∀ q ∈ V', (∃ k p, q = (ufRowT k p, ufRowT k p)) ∨
    (∃ f as, q = nodeSelf f as ∧ selfRow (.app f as) ∈ V') ∨
    (∃ f as, q = (subRowT f as, subRowT f as) ∧ Term.app f as ∈ M) ∨ (∃ t ∈ M, q = (t, t))
  down : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → p = k ∨ Term.blt p k = true
  selfLoop : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → selfRow k ∈ V' ∧ selfRow p ∈ V'
  cong : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → ∀ D : Database, V ⊆ D.eqs →
    (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → Cong D k p
  ends : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → ∀ D : Database, V ⊆ D.eqs →
    (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → k ∈ D.terms ∧ p ∈ D.terms
  derivable : ∀ q ∈ V, ∀ E : Database,
    (∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → (k, p) ∈ E.eqs) → Cong E q.1 q.2
  covers : ∀ q ∈ V, ∀ u, Term.IsSubterm u q.1 ∨ Term.IsSubterm u q.2 →
    (selfRow u ∈ V' ∧ ∀ g us, u = .app g us → sub = true → nodeSelf g us ∈ V') ∨
      ∃ v w, Env.lookup v σ = some w ∧ Term.IsSubterm u w
  marks : ∀ t ∈ M, ∃ f as, t = .app f as ∧ (subRowT f as, subRowT f as) ∈ V' ∧
    selfRow t ∈ V' ∧ (t, t) ∈ V

theorem HeadWrites.empty (σ : Env) : HeadWrites sub σ ∅ ∅ ∅ where
  shape := by simp
  down := by simp
  selfLoop := by simp
  cong := by simp
  ends := by simp
  derivable := by simp
  covers := by simp
  marks := by simp

theorem HeadWrites.union {σ : Env} {V₁ V₁' V₂ V₂' : Set (Term × Term)} {M₁ M₂ : Set Term}
    (h₁ : HeadWrites sub σ V₁ V₁' M₁) (h₂ : HeadWrites sub σ V₂ V₂' M₂) :
    HeadWrites sub σ (V₁ ∪ V₂) (V₁' ∪ V₂') (M₁ ∪ M₂) where
  shape := fun q hq => hq.elim
    (fun hq => (h₁.shape q hq).imp id (Or.imp
      (fun ⟨f, as, hq, hs⟩ => ⟨f, as, hq, Or.inl hs⟩)
      (Or.imp (fun ⟨f, as, hq, hm⟩ => ⟨f, as, hq, Or.inl hm⟩)
        (fun ⟨t, ht, hq⟩ => ⟨t, Or.inl ht, hq⟩))))
    (fun hq => (h₂.shape q hq).imp id (Or.imp
      (fun ⟨f, as, hq, hs⟩ => ⟨f, as, hq, Or.inr hs⟩)
      (Or.imp (fun ⟨f, as, hq, hm⟩ => ⟨f, as, hq, Or.inr hm⟩)
        (fun ⟨t, ht, hq⟩ => ⟨t, Or.inr ht, hq⟩))))
  down := fun k p hq => hq.elim (h₁.down k p) (h₂.down k p)
  selfLoop := fun k p hq => hq.elim
    (fun hq => ⟨Or.inl (h₁.selfLoop k p hq).1, Or.inl (h₁.selfLoop k p hq).2⟩)
    (fun hq => ⟨Or.inr (h₂.selfLoop k p hq).1, Or.inr (h₂.selfLoop k p hq).2⟩)
  cong := fun k p hq D hD hσ => hq.elim
    (fun hq => h₁.cong k p hq D (Set.subset_union_left.trans hD) hσ)
    (fun hq => h₂.cong k p hq D (Set.subset_union_right.trans hD) hσ)
  ends := fun k p hq D hD hσ => hq.elim
    (fun hq => h₁.ends k p hq D (Set.subset_union_left.trans hD) hσ)
    (fun hq => h₂.ends k p hq D (Set.subset_union_right.trans hD) hσ)
  derivable := fun q hq E hE => hq.elim
    (fun hq => h₁.derivable q hq E fun k p hkp => hE k p (Or.inl hkp))
    (fun hq => h₂.derivable q hq E fun k p hkp => hE k p (Or.inr hkp))
  covers := fun q hq u hu => hq.elim
    (fun hq => (h₁.covers q hq u hu).imp_left fun ⟨hs, hn⟩ =>
      ⟨Or.inl hs, fun g us heq hon => Or.inl (hn g us heq hon)⟩)
    (fun hq => (h₂.covers q hq u hu).imp_left fun ⟨hs, hn⟩ =>
      ⟨Or.inr hs, fun g us heq hon => Or.inr (hn g us heq hon)⟩)
  marks := fun t ht => ht.elim
    (fun ht => let ⟨f, as, heq, hm, hs, hv⟩ := h₁.marks t ht
      ⟨f, as, heq, Or.inl hm, Or.inl hs, Or.inl hv⟩)
    (fun ht => let ⟨f, as, heq, hm, hs, hv⟩ := h₂.marks t ht
      ⟨f, as, heq, Or.inr hm, Or.inr hs, Or.inr hv⟩)

/-- A source write's endpoints are held once it is asserted. -/
theorem mem_terms_of_mem_eqs {D : Database} {q : Term × Term} (hq : q ∈ D.eqs) :
    q.1 ∈ D.terms ∧ q.2 ∈ D.terms :=
  ⟨⟨q, hq, Or.inl (Term.self_mem_subterms _)⟩, ⟨q, hq, Or.inr (Term.self_mem_subterms _)⟩⟩

theorem subterm_mem_terms {D : Database} {t u : Term} (ht : t ∈ D.terms) (hu : Term.IsSubterm u t) :
    u ∈ D.terms := D.subtermClosed t ht hu

/-- The rows a build writes, relative to its value: self-loops of subterms of the value or
of bindings, including the value's own, and node rows of applications the build spells,
covering every subterm not inside a binding. -/
theorem build_rows {σ : Env} {e : Expr} (ho : e.MinOverVars)
    (hb : ∀ v ∈ e.vars, (Env.lookup v σ).isSome) {t : Term} (ht : e.eval σ = some t)
    {V' : Set (Term × Term)} (hV' : Action.writes σ (encodeBuildWith { subsumption := sub } e) = some V') :
    (∀ k p, (ufRowT k p, ufRowT k p) ∈ V' →
      k = p ∧ (Term.IsSubterm k t ∨ ∃ v, Env.lookup v σ = some k)) ∧
    (∀ q ∈ V', (∃ u, q = selfRow u) ∨ ∃ g us, q = nodeSelf g us ∧ selfRow (.app g us) ∈ V') ∧
    selfRow t ∈ V' ∧
    ∀ u, Term.IsSubterm u t →
      (selfRow u ∈ V' ∧ ∀ g us, u = .app g us → sub = true → nodeSelf g us ∈ V') ∨
        ∃ v w, Env.lookup v σ = some w ∧ Term.IsSubterm u w := by
  obtain ⟨W, hW, hmem⟩ := build_writes e ho hb
  rw [hW] at hV'
  obtain rfl := Option.some.inj hV'
  refine ⟨fun k p hkp => ?_, fun q hq => ?_, (hmem _).mpr (Or.inl ⟨t, BuildTerm.self ho ht, rfl⟩),
    fun u hu => ?_⟩
  · rcases (hmem _).mp hkp with ⟨u, hu, heq⟩ | ⟨g, us, _, _, heq⟩
    · obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
      exact ⟨rfl, hu.subterm_or_bound ho ht⟩
    · exact (nodeName_ne_ufName g (Term.app.inj (Prod.mk.inj heq).1).1.symm).elim
  · rcases (hmem q).mp hq with ⟨u, _, rfl⟩ | ⟨g, us, hon, hn, rfl⟩
    · exact Or.inl ⟨u, rfl⟩
    · exact Or.inr ⟨g, us, rfl, (hmem _).mpr (Or.inl ⟨_, hn.buildTerm, rfl⟩)⟩
  · rcases subterm_build e ho ht hu with ⟨hbt, hn⟩ | ⟨v, _, w, hw, huw⟩
    · exact Or.inl ⟨(hmem _).mpr (Or.inl ⟨u, hbt, rfl⟩),
        fun g us heq hon => (hmem _).mpr (Or.inr ⟨g, us, hon, hn g us heq, rfl⟩)⟩
    · exact Or.inr ⟨v, w, hw, huw⟩

theorem mem_terms_of_subterm_eq {D : Database} {t u : Term} {q : Term × Term} (hq : q ∈ D.eqs)
    (ht : t = q.1 ∨ t = q.2) (hu : Term.IsSubterm u t) : u ∈ D.terms := by
  rcases ht with rfl | rfl
  · exact subterm_mem_terms (mem_terms_of_mem_eqs hq).1 hu
  · exact subterm_mem_terms (mem_terms_of_mem_eqs hq).2 hu

/-- The rows of a build stand to the write `(t, t)` of its value as `HeadWrites` requires,
with no marks. -/
theorem build_headWrites {σ : Env} {e : Expr} (ho : e.MinOverVars)
    (hb : ∀ v ∈ e.vars, (Env.lookup v σ).isSome) {t : Term} (ht : e.eval σ = some t)
    {W : Set (Term × Term)} (hW : Action.writes σ (encodeBuildWith { subsumption := sub } e) = some W) :
    HeadWrites sub σ {(t, t)} W ∅ := by
  obtain ⟨hpair, hshape, hself, hcov⟩ := build_rows ho hb ht hW
  -- A build term is held once the value is asserted and the bindings are held.
  have hheld : ∀ k, (Term.IsSubterm k t ∨ ∃ v, Env.lookup v σ = some k) → ∀ D : Database,
      {(t, t)} ⊆ D.eqs → (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → k ∈ D.terms := by
    intro k hk D hD hσ
    rcases hk with hk | ⟨v, hv⟩
    · exact mem_terms_of_subterm_eq (hD rfl) (Or.inl rfl) hk
    · exact hσ v k hv
  refine ⟨fun q hq => ?_, fun k p hkp => ?_, fun k p hkp => ?_, fun k p hkp D hD hσ => ?_,
    fun k p hkp D hD hσ => ?_, fun q hq E hE => ?_, fun q hq u hu => ?_, by simp⟩
  · rcases hshape q hq with ⟨u, rfl⟩ | ⟨g, us, rfl, hs⟩
    · exact Or.inl ⟨u, u, rfl⟩
    · exact Or.inr (Or.inl ⟨g, us, rfl, hs⟩)
  · exact Or.inl (hpair k p hkp).1.symm
  · obtain ⟨rfl, _⟩ := hpair k p hkp
    exact ⟨hkp, hkp⟩
  · obtain ⟨rfl, hk⟩ := hpair k p hkp
    exact Database.toCong (hheld k hk D hD hσ)
  · obtain ⟨rfl, hk⟩ := hpair k p hkp
    exact ⟨hheld k hk D hD hσ, hheld k hk D hD hσ⟩
  · rw [Set.mem_singleton_iff] at hq
    subst hq
    exact .direct (hE t t hself)
  · rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hcov u (hu.elim id id)

/-- The compiled rows and marks of a source action. -/
theorem action_headWrites {σ : Env} {a : Action} (ho : a.MinOverVars)
    (hname : ∀ f es, a = .subsume f es → SourceName f ∧ sub = true)
    (hb : ∀ v ∈ a.vars, (Env.lookup v σ).isSome) {V : Set (Term × Term)} {M : Set Term}
    (hV : a.write σ = some V) (hM : a.mark σ = some M) :
    ∃ V', Action.writes σ (encodeActionWith { subsumption := sub } a) = some V' ∧ HeadWrites sub σ V V' M := by
  cases a with
  | expr e =>
    rw [Action.write] at hV
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hV
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hM
    rw [encodeAction_expr]
    obtain ⟨W, hW, _⟩ := build_writes e ho hb
    exact ⟨W, hW, build_headWrites ho hb ht hW⟩
  | union a b =>
    obtain ⟨hoa, hob⟩ := Action.minOverVars_union ho
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hM
    rw [Action.write] at hV
    obtain ⟨t₁, ht₁, hV⟩ := Option.bind_eq_some_iff.mp hV
    obtain ⟨t₂, ht₂, hV⟩ := Option.bind_eq_some_iff.mp hV
    split at hV
    · cases hV
    · obtain rfl := Option.some.inj hV
      have hba : ∀ v ∈ a.vars, (Env.lookup v σ).isSome := fun v hv =>
        hb v (by simp [Action.vars, hv])
      have hbb : ∀ v ∈ b.vars, (Env.lookup v σ).isSome := fun v hv =>
        hb v (by simp [Action.vars, hv])
      obtain ⟨W₁, hW₁, _⟩ := build_writes a hoa hba
      obtain ⟨W₂, hW₂, _⟩ := build_writes b hob hbb
      have hh₁ := build_headWrites hoa hba ht₁ hW₁
      have hh₂ := build_headWrites hob hbb ht₂ hW₂
      obtain ⟨hrows₁, -, hself₁, hcov₁⟩ := build_rows hoa hba ht₁ hW₁
      obtain ⟨hrows₂, -, hself₂, hcov₂⟩ := build_rows hob hbb ht₂ hW₂
      set m := Term.least t₁ t₂ with hm
      have hmin : (Expr.min a b).eval σ = some m := by
        rw [Expr.eval_min, ht₁, Option.bind_some, ht₂, Option.map_some]
      have hpair : Action.writes σ [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))] =
          some ({(ufRowT t₁ m, ufRowT t₁ m)} ∪ ({(ufRowT t₂ m, ufRowT t₂ m)} ∪ ∅)) := by
        simp [Action.writes, Action.write, ufRow, Expr.evalList, ht₁, ht₂, hmin]
      set P : Set (Term × Term) :=
        {(ufRowT t₁ m, ufRowT t₁ m)} ∪ ({(ufRowT t₂ m, ufRowT t₂ m)} ∪ ∅) with hP
      have hPmem : ∀ q, q ∈ P ↔
          q = (ufRowT t₁ m, ufRowT t₁ m) ∨ q = (ufRowT t₂ m, ufRowT t₂ m) := by
        intro q
        rw [hP]
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
      refine ⟨W₁ ∪ W₂ ∪ P, ?_, ?_⟩
      · rw [encodeAction_union, Action.writes_append, Action.writes_append, hW₁, Option.bind_some,
          hW₂, Option.map_some, Option.bind_some, hpair, Option.map_some]
      have hm_or : m = t₁ ∨ m = t₂ := Term.least_eq_or t₁ t₂
      have hselfm : selfRow m ∈ W₁ ∪ W₂ := by
        rcases hm_or with hm' | hm' <;> rw [hm']
        · exact Or.inl hself₁
        · exact Or.inr hself₂
      have hdown₁ : m = t₁ ∨ Term.blt m t₁ = true := by
        rw [Term.least_eq_ite] at hm
        by_cases h12 : Term.blt t₁ t₂ = true
        · rw [if_pos h12] at hm; exact Or.inl hm
        · rw [if_neg h12] at hm
          rcases eq_or_ne t₁ t₂ with heq | hne
          · exact Or.inl (hm.trans heq.symm)
          · rcases Term.blt_total t₁ t₂ hne with h | h
            · exact (h12 h).elim
            · exact Or.inr (hm ▸ h)
      have hdown₂ : m = t₂ ∨ Term.blt m t₂ = true := by
        rw [Term.least_eq_ite] at hm
        by_cases h12 : Term.blt t₁ t₂ = true
        · rw [if_pos h12] at hm; exact Or.inr (hm ▸ h12)
        · rw [if_neg h12] at hm; exact Or.inl hm
      -- Rows of the builds: self-loops of subterms of an endpoint, or of a binding.
      have hW : ∀ k p, (ufRowT k p, ufRowT k p) ∈ W₁ ∪ W₂ →
          k = p ∧ (Term.IsSubterm k t₁ ∨ Term.IsSubterm k t₂ ∨
            ∃ v, Env.lookup v σ = some k) := by
        intro k p hkp
        rcases hkp with hkp | hkp
        · obtain ⟨rfl, hu⟩ := hrows₁ _ _ hkp
          exact ⟨rfl, hu.imp_right Or.inr⟩
        · obtain ⟨rfl, hu⟩ := hrows₂ _ _ hkp
          exact ⟨rfl, Or.inr hu⟩
      have hendD : ∀ D : Database, {(t₁, t₂)} ⊆ D.eqs →
          (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → ∀ u,
          Term.IsSubterm u t₁ ∨ Term.IsSubterm u t₂ ∨ (∃ v, Env.lookup v σ = some u) →
          u ∈ D.terms := by
        intro D hD hσ u hu
        rcases hu with hu | hu | ⟨v, hv⟩
        · exact mem_terms_of_subterm_eq (hD rfl) (Or.inl rfl) hu
        · exact mem_terms_of_subterm_eq (hD rfl) (Or.inr rfl) hu
        · exact hσ v u hv
      have hmD : ∀ D : Database, {(t₁, t₂)} ⊆ D.eqs → m ∈ D.terms := by
        intro D hD
        rcases hm_or with hm' | hm' <;> rw [hm']
        · exact (mem_terms_of_mem_eqs (hD rfl)).1
        · exact (mem_terms_of_mem_eqs (hD rfl)).2
      have hcongm : ∀ D : Database, {(t₁, t₂)} ⊆ D.eqs → Cong D t₁ m ∧ Cong D t₂ m := by
        intro D hD
        have h12 : Cong D t₁ t₂ := .direct (hD rfl)
        rcases hm_or with hm' | hm' <;> rw [hm']
        · exact ⟨h12.trans h12.symm, h12.symm⟩
        · exact ⟨h12, h12.symm.trans h12⟩
      have hunion := hh₁.union hh₂
      refine ⟨fun q hq => ?_, fun k p hkp => ?_, fun k p hkp => ?_, fun k p hkp D hD hσ => ?_,
        fun k p hkp D hD hσ => ?_, fun q hq E hE => ?_, fun q hq u hu => ?_, by simp⟩
      · rcases hq with hq | hq
        · rcases hunion.shape q hq with hq | ⟨g, us, rfl, hs⟩ | ⟨g, us, _, hm⟩ | ⟨t, ht, _⟩
          · exact Or.inl hq
          · exact Or.inr (Or.inl ⟨g, us, rfl, Or.inl hs⟩)
          · simpa using hm
          · simpa using ht
        · rcases (hPmem q).mp hq with rfl | rfl
          · exact Or.inl ⟨t₁, m, rfl⟩
          · exact Or.inl ⟨t₂, m, rfl⟩
      · rcases hkp with hkp | hkp
        · exact Or.inl (hW k p hkp).1.symm
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact hdown₁
          · exact hdown₂
      · rcases hkp with hkp | hkp
        · obtain ⟨rfl, _⟩ := hW k p hkp
          exact ⟨Or.inl hkp, Or.inl hkp⟩
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact ⟨Or.inl (Or.inl hself₁), Or.inl hselfm⟩
          · exact ⟨Or.inl (Or.inr hself₂), Or.inl hselfm⟩
      · rcases hkp with hkp | hkp
        · obtain ⟨rfl, hk⟩ := hW k p hkp
          exact Database.toCong (hendD D hD hσ k hk)
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact (hcongm D hD).1
          · exact (hcongm D hD).2
      · rcases hkp with hkp | hkp
        · obtain ⟨rfl, hk⟩ := hW k p hkp
          exact ⟨hendD D hD hσ k hk, hendD D hD hσ k hk⟩
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact ⟨(mem_terms_of_mem_eqs (hD rfl)).1, hmD D hD⟩
          · exact ⟨(mem_terms_of_mem_eqs (hD rfl)).2, hmD D hD⟩
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        have h₁ : (t₁, m) ∈ E.eqs := hE t₁ m (Or.inr ((hPmem _).mpr (Or.inl rfl)))
        have h₂ : (t₂, m) ∈ E.eqs := hE t₂ m (Or.inr ((hPmem _).mpr (Or.inr rfl)))
        exact (Cong.direct h₁).trans (Cong.direct h₂).symm
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        rcases hu with hu | hu
        · exact (hcov₁ u hu).imp_left fun ⟨hs, hn⟩ =>
            ⟨Or.inl (Or.inl hs), fun g us heq hon => Or.inl (Or.inl (hn g us heq hon))⟩
        · exact (hcov₂ u hu).imp_left fun ⟨hs, hn⟩ =>
            ⟨Or.inl (Or.inr hs), fun g us heq hon => Or.inl (Or.inr (hn g us heq hon))⟩
  | subsume f es =>
    obtain ⟨hf, rfl⟩ := hname f es rfl
    rw [Action.write] at hV
    rw [Action.mark] at hM
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hV
    obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp hM
    obtain rfl : ts = ts' := Option.some.inj (hts.symm.trans hts')
    set t := Term.app f ts with ht
    have hev : (Expr.app f es).eval σ = some t := by rw [Expr.eval_app_ctor, hts]; rfl
    have hbe : ∀ v ∈ (Expr.app f es).vars, (Env.lookup v σ).isSome := by simpa [Action.vars] using hb
    obtain ⟨W, hW, hmem⟩ := build_writes (.app f es) ho hbe
    have hh := build_headWrites ho hbe hev hW
    obtain ⟨hrows, -, hself, hcov⟩ := build_rows ho hbe hev hW
    have hnode : nodeSelf f ts ∈ W := (hmem _).mpr (Or.inr ⟨f, ts, rfl, .self hts, rfl⟩)
    have hmarker : Action.writes σ [.subsume f es, .expr (subRow f es)] =
        some ({(t, t)} ∪ ({(subRowT f ts, subRowT f ts)} ∪ ∅)) := by
      simp [Action.writes, Action.write, hts, subRow, ht]
    set Q : Set (Term × Term) := {(t, t)} ∪ ({(subRowT f ts, subRowT f ts)} ∪ ∅) with hQ
    have hQmem : ∀ q, q ∈ Q ↔ q = (t, t) ∨ q = (subRowT f ts, subRowT f ts) := by
      intro q
      rw [hQ]
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
    refine ⟨W ∪ Q, ?_, ?_⟩
    · rw [encodeAction_subsume]
      change Action.writes σ (encodeBuildWith { subsumption := true } (.app f es) ++
        [.subsume f es, .expr (subRow f es)]) = _
      rw [Action.writes_append, hW, Option.bind_some, hmarker,
        Option.map_some]
    -- The source row and the marker are no union-find rows.
    have hnotuf : ∀ k p, (ufRowT k p, ufRowT k p) ∈ Q → False := by
      intro k p hkp
      rcases (hQmem _).mp hkp with heq | heq
      · exact hf.ne_ufName (Term.app.inj (Prod.mk.inj heq).1).1.symm
      · exact subName_ne_ufName f (Term.app.inj (Prod.mk.inj heq).1).1.symm
    refine ⟨fun q hq => ?_, fun k p hkp => ?_, fun k p hkp => ?_, fun k p hkp D hD hσ => ?_,
      fun k p hkp D hD hσ => ?_, fun q hq E hE => ?_, fun q hq u hu => ?_, fun u hu => ?_⟩
    · rcases hq with hq | hq
      · rcases hh.shape q hq with hq | ⟨g, us, rfl, hs⟩ | ⟨g, us, _, hm⟩ | ⟨u, hu, _⟩
        · exact Or.inl hq
        · exact Or.inr (Or.inl ⟨g, us, rfl, Or.inl hs⟩)
        · exact hm.elim
        · exact hu.elim
      · rcases (hQmem q).mp hq with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr ⟨t, rfl, rfl⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨f, ts, rfl, rfl⟩))
    · rcases hkp with hkp | hkp
      · exact hh.down k p hkp
      · exact (hnotuf k p hkp).elim
    · rcases hkp with hkp | hkp
      · exact ⟨Or.inl (hh.selfLoop k p hkp).1, Or.inl (hh.selfLoop k p hkp).2⟩
      · exact (hnotuf k p hkp).elim
    · rcases hkp with hkp | hkp
      · exact hh.cong k p hkp D hD hσ
      · exact (hnotuf k p hkp).elim
    · rcases hkp with hkp | hkp
      · exact hh.ends k p hkp D hD hσ
      · exact (hnotuf k p hkp).elim
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact .direct (hE t t (Or.inl hself))
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact (hcov u (hu.elim id id)).imp_left fun ⟨hs, hn⟩ =>
        ⟨Or.inl hs, fun g us heq hon => Or.inl (hn g us heq hon)⟩
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨f, ts, rfl, Or.inr ((hQmem _).mpr (Or.inr rfl)), Or.inl hself, rfl⟩

/-- The compiled rows and marks of a head. -/
theorem actions_headWrites {σ : Env} : ∀ {as : List Action}, Actions.MinOverVars as →
    (∀ a ∈ as, ∀ f es, a = .subsume f es → SourceName f ∧ sub = true) →
    (∀ a ∈ as, ∀ v ∈ a.vars, (Env.lookup v σ).isSome) →
    ∀ {V : Set (Term × Term)} {M : Set Term}, Action.writes σ as = some V →
    Action.marks σ as = some M →
    ∃ V', Action.writes σ (encodeActionsWith { subsumption := sub } as) = some V' ∧ HeadWrites sub σ V V' M
  | [], _, _, _, V, M, hV, hM => by
      rw [Action.writes] at hV
      rw [Action.marks] at hM
      obtain rfl := Option.some.inj hV
      obtain rfl := Option.some.inj hM
      exact ⟨∅, rfl, HeadWrites.empty σ⟩
  | a :: as, ho, hname, hb, V, M, hV, hM => by
      rw [Action.writes] at hV
      rw [Action.marks] at hM
      obtain ⟨V₁, hV₁, hV⟩ := Option.bind_eq_some_iff.mp hV
      obtain ⟨V₂, hV₂, rfl⟩ := Option.map_eq_some_iff.mp hV
      obtain ⟨M₁, hM₁, hM⟩ := Option.bind_eq_some_iff.mp hM
      obtain ⟨M₂, hM₂, rfl⟩ := Option.map_eq_some_iff.mp hM
      obtain ⟨W₁, hW₁, hh₁⟩ := action_headWrites (ho a (by simp)) (hname a (by simp))
        (hb a (by simp)) hV₁ hM₁
      obtain ⟨W₂, hW₂, hh₂⟩ := actions_headWrites (fun x hx => ho x (by simp [hx]))
        (fun x hx => hname x (by simp [hx])) (fun x hx => hb x (by simp [hx])) hV₂ hM₂
      refine ⟨W₁ ∪ W₂, ?_, hh₁.union hh₂⟩
      rw [encodeActions_cons, Action.writes_append, hW₁, Option.bind_some, hW₂, Option.map_some]

/-! ### The firings of a run -/

theorem mem_runWrites_iff {R : List Rule} {db : Database} {q : Term × Term} :
    q ∈ RunWrites R db ↔ ∃ r ∈ R, ∃ σ W, QueryMatches db r.query σ ∧
      Action.writes σ r.actions = some W ∧ q ∈ W := by
  unfold RunWrites
  rw [Set.mem_sUnion]
  constructor
  · rintro ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩; exact ⟨r, hr, σ, W, hσ, hW, hq⟩
  · rintro ⟨r, hr, σ, W, hσ, hW, hq⟩; exact ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩

theorem mem_runMarks_iff {R : List Rule} {db : Database} {t : Term} :
    t ∈ RunMarks R db ↔ ∃ r ∈ R, ∃ σ X, QueryMatches db r.query σ ∧
      Action.marks σ r.actions = some X ∧ t ∈ X := by
  unfold RunMarks
  rw [Set.mem_sUnion]
  constructor
  · rintro ⟨X, ⟨r, hr, σ, hσ, hX⟩, ht⟩; exact ⟨r, hr, σ, X, hσ, hX, ht⟩
  · rintro ⟨r, hr, σ, X, hσ, hX, ht⟩; exact ⟨X, ⟨r, hr, σ, hσ, hX⟩, ht⟩

theorem writes_subset_runWrites' {R : List Rule} {db : Database} {r : Rule} (hr : r ∈ R)
    {σ : Env} (hσ : QueryMatches db r.query σ) {W : Set (Term × Term)}
    (hW : Action.writes σ r.actions = some W) : W ⊆ RunWrites R db :=
  fun _ hq => mem_runWrites_iff.mpr ⟨r, hr, σ, W, hσ, hW, hq⟩

theorem marks_subset_runMarks' {R : List Rule} {db : Database} {r : Rule} (hr : r ∈ R)
    {σ : Env} (hσ : QueryMatches db r.query σ) {X : Set Term}
    (hX : Action.marks σ r.actions = some X) : X ⊆ RunMarks R db :=
  fun _ ht => mem_runMarks_iff.mpr ⟨r, hr, σ, X, hσ, hX, ht⟩

/-- The conditions on a source rule the round correspondence uses. A source subsume
requires enabled subsumption; this clause rules out source marks in plain mode. -/
structure RuleOk (sub : Bool) (r : Rule) : Prop where
  query : QueryOk r.query
  keyed : Query.VarsKeyed r.query
  heads : r.HeadScoped
  minOverVars : Actions.MinOverVars r.actions
  names : ∀ a ∈ r.actions, ∀ f es, a = .subsume f es → SourceName f ∧ sub = true

theorem encodeRule_query (r : Rule) :
    (encodeRuleWith { subsumption := sub } r).query = (encodeQueryWith {} r.query 0).1 := rfl

theorem encodeRule_actions (r : Rule) :
    (encodeRuleWith { subsumption := sub } r).actions = encodeActionsWith { subsumption := sub } r.actions := rfl

/-- A firing of a source rule, with its source writes and marks and its compiled rows. The
compiled head marks exactly the rows the source head marks. -/
structure Firing (sub : Bool) (src d : Database) (R : List Rule) (r : Rule) (σ : Env)
    (V V' : Set (Term × Term)) (M : Set Term) : Prop where
  mem : r ∈ R
  qmatch : QueryMatches src r.query σ
  writes : Action.writes σ r.actions = some V
  marks : Action.marks σ r.actions = some M
  compiled : Action.writes σ (encodeActionsWith { subsumption := sub } r.actions) = some V'
  head : HeadWrites sub σ V V' M
  src_sub : V ⊆ RunWrites R src
  src_marks : M ⊆ RunMarks R src
  tgt_sub : V' ⊆ RunWrites (R.map (encodeRuleWith { subsumption := sub })) d
  tgt_marks : M ⊆ RunMarks (R.map (encodeRuleWith { subsumption := sub })) d

variable {src d : Database}

/-- Every source firing at a canonical state has a compiled firing with the same source
bindings. -/
theorem firing_data (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk sub r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {r : Rule} (hr : r ∈ R) {σ : Env} (hσ : QueryMatches src r.query σ) :
    ∃ V V' M, Firing sub src d R r σ V V' M := by
  have hok := hR r hr
  obtain ⟨V, hV⟩ := hfire r hr σ hσ
  obtain ⟨M, hM⟩ : ∃ M, Action.marks σ r.actions = some M := by
    apply Option.isSome_iff_exists.mp
    rw [Action.marks_isSome, hV]
    rfl
  have hbound : ∀ a ∈ r.actions, ∀ v ∈ a.vars, (Env.lookup v σ).isSome := by
    intro a ha v hv
    apply Env.lookup_isSome_iff_mem_dom.mpr
    exact hσ.1.1.mem_iff.mpr (Actions.vars_subset_of_scoped hok.heads a ha v hv)
  obtain ⟨V', hV', hhead⟩ := actions_headWrites hok.minOverVars hok.names hbound hV hM
  obtain ⟨M', hM'⟩ : ∃ M', Action.marks σ (encodeActionsWith { subsumption := sub } r.actions) = some M' := by
    apply Option.isSome_iff_exists.mp
    rw [Action.marks_isSome, hV']
    rfl
  have hMM : M' = M := encodeActions_marks hM' hM
  subst M'
  obtain ⟨σ', hσ', hag⟩ := fire_complete h hc hw hok.query hσ
  have hag' : ∀ a ∈ r.actions, ∀ v ∈ a.vars, Env.lookup v σ' = Env.lookup v σ :=
    fun a ha v hv => hag v (Actions.vars_subset_of_scoped hok.heads a ha v hv)
  refine ⟨V, V', M, hr, hσ, hV, hM, hV', hhead, writes_subset_runWrites' hr hσ hV,
    marks_subset_runMarks' hr hσ hM, ?_, ?_⟩
  · have hmem : encodeRuleWith { subsumption := sub } r ∈ R.map (encodeRuleWith { subsumption := sub }) := List.mem_map_of_mem hr
    have hW' : Action.writes σ' (encodeRuleWith { subsumption := sub } r).actions = some V' := by
      rw [encodeRule_actions, actions_writes_agreeOn r.actions hag']
      exact hV'
    exact writes_subset_runWrites' hmem hσ' hW'
  · have hmem : encodeRuleWith { subsumption := sub } r ∈ R.map (encodeRuleWith { subsumption := sub }) := List.mem_map_of_mem hr
    have hX' : Action.marks σ' (encodeRuleWith { subsumption := sub } r).actions = some M := by
      rw [encodeRule_actions, actions_marks_agreeOn r.actions hag']
      exact hM'
    exact marks_subset_runMarks' hmem hσ' hX'

/-- Every compiled write comes from a source firing. -/
theorem firing_of_compiled (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk sub r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {q : Term × Term} (hq : q ∈ RunWrites (R.map (encodeRuleWith { subsumption := sub })) d) :
    ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ q ∈ V' := by
  obtain ⟨r', hr', σ', W', hσ', hW', hqW⟩ := mem_runWrites_iff.mp hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  have hok := hR r hr
  rw [encodeRule_query] at hσ'
  obtain ⟨hσ, hag⟩ := fire_sound h hc hw hok.query hok.keyed hσ'
  obtain ⟨V, V', M, hf⟩ := firing_data h hc hw hR hfire hr hσ
  have hag' : ∀ a ∈ r.actions, ∀ v ∈ a.vars,
      Env.lookup v (restrict (Query.vars r.query) σ') = Env.lookup v σ' :=
    fun a ha v hv => hag v (Actions.vars_subset_of_scoped hok.heads a ha v hv)
  have hV' : Action.writes σ' (encodeActionsWith { subsumption := sub } r.actions) = some V' := by
    rw [← actions_writes_agreeOn r.actions hag']
    exact hf.compiled
  rw [encodeRule_actions, hV'] at hW'
  obtain rfl := Option.some.inj hW'
  exact ⟨r, _, V, V', M, hf, hqW⟩

/-- Every compiled mark comes from a source firing. -/
theorem firing_of_compiled_mark (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk sub r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {t : Term} (ht : t ∈ RunMarks (R.map (encodeRuleWith { subsumption := sub })) d) :
    ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ t ∈ M := by
  obtain ⟨r', hr', σ', X', hσ', hX', htX⟩ := mem_runMarks_iff.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  have hok := hR r hr
  rw [encodeRule_query] at hσ'
  obtain ⟨hσ, hag⟩ := fire_sound h hc hw hok.query hok.keyed hσ'
  obtain ⟨V, V', M, hf⟩ := firing_data h hc hw hR hfire hr hσ
  have hag' : ∀ a ∈ r.actions, ∀ v ∈ a.vars,
      Env.lookup v (restrict (Query.vars r.query) σ') = Env.lookup v σ' :=
    fun a ha v hv => hag v (Actions.vars_subset_of_scoped hok.heads a ha v hv)
  obtain ⟨M', hM'⟩ : ∃ M', Action.marks (restrict (Query.vars r.query) σ')
      (encodeActionsWith { subsumption := sub } r.actions) = some M' := by
    apply Option.isSome_iff_exists.mp
    rw [Action.marks_isSome, hf.compiled]
    rfl
  have hMM : M' = M := encodeActions_marks hM' hf.marks
  subst M'
  rw [encodeRule_actions, ← actions_marks_agreeOn r.actions hag', hM'] at hX'
  have hXM : M = X' := Option.some.inj hX'
  subst X'
  exact ⟨r, _, V, V', M, hf, htX⟩

/-- Every source write comes from a firing with compiled rows. -/
theorem firing_of_source (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk sub r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {q : Term × Term} (hq : q ∈ RunWrites R src) :
    ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ q ∈ V := by
  obtain ⟨r, hr, σ, W, hσ, hW, hqW⟩ := mem_runWrites_iff.mp hq
  obtain ⟨V, V', M, hf⟩ := firing_data h hc hw hR hfire hr hσ
  rw [hf.writes] at hW
  obtain rfl := Option.some.inj hW
  exact ⟨r, σ, V, V', M, hf, hqW⟩

/-- Every source mark comes from a firing with compiled rows. -/
theorem firing_of_source_mark (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk sub r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {t : Term} (ht : t ∈ RunMarks R src) :
    ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ t ∈ M := by
  obtain ⟨r, hr, σ, X, hσ, hX, htX⟩ := mem_runMarks_iff.mp ht
  obtain ⟨V, V', M, hf⟩ := firing_data h hc hw hR hfire hr hσ
  rw [hf.marks] at hX
  obtain rfl := Option.some.inj hX
  exact ⟨r, σ, V, V', M, hf, htX⟩

/-- A source run and its compiled run preserve the relation. -/
theorem run_rel (h : Rel sub src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk sub r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    (havoid : ∀ t ∈ (RunRules R src).terms, t.SourceShaped) :
    Rel sub (RunRules R src) (RunRules (R.map (encodeRuleWith { subsumption := sub })) d) := by
  set src' := RunRules R src with hsrc'
  set d' := RunRules (R.map (encodeRuleWith { subsumption := sub })) d with hd'
  have hseqs : src'.eqs = src.eqs ∪ RunWrites R src := by rw [hsrc', RunRules.eq_pair]
  have hssub : src'.subsumed = src.subsumed ∪ RunMarks R src := by rw [hsrc', RunRules.eq_pair]
  have hdeqs : d'.eqs = d.eqs ∪ RunWrites (R.map (encodeRuleWith { subsumption := sub })) d := by
    rw [hd', RunRules.eq_pair]
  have hdsub : d'.subsumed = d.subsumed ∪ RunMarks (R.map (encodeRuleWith { subsumption := sub })) d := by
    rw [hd', RunRules.eq_pair]
  have hdmono : d.eqs ⊆ d'.eqs := hdeqs ▸ Set.subset_union_left
  have hsmono : src.eqs ⊆ src'.eqs := hseqs ▸ Set.subset_union_left
  have hsrcW : RunWrites R src ⊆ src'.eqs := hseqs ▸ Set.subset_union_right
  have hdW : RunWrites (R.map (encodeRuleWith { subsumption := sub })) d ⊆ d'.eqs := hdeqs ▸ Set.subset_union_right
  have hkeys_mono : Keys d ⊆ Keys d' := Keys.mono hdmono
  -- A new equation of the compiled state comes from a firing.
  have hnew : ∀ q ∈ d'.eqs, q ∈ d.eqs ∨
      ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ q ∈ V' := by
    intro q hq
    have : q ∈ d.eqs ∪ RunWrites (R.map (encodeRuleWith { subsumption := sub })) d := hdeqs ▸ hq
    rcases this with hq | hq
    · exact Or.inl hq
    · exact Or.inr (firing_of_compiled h hc hw hR hfire hq)
  -- The bindings of a firing are source representatives, held before and after the round.
  have hbind : ∀ {r : Rule} {σ : Env} {V V' : Set (Term × Term)} {M : Set Term},
      Firing sub src d R r σ V V' M → ∀ v w, Env.lookup v σ = some w → w ∈ src'.terms :=
    fun hf v w hvw =>
      Database.mem_terms_of_eqs hsmono (hf.qmatch.1.2 (v, w) (Env.mem_of_lookup hvw)).1
  -- A mark of a firing is a source-shaped term the source holds afterwards.
  have hmarkTerm : ∀ {r : Rule} {σ : Env} {V V' : Set (Term × Term)} {M : Set Term},
      Firing sub src d R r σ V V' M → ∀ t ∈ M, t ∈ src'.terms ∧ t.SourceShaped := by
    intro r σ V V' M hf t ht
    obtain ⟨f, as, rfl, -, -, hv⟩ := hf.head.marks t ht
    have hmem : Term.app f as ∈ src'.terms := (mem_terms_of_mem_eqs (hsrcW (hf.src_sub hv))).1
    exact ⟨hmem, havoid _ hmem⟩
  -- The kinds of new equations.
  have hrow : ∀ k p, Row d' k p → Row d k p ∨
      ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ (ufRowT k p, ufRowT k p) ∈ V' := fun k p hr => hnew _ hr
  have hnode_new : ∀ f as, Node d' f as → Node d f as ∨
      ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ selfRow (.app f as) ∈ V' := by
    intro f as hn
    rcases hnew _ hn with hn | ⟨r, σ, V, V', M, hf, hV'⟩
    · exact Or.inl hn
    · right
      refine ⟨r, σ, V, V', M, hf, ?_⟩
      rcases hf.head.shape _ hV' with ⟨k, p, heq⟩ | ⟨g, bs, heq, hs⟩ | ⟨g, bs, heq, _⟩ |
        ⟨t, ht, heq⟩
      · exact (nodeName_ne_ufName f (Term.app.inj (Prod.mk.inj heq).1).1).elim
      · obtain ⟨rfl, rfl⟩ := nodeRowT_inj (Prod.mk.inj heq).1
        exact hs
      · exact (subName_ne_nodeName g f (Term.app.inj (Prod.mk.inj heq).1).1.symm).elim
      · exact (Term.SourceShaped.ne_nodeRowT (hmarkTerm hf t ht).2 f as (Prod.mk.inj heq).1.symm).elim
  have hmarker_new : ∀ f as, Marker d' f as → Marker d f as ∨
      ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ Term.app f as ∈ M := by
    intro f as hm
    rcases hnew _ hm with hm | ⟨r, σ, V, V', M, hf, hV'⟩
    · exact Or.inl hm
    · right
      refine ⟨r, σ, V, V', M, hf, ?_⟩
      rcases hf.head.shape _ hV' with ⟨k, p, heq⟩ | ⟨g, bs, heq, _⟩ | ⟨g, bs, heq, hM⟩ |
        ⟨t, ht, heq⟩
      · exact (subName_ne_ufName f (Term.app.inj (Prod.mk.inj heq).1).1).elim
      · exact (subName_ne_nodeName f g (Term.app.inj (Prod.mk.inj heq).1).1).elim
      · obtain ⟨rfl, rfl⟩ := subRowT_inj (Prod.mk.inj heq).1
        exact hM
      · exact (Term.SourceShaped.ne_subRowT (hmarkTerm hf t ht).2 f as (Prod.mk.inj heq).1.symm).elim
  have hdiag : d'.Diag := by
    intro q hq
    rcases hnew q hq with hq | ⟨r, σ, V, V', M, hf, hqV⟩
    · exact h.diag q hq
    · rcases hf.head.shape q hqV with ⟨k, p, rfl⟩ | ⟨g, bs, rfl, _⟩ | ⟨g, bs, rfl, _⟩ |
        ⟨t, _, rfl⟩ <;> rfl
  have hkeys_sub : ∀ k p, Row d' k p → k ∈ src'.terms := by
    intro k p hr
    rcases hrow k p hr with hr | ⟨r, σ, V, V', M, hf, hkp⟩
    · exact Database.mem_terms_of_eqs hsmono (h.key_mem_src hr.mem_keys)
    · exact (hf.head.ends k p hkp src' (hf.src_sub.trans hsrcW) (hbind hf)).1
  have hself : ∀ k p, Row d' k p → Row d' k k ∧ Row d' p p := by
    intro k p hr
    rcases hrow k p hr with hr | ⟨r, σ, V, V', M, hf, hkp⟩
    · exact ⟨(h.selfLoop k p hr).1.mono hdmono, (h.selfLoop k p hr).2.mono hdmono⟩
    · obtain ⟨h₁, h₂⟩ := hf.head.selfLoop k p hkp
      exact ⟨hdW (hf.tgt_sub h₁), hdW (hf.tgt_sub h₂)⟩
  -- Every new source term is covered by a compiled self-loop and node row.
  have hcover : ∀ t ∈ src'.terms, t ∈ src.terms ∨
      ∃ r σ V V' M, Firing sub src d R r σ V V' M ∧ selfRow t ∈ V' ∧
        ∀ g us, t = .app g us → sub = true → nodeSelf g us ∈ V' := by
    intro t ht
    obtain ⟨q, hq, hsub⟩ := ht
    have : q ∈ src.eqs ∪ RunWrites R src := hseqs ▸ hq
    rcases this with hq | hq
    · exact Or.inl ⟨q, hq, hsub⟩
    · obtain ⟨r, σ, V, V', M, hf, hqV⟩ := firing_of_source h hc hw hR hfire hq
      rcases hf.head.covers q hqV t hsub with ⟨hself', hn⟩ | ⟨v, w, hw', htw⟩
      · exact Or.inr ⟨r, σ, V, V', M, hf, hself', hn⟩
      · have hwsrc : w ∈ src.terms := (hf.qmatch.1.2 (v, w) (Env.mem_of_lookup hw')).1
        exact Or.inl (src.subtermClosed w hwsrc htw)
  have hkeys : Keys d' = src'.terms := by
    apply Set.Subset.antisymm
    · rintro k ⟨p, hr⟩
      exact hkeys_sub k p hr
    · intro t ht
      rcases hcover t ht with ht | ⟨r, σ, V, V', M, hf, hself', -⟩
      · exact hkeys_mono (h.mem_keys_of_src ht)
      · exact ⟨t, hdW (hf.tgt_sub hself')⟩
  have hnodes : ∀ f as, (Node d' f as → Term.app f as ∈ Keys d') ∧
      (Term.app f as ∈ Keys d' → sub = true → Node d' f as) := by
    intro f as
    constructor
    · intro hn
      rcases hnode_new f as hn with hn | ⟨r, σ, V, V', M, hf, hs⟩
      · exact hkeys_mono (h.shape.nodes f as hn)
      · exact ⟨_, hdW (hf.tgt_sub hs)⟩
    · intro hk hon
      rw [hkeys] at hk
      rcases hcover _ hk with ht | ⟨r, σ, V, V', M, hf, -, hn⟩
      · exact (h.nodes f as (h.mem_keys_of_src ht) hon).mono hdmono
      · exact hdW (hf.tgt_sub (hn f as rfl hon))
  have hmarker : ∀ f as, Marker d' f as ↔ Term.app f as ∈ src'.subsumed := by
    intro f as
    rw [hssub]
    constructor
    · intro hm
      rcases hmarker_new f as hm with hm | ⟨r, σ, V, V', M, hf, hM⟩
      · exact Or.inl ((h.marker f as).mp hm)
      · exact Or.inr (hf.src_marks hM)
    · rintro (hs | hs)
      · exact ((h.marker f as).mpr hs).mono hdmono
      · obtain ⟨r, σ, V, V', M, hf, hM⟩ := firing_of_source_mark h hc hw hR hfire hs
        obtain ⟨g, bs, heq, hmk, -, -⟩ := hf.head.marks _ hM
        obtain ⟨rfl, rfl⟩ := Term.app.inj heq
        exact hdW (hf.tgt_sub hmk)
  have hmarker_key : ∀ f as, Marker d' f as → Term.app f as ∈ Keys d' := by
    intro f as hm
    rcases hmarker_new f as hm with hm | ⟨r, σ, V, V', M, hf, hM⟩
    · exact hkeys_mono (h.marker_key hm)
    · obtain ⟨g, bs, heq, -, hs, -⟩ := hf.head.marks _ hM
      obtain ⟨rfl, rfl⟩ := Term.app.inj heq
      exact ⟨_, hdW (hf.tgt_sub hs)⟩
  have hshape : Shape d' := by
    refine ⟨fun q hq => ?_, fun k hk => havoid k (hkeys ▸ hk), fun k p hr => ?_,
      fun f as hn => (hnodes f as).1 hn, hmarker_key⟩
    · rcases hnew q hq with hq | ⟨r, σ, V, V', M, hf, hqV⟩
      · rcases h.shape.eqs q hq with hq | hq | hq | ⟨t, rfl, ht⟩
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inl hq))
        · exact Or.inr (Or.inr (Or.inr ⟨t, rfl, hkeys_mono ht⟩))
      · rcases hf.head.shape q hqV with hq | ⟨g, bs, rfl, _⟩ | ⟨g, bs, rfl, _⟩ | ⟨t, ht, rfl⟩
        · exact Or.inl hq
        · exact Or.inr (Or.inl ⟨g, bs, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨g, bs, rfl⟩))
        · obtain ⟨g, bs, rfl, -, hs, -⟩ := hf.head.marks t ht
          exact Or.inr (Or.inr (Or.inr ⟨_, rfl, ⟨_, hdW (hf.tgt_sub hs)⟩⟩))
    · rcases hrow k p hr with hr | ⟨r, σ, V, V', M, hf, hkp⟩
      · exact hkeys_mono (h.parent_mem_keys hr)
      · exact ⟨_, hdW (hf.tgt_sub (hf.head.selfLoop k p hkp).2)⟩
  have hcong : ∀ a b, Cong src' a b ↔ Cong (view d') a b := by
    intro a b
    constructor
    · intro hab
      refine Cong.replay (D := src') (E := view d') (fun q hq => ?_) hab
      have : q ∈ src.eqs ∪ RunWrites R src := hseqs ▸ hq
      rcases this with hq | hq
      · exact Cong.mono_eqs (view_mono hdmono) ((h.cong q.1 q.2).mp (.direct hq))
      · obtain ⟨r, σ, V, V', M, hf, hqV⟩ := firing_of_source h hc hw hR hfire hq
        exact hf.head.derivable q hqV (view d') fun k p hkp => hdW (hf.tgt_sub hkp)
    · intro hab
      refine Cong.replay (D := view d') (E := src') (fun q hq => ?_) hab
      rcases hrow q.1 q.2 hq with hr | ⟨r, σ, V, V', M, hf, hkp⟩
      · exact Cong.mono_eqs hsmono ((h.cong q.1 q.2).mpr hr.cong_view)
      · exact hf.head.cong q.1 q.2 hkp src' (hf.src_sub.trans hsrcW) (hbind hf)
  -- A new mark is a source row; no new union-find row is marked.
  have hnewmark : ∀ t ∈ RunMarks (R.map (encodeRuleWith { subsumption := sub })) d,
      ∃ f as, t = Term.app f as ∧ Term.app f as ∈ Keys d' ∧ Marker d' f as ∧
        CongList src' as as := by
    intro t ht
    obtain ⟨r, σ, V, V', M, hf, hM⟩ := firing_of_compiled_mark h hc hw hR hfire ht
    obtain ⟨f, as, rfl, hmk, hs, hv⟩ := hf.head.marks t hM
    have hmem : Term.app f as ∈ src'.terms := (mem_terms_of_mem_eqs (hsrcW (hf.src_sub hv))).1
    refine ⟨f, as, rfl, ⟨_, hdW (hf.tgt_sub hs)⟩, hdW (hf.tgt_sub hmk), ?_⟩
    rw [CongList.forall₂]
    exact List.forall₂_same.mpr fun a ha =>
      Database.toCong (src'.subtermClosed _ hmem (Term.arg_subterms ha (Term.self_mem_subterms _)))
  have huf_marks : ∀ k p, ufRowT k p ∈ d'.subsumed → ufRowT k p ∈ d.subsumed := by
    intro k p hs
    rw [hdsub] at hs
    rcases hs with hs | hs
    · exact hs
    · obtain ⟨f, as, heq, hkey, -, -⟩ := hnewmark _ hs
      exact (Term.SourceShaped.ne_ufRowT (hshape.keys _ hkey) k p heq.symm).elim
  exact {
    diag := hdiag
    shape := hshape
    finite := RunRules.finite_eqs h.finite _
    marks := by
      intro t ht
      rw [hdsub] at ht
      rcases ht with ht | ht
      · rcases h.marks t ht with ⟨k, p, q, heq, hkp, hkq, hpq, hlt⟩ |
          ⟨f, bs, as, heq, hkey, hm, hcl⟩
        · exact Or.inl ⟨k, p, q, heq, hkp.mono hdmono, hkq.mono hdmono, hpq.mono hdmono, hlt⟩
        · refine Or.inr ⟨f, bs, as, heq, hkeys_mono hkey, hm.mono hdmono, ?_⟩
          rw [CongList.forall₂] at hcl ⊢
          exact hcl.imp fun _ _ hc' => Cong.mono_eqs hsmono hc'
      · obtain ⟨f, as, rfl, hkey, hm, hcl⟩ := hnewmark t ht
        exact Or.inr ⟨f, as, as, rfl, hkey, hm, hcl⟩
    down := by
      intro k p hr
      rcases hrow k p hr with hr | ⟨r, σ, V, V', M, hf, hkp⟩
      · exact h.down k p hr
      · exact hf.head.down k p hkp
    selfLoop := hself
    keys := hkeys
    nodes := fun f as hk => (hnodes f as).2 hk
    plain := by
      intro hoff
      rw [hssub, h.plain hoff]
      have hsf : ∀ r ∈ R, Actions.SubsumeFree r.actions := by
        intro r hr a ha
        cases a with
        | expr e => trivial
        | union a b => trivial
        | subsume f es =>
          have hon := ((hR r hr).names _ ha f es rfl).2
          simp [hoff] at hon
      rw [RunMarks.eq_empty hsf, Set.union_empty]
    marker := hmarker
    cong := hcong
    liveCong := by
      intro k p hr
      by_cases hs : ufRowT k p ∈ d'.subsumed
      · obtain ⟨q, hkp, -⟩ := h.uf_mark (huf_marks k p hs)
        have := h.liveCong k p hkp
        exact Cong.mono_eqs (d := liveView d) (e := liveView d')
          (fun q hq => Edge.mono h.diag h.shape hdiag hshape hdmono huf_marks hq) this
      · exact (Edge.of_row hdiag hshape hr hs).cong_liveView }

end Egglog.Congruence
