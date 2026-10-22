import EgglogSemantics.Proofs.Source.Execution

/-! Constructor names and arities across constructor-source executions. -/

namespace Egglog

/-- Every application inside `t` is one `P` applies at that arity. -/
def Term.CtorsIn (P : Program) (t : Term) : Prop :=
  ∀ g bs, Term.app g bs ∈ t.subterms → (g, bs.length) ∈ P.ctors

@[simp] theorem Term.ctorsIn_lit {P : Program} {l : Lit} : Term.CtorsIn P (.lit l) := by
  intro g bs hs
  exact absurd (Term.subterms_lit ▸ hs) (by simp)

theorem Term.ctorsIn_app {P : Program} {f : FnName} {args : List Term} :
    Term.CtorsIn P (.app f args) ↔
      (f, args.length) ∈ P.ctors ∧ ∀ a ∈ args, Term.CtorsIn P a := by
  simp only [Term.CtorsIn, Term.subterms_app, Set.mem_insert_iff, Set.mem_iUnion,
    exists_prop]
  constructor
  · intro h
    refine ⟨h f args (Or.inl rfl), fun a ha g bs hs => h g bs (Or.inr ⟨a, ha, hs⟩)⟩
  · rintro ⟨hf, h⟩ g bs hs
    rcases hs with hs' | ⟨a, ha, hs'⟩
    · obtain ⟨rfl, rfl⟩ : g = f ∧ bs = args := by
        constructor <;> [exact (Term.app.inj hs').1; exact (Term.app.inj hs').2]
      exact hf
    · exact h a ha g bs hs'

/-- Every application the state holds is one `P` applies at that arity. -/
def Database.CtorsIn (db : Database) (P : Program) : Prop :=
  ∀ f as, Term.app f as ∈ db.terms → (f, as.length) ∈ P.ctors

theorem Database.CtorsIn.term {db : Database} {P : Program} (hw : db.WF) (h : db.CtorsIn P)
    {t : Term} (ht : t ∈ db.terms) : Term.CtorsIn P t :=
  fun g bs hs => h g bs (hw.subtermClosed t ht hs)

theorem Database.empty_ctorsIn {P : Program} : Database.empty.CtorsIn P := by
  intro f as ht; exact absurd ht (by simp)

mutual

/-- **An expression whose applications `P` makes evaluates to a term whose applications `P`
makes**, in an environment whose bindings do. Building applies a head `Expr.ctors` recorded,
and `min` returns one of its operands, exactly as for `Expr.eval_litFree`. -/
theorem Expr.eval_ctorsIn {P : Program} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.CtorsIn P t) :
    ∀ (e : Expr) {t : Term}, (∀ fk ∈ e.ctors, fk ∈ P.ctors) →
      e.eval σ = some t → Term.CtorsIn P t
  | .lit _, _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      exact Term.ctorsIn_lit
  | .var v, t, _, he => hσ v t he
  | .app f args, t, hc, he => by
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      refine Term.ctorsIn_app.mpr ⟨?_, ?_⟩
      · rw [Expr.evalList_length hts]
        exact hc _ (by rw [Expr.ctors]; exact List.mem_cons_self)
      · exact Expr.evalList_ctorsIn hσ args
          (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk)) hts
  | .min a b, t, hc, he => by
      rw [Expr.eval_min, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, hmap⟩ := he
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rcases Term.least_eq_or x y with h | h <;> rw [h]
      · exact Expr.eval_ctorsIn hσ a
          (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_append_left _ hk)) hx
      · exact Expr.eval_ctorsIn hσ b
          (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_append_right _ hk)) hy
@[inherit_doc Expr.eval_ctorsIn]
theorem Expr.evalList_ctorsIn {P : Program} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.CtorsIn P t) :
    ∀ (es : List Expr) {ts : List Term}, (∀ fk ∈ Expr.ctorsList es, fk ∈ P.ctors) →
      Expr.evalList es σ = some ts → ∀ t ∈ ts, Term.CtorsIn P t
  | [], _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp
  | e :: es, ts, hc, he => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_ctorsIn hσ e
          (fun fk hk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_left _ hk)) hu
      · exact Expr.evalList_ctorsIn hσ es
          (fun fk hk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_right _ hk))
          hus t ht'

end

/-- An action applies only constructor names and arities found in the source program. -/
def Action.CtorsIn (a : Action) (P : Program) : Prop := ∀ fk ∈ a.ctors, fk ∈ P.ctors

/-- `Action.CtorsIn` at every action a command runs. -/
def Cmd.CtorsIn (c : Cmd) (P : Program) : Prop :=
  ∀ r ∈ c.rules, ∀ a ∈ r.actions, a.CtorsIn P

/-- A command's constructor uses are included in its program. -/
theorem Cmd.CtorsIn.of_domain {P : Program} (_hdom : P.Fragment)
    {c : Cmd} (hc : c ∈ P.commands) : c.CtorsIn P := by
  intro r hr a ha fk hk
  exact mem_program_ctors hc (List.mem_flatMap.mpr ⟨r, hr,
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)⟩)

theorem Term.CtorsIn.subterm {P : Program} {t u : Term} (h : t.CtorsIn P)
    (hu : u ∈ t.subterms) : u.CtorsIn P := fun f as hs => h f as (hs.trans hu)

theorem Database.CtorsIn.lookup {db : Database} {P : Program} (hw : db.WF)
    (h : db.CtorsIn P) {σ : Env} (hs : ∀ b ∈ σ, b.2 ∈ db.terms) :
    ∀ v t, Env.lookup v σ = some t → Term.CtorsIn P t := fun v t hv =>
  h.term hw (hs (v, t) (Env.mem_of_lookup hv))

theorem Action.evalTerms_ctorsIn {P : Program} {σ : Env} {a : Action} (ha : a.CtorsIn P)
    (hs : ∀ v t, Env.lookup v σ = some t → t.CtorsIn P) :
    a.EvalTerms σ (Term.CtorsIn P) := by
  cases a with
  | expr e | delete e => exact fun t ht => Expr.eval_ctorsIn hs e ha ht
  | union a b =>
    exact ⟨fun t ht => Expr.eval_ctorsIn hs a
      (fun fk hk => ha fk (List.mem_append_left _ hk)) ht,
      fun t ht => Expr.eval_ctorsIn hs b
      (fun fk hk => ha fk (List.mem_append_right _ hk)) ht⟩

theorem evalAction_ctorsIn {σ : Env} {db db' : Database} {P : Program}
    (hw : db.WF) (h : db.CtorsIn P)
    (hs : ∀ v t, Env.lookup v σ = some t → t.CtorsIn P)
    {a : Action} (ha : a.CtorsIn P) (hv : evalAction σ db a = some db') : db'.CtorsIn P := by
  have hh := evalAction_preserves (P := Term.CtorsIn P)
    (fun _ ht _ hsub => ht.subterm hsub) (fun _ ht => h.term hw ht)
    (Action.evalTerms_ctorsIn ha hs) hv
  exact fun f as ht => hh _ ht f as (.refl _)

theorem evalActions_ctorsIn {σ : Env} {db db' : Database} {P : Program}
    (hw : db.WF) (h : db.CtorsIn P)
    (hs : ∀ v t, Env.lookup v σ = some t → t.CtorsIn P)
    {as : List Action} (ha : ∀ a ∈ as, a.CtorsIn P) (hv : evalActions σ db as = some db') :
    db'.CtorsIn P := by
  have hh := evalActions_preserves (P := Term.CtorsIn P)
    (fun _ ht _ hsub => ht.subterm hsub) (fun _ ht => h.term hw ht)
    (fun a ha' => Action.evalTerms_ctorsIn (ha a ha') hs) hv
  exact fun f as ht => hh _ ht f as (.refl _)

theorem evalLocalActions_ctorsIn {db db' : Database} {P : Program} (hw : db.WF)
    (h : db.CtorsIn P) {as : List Action} (hl : ∀ a ∈ as, a.CtorsIn P) {σ : Env}
    (hs : ∀ b ∈ σ, b.2 ∈ db.terms) (hv : evalActions σ db as = some db') : db'.CtorsIn P :=
  evalActions_ctorsIn hw h (h.lookup hw hs) hl hv

structure Database.CtorsInState (db : Database) (P : Program) : Prop where
  terms : db.CtorsIn P

theorem Database.empty_ctorsInState {P : Program} : Database.empty.CtorsInState P :=
  ⟨Database.empty_ctorsIn⟩

theorem Database.CtorsInState.runRules {R : List Rule} {db : Database} {P : Program}
    (hw : db.WF) (h : db.CtorsInState P) (hn : ∀ r ∈ R, ∀ a ∈ r.actions, a.CtorsIn P) :
    (RunRules R db).CtorsInState P := by
  refine ⟨?_⟩
  have hh := RunRules.preserves_evalTerms (R := R) (P := Term.CtorsIn P)
    (fun _ ht _ hsub => ht.subterm hsub) (fun _ ht => h.terms.term hw ht)
    (fun r hr σ hσ a ha => Action.evalTerms_ctorsIn (hn r hr a ha)
      (h.terms.lookup hw hσ.1.2))
  exact fun f as ht => hh _ ht f as (.refl _)

theorem cmdStep_ctorsIn {db db' : Database} {P : Program} (hw : db.WF)
    (h : db.CtorsInState P) {c : Cmd} (hn : c.CtorsIn P)
    (hs : CmdStep db c db') : db'.CtorsInState P := by
  cases c with
  | run R => subst db'; exact h.runRules hw hn
  | saturate R =>
    induction hs with
    | fixpoint => exact h.runRules hw hn
    | again _ _ ih => exact ih (RunRules.wf hw) (h.runRules hw hn)

theorem programStep_ctorsIn {db db' : Database} {P : Program} (hw : db.WF)
    (h : db.CtorsInState P) {p : List Cmd} (hn : ∀ c ∈ p, c.CtorsIn P)
    (hs : ProgramStep db p db') : db'.CtorsInState P := by
  induction hs with
  | nil => exact h
  | cons hc _ ih =>
    exact ih (hc.wf hw) (cmdStep_ctorsIn hw h (hn _ (by simp)) hc)
      (fun c hc => hn c (by simp [hc]))

theorem ctorsIn_of_prefixStep {P : Program} (hdom : P.Fragment) {p : List Cmd}
    (hsub : ∀ c ∈ p, c ∈ P.commands) {sd : Database} (hs : ProgramStep Database.empty p sd) :
    sd.CtorsIn P :=
  (programStep_ctorsIn Database.WF.empty Database.empty_ctorsInState
    (fun c hc => Cmd.CtorsIn.of_domain hdom (hsub c hc)) hs).terms

end Egglog
