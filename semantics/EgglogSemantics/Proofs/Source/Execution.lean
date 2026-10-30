import EgglogSemantics.Proofs.Source.Domain
import EgglogSemantics.Source.Names
import EgglogSemantics.Proofs.Scope
import EgglogSemantics.Proofs.StatePreservation

/-! Execution properties of the constructor source fragment. Scoped rule heads use
arbitrary constructor names; the domain's union condition prevents literal unions. These
facts are independent of either compiler or proof annotations. -/

namespace Egglog

mutual
/-- **A head an expression applies is one of its `Expr.ctors`.** `Expr.fns` deduplicates and
`Expr.ctors` carries arities; the two name the same heads. -/
theorem Expr.exists_ctor_of_mem_fns : ∀ {e : Expr} {g : FnName}, g ∈ e.fns →
    ∃ k, (g, k) ∈ e.ctors
  | .lit _, _, hg => absurd hg (by simp [Expr.fns])
  | .var _, _, hg => absurd hg (by simp [Expr.fns])
  | .app f args, g, hg => by
      rw [Expr.fns, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨args.length, by rw [Expr.ctors]; exact List.mem_cons_self⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk⟩
  | .min a b, g, hg => by
      rw [Expr.fns] at hg
      rcases List.mem_union_iff.mp hg with hg' | hg'
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_append_left _ hk⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_append_right _ hk⟩
@[inherit_doc Expr.exists_ctor_of_mem_fns]
theorem Expr.exists_ctorList_of_mem_fnsList : ∀ {es : List Expr} {g : FnName},
    g ∈ Expr.fnsList es → ∃ k, (g, k) ∈ Expr.ctorsList es
  | [], _, hg => absurd hg (by simp [Expr.fnsList])
  | e :: es, g, hg => by
      rw [Expr.fnsList] at hg
      rcases List.mem_union_iff.mp hg with hg' | hg'
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_left _ hk⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_right _ hk⟩
end

/-- A `(name, arity)` pair one command applies is one the whole program applies. -/
theorem mem_program_ctors {Q : Program} {c : Cmd} (hc : c ∈ Q.commands) {p : FnName × Nat}
    (hp : p ∈ c.ctors) : p ∈ Q.ctors := by
  rw [Program.ctors, List.mem_dedup]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, hp⟩)

/-- `Program.OrderingFree` at a member command. -/
theorem Program.OrderingFree.of_mem {P : Program} (h : Program.OrderingFree P)
    {c : Cmd} (hc : c ∈ P.commands) : c.OrderingFree := h.1 c hc

/-- No literal occurs in `t`. -/
def Term.LitFree (t : Term) : Prop := ∀ s ∈ t.subterms, ¬ s.isLit

theorem Term.litFree_app {f : FnName} {args : List Term} :
    Term.LitFree (.app f args) ↔ ∀ a ∈ args, Term.LitFree a := by
  simp only [Term.LitFree, Term.subterms_app, Set.mem_insert_iff, Set.mem_iUnion,
    exists_prop, forall_eq_or_imp]
  constructor
  · rintro ⟨-, h⟩ a ha s hs
    exact h s ⟨a, ha, hs⟩
  · rintro h
    refine ⟨by simp [Term.isLit], ?_⟩
    rintro s ⟨a, ha, hs⟩
    exact h a ha s hs

/-- No term the state holds is a literal. -/
def Database.LitFree (db : Database) : Prop := ∀ t ∈ db.terms, ¬ t.isLit

theorem Database.LitFree.term {db : Database} (hw : db.WF) (h : db.LitFree) {t : Term}
    (ht : t ∈ db.terms) : Term.LitFree t :=
  fun s hs => h s (hw.subtermClosed t ht hs)

theorem Database.empty_litFree : Database.empty.LitFree := by
  intro t ht; exact absurd ht (by simp)

/-! ##### Evaluation of a literal-free expression builds a literal-free term -/

mutual

/-- **A literal-free expression evaluates to a literal-free term**, in an environment whose
bindings are literal-free. Building wraps literal-free arguments, and `min` returns one of
its operands, so nothing an expression computes can introduce a literal. -/
theorem Expr.eval_litFree {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (e : Expr) {t : Term}, e.litFreeB = true → e.eval σ = some t → Term.LitFree t
  | .lit _, _, hl, _ => by simp [Expr.litFreeB] at hl
  | .var v, t, _, he => hσ v t he
  | .app f args, t, hl, he => by
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      exact Term.litFree_app.mpr (Expr.evalList_litFree hσ args hl hts)
  | .min a b, t, hl, he => by
      rw [Expr.litFreeB, Bool.and_eq_true] at hl
      rw [Expr.eval_min, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, hmap⟩ := he
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rcases Term.least_eq_or x y with h | h <;> rw [h]
      · exact Expr.eval_litFree hσ a hl.1 hx
      · exact Expr.eval_litFree hσ b hl.2 hy
@[inherit_doc Expr.eval_litFree]
theorem Expr.evalList_litFree {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (es : List Expr) {ts : List Term}, Expr.litFreeListB es = true →
      Expr.evalList es σ = some ts → ∀ t ∈ ts, Term.LitFree t
  | [], _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp
  | e :: es, ts, hl, he => by
      rw [Expr.litFreeListB, Bool.and_eq_true] at hl
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_litFree hσ e hl.1 hu
      · exact Expr.evalList_litFree hσ es hl.2 hus t ht'

end


theorem Term.LitFree.subterm {t s : Term} (h : t.LitFree) (hs : s ∈ t.subterms) : s.LitFree :=
  fun u hu => h u (hu.trans hs)

theorem Database.LitFree.lookup {db : Database} (hw : db.WF) (h : db.LitFree)
    {σ : Env} (hs : ∀ b ∈ σ, b.2 ∈ db.terms) :
    ∀ v t, Env.lookup v σ = some t → Term.LitFree t := fun v t hv =>
  h.term hw (hs (v, t) (Env.mem_of_lookup hv))

def Action.NoLits (a : Action) : Prop := a.litFreeB = true

def Cmd.NoLits (c : Cmd) : Prop := ∀ r ∈ c.rules, ∀ a ∈ r.actions, a.NoLits

theorem Action.evalTerms_litFree {σ : Env} {a : Action} (hl : a.NoLits)
    (hs : ∀ v t, Env.lookup v σ = some t → t.LitFree) : a.EvalTerms σ Term.LitFree := by
  cases a with
  | expr e | delete e => exact fun t ht => Expr.eval_litFree hs e hl ht
  | union a b =>
    have hl' := Bool.and_eq_true_iff.mp hl
    exact ⟨fun t ht => Expr.eval_litFree hs a hl'.1 ht,
      fun t ht => Expr.eval_litFree hs b hl'.2 ht⟩

theorem evalAction_litFree {σ : Env} {db db' : Database} (hw : db.WF) (h : db.LitFree)
    (hs : ∀ v t, Env.lookup v σ = some t → t.LitFree)
    {a : Action} (hl : a.litFreeB = true) (hv : evalAction σ db a = some db') : db'.LitFree := by
  have hh := evalAction_preserves (P := Term.LitFree)
    (fun _ ht _ hsub => ht.subterm hsub) (fun _ ht => h.term hw ht)
    (Action.evalTerms_litFree hl hs) hv
  exact fun t ht => hh t ht t (.refl _)

theorem evalActions_litFree {σ : Env} {db db' : Database} (hw : db.WF) (h : db.LitFree)
    (hs : ∀ v t, Env.lookup v σ = some t → t.LitFree)
    {as : List Action} (hl : ∀ a ∈ as, a.NoLits) (hv : evalActions σ db as = some db') :
    db'.LitFree := by
  have hh := evalActions_preserves (P := Term.LitFree)
    (fun _ ht _ hsub => ht.subterm hsub) (fun _ ht => h.term hw ht)
    (fun a ha => Action.evalTerms_litFree (hl a ha) hs) hv
  exact fun t ht => hh t ht t (.refl _)

theorem evalLocalActions_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {as : List Action} (hl : ∀ a ∈ as, a.NoLits) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (hv : evalActions σ db as = some db') : db'.LitFree :=
  evalActions_litFree hw h (h.lookup hw hσ) hl hv

structure Database.NoLits (db : Database) : Prop where
  terms : db.LitFree

theorem Database.empty_noLits : Database.empty.NoLits :=
  ⟨Database.empty_litFree⟩

theorem Database.NoLits.runRules {R : List Rule} {db : Database} (hw : db.WF)
    (h : db.NoLits) (hn : ∀ r ∈ R, ∀ a ∈ r.actions, a.NoLits) : (RunRules R db).NoLits := by
  refine ⟨?_⟩
  have hh := RunRules.preserves_evalTerms (R := R) (P := Term.LitFree)
    (fun _ ht _ hsub => ht.subterm hsub) (fun _ ht => h.terms.term hw ht)
    (fun r hr σ hσ a ha => Action.evalTerms_litFree (hn r hr a ha)
      (h.terms.lookup hw hσ.1.2))
  exact fun t ht => hh t ht t (.refl _)

theorem cmdStep_noLits {db db' : Database} (hw : db.WF) (h : db.NoLits)
    {c : Cmd} (hn : c.NoLits) (hs : CmdStep db c db') : db'.NoLits := by
  cases c with
  | run R => subst db'; exact h.runRules hw hn
  | saturate R =>
    induction hs with
    | fixpoint => exact h.runRules hw hn
    | again _ _ ih => exact ih (RunRules.wf hw) (h.runRules hw hn)

theorem programStep_noLits {db db' : Database} (hw : db.WF) (h : db.NoLits)
    {p : List Cmd} (hn : ∀ c ∈ p, c.NoLits) (hs : ProgramStep db p db') : db'.NoLits := by
  induction hs with
  | nil => exact h
  | cons hc _ ih =>
    exact ih (hc.wf hw) (cmdStep_noLits hw h (hn _ (by simp)) hc)
      (fun c hc => hn c (by simp [hc]))

def Actions.UnionRunnable (as : List Action) (db : Database) : Prop :=
  Actions.UnionFree as ∨ (db.LitFree ∧ ∀ a ∈ as, a.NoLits)

theorem evalActions_isSome_of_builds {σ : Env} {db : Database} {Γ : Scope}
    (hm : Γ.Models σ) (hw : db.WF) (hσ : ∀ b ∈ σ, b.2 ∈ db.terms)
    {as : List Action} (hsc : Actions.Scoped as Γ) (hr : Actions.UnionRunnable as db) :
    ∃ db', evalActions σ db as = some db' := by
  apply evalActions_isSome_of_scoped hm hsc
  intro a ha e₁ e₂ he t₁ t₂ h₁ h₂
  subst a
  rcases hr with hu | ⟨hl, he⟩
  · have ha' : ∀ a ∈ as, a.UnionFree := by
      clear ha hsc
      induction as with
      | nil => simp
      | cons a as ih =>
        exact List.forall_mem_cons.mpr ⟨hu.1, ih hu.2⟩
    exact (ha' _ ha).elim
  · have hs := Action.evalTerms_litFree (he _ ha) (hl.lookup hw hσ)
    exact fun hn => hn.elim (hs.1 _ h₁ _ (.refl _)) (hs.2 _ h₂ _ (.refl _))

theorem evalAction_isSome_of_builds {σ : Env} {db : Database} {Γ : Scope}
    (hm : Γ.Models σ) (hw : db.WF) (hσ : ∀ b ∈ σ, b.2 ∈ db.terms)
    {a : Action} (hsc : a.Scoped Γ) (hr : Actions.UnionRunnable [a] db) :
    ∃ db', evalAction σ db a = some db' := by
  obtain ⟨d, hd⟩ := evalActions_isSome_of_builds (as := [a]) hm hw hσ ⟨hsc, trivial⟩ hr
  refine ⟨d, ?_⟩
  simpa [evalActions] using hd

theorem evalLocalActions_isSome_of_builds {db : Database} (hw : db.WF) {r : Rule}
    (hsc : Actions.Scoped r.actions (Query.bind r.query []))
    (hr : Actions.UnionRunnable r.actions db) {σ : Env}
    (hq : ValidQuerySubst db r.query σ) : ∃ d, evalActions σ db r.actions = some d := by
  have hm : (Query.bind r.query []).Models σ := by
    simpa using Query.bind_models Scope.Models.empty hq
  exact evalActions_isSome_of_builds hm hw hq.mem_terms hsc hr

theorem Cmd.NoLits.of_domain {P : Program} (_hdom : P.Fragment)
    (hlit : ∀ c ∈ P.commands, c.litFreeB = true) {c : Cmd} (hc : c ∈ P.commands) : c.NoLits := by
  intro r hr a ha
  exact List.all_eq_true.mp (List.all_eq_true.mp (hlit c hc) r hr) a ha

/-- **`Database.NoLits` at every state the source run reaches**, under `noLitUnion`'s second
arm. Applied to a *prefix* of the program it is the invariant at the state a firing command
starts from. -/
theorem noLits_of_programStep {P : Program} (hdom : P.Fragment)
    (hlit : ∀ c ∈ P.commands, c.litFreeB = true) {p : List Cmd} (hp : ∀ c ∈ p, c ∈ P.commands)
    {sd : Database} (hstep : ProgramStep Database.empty p sd) : sd.NoLits :=
  programStep_noLits Database.WF.empty Database.empty_noLits
    (fun c hc => Cmd.NoLits.of_domain hdom hlit (hp c hc))
    hstep

/-- `Expr.Scoped` in the scope. -/
theorem Expr.Scoped.mono {e : Expr} {Γ Γ' : Scope} (hsub : ∀ v ∈ Γ, v ∈ Γ')
    (h : e.Scoped Γ) : e.Scoped Γ' := fun v hv => hsub v (h v hv)

@[inherit_doc Expr.Scoped.mono]
theorem Action.Scoped.mono {a : Action} {Γ Γ' : Scope} (hsub : ∀ v ∈ Γ, v ∈ Γ')
    (h : a.Scoped Γ) : a.Scoped Γ' := by
  cases a with
  | expr e | delete e => exact ⟨h.1, Expr.Scoped.mono hsub h.2⟩
  | union e₁ e₂ => exact ⟨Expr.Scoped.mono hsub h.1, Expr.Scoped.mono hsub h.2⟩

@[inherit_doc Expr.Scoped.mono]
theorem Actions.Scoped.mono : ∀ (as : List Action) {Γ Γ' : Scope}, (∀ v ∈ Γ, v ∈ Γ') →
    Actions.Scoped as Γ → Actions.Scoped as Γ' := by
  intro as
  induction as with
  | nil => intro _ _ _ _; trivial
  | cons a as ih =>
    intro Γ Γ' hsub h
    exact ⟨Action.Scoped.mono hsub h.1, ih hsub h.2⟩

/-- An environment models its own domain. -/
theorem Scope.Models.dom (σ : Env) : Scope.Models (Env.dom σ) σ := fun _ => Iff.rfl

end Egglog
