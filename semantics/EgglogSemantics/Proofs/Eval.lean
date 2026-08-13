import EgglogSemantics.Spec.Eval
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Congruence

namespace Egglog
/-! ### The terms depend on `eqs` alone

`Database.terms` is `{t | Cong db t t}` and `Cong` reads `eqs`, so an update to `sig`,
`env` or `rules` leaves the terms alone — and, at an environment whose values the database
holds, leaves `WF` alone too. Every field update the semantics performs is one of these. -/

/-- Two databases asserting the same equations hold the same terms. -/
theorem Database.terms_eq_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) :
    d₁.terms = d₂.terms :=
  Set.Subset.antisymm (Database.Contained.terms ⟨h.subset⟩)
    (Database.Contained.terms ⟨h.symm.subset⟩)

@[simp] theorem Database.terms_setEnv {db : Database} {σ : Env} :
    ({ db with env := σ } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

@[simp] theorem Database.terms_setEnvRules {db : Database} {σ : Env} {R : Set Rule} :
    ({ db with env := σ, rules := R } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

theorem Database.terms_setSig {db : Database} {s : Signature} :
    ({ db with sig := s } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

theorem Database.terms_setRules {db : Database} {R : Set Rule} :
    ({ db with rules := R } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

/-- `WF` reads `eqs` and `env` only: a database agreeing in both is well formed too. -/
theorem Database.WF.congr {d₁ d₂ : Database} (hw : d₁.WF) (heqs : d₁.eqs = d₂.eqs)
    (henv : d₁.env = d₂.env) : d₂.WF := by
  have ht : d₁.terms = d₂.terms := Database.terms_eq_of_eqs_eq heqs
  refine ⟨fun t htm => ?_, fun t htm => ?_, fun b hb => ?_, fun p hp => ?_⟩
  · rw [← heqs, ← ht] at *
    exact hw.eqsRefl t htm
  · rw [← ht] at htm ⊢
    exact hw.subtermClosed t htm
  · rw [← ht]
    exact hw.envInTerms b (by rw [henv]; exact hb)
  · exact hw.litsIsolated p (by rw [heqs]; exact hp)

/-- Replacing the environment by one whose values the database holds keeps `WF`. -/
theorem Database.WF.setEnv {db : Database} (hw : db.WF) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) : Database.WF { db with env := σ } where
  eqsRefl := by simpa using hw.eqsRefl
  subtermClosed := by simpa using hw.subtermClosed
  envInTerms b hb := by simpa using hσ b hb
  litsIsolated := hw.litsIsolated

/-- `WF.setEnv` at the one environment the semantics imposes: the globals extended by a
rule-local substitution. -/
theorem Database.WF.appendEnv {db : Database} (hw : db.WF) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) : Database.WF { db with env := db.env ++ σ } :=
  hw.setEnv fun b hb => (List.mem_append.mp hb).elim (hw.envInTerms b) (hσ b)

/-- Each argument of an application the database holds is a term the database holds:
`WF.subtermClosed` at depth one. -/
theorem Database.mem_terms_of_arg {db : Database} (hwf : db.WF) {f : FnName}
    {args : List Term} (h : Term.app f args ∈ db.terms) {t : Term} (ht : t ∈ args) :
    t ∈ db.terms :=
  hwf.subtermClosed _ h
    (Term.mem_subterms.mpr (Term.IsSubterm.arg ht (Term.IsSubterm.refl t)))

namespace Expr
@[simp] theorem eval_lit {sig : Signature} {l : Lit} {σ : Env} :
    (Expr.lit l).eval sig σ = some (.lit l) := rfl

@[simp] theorem eval_var {sig : Signature} {v : Var} {σ : Env} :
    (Expr.var v).eval sig σ = Env.lookup v σ := rfl

/-- The building case, which is the only one the constructor fragment ever takes. -/
@[simp] theorem eval_app_ctor {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hp : Prim.ofName f = none) (hc : sig.IsCtor f) :
    (Expr.app f args).eval sig σ = (Expr.evalList sig args σ).map (Term.app f) := by
  simp only [Expr.eval, hp, if_pos hc]

/-- The computing case. A reserved name shadows a user function, so this needs no
condition on the signature. -/
theorem eval_app_prim {sig : Signature} {f : FnName} {p : Prim} {args : List Expr}
    {σ : Env} (hp : Prim.ofName f = some p) :
    (Expr.app f args).eval sig σ = (Expr.evalList sig args σ).bind p.apply := by
  simp only [Expr.eval, hp]

/-- **The stuck case**, all of it: anything that is neither a primitive nor a *declared*
constructor has no rule. It covers the two lookups — a `:merge` and a `:no-merge` function
— and, since declaration is required, the name nobody declared. -/
theorem eval_app_not_ctor {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hp : Prim.ofName f = none) (hc : ¬ sig.IsCtor f) :
    (Expr.app f args).eval sig σ = none := by
  simp only [Expr.eval, hp, if_neg hc]

/-- The reading case, which has no rule: an application of a merge function is a lookup,
and `Impl/Check.lean`'s `noLookup` rejects one in every position this is called from. -/
theorem eval_app_merge {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    {body : List Action} {res : List Expr} (hp : Prim.ofName f = none)
    (hc : sig.mergeOf f = some (MergeSpec.merge body res)) :
    (Expr.app f args).eval sig σ = none :=
  eval_app_not_ctor hp (Signature.not_isCtor hc)

/-- `eval_app_merge` for a `:no-merge` function, which is a lookup for the same reason. -/
theorem eval_app_noMerge {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hp : Prim.ofName f = none) (hc : sig.mergeOf f = some MergeSpec.noMerge) :
    (Expr.app f args).eval sig σ = none :=
  eval_app_not_ctor hp (Signature.not_isCtor hc)

/-- The undeclared case, spelled out: a name the signature does not mention builds
nothing. -/
theorem eval_app_undeclared {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hp : Prim.ofName f = none) (hc : sig f = none) :
    (Expr.app f args).eval sig σ = none :=
  eval_app_not_ctor hp (Signature.not_isCtor_of_none hc)

@[simp] theorem evalList_nil {sig : Signature} {σ : Env} :
    Expr.evalList sig [] σ = some [] := rfl

@[simp] theorem evalList_cons {sig : Signature} {e : Expr} {es : List Expr} {σ : Env} :
    Expr.evalList sig (e :: es) σ =
      (e.eval sig σ).bind fun t => (Expr.evalList sig es σ).map (t :: ·) := rfl

/-- `Expr.evalList` is length-preserving, which is how a `set`'s declared column widths
become the *term* widths `MergeStep.collide` asks about. -/
theorem evalList_length {sig : Signature} {σ : Env} {es : List Expr} {ts : List Term}
    (h : Expr.evalList sig es σ = some ts) : ts.length = es.length := by
  induction es generalizing ts with
  | nil => rw [Expr.evalList_nil, Option.some.injEq] at h; exact h ▸ rfl
  | cons e es ih =>
    rw [Expr.evalList_cons] at h
    obtain ⟨t, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
    simp [ih hus]

end Expr
/-! ### Evaluation stays inside the constructor fragment

The condition on a single term, and the fact that `Expr.eval` only ever produces such
terms. It lives here rather than with the invariant that reads it because it is a fact
about `Expr.eval` and nothing else; `Proofs/Merge.lean`'s `FDatabase.Inv` needs it. -/

/-- A term built only from constructor applications: the condition the operations that
*insert* a term have to be given. -/
def Term.CtorTerm (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → sig.IsCtor f

/-- A literal mentions no application. -/
theorem Term.ctorTerm_lit {sig : Signature} {l : Lit} : Term.CtorTerm sig (.lit l) := by
  intro f as hsub
  rw [Term.subterms_lit] at hsub
  exact absurd hsub (by simp)

/-- A primitive returns one of its operands or a fresh literal, so it cannot introduce a
non-constructor application. -/
theorem Prim.apply_ctorTerm {sig : Signature} {p : Prim} {ts : List Term} {v : Term}
    (hts : ∀ t ∈ ts, Term.CtorTerm sig t) (h : p.apply ts = some v) :
    Term.CtorTerm sig v := by
  unfold Prim.apply at h
  split at h
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMin
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMax
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h; subst h; exact Term.ctorTerm_lit
  · simp only [Option.some_inj] at h; subst h; exact Term.ctorTerm_lit
  · exact absurd h (by simp)

mutual

/-- **Evaluation only ever builds constructor terms.**

Each branch that produces a term stays inside the constructor fragment: the building
branch's head is a *declared* constructor by the guard the evaluator just tested, and a
primitive returns an operand or a literal. Nothing reads a row, so no case has to place a
recorded output back in `terms`. This is what `FDatabase.Inv.execAction` needs. -/
theorem Expr.eval_ctorTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.CtorTerm sig b.2) {e : Expr} {t : Term}
    (hs : e.eval sig σ = some t) : Term.CtorTerm sig t := by
  match e with
  | .lit l =>
    rw [Expr.eval_lit, Option.some_inj] at hs
    subst hs; exact Term.ctorTerm_lit
  | .var v =>
    rw [Expr.eval_var] at hs
    exact hσ (v, t) (Env.mem_of_lookup hs)
  | .app f args =>
    cases hp : Prim.ofName f with
    | some p =>
      rw [Expr.eval_app_prim hp, Option.bind_eq_some_iff] at hs
      obtain ⟨ts, hts, happ⟩ := hs
      exact Prim.apply_ctorTerm (Expr.evalList_ctorTerm hσ hts) happ
    | none =>
      by_cases hu : sig.IsCtor f
      · rw [Expr.eval_app_ctor hp hu, Option.map_eq_some_iff] at hs
        obtain ⟨ts, hts, rfl⟩ := hs
        have hts' := Expr.evalList_ctorTerm hσ hts
        intro g bs hsub
        rw [Term.subterms_app] at hsub
        rcases Set.mem_insert_iff.mp hsub with heq | hmem
        · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
          exact hu
        · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
          exact hts' x hx g bs hxs
      · rw [Expr.eval_app_not_ctor hp hu] at hs; exact absurd hs (by simp)

theorem Expr.evalList_ctorTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.CtorTerm sig b.2) {es : List Expr} {ts : List Term}
    (hs : Expr.evalList sig es σ = some ts) : ∀ t ∈ ts, Term.CtorTerm sig t := by
  match es with
  | [] =>
    rw [Expr.evalList_nil, Option.some_inj] at hs
    subst hs; simp
  | e :: es =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at hs
    obtain ⟨t, ht, hmap⟩ := hs
    obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some_iff.mp hmap
    subst heq
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Expr.eval_ctorTerm hσ ht
    · exact Expr.evalList_ctorTerm hσ hrest x hx

end

/-! ### Evaluation builds terms of the declared width

`Term.CtorTerm`'s width twin: it reads a head's *column counts* where that reads its kind,
and it is `Database.DeclaredTerms` on a single term. The check that supplies the counts is
`Expr.WidthOk`. -/

/-- `Database.DeclaredTerms` on a single term: the condition the operations that *insert* a
term have to be given. -/
def Term.DeclaredTerm (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → ∃ d, sig f = some d ∧ as.length = d.entryWidth

/-- A literal mentions no application. -/
theorem Term.declaredTerm_lit {sig : Signature} {l : Lit} :
    Term.DeclaredTerm sig (.lit l) := by
  intro f as hsub
  rw [Term.subterms_lit] at hsub
  exact absurd hsub (by simp)

/-- A primitive returns one of its operands or a fresh literal, so it builds no application
of its own. -/
theorem Prim.apply_declaredTerm {sig : Signature} {p : Prim} {ts : List Term} {v : Term}
    (hts : ∀ t ∈ ts, Term.DeclaredTerm sig t) (h : p.apply ts = some v) :
    Term.DeclaredTerm sig v := by
  unfold Prim.apply at h
  split at h
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMin
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMax
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h; subst h; exact Term.declaredTerm_lit
  · simp only [Option.some_inj] at h; subst h; exact Term.declaredTerm_lit
  · exact absurd h (by simp)

mutual

/-- **A width-checked expression evaluates to a term of the declared width.** The building
branch's head is a declared constructor, whose `entryWidth` is its `arity`, and `WidthOk`
supplies the argument count; a primitive returns an operand or a literal. -/
theorem Expr.eval_declaredTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.DeclaredTerm sig b.2) {e : Expr} {t : Term}
    (hw : e.WidthOk sig) (hs : e.eval sig σ = some t) : Term.DeclaredTerm sig t := by
  match e with
  | .lit l =>
    rw [Expr.eval_lit, Option.some_inj] at hs
    subst hs; exact Term.declaredTerm_lit
  | .var v =>
    rw [Expr.eval_var] at hs
    exact hσ (v, t) (Env.mem_of_lookup hs)
  | .app f args =>
    cases hp : Prim.ofName f with
    | some p =>
      rw [Expr.eval_app_prim hp, Option.bind_eq_some_iff] at hs
      obtain ⟨ts, hts, happ⟩ := hs
      exact Prim.apply_declaredTerm (Expr.evalList_declaredTerm hσ hw.2 hts) happ
    | none =>
      by_cases hu : sig.IsCtor f
      · rw [Expr.eval_app_ctor hp hu, Option.map_eq_some_iff] at hs
        obtain ⟨ts, hts, rfl⟩ := hs
        have hts' := Expr.evalList_declaredTerm hσ hw.2 hts
        obtain ⟨d, hd, hdm⟩ := hu
        intro g bs hsub
        rw [Term.subterms_app] at hsub
        rcases Set.mem_insert_iff.mp hsub with heq | hmem
        · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
          refine ⟨d, hd, ?_⟩
          rw [Expr.evalList_length hts, hw.1 d hd, FnDecl.entryWidth, if_pos]
          simp [hdm]
        · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
          exact hts' x hx g bs hxs
      · rw [Expr.eval_app_not_ctor hp hu] at hs; exact absurd hs (by simp)

theorem Expr.evalList_declaredTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.DeclaredTerm sig b.2) {es : List Expr} {ts : List Term}
    (hw : Expr.WidthOkList es sig) (hs : Expr.evalList sig es σ = some ts) :
    ∀ t ∈ ts, Term.DeclaredTerm sig t := by
  match es with
  | [] =>
    rw [Expr.evalList_nil, Option.some_inj] at hs
    subst hs; simp
  | e :: es =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at hs
    obtain ⟨t, ht, hmap⟩ := hs
    obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some_iff.mp hmap
    subst heq
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Expr.eval_declaredTerm hσ hw.1 ht
    · exact Expr.evalList_declaredTerm hσ hw.2 hrest x hx

end

/-! ### `DeclaredTerms`, term by term

`Database.DeclaredTerms` and `Term.DeclaredTerm` are the same condition read of a state and
of a term. `WF.subtermClosed` moves it in one direction, and the two `add` operations move
it back. -/

theorem Database.declaredTerm_of_mem {db : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    {t : Term} (ht : t ∈ db.terms) : Term.DeclaredTerm db.sig t := fun f as hsub =>
  hdt f as (hwf.subtermClosed t ht hsub)

theorem Database.env_declaredTerm {db : Database} (hwf : db.WF) (hdt : db.DeclaredTerms) :
    ∀ b ∈ db.env, Term.DeclaredTerm db.sig b.2 :=
  fun b hb => Database.declaredTerm_of_mem hwf hdt (hwf.envInTerms b hb)

theorem Database.declaredTerms_addTerm {db : Database} (hdt : db.DeclaredTerms) {t : Term}
    (ht : Term.DeclaredTerm db.sig t) : (db.addTerm t).DeclaredTerms := by
  intro f as hmem
  rw [Database.addTerm_terms] at hmem
  rcases hmem with h | h
  · exact hdt f as h
  · exact ht f as h

theorem Database.declaredTerms_addEq {db : Database} (hdt : db.DeclaredTerms) {a b : Term}
    (ha : Term.DeclaredTerm db.sig a) (hb : Term.DeclaredTerm db.sig b) :
    (db.addEq a b).DeclaredTerms := by
  intro f as hmem
  rw [Database.addEq_terms] at hmem
  rcases hmem with (h | h) | h
  · exact hdt f as h
  · exact ha f as h
  · exact hb f as h

theorem Database.empty_declaredTerms : Database.empty.DeclaredTerms := by
  intro f as hmem
  rw [Database.empty_terms] at hmem
  exact absurd hmem (by simp)

mutual

/-- Evaluation reads the environment only through `lookup`, so environments that
agree are interchangeable. This is what lets `Env.UnionAll`'s duplicate bindings be
ignored. -/
theorem Expr.eval_agree {sig : Signature} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (e : Expr) :
    e.eval sig σ₁ = e.eval sig σ₂ := by
  match e with
  | .lit _ => rfl
  | .var v => exact h v
  | .app f args => simp only [Expr.eval, Expr.evalList_agree h args]

theorem Expr.evalList_agree {sig : Signature} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂)
    (es : List Expr) : Expr.evalList sig es σ₁ = Expr.evalList sig es σ₂ := by
  match es with
  | [] => rfl
  | e :: es =>
    rw [Expr.evalList_cons, Expr.evalList_cons, Expr.eval_agree h e, Expr.evalList_agree h es]

end

mutual

/-- Evaluation gets stuck on an unbound variable, on a lookup and on a primitive; an
expression with none of the three evaluates. The two conditions are exactly
`Expr.Scoped` and `Expr.Evaluable` (`Spec/Scope.lean`). -/
theorem Expr.eval_isSome {sig : Signature} {σ : Env} (e : Expr)
    (h : ∀ v ∈ e.vars, v ∈ Env.dom σ)
    (hf : ∀ f ∈ e.fns, Prim.ofName f = none ∧ sig.IsCtor f) :
    ∃ t, e.eval sig σ = some t := by
  match e with
  | .lit l => exact ⟨.lit l, rfl⟩
  | .var v =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      (Env.lookup_isSome_iff_mem_dom.mpr (h v (by simp)))
    exact ⟨t, ht⟩
  | .app f args =>
    obtain ⟨hp, hc⟩ := hf f (by simp)
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome args (by simpa using h)
      (fun g hg => hf g (by simp [hg]))
    exact ⟨.app f ts, by rw [Expr.eval_app_ctor hp hc, hts, Option.map_some]⟩

theorem Expr.evalList_isSome {sig : Signature} {σ : Env} (es : List Expr)
    (h : ∀ v ∈ Expr.varsList es, v ∈ Env.dom σ)
    (hf : ∀ f ∈ Expr.fnsList es, Prim.ofName f = none ∧ sig.IsCtor f) :
    ∃ ts, Expr.evalList sig es σ = some ts := by
  match es with
  | [] => exact ⟨[], rfl⟩
  | e :: es =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome e (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inl hv)))
      (fun g hg => hf g (List.mem_union_iff.mpr (Or.inl hg)))
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome es (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inr hv)))
      (fun g hg => hf g (List.mem_union_iff.mpr (Or.inr hg)))
    exact ⟨t :: ts, by rw [Expr.evalList_cons, ht, Option.bind_some, hts, Option.map_some]⟩

end

@[simp] theorem evalActions_nil {db : Database} : evalActions db [] = some db := rfl

@[simp] theorem evalActions_cons {db : Database} {a : Action} {as : List Action} :
    evalActions db (a :: as) = (evalAction db a).bind fun db' => evalActions db' as := rfl

/-! ### Actions only add -/
/-- What an action produces, per case. Every fact below about `evalAction` is a
three-way `rcases` on this rather than a repeat of the case analysis. -/
theorem evalAction_eq_some {db db' : Database} {a : Action}
    (h : evalAction db a = some db') :
    (∃ e t, a = .expr e ∧ e.eval db.sig db.env = some t ∧ db' = db.addTerm t) ∨
      (∃ v e t, a = .letBind v e ∧ e.eval db.sig db.env = some t ∧
        db' = { db.addTerm t with env := (v, t) :: db.env }) ∨
      (∃ e₁ e₂ t₁ t₂, a = .union e₁ e₂ ∧ e₁.eval db.sig db.env = some t₁ ∧
        e₂.eval db.sig db.env = some t₂ ∧ ¬ (t₁.isLit ∨ t₂.isLit) ∧ db' = db.addEq t₁ t₂) ∨
      (∃ f args out as vs, a = .set f args out ∧ Expr.evalList db.sig args db.env = some as ∧
        Expr.evalList db.sig out db.env = some vs ∧
        db' = db.addTerm (.app f (as ++ vs))) := by
  cases a with
  | expr e =>
    cases hv : e.eval db.sig db.env with
    | none => simp [evalAction, hv] at h
    | some t =>
      simp only [evalAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inl ⟨e, t, rfl, hv, h.symm⟩
  | letBind v e =>
    cases hv : e.eval db.sig db.env with
    | none => simp [evalAction, hv] at h
    | some t =>
      simp only [evalAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨v, e, t, rfl, hv, h.symm⟩)
  | union e₁ e₂ =>
    cases hv₁ : e₁.eval db.sig db.env with
    | none => simp [evalAction, hv₁] at h
    | some t₁ =>
      cases hv₂ : e₂.eval db.sig db.env with
      | none => simp [evalAction, hv₁, hv₂] at h
      | some t₂ =>
        simp only [evalAction, hv₁, hv₂, Option.bind_some] at h
        split at h
        · simp at h
        · rename_i hlit
          simp only [Option.some.injEq] at h
          exact Or.inr (Or.inr (Or.inl ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, by
            simpa using hlit, h.symm⟩))
  | set f args out =>
    cases hv₁ : Expr.evalList db.sig args db.env with
    | none => simp [evalAction, hv₁] at h
    | some as =>
      cases hv₂ : Expr.evalList db.sig out db.env with
      | none => simp [evalAction, hv₁, hv₂] at h
      | some vs =>
        simp only [evalAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inr ⟨f, args, out, as, vs, rfl, hv₁, hv₂, h.symm⟩))

theorem evalAction_contained {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db.Contained db' := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, -, rfl⟩ | ⟨f, _, _, as, vs, -, -, -, rfl⟩
  · exact .addTerm t db
  · exact ⟨Set.subset_union_left⟩
  · exact .addEq t₁ t₂ db
  · exact .addTerm _ db

theorem evalAction_rules {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.rules = db.rules := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ | ⟨_, _, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, rfl⟩ <;> rfl

/-- No action touches the signature; only `Cmd.decl` writes it. -/
theorem evalAction_sig {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.sig = db.sig := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ | ⟨_, _, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, rfl⟩ <;> rfl

theorem evalAction_wf {db db' : Database} (hw : db.WF) {a : Action}
    (h : evalAction db a = some db') : db'.WF := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, hlit, rfl⟩ | ⟨f, _, _, as, vs, -, -, -, rfl⟩
  · exact hw.addTerm t
  · refine (hw.addTerm t).setEnv fun b hb => ?_
    rcases List.mem_cons.mp hb with rfl | hb
    · exact db.mem_addTerm t
    · exact (hw.addTerm t).envInTerms b hb
  · exact hw.addEq t₁ t₂ fun hl => absurd hl hlit
  · exact hw.addTerm _

theorem evalActions_contained {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db.Contained db' := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ .refl db
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact (evalAction_contained hv).trans (ih h)

theorem evalActions_sig {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db'.sig = db.sig := by
  induction as generalizing db with
  | nil => simp only [evalActions_nil, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      rw [ih h, evalAction_sig hv]

theorem evalActions_rules {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db'.rules = db.rules := by
  induction as generalizing db with
  | nil => simp only [evalActions_nil, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      rw [ih h, evalAction_rules hv]

theorem evalActions_wf {db db' : Database} (hw : db.WF) {as : List Action}
    (h : evalActions db as = some db') : db'.WF := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hw
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact ih (evalAction_wf hw hv) h

/-! ### Actions keep `DeclaredTerms`

The two front-end checks that bear on what an action *writes*: `Action.WidthOk` for the
terms it builds, `Action.SetLegal` for the entry a `set` records. `SetLegal` is load-bearing
in the `set` case and not decoration — it is what turns `args.length = arity` and
`out.length = outArity` into `FnDecl.entryWidth`, which is `arity + outArity` for a merge
function and `arity` alone for a constructor. `Proofs/Counterexamples.lean`'s
`setCtor_not_declaredTerms` is a `set` on a constructor that passes `WidthOk` and breaks
`DeclaredTerms`. -/

/-- **`DeclaredTerms` is preserved by an action.** -/
theorem evalAction_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    {a : Action} (hw : a.WidthOk db.sig) (hsl : a.SetLegal db.sig)
    (h : evalAction db a = some db') : db'.DeclaredTerms := by
  have henv := Database.env_declaredTerm hwf hdt
  rcases evalAction_eq_some h with ⟨e, t, rfl, ht, rfl⟩ | ⟨v, e, t, rfl, ht, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, ht₁, ht₂, -, rfl⟩ | ⟨f, args, out, as, vs, rfl, has, hvs, rfl⟩
  · exact Database.declaredTerms_addTerm hdt (Expr.eval_declaredTerm henv hw ht)
  · intro g bs hmem
    rw [Database.terms_setEnv] at hmem
    exact Database.declaredTerms_addTerm hdt (Expr.eval_declaredTerm henv hw ht) g bs hmem
  · exact Database.declaredTerms_addEq hdt (Expr.eval_declaredTerm henv hw.1 ht₁)
      (Expr.eval_declaredTerm henv hw.2 ht₂)
  · obtain ⟨d, hd⟩ : ∃ d, db.sig f = some d := by
      cases hdf : db.sig f with
      | none => exact absurd (by simp [Signature.mergeOf, hdf]) hsl
      | some d => exact ⟨d, rfl⟩
    have hdm : d.merge ≠ none := fun hne => hsl (by simp [Signature.mergeOf, hd, hne])
    obtain ⟨hka, hkv⟩ := hw.1 d hd
    refine Database.declaredTerms_addTerm hdt ?_
    intro g bs hsub
    rw [Term.subterms_app] at hsub
    rcases Set.mem_insert_iff.mp hsub with heq | hmem
    · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
      refine ⟨d, hd, ?_⟩
      rw [List.length_append, (Expr.evalList_length has).trans hka,
        (Expr.evalList_length hvs).trans hkv, FnDecl.entryWidth, if_neg]
      simpa using hdm
    · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
      rcases List.mem_append.mp hx with hx | hx
      · exact Expr.evalList_declaredTerm henv hw.2.1 has x hx g bs hxs
      · exact Expr.evalList_declaredTerm henv hw.2.2 hvs x hx g bs hxs

theorem evalActions_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    {as : List Action} (hw : Actions.WidthOk as db.sig) (hsl : Actions.SetLegal as db.sig)
    (h : evalActions db as = some db') : db'.DeclaredTerms := by
  induction as generalizing db with
  | nil => rw [evalActions_nil, Option.some_inj] at h; exact h ▸ hdt
  | cons a as ih =>
    rw [evalActions_cons, Option.bind_eq_some_iff] at h
    obtain ⟨d, hd, hrest⟩ := h
    have hsig : d.sig = db.sig := evalAction_sig hd
    exact ih (evalAction_wf hwf hd) (evalAction_declaredTerms hwf hdt hw.1 hsl.1 hd)
      (by rw [hsig]; exact hw.2) (by rw [hsig]; exact hsl.2) hrest

/-! ### Agreeing environments are interchangeable

`Expr.eval_agree` says evaluation reads the environment only through `lookup`. Lifting
that to whole action sequences is what justifies two places the semantics is loose
about environments on purpose: `Env.Union2` can leave a variable bound twice, and
`ValidEnv` fixes a substitution's domain only up to permutation. -/
theorem evalAction_envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (a : Action) :
    Option.Rel Database.EnvAgree (evalAction d₁ a) (evalAction d₂ a) := by
  cases a with
  | expr e =>
    simp only [evalAction, ← h.sig, ← Expr.eval_agree (sig := d₁.sig) h.env e]
    cases e.eval d₁.sig d₁.env with
    | none => exact .none
    | some t => exact .some (h.addTerm t)
  | letBind v e =>
    simp only [evalAction, ← h.sig, ← Expr.eval_agree (sig := d₁.sig) h.env e]
    cases e.eval d₁.sig d₁.env with
    | none => exact .none
    | some t =>
      refine .some ⟨h.sig, (h.addTerm t).eqs, h.rules, fun w => ?_⟩
      by_cases hw : w = v <;> simp [hw, h.env w]
  | union e₁ e₂ =>
    simp only [evalAction, ← h.sig, ← Expr.eval_agree (sig := d₁.sig) h.env e₁,
      ← Expr.eval_agree (sig := d₁.sig) h.env e₂]
    cases e₁.eval d₁.sig d₁.env with
    | none => exact .none
    | some t₁ =>
      cases e₂.eval d₁.sig d₁.env with
      | none => exact .none
      | some t₂ =>
        simp only [Option.bind_some]
        by_cases hlit : t₁.isLit || t₂.isLit
        · simp only [if_pos hlit]; exact .none
        · simp only [if_neg hlit]
          exact .some ⟨h.sig,
            by simp only [Database.addEq_eqs, ((h.addTerm t₁).addTerm t₂).eqs], h.rules, h.env⟩
  | set f args out =>
    simp only [evalAction, ← h.sig, ← Expr.evalList_agree (sig := d₁.sig) h.env args,
      ← Expr.evalList_agree (sig := d₁.sig) h.env out]
    cases Expr.evalList d₁.sig args d₁.env with
    | none => exact .none
    | some as =>
      cases Expr.evalList d₁.sig out d₁.env with
      | none => exact .none
      | some vs => exact .some (h.addTerm _)

theorem evalActions_envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (as : List Action) :
    Option.Rel Database.EnvAgree (evalActions d₁ as) (evalActions d₂ as) := by
  induction as generalizing d₁ d₂ with
  | nil => exact .some h
  | cons a as ih =>
    have hrel := evalAction_envAgree h a
    cases h₁ : evalAction d₁ a with
    | none =>
      cases h₂ : evalAction d₂ a with
      | none => simp only [evalActions_cons, h₁, h₂, Option.bind_none]; exact .none
      | some e₂ => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
    | some e₁ =>
      cases h₂ : evalAction d₂ a with
      | none => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
      | some e₂ =>
        rw [h₁, h₂] at hrel
        cases hrel with
        | some he =>
          simp only [evalActions_cons, h₁, h₂, Option.bind_some]
          exact ih he

/-- Local actions cannot tell agreeing substitutions apart. -/
theorem evalLocalActions_agree {db : Database} (as : List Action) {σ₁ σ₂ : Env}
    (h : Env.Agree σ₁ σ₂) : evalLocalActions db as σ₁ = evalLocalActions db as σ₂ := by
  have hE : Database.EnvAgree { db with env := db.env ++ σ₁ } { db with env := db.env ++ σ₂ } :=
    ⟨rfl, rfl, rfl, Env.Agree.append_left db.env h⟩
  have hrel := evalActions_envAgree hE as
  simp only [evalLocalActions]
  cases h₁ : evalActions { db with env := db.env ++ σ₁ } as with
  | none =>
    cases h₂ : evalActions { db with env := db.env ++ σ₂ } as with
    | none => rfl
    | some e₂ => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
  | some e₁ =>
    cases h₂ : evalActions { db with env := db.env ++ σ₂ } as with
    | none => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
    | some e₂ =>
      rw [h₁, h₂] at hrel
      cases hrel with
      | some he => simp only [Option.map_some, he.eq_of_env_rules db.env db.rules]

/-! ### Local actions preserve the caller's environment and rules -/
/-- Local actions run the actions with `σ` in scope and then put the caller's
environment and rules back. -/
theorem evalLocalActions_eq_some {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') :
    ∃ d, evalActions { db with env := db.env ++ σ } as = some d ∧
      db' = { d with env := db.env, rules := db.rules } := by
  cases hv : evalActions { db with env := db.env ++ σ } as with
  | none => simp [evalLocalActions, hv] at h
  | some d =>
    simp only [evalLocalActions, hv, Option.map_some, Option.some.injEq] at h
    exact ⟨d, rfl, h.symm⟩

theorem evalLocalActions_env {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.env = db.env := by
  obtain ⟨_, _, rfl⟩ := evalLocalActions_eq_some h; rfl

theorem evalLocalActions_rules {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.rules = db.rules := by
  obtain ⟨_, _, rfl⟩ := evalLocalActions_eq_some h; rfl

theorem evalLocalActions_sig {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.sig = db.sig := by
  obtain ⟨_, hv, rfl⟩ := evalLocalActions_eq_some h
  exact (evalActions_sig hv : _ = ({ db with env := db.env ++ σ } : Database).sig)

theorem evalLocalActions_contained {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db.Contained db' := by
  obtain ⟨_, hv, rfl⟩ := evalLocalActions_eq_some h
  exact ⟨(evalActions_contained hv).eqs⟩

/-- Local actions preserve well-formedness provided the substitution only mentions
terms the database holds — which is what `ValidEnv` guarantees. -/
theorem evalLocalActions_wf {db db' : Database} (hw : db.WF) {as : List Action} {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (h : evalLocalActions db as σ = some db') : db'.WF := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  have hd := evalActions_wf (hw.appendEnv hσ) hv
  exact ⟨by simpa using hd.eqsRefl, by simpa using hd.subtermClosed,
    fun b hb => Database.terms_setEnvRules ▸ (evalActions_contained hv).terms
      (Database.terms_setEnv ▸ hw.envInTerms b hb),
    hd.litsIsolated⟩

/-- Local actions keep `DeclaredTerms`, under `evalLocalActions_wf`'s condition on the
substitution and the two checks `evalActions_declaredTerms` asks of the block. -/
theorem evalLocalActions_declaredTerms {db db' : Database} (hwf : db.WF)
    (hdt : db.DeclaredTerms) {as : List Action} {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (hw : Actions.WidthOk as db.sig)
    (hsl : Actions.SetLegal as db.sig) (h : evalLocalActions db as σ = some db') :
    db'.DeclaredTerms := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  intro g cs hmem
  rw [Database.terms_setEnvRules] at hmem
  exact evalActions_declaredTerms (hwf.appendEnv hσ)
    (by intro g cs hm; rw [Database.terms_setEnv] at hm; exact hdt g cs hm) hw hsl hv g cs hmem

end Egglog
