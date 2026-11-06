import EgglogSemantics.Spec.Facts
import EgglogSemantics.Source.Domain
import EgglogSemantics.Proofs.SemanticCong

namespace Egglog

/-- An action that removes no rows. -/
abbrev Action.SubsumeFree (a : Action) : Prop := a.monotoneB = true

def Actions.SubsumeFree (as : List Action) : Prop := ∀ a ∈ as, a.SubsumeFree
@[simp] theorem Actions.subsumeFree_nil : Actions.SubsumeFree [] := by simp [Actions.SubsumeFree]
@[simp] theorem Actions.subsumeFree_cons {a : Action} {as : List Action} :
    Actions.SubsumeFree (a :: as) ↔ a.SubsumeFree ∧ Actions.SubsumeFree as := by
  simp [Actions.SubsumeFree]
theorem Actions.subsumeFree_of_all {as : List Action} (h : as.all Action.monotoneB = true) :
    Actions.SubsumeFree as := List.all_eq_true.mp h
def Rule.SubsumeFree (r : Rule) : Prop := Actions.SubsumeFree r.actions

theorem Database.WF.congr {d₁ d₂ : Database} (hw : d₁.WF) (heqs : d₁.eqs = d₂.eqs) :
    d₂.WF := ⟨by simpa [Database.LitsIsolated, ← heqs] using hw.litsIsolated⟩

theorem Database.mem_terms_of_arg {db : Database} (hwf : db.WF) {f : FnName}
    {args : List Term} (h : Term.app f args ∈ db.terms) {t : Term} (ht : t ∈ args) :
    t ∈ db.terms :=
  hwf.subtermClosed _ h
    (Term.mem_subterms.mpr (Term.IsSubterm.arg ht (Term.IsSubterm.refl t)))

/-- `Term.least` answers with one of its operands. -/
theorem Term.least_eq_or (s t : Term) : Term.least s t = s ∨ Term.least s t = t := by
  unfold Term.least
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

namespace Expr
@[simp] theorem eval_lit {l : Lit} {σ : Env} :
    (Expr.lit l).eval σ = some (.lit l) := rfl

@[simp] theorem eval_var {v : Var} {σ : Env} :
    (Expr.var v).eval σ = Env.lookup v σ := rfl

/-- The building case, which is the only one the constructor fragment ever takes. -/
@[simp] theorem eval_app_ctor {f : FnName} {args : List Expr} {σ : Env}
    :
    (Expr.app f args).eval σ = (Expr.evalList args σ).map (Term.app f) := by
  rfl

/-- The choosing case: the smaller of the two operands in the term order. -/
@[simp] theorem eval_min {a b : Expr} {σ : Env} :
    (Expr.min a b).eval σ =
      (a.eval σ).bind fun x => (b.eval σ).map (Term.least x) := rfl

@[simp] theorem evalList_nil {σ : Env} :
    Expr.evalList [] σ = some [] := rfl

@[simp] theorem evalList_cons {e : Expr} {es : List Expr} {σ : Env} :
    Expr.evalList (e :: es) σ =
      (e.eval σ).bind fun t => (Expr.evalList es σ).map (t :: ·) := rfl

/-- Evaluating arguments preserves their length. -/
theorem evalList_length {σ : Env} {es : List Expr} {ts : List Term}
    (h : Expr.evalList es σ = some ts) : ts.length = es.length := by
  induction es generalizing ts with
  | nil => rw [Expr.evalList_nil, Option.some.injEq] at h; exact h ▸ rfl
  | cons e es ih =>
    rw [Expr.evalList_cons] at h
    obtain ⟨t, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
    simp [ih hus]

theorem lookup_isSome_of_mem_evalList {ρ : Env} {v : Var}
    {es : List Expr} {ts : List Term} (h : Expr.evalList es ρ = some ts)
    (hv : Expr.var v ∈ es) : (Env.lookup v ρ).isSome := by
  induction es generalizing ts with
  | nil => simp at hv
  | cons e es ih =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h'⟩ := h
    obtain ⟨us, hus, -⟩ := Option.map_eq_some_iff.mp h'
    rcases List.mem_cons.mp hv with rfl | hv'
    · rw [Expr.eval_var] at ht
      rw [ht]
      rfl
    · exact ih hus hv'

end Expr
mutual

/-- Evaluation reads the environment only through `lookup`, so environments that
agree are interchangeable. This is what lets `Env.UnionAll`'s duplicate bindings be
ignored. -/
theorem Expr.eval_agree {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (e : Expr) :
    e.eval σ₁ = e.eval σ₂ := by
  match e with
  | .lit _ => rfl
  | .var v => simp only [Expr.eval, h v]
  | .app f args => simp only [Expr.eval, Expr.evalList_agree h args]
  | .min a b => simp only [Expr.eval, Expr.eval_agree h a, Expr.eval_agree h b]
theorem Expr.evalList_agree {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂)
    (es : List Expr) : Expr.evalList es σ₁ = Expr.evalList es σ₂ := by
  match es with
  | [] => rfl
  | e :: es =>
    rw [Expr.evalList_cons, Expr.evalList_cons, Expr.eval_agree h e, Expr.evalList_agree h es]

end

mutual

/-- **Evaluation depends only on the variables the expression mentions.** The partial form of
`Expr.eval_agree`: the two environments need agree nowhere else, so a substitution may be
extended or narrowed away from `e.vars` freely.

`Env.Agree` is the total case, and total agreement is more than a caller usually has — one
atom of a joined query is matched under its own substitution and read under the union, and
those agree only on that atom's own variables. -/
theorem Expr.eval_agreeOn {σ₁ σ₂ : Env} (e : Expr)
    (h : ∀ v ∈ e.vars, Env.lookup v σ₁ = Env.lookup v σ₂) :
    e.eval σ₁ = e.eval σ₂ := by
  match e with
  | .lit _ => rfl
  | .var v => simp only [Expr.eval, h v (by simp)]
  | .app f args => simp only [Expr.eval, Expr.evalList_agreeOn args (by simpa using h)]
  | .min a b =>
    simp only [Expr.eval, Expr.eval_agreeOn a (fun v hv => h v (by simp [hv])),
      Expr.eval_agreeOn b (fun v hv => h v (by simp [hv]))]
@[inherit_doc Expr.eval_agreeOn]
theorem Expr.evalList_agreeOn {σ₁ σ₂ : Env} (es : List Expr)
    (h : ∀ v ∈ Expr.varsList es, Env.lookup v σ₁ = Env.lookup v σ₂) :
    Expr.evalList es σ₁ = Expr.evalList es σ₂ := by
  match es with
  | [] => rfl
  | e :: es =>
    rw [Expr.evalList_cons, Expr.evalList_cons,
      Expr.eval_agreeOn e (fun v hv => h v (List.mem_union_iff.mpr (Or.inl hv))),
      Expr.evalList_agreeOn es (fun v hv => h v (List.mem_union_iff.mpr (Or.inr hv)))]

end

mutual

/-- Every expression whose variables are bound evaluates. -/
theorem Expr.eval_isSome {σ : Env} (e : Expr)
    (h : ∀ v ∈ e.vars, v ∈ Env.dom σ) :
    ∃ t, e.eval σ = some t := by
  match e with
  | .lit l => exact ⟨.lit l, rfl⟩
  | .var v =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      (Env.lookup_isSome_iff_mem_dom.mpr (h v (by simp)))
    exact ⟨t, ht⟩
  | .app f args =>
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome args (by simpa using h)
    exact ⟨.app f ts, by rw [Expr.eval_app_ctor, hts, Option.map_some]⟩
  | .min a b =>
    obtain ⟨x, hx⟩ := Expr.eval_isSome a (fun v hv => h v (by simp [hv]))
    obtain ⟨y, hy⟩ := Expr.eval_isSome b (fun v hv => h v (by simp [hv]))
    exact ⟨Term.least x y, by rw [Expr.eval_min, hx, Option.bind_some, hy, Option.map_some]⟩
theorem Expr.evalList_isSome {σ : Env} (es : List Expr)
    (h : ∀ v ∈ Expr.varsList es, v ∈ Env.dom σ) :
    ∃ ts, Expr.evalList es σ = some ts := by
  match es with
  | [] => exact ⟨[], rfl⟩
  | e :: es =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome e (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inl hv)))
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome es (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inr hv)))
    exact ⟨t :: ts, by rw [Expr.evalList_cons, ht, Option.bind_some, hts, Option.map_some]⟩

end

mutual

/-- **Extending the environment on the right keeps a value.** `Env.lookup` is left-biased, so
a variable the prefix already binds reads the same either way. -/
theorem Expr.eval_append_env {σ τ : Env} :
    ∀ (e : Expr) {t : Term}, e.eval σ = some t → e.eval (σ ++ τ) = some t
  | .lit _, _, h => h
  | .var _, _, h => Env.lookup_append_of_some h
  | .app f args, t, h => by
      rw [Expr.eval_app_ctor] at h ⊢
      obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
      rw [Expr.evalList_append_env args hts, Option.map_some]
      exact congrArg some hap
  | .min a b, t, h => by
      rw [Expr.eval_min] at h ⊢
      obtain ⟨x, hx, hmap⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rw [Expr.eval_append_env a hx, Option.bind_some, Expr.eval_append_env b hy,
        Option.map_some]
@[inherit_doc Expr.eval_append_env]
theorem Expr.evalList_append_env {σ τ : Env} :
    ∀ (es : List Expr) {ts : List Term},
      Expr.evalList es σ = some ts → Expr.evalList es (σ ++ τ) = some ts
  | [], _, h => h
  | e :: es, _, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [Expr.eval_append_env e ht, Option.bind_some,
        Expr.evalList_append_env es hts, Option.map_some]
      exact congrArg some hcons

end

theorem Expr.evalList_append {σ : Env} :
    ∀ {es fs : List Expr} {ts : List Term}, Expr.evalList (es ++ fs) σ = some ts →
      ∃ as bs, Expr.evalList es σ = some as ∧ Expr.evalList fs σ = some bs ∧
        ts = as ++ bs := by
  intro es
  induction es with
  | nil => intro fs ts h; exact ⟨[], ts, rfl, h, rfl⟩
  | cons e es ih =>
    intro fs ts h
    rw [List.cons_append, Expr.evalList] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨as, bs, has, hbs, rfl⟩ := ih hus
    exact ⟨t :: as, bs, by rw [Expr.evalList, ht, Option.bind_some, has, Option.map_some],
      hbs, rfl⟩



@[simp] theorem evalActions_nil {σ : Env} {db : Database} : evalActions σ db [] = some db := rfl
@[simp] theorem evalActions_cons {σ : Env} {db : Database} {a : Action} {as : List Action} :
    evalActions σ db (a :: as) = (evalAction σ db a).bind fun d => evalActions σ d as := rfl

theorem evalAction_expr_of_eval {σ : Env} {db : Database} {e : Expr} {t : Term}
    (h : e.eval σ = some t) : evalAction σ db (.expr e) = some (db.addTerm t) := by
  simp [evalAction, h]

theorem evalAction_eq_some {σ : Env} {db db' : Database} {a : Action}
    (h : evalAction σ db a = some db') :
    (∃ e t, a = .expr e ∧ e.eval σ = some t ∧ db' = db.addTerm t) ∨
    (∃ e₁ e₂ t₁ t₂, a = .union e₁ e₂ ∧ e₁.eval σ = some t₁ ∧
      e₂.eval σ = some t₂ ∧ ¬ (t₁.isLit ∨ t₂.isLit) ∧ db' = db.addEq t₁ t₂) ∨
    (∃ f es ts, a = .subsume f es ∧ Expr.evalList es σ = some ts ∧
      db' = (db.addTerm (.app f ts)).addSubsumed {.app f ts}) := by
  cases a with
  | expr e =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨e, t, rfl, ht, rfl⟩
  | union e₁ e₂ =>
    obtain ⟨t₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp at h
    · next hl =>
      cases Option.some.inj h
      exact .inr (.inl ⟨e₁, e₂, t₁, t₂, rfl, h₁, h₂, by simpa using hl, rfl⟩)
  | subsume f es =>
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr (.inr ⟨f, es, ts, rfl, hts, rfl⟩)

theorem evalAction_contained {σ : Env} {db db' : Database} {a : Action}
    (hdf : a.SubsumeFree) (h : evalAction σ db a = some db') : db.Contained db' := by
  rcases evalAction_eq_some h with ⟨_, t, rfl, _, rfl⟩ |
    ⟨_, _, t₁, t₂, rfl, _, _, _, rfl⟩ | ⟨_, _, _, rfl, _, _⟩
  · exact .addTerm t db
  · exact .addEq t₁ t₂ db
  · simp [Action.SubsumeFree, Action.monotoneB] at hdf


theorem evalAction_wf {σ : Env} {db db' : Database} (hw : db.WF) {a : Action}
    (h : evalAction σ db a = some db') : db'.WF := by
  rcases evalAction_eq_some h with ⟨_, t, _, _, rfl⟩ |
    ⟨_, _, t₁, t₂, _, _, _, hlit, rfl⟩ | ⟨f, _, ts, _, _, rfl⟩
  · exact hw.addTerm t
  · exact hw.addEq t₁ t₂ fun hl => absurd hl hlit
  · exact (hw.addTerm (.app f ts)).addSubsumed {.app f ts}

theorem evalActions_contained {σ : Env} {db db' : Database} {as : List Action}
    (hdf : Actions.SubsumeFree as) (h : evalActions σ db as = some db') : db.Contained db' := by
  induction as generalizing db with
  | nil => cases Option.some.inj h; exact .refl _
  | cons a as ih =>
    obtain ⟨d, ha, has⟩ := Option.bind_eq_some_iff.mp h
    exact (evalAction_contained (Actions.subsumeFree_cons.mp hdf).1 ha).trans
      (ih (Actions.subsumeFree_cons.mp hdf).2 has)


theorem evalActions_wf {σ : Env} {db db' : Database} (hw : db.WF) {as : List Action}
    (h : evalActions σ db as = some db') : db'.WF := by
  induction as generalizing db with
  | nil => cases Option.some.inj h; exact hw
  | cons a as ih =>
    obtain ⟨d, ha, has⟩ := Option.bind_eq_some_iff.mp h
    exact ih (evalAction_wf hw ha) has

theorem evalAction_agree {σ τ : Env} (h : Env.Agree σ τ) (db : Database) (a : Action) :
    evalAction σ db a = evalAction τ db a := by
  cases a <;> simp only [evalAction, Expr.eval_agree h, Expr.evalList_agree h]

theorem evalActions_agree {σ τ : Env} (h : Env.Agree σ τ) (db : Database) (as : List Action) :
    evalActions σ db as = evalActions τ db as := by
  induction as generalizing db with
  | nil => rfl
  | cons a as ih => simp only [evalActions, evalAction_agree h, ih]

theorem evalAction_subsumed {σ : Env} {d e : Database} {a : Action}
    (hdf : a.SubsumeFree) (h : evalAction σ d a = some e) : e.subsumed = d.subsumed := by
  rcases evalAction_eq_some h with ⟨_, _, rfl, _, rfl⟩ |
    ⟨_, _, _, _, rfl, _, _, _, rfl⟩ | ⟨_, _, _, rfl, _, rfl⟩
  · rfl
  · rfl
  · simp [Action.SubsumeFree, Action.monotoneB] at hdf

theorem evalActions_subsumed {σ : Env} {d e : Database} {as : List Action}
    (hdf : Actions.SubsumeFree as) (h : evalActions σ d as = some e) :
    e.subsumed = d.subsumed := by
  induction as generalizing d with
  | nil => cases h; rfl
  | cons a as ih =>
    obtain ⟨mid, ha, hs⟩ := Option.bind_eq_some_iff.mp h
    exact (ih (Actions.subsumeFree_cons.mp hdf).2 hs).trans
      (evalAction_subsumed (Actions.subsumeFree_cons.mp hdf).1 ha)

end Egglog
