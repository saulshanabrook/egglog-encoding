import EgglogSemantics.Spec.Eval
import EgglogSemantics.Proofs.Congruence

namespace Egglog
namespace Expr
@[simp] theorem eval_lit {l : Lit} {σ : Env} : (Expr.lit l).eval σ = some (.lit l) := rfl

@[simp] theorem eval_var {v : Var} {σ : Env} : (Expr.var v).eval σ = Env.lookup v σ := rfl

@[simp] theorem eval_app {f : FnName} {args : List Expr} {σ : Env} :
    (Expr.app f args).eval σ = (Expr.evalList args σ).map (Term.app f) := rfl

@[simp] theorem evalList_nil {σ : Env} : Expr.evalList [] σ = some [] := rfl

@[simp] theorem evalList_cons {e : Expr} {es : List Expr} {σ : Env} :
    Expr.evalList (e :: es) σ = (e.eval σ).bind fun t => (Expr.evalList es σ).map (t :: ·) :=
  rfl

end Expr
mutual

/-- Evaluation reads the environment only through `lookup`, so environments that
agree are interchangeable. This is what lets `Env-Union`'s duplicate bindings be
ignored. -/
theorem Expr.eval_agree {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (e : Expr) :
    e.eval σ₁ = e.eval σ₂ := by
  match e with
  | .lit _ => rfl
  | .var v => exact h v
  | .app f args => rw [Expr.eval_app, Expr.eval_app, Expr.evalList_agree h args]

theorem Expr.evalList_agree {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (es : List Expr) :
    Expr.evalList es σ₁ = Expr.evalList es σ₂ := by
  match es with
  | [] => rfl
  | e :: es =>
    rw [Expr.evalList_cons, Expr.evalList_cons, Expr.eval_agree h e, Expr.evalList_agree h es]

end

mutual

/-- Evaluation gets stuck only on an unbound variable, so an expression whose
variables the environment all bind evaluates. This is the whole content of the
Redex's type checker. -/
theorem Expr.eval_isSome {σ : Env} (e : Expr) (h : ∀ v ∈ e.vars, v ∈ Env.dom σ) :
    ∃ t, e.eval σ = some t := by
  match e with
  | .lit l => exact ⟨.lit l, rfl⟩
  | .var v =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      (Env.lookup_isSome_iff_mem_dom.mpr (h v (by simp)))
    exact ⟨t, ht⟩
  | .app f args =>
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome args (by simpa using h)
    exact ⟨.app f ts, by rw [Expr.eval_app, hts, Option.map_some]⟩

theorem Expr.evalList_isSome {σ : Env} (es : List Expr)
    (h : ∀ v ∈ Expr.varsList es, v ∈ Env.dom σ) : ∃ ts, Expr.evalList es σ = some ts := by
  match es with
  | [] => exact ⟨[], rfl⟩
  | e :: es =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome e fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inl hv))
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome es fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inr hv))
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
    (∃ e t, a = .expr e ∧ e.eval db.env = some t ∧ db' = db.addTerm t) ∨
      (∃ v e t, a = .letBind v e ∧ e.eval db.env = some t ∧
        db' = { db.addTerm t with env := (v, t) :: db.env }) ∨
      (∃ e₁ e₂ t₁ t₂, a = .union e₁ e₂ ∧ e₁.eval db.env = some t₁ ∧
        e₂.eval db.env = some t₂ ∧ db' = db.addEq t₁ t₂) ∨
      (∃ f args out as vs, a = .set f args out ∧ Expr.evalList args db.env = some as ∧
        Expr.evalList out db.env = some vs ∧ db' = db.addRow f as vs) := by
  cases a with
  | expr e =>
    cases hv : e.eval db.env with
    | none => simp [evalAction, hv] at h
    | some t =>
      simp only [evalAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inl ⟨e, t, rfl, hv, h.symm⟩
  | letBind v e =>
    cases hv : e.eval db.env with
    | none => simp [evalAction, hv] at h
    | some t =>
      simp only [evalAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨v, e, t, rfl, hv, h.symm⟩)
  | union e₁ e₂ =>
    cases hv₁ : e₁.eval db.env with
    | none => simp [evalAction, hv₁] at h
    | some t₁ =>
      cases hv₂ : e₂.eval db.env with
      | none => simp [evalAction, hv₁, hv₂] at h
      | some t₂ =>
        simp only [evalAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inl ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, h.symm⟩))
  | set f args out =>
    cases hv₁ : Expr.evalList args db.env with
    | none => simp [evalAction, hv₁] at h
    | some as =>
      cases hv₂ : Expr.evalList out db.env with
      | none => simp [evalAction, hv₁, hv₂] at h
      | some vs =>
        simp only [evalAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inr ⟨f, args, out, as, vs, rfl, hv₁, hv₂, h.symm⟩))

theorem evalAction_contained {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db.Contained db' := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, rfl⟩ | ⟨f, _, _, as, vs, -, -, -, rfl⟩
  · exact .addTerm t db
  · exact ⟨Set.subset_union_left, Set.subset_union_left, subset_rfl⟩
  · exact .addEq t₁ t₂ db
  · exact .addRow f as vs db

theorem evalAction_rules {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.rules = db.rules := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ | ⟨_, _, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, rfl⟩
  · rfl
  · rfl
  · rfl
  · simp

theorem evalAction_wf {db db' : Database} (hw : db.WF) {a : Action}
    (h : evalAction db a = some db') : db'.WF := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, rfl⟩ | ⟨f, _, _, as, vs, -, -, -, rfl⟩
  · exact hw.addTerm t
  · refine ⟨(hw.addTerm t).subtermClosed, (hw.addTerm t).eqsInTerms, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact db.mem_addTerm t
    · exact (hw.addTerm t).envInTerms b hb
  · exact hw.addEq t₁ t₂
  · exact hw.addRow f as vs

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

/-! ### Agreeing environments are interchangeable

`Expr.eval_agree` says evaluation reads the environment only through `lookup`. Lifting
that to whole action sequences is what justifies two places the semantics is loose
about environments on purpose: the Redex `Env-Union` can leave a variable bound twice,
and `ValidEnv` fixes a substitution's domain only up to permutation. -/
theorem evalAction_envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (a : Action) :
    Option.Rel Database.EnvAgree (evalAction d₁ a) (evalAction d₂ a) := by
  cases a with
  | expr e =>
    simp only [evalAction, ← Expr.eval_agree h.env e]
    cases e.eval d₁.env with
    | none => exact .none
    | some t =>
      exact .some ⟨h.sig, by simp [Database.addTerm, h.terms],
        by simp [Database.addTerm, h.rows], h.eqs, h.rules, h.env⟩
  | letBind v e =>
    simp only [evalAction, ← Expr.eval_agree h.env e]
    cases e.eval d₁.env with
    | none => exact .none
    | some t =>
      refine .some ⟨h.sig, by simp [Database.addTerm, h.terms],
        by simp [Database.addTerm, h.rows], h.eqs, h.rules, fun w => ?_⟩
      by_cases hw : w = v <;> simp [hw, h.env w]
  | union e₁ e₂ =>
    simp only [evalAction, ← Expr.eval_agree h.env e₁, ← Expr.eval_agree h.env e₂]
    cases e₁.eval d₁.env with
    | none => exact .none
    | some t₁ =>
      cases e₂.eval d₁.env with
      | none => exact .none
      | some t₂ =>
        exact .some ⟨h.sig, by simp [Database.addEq, Database.addTerm, h.terms],
          by simp [Database.addEq, Database.addTerm, h.rows],
          by simp [Database.addEq, h.eqs], h.rules, h.env⟩
  | set f args out =>
    simp only [evalAction, ← Expr.evalList_agree h.env args, ← Expr.evalList_agree h.env out]
    cases Expr.evalList args d₁.env with
    | none => exact .none
    | some as =>
      cases Expr.evalList out d₁.env with
      | none => exact .none
      | some vs =>
        exact .some (h.addRow f as vs)

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
    ⟨rfl, rfl, rfl, rfl, rfl, Env.Agree.append_left db.env h⟩
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

theorem evalLocalActions_contained {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db.Contained db' := by
  obtain ⟨_, hv, rfl⟩ := evalLocalActions_eq_some h
  exact ⟨(evalActions_contained hv).terms, (evalActions_contained hv).rows,
    (evalActions_contained hv).eqs⟩

/-- Local actions preserve well-formedness provided the substitution only mentions
terms the database holds — which is what `ValidEnv` guarantees. -/
theorem evalLocalActions_wf {db db' : Database} (hw : db.WF) {as : List Action} {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (h : evalLocalActions db as σ = some db') : db'.WF := by
  have hw' : Database.WF { db with env := db.env ++ σ } := by
    refine ⟨hw.subtermClosed, hw.eqsInTerms, fun b hb => ?_⟩
    exact (List.mem_append.mp hb).elim (hw.envInTerms b) (hσ b)
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  have hd := evalActions_wf hw' hv
  exact ⟨hd.subtermClosed, hd.eqsInTerms,
    fun b hb => (evalActions_contained hv).terms (hw.envInTerms b hb)⟩

end Egglog
