import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Step

namespace Egglog
/-- The scope after a sequence of actions. The induction invariant of
`evalActions_isSome_of_scoped`, and not a static check, so it is here and not in `Spec/`. -/
def Actions.bind : List Action → Scope → Scope
  | [], Γ => Γ
  | a :: as, Γ => Actions.bind as (a.bind Γ)

/-- The scope after a program, as `Actions.bind`. -/
def Program.bind : Program → Scope → Scope
  | [], Γ => Γ
  | c :: cs, Γ => Program.bind cs (c.bind Γ)

/-- The scope describes the environment's domain exactly. This is the induction invariant
`programStep_of_scoped` carries across a run. -/
def Scope.Models (Γ : Scope) (σ : Env) : Prop := ∀ v, v ∈ Γ ↔ v ∈ Env.dom σ

theorem Scope.Models.empty : Scope.Models [] ([] : Env) := by simp [Models]

/-! ### Scoped, evaluable expressions evaluate -/
theorem Expr.eval_isSome_of_scoped {sig : Signature} {e : Expr} {Γ : Scope} {σ : Env}
    (hm : Γ.Models σ) (h : e.Scoped Γ) (he : e.Evaluable sig) :
    ∃ t, e.eval sig σ = some t :=
  e.eval_isSome (fun v hv => (hm v).mp (h v hv)) he

/-- An `Evaluable` application builds, so its value is not a literal. This is what
`Action.Evaluable` asks of a `union` operand, and what `evalAction`'s check then needs. -/
theorem Expr.not_isLit_of_isApp {sig : Signature} {e : Expr} {σ : Env} {t : Term}
    (ha : e.IsApp) (he : e.Evaluable sig) (h : e.eval sig σ = some t) : ¬ t.isLit := by
  match e with
  | .app f args =>
    obtain ⟨hp, hc⟩ := he f (by simp [Expr.fns])
    rw [Expr.eval_app_ctor hp hc] at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Term.isLit]

/-! ### Actions do not get stuck -/
theorem evalAction_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {a : Action} (h : a.Scoped Γ) (he : a.Evaluable db.sig) :
    ∃ db', evalAction db a = some db' ∧ (a.bind Γ).Models db'.env := by
  cases a with
  | expr e =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm h.2 he
    exact ⟨db.addTerm t, by simp [evalAction, ht], hm⟩
  | letBind v e =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm h he
    refine ⟨{ db.addTerm t with env := (v, t) :: db.env }, by simp [evalAction, ht], ?_⟩
    intro w
    simp only [Action.bind, List.mem_cons, Env.dom_cons]
    exact or_congr_right (hm w)
  | union e₁ e₂ =>
    obtain ⟨t₁, ht₁⟩ := Expr.eval_isSome_of_scoped hm h.1 he.1.2
    obtain ⟨t₂, ht₂⟩ := Expr.eval_isSome_of_scoped hm h.2 he.2.2
    have hl₁ := Expr.not_isLit_of_isApp he.1.1 he.1.2 ht₁
    have hl₂ := Expr.not_isLit_of_isApp he.2.1 he.2.2 ht₂
    exact ⟨db.addEq t₁ t₂, by simp [evalAction, ht₁, ht₂, hl₁, hl₂], hm⟩
  | set f args out =>
    obtain ⟨as, has⟩ := Expr.evalList_isSome args
      (fun v hv => by
        obtain ⟨e, hmem, hve⟩ := Expr.mem_varsList hv
        exact (hm v).mp (h.1 e hmem v hve))
      (fun g hg => by
        obtain ⟨e, hmem, hge⟩ := Expr.mem_fnsList hg
        exact he.1 e hmem g hge)
    obtain ⟨vs, hvs⟩ := Expr.evalList_isSome out
      (fun v hv => by
        obtain ⟨e, hmem, hve⟩ := Expr.mem_varsList hv
        exact (hm v).mp (h.2 e hmem v hve))
      (fun g hg => by
        obtain ⟨e, hmem, hge⟩ := Expr.mem_fnsList hg
        exact he.2 e hmem g hge)
    refine ⟨db.addTerm (.app f (as ++ vs)), by simp [evalAction, has, hvs], ?_⟩
    simpa [Action.bind] using hm

theorem evalActions_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {as : List Action} (h : Actions.Scoped as Γ) (he : Actions.Evaluable as db.sig) :
    ∃ db', evalActions db as = some db' ∧ (Actions.bind as Γ).Models db'.env := by
  induction as generalizing db Γ with
  | nil => exact ⟨db, rfl, hm⟩
  | cons a as ih =>
    obtain ⟨db₁, h₁, hm₁⟩ := evalAction_isSome_of_scoped hm h.1 he.1
    obtain ⟨db₂, h₂, hm₂⟩ := ih hm₁ h.2 (by rw [evalAction_sig h₁]; exact he.2)
    exact ⟨db₂, by simp [h₁, h₂], hm₂⟩

/-! ### A scoped, evaluable rule contributes on every match

`RunRules` unions the results of the firings whose actions succeed, so a rule whose
actions get stuck silently contributes nothing. This says that never happens for a
scoped, evaluable rule: the query binds exactly the pattern variables the actions were
checked against. -/
/-- A query substitution together with the globals models exactly the scope the
query binds. -/
theorem Query.bind_models {db : Database} {Γ : Scope} (hm : Γ.Models db.env) {q : Query}
    {σ : Env} (hσ : ValidQuerySubst db q σ) : (Query.bind q Γ).Models (db.env ++ σ) := by
  intro v
  rw [Query.bind, List.mem_union_iff, Env.dom_append, List.mem_append, hm v,
    hσ.mem_dom_iff, Query.mem_vars]
  constructor
  · rintro (hv | ⟨p, hp, hv⟩)
    · exact Or.inl hv
    · by_cases hd : v ∈ Env.dom db.env
      · exact Or.inl hd
      · exact Or.inr ⟨p, hp, p.mem_freeVars.mpr ⟨hv, hd⟩⟩
  · rintro (hv | ⟨p, hp, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨p, hp, (p.mem_freeVars.mp hv).1⟩

theorem evalLocalActions_isSome_of_scoped {db : Database} {Γ : Scope}
    (hm : Γ.Models db.env) {r : Rule} (hr : r.Scoped Γ) (hre : r.Evaluable db.sig)
    {σ : Env} (hσ : ValidQuerySubst db r.query σ) :
    ∃ d, evalLocalActions db r.actions σ = some d := by
  obtain ⟨d, hd, _⟩ := evalActions_isSome_of_scoped
    (db := { db with env := db.env ++ σ }) (Query.bind_models hm hσ) hr.2 hre
  exact ⟨{ d with env := db.env, rules := db.rules }, by simp [evalLocalActions, hd]⟩

/-! ### Scoped, evaluable programs do not get stuck

`Cmd.sigBind` is what the signature half of the invariant is: a command leaves the
signature `Program.Evaluable` checks the rest of the program against. -/
theorem cmdStep_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {c : Cmd} (hns : c.NoSaturate) (h : c.Scoped Γ) (he : c.Evaluable db.sig) :
    ∃ db', CmdStep db c db' ∧ (c.bind Γ).Models db'.env ∧
      db'.sig = c.sigBind db.sig := by
  cases c with
  | action a =>
    obtain ⟨db', hv, hm'⟩ := evalAction_isSome_of_scoped hm h he
    exact ⟨db', ⟨db', hv, Relation.ReflTransGen.refl⟩, hm', evalAction_sig hv⟩
  | rule r => exact ⟨_, ⟨_, rfl, Relation.ReflTransGen.refl⟩, hm, rfl⟩
  | run R => exact ⟨_, ⟨_, rfl, Relation.ReflTransGen.refl⟩, hm, rfl⟩
  | saturate R => exact (hns : False).elim
  | decl f d => exact ⟨_, ⟨_, rfl, Relation.ReflTransGen.refl⟩, hm, rfl⟩

theorem programStep_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {p : Program} (hns : p.NoSaturate) (h : Program.Scoped p Γ)
    (he : Program.Evaluable p db.sig) :
    ∃ db', ProgramStep db p db' ∧ (Program.bind p Γ).Models db'.env := by
  induction p generalizing db Γ with
  | nil => exact ⟨db, .nil, hm⟩
  | cons c cs ih =>
    obtain ⟨db₁, h₁, hm₁, hs₁⟩ := cmdStep_of_scoped hm (hns c List.mem_cons_self) h.1 he.1
    obtain ⟨db₂, h₂, hm₂⟩ :=
      ih hm₁ (fun c' hc' => hns c' (List.mem_cons_of_mem c hc')) h.2 (by rw [hs₁]; exact he.2)
    exact ⟨db₂, .cons h₁ h₂, hm₂⟩

/-- A program whose variables are bound and whose applications all build runs to
completion: some state is reachable, rather than the run getting stuck at an action that
cannot evaluate.

`Evaluable` is a hypothesis rather than part of `WellScoped` because it is not about
scope: it is what `Expr.eval` needs on top of a bound environment, and folding it into
the scope check would make "well-scoped" reject `(min 1 2)`, which egglog accepts.

The merge phase is what stops this from being uniqueness as well: `CmdStep` may stop
anywhere in `MergeClosure`. On the constructor fragment there is nothing to stop in, and
`ProgramStep.det` says so.

`hns` is not removable: a `Cmd.saturate` reaches a state only if its ruleset *has* a
fixpoint, and `(rule () ((f (g x))))` under a saturating run has none. Scope and
evaluability are properties of the syntax and cannot see that, so the totality theorem is
for the fragment whose round counts are written down. -/
theorem programStep_isSome {p : Program} (hns : p.NoSaturate) (h : WellScoped p)
    (he : p.Evaluable Database.empty.sig) : ∃ db, ProgramStep Database.empty p db := by
  obtain ⟨db, hdb, _⟩ := programStep_of_scoped
    (db := Database.empty) Scope.Models.empty hns h he
  exact ⟨db, hdb⟩

end Egglog
