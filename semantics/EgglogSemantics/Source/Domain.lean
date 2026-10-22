import EgglogSemantics.Spec.Scope
import EgglogSemantics.Spec.Eval

/-!
# The source fragment

Constructor discovery, source scoping, and `Program.Fragment`: the one definition of the
source programs the congruence pass compiles and the source proof checker accepts. Decided
by `instDecidableFragment`, so a program is checked by `decide`.
-/

namespace Egglog

/-! ### The constructors a program mentions

The language has no declarations, so the names and arities a program uses are read off
its expressions; each pass prepares its generated tables from them. -/
mutual

/-- The `(name, arity)` pairs an expression applies. -/
def Expr.ctors : Expr → List (FnName × Nat)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args.length) :: Expr.ctorsList args
  | .min a b => a.ctors ++ b.ctors

/-- `Expr.ctors` over an argument list. -/
def Expr.ctorsList : List Expr → List (FnName × Nat)
  | [] => []
  | e :: es => e.ctors ++ Expr.ctorsList es

end

/-- `Expr.ctors` over a pattern. -/
def Pattern.ctors : Pattern → List (FnName × Nat)
  | .expr e => e.ctors
  | .eq e₁ e₂ => e₁.ctors ++ e₂.ctors
  | .ne e₁ e₂ => e₁.ctors ++ e₂.ctors

/-- Constructor occurrences in a source action. -/
def Action.ctors : Action → List (FnName × Nat)
  | .expr e => e.ctors
  | .union e₁ e₂ => e₁.ctors ++ e₂.ctors
  | .delete e => e.ctors

/-- `Expr.ctors` over a rule. -/
def Rule.ctors (r : Rule) : List (FnName × Nat) :=
  (r.query.flatMap Pattern.ctors) ++ (r.actions.flatMap Action.ctors)

/-- `Expr.ctors` over a command. -/
def Cmd.ctors (c : Cmd) : List (FnName × Nat) := c.rules.flatMap Rule.ctors

/-- Every function name and arity the program mentions, deduplicated. -/
def Program.ctors (P : Program) : List (FnName × Nat) :=
  (P.commands.flatMap Cmd.ctors ++ P.check.flatMap Pattern.ctors).dedup

/-! ### Names -/

/-- The variables an action mentions. -/
def Action.vars : Action → List Var
  | .expr e => e.vars
  | .union e₁ e₂ => e₁.vars ∪ e₂.vars
  | .delete e => e.vars

/-- The variables a rule mentions. -/
def Rule.vars (r : Rule) : List Var := r.query.vars ∪ (r.actions.flatMap Action.vars)

/-- `Rule.vars` over a command. -/
def Cmd.vars (c : Cmd) : List Var := c.rules.flatMap Rule.vars

/-- Every variable the program mentions. -/
def Program.vars (P : Program) : List Var :=
  (P.commands.flatMap Cmd.vars ++ P.check.vars).dedup

/-- **Every name the source text mentions**, of the two kinds the generated namespace has
to stay clear of: a function name and a variable. -/
def Program.names (P : Program) : List String :=
  P.ctors.map Prod.fst ++ P.vars

/-! ### What the query flattening drops

`encodeQueryExpr` flattens an *application* and returns a leaf unchanged, so `encodePattern`
emits **no atom** for a source pattern whose expression is a bare literal or a bare variable.
Both are conditions on the source program's **text**, decidable, and both are folded into
`Program.Fragment` below. -/
/-- **The pattern has a witness position.** `Matches` asks for a term the source *holds*
congruent to the instance, and a bare literal has none: the source may never have built it,
and `encodePattern` emits no atom that would say it did. -/
def Pattern.Grounded : Pattern → Prop
  | .expr e => ∀ l, e ≠ .lit l
  | .eq e₁ e₂ => (∀ l, e₁ ≠ .lit l) ∨ (∀ l, e₂ ≠ .lit l)
  | .ne e₁ e₂ => (∀ l, e₁ ≠ .lit l) ∨ (∀ l, e₂ ≠ .lit l)

/-- **The witness position exists at this source state.** `Pattern.Grounded` says the pattern
is not a bare literal, which is one way to have a witness; a bare literal the source **holds**
is another. This is what the correspondence consumes; `Pattern.Grounded` is the text condition
`Program.Fragment` states and implies it. -/
def Pattern.GroundedAt (src : Database) : Pattern → Prop
  | .expr e => ∀ l, e = .lit l → Term.lit l ∈ src.terms
  | .eq e₁ e₂ => (∀ l, e₁ = .lit l → Term.lit l ∈ src.terms) ∨
      (∀ l, e₂ = .lit l → Term.lit l ∈ src.terms)
  | .ne e₁ e₂ => (∀ l, e₁ = .lit l → Term.lit l ∈ src.terms) ∨
      (∀ l, e₂ = .lit l → Term.lit l ∈ src.terms)

/-- **The queries the flattening handles.** Every pattern is `Pattern.Grounded` and
`Pattern.Scoped` — no bare literal, and a fact is an application, as in egglog — and the
query is `Query.VarsKeyed`. -/
def Query.Encodable (q : Query) : Prop :=
  (∀ p ∈ q, p.Grounded ∧ p.Scoped) ∧ Query.VarsKeyed q

/-- `Query.Encodable` at every rule the command fires. -/
def Cmd.QueryEncodable (c : Cmd) : Prop := ∀ r ∈ c.rules, r.query.Encodable

/-- `Query.Encodable` at every rule and at the final check. -/
def Program.QueriesEncodable (P : Program) : Prop :=
  (∀ c ∈ P.commands, c.QueryEncodable) ∧ P.check.Encodable

/-! ### Rule-head legality

A stuck rule head contributes no writes. The fragment excludes literal unions so that
source and compiled firings agree. -/

mutual

/-- No literal occurs in the expression. -/
def Expr.litFreeB : Expr → Bool
  | .lit _ => false
  | .var _ => true
  | .app _ args => Expr.litFreeListB args
  | .min a b => Expr.litFreeB a && Expr.litFreeB b

/-- `Expr.litFreeB` over an argument list. -/
def Expr.litFreeListB : List Expr → Bool
  | [] => true
  | e :: es => Expr.litFreeB e && Expr.litFreeListB es

end

/-- No literal occurs in an expression the action **evaluates**. Patterns are not read: a
literal in a query builds nothing, and a variable is only ever bound to a term the source
holds. -/
def Action.litFreeB : Action → Bool
  | .expr e => e.litFreeB
  | .union e₁ e₂ => e₁.litFreeB && e₂.litFreeB
  | .delete e => e.litFreeB

/-- `Action.litFreeB` at every action a rule runs. -/
def Rule.litFreeB (r : Rule) : Bool := r.actions.all Action.litFreeB

/-- `Rule.litFreeB` at every rule a command fires. -/
def Cmd.litFreeB (c : Cmd) : Bool := c.rules.all Rule.litFreeB

/-- `Action.UnionFree`, computed. -/
def Action.unionFreeB : Action → Bool
  | .union _ _ => false
  | _ => true

/-- The rule head asserts no union. -/
def Rule.unionFreeB (r : Rule) : Bool := r.actions.all Action.unionFreeB

/-- No rule head asserts a union. -/
def Cmd.ruleUnionFreeB (c : Cmd) : Bool := c.rules.all Rule.unionFreeB

/-! ### Monotone source programs

Disequality guards and deletes are what the compiled rebuilding uses to replace rows.
Source programs only add facts, so both are excluded from the fragment; their semantics
is nonetheless the general one. -/

/-- No disequality guard. -/
def Pattern.monotoneB : Pattern → Bool
  | .ne _ _ => false
  | _ => true

/-- No delete. -/
def Action.monotoneB : Action → Bool
  | .delete _ => false
  | _ => true

/-- The rule tests no disequality and deletes no row. -/
def Rule.monotoneB (r : Rule) : Bool :=
  r.query.all Pattern.monotoneB && r.actions.all Action.monotoneB

/-- The command tests no disequality and deletes no row. -/
def Cmd.monotoneB (c : Cmd) : Bool := c.rules.all Rule.monotoneB

/-- No rule and not the final check tests a disequality, and no rule deletes a row. -/
def Program.monotoneB (P : Program) : Bool :=
  P.commands.all Cmd.monotoneB && P.check.all Pattern.monotoneB

/-! #### The head-scope check, and deciding it

`Spec/Scope.lean`'s `Actions.Scoped` at a rule's own query variables. Every action in
the head uses the same query substitution; actions do not introduce bindings. -/

/-- **Every variable a rule head reads is one the rule's own query binds**, and a build or
delete is an application. -/
def Rule.HeadScoped (r : Rule) : Prop := Actions.Scoped r.actions (Query.vars r.query)

@[inherit_doc Rule.HeadScoped]
def Cmd.HeadScoped (c : Cmd) : Prop := ∀ r ∈ c.rules, r.HeadScoped

@[inherit_doc Rule.HeadScoped]
def Program.HeadsScoped (P : Program) : Prop := ∀ c ∈ P.commands, c.HeadScoped

instance Expr.decidableIsApp : ∀ e : Expr, Decidable e.IsApp
  | .app _ _ => .isTrue trivial
  | .lit _ => .isFalse (fun h => (h : False))
  | .var _ => .isFalse (fun h => (h : False))
  | .min _ _ => .isFalse (fun h => (h : False))

instance Expr.decidableScoped (e : Expr) (Γ : Scope) : Decidable (e.Scoped Γ) :=
  inferInstanceAs (Decidable (∀ v ∈ e.vars, v ∈ Γ))

instance Action.decidableScoped : ∀ (a : Action) (Γ : Scope), Decidable (a.Scoped Γ)
  | .expr e, Γ => inferInstanceAs (Decidable (e.IsApp ∧ e.Scoped Γ))
  | .union e₁ e₂, Γ => inferInstanceAs (Decidable (e₁.Scoped Γ ∧ e₂.Scoped Γ))
  | .delete e, Γ => inferInstanceAs (Decidable (e.IsApp ∧ e.Scoped Γ))

instance Actions.decidableScoped : ∀ (as : List Action) (Γ : Scope),
    Decidable (Actions.Scoped as Γ)
  | [], _ => .isTrue trivial
  | a :: as, Γ => @instDecidableAnd _ _ (Action.decidableScoped a Γ)
      (Actions.decidableScoped as Γ)

instance Rule.decidableHeadScoped (r : Rule) : Decidable r.HeadScoped :=
  inferInstanceAs (Decidable (Actions.Scoped r.actions (Query.vars r.query)))

instance Cmd.decidableHeadScoped (c : Cmd) : Decidable c.HeadScoped :=
  inferInstanceAs (Decidable (∀ r ∈ c.rules, r.HeadScoped))

instance Program.decidableHeadsScoped (P : Program) : Decidable P.HeadsScoped :=
  inferInstanceAs (Decidable (∀ c ∈ P.commands, c.HeadScoped))

/-- Every name is applied at one arity. -/
def Program.AritiesAgree (P : Program) : Prop :=
  ∀ p ∈ P.ctors, ∀ q ∈ P.ctors, p.1 = q.1 → p.2 = q.2

instance (P : Program) : Decidable P.AritiesAgree :=
  inferInstanceAs (Decidable (∀ p ∈ P.ctors, ∀ q ∈ P.ctors, p.1 = q.1 → p.2 = q.2))

/-- **The source fragment**: the programs the congruence pass compiles, the completeness
theorem is about, and the source proof checker accepts. -/
@[blueprint "def:fragment"
  (title := /-- Supported source fragment -/)
  (statement := /-- Source programs contain no disequality guard, no delete, and no
  $\min$, and their names avoid the generated \texttt{@} prefix. Expression patterns and
  build actions are applications. Equality patterns are not pairs of bare literals, and
  every query variable occurs as an application argument. Head variables are query-bound,
  and each name has a consistent arity. Finally, either all heads are union-free or all
  head expressions are literal-free. -/)]
structure Program.Fragment (P : Program) : Prop where
  /-- Source programs only add facts; disequality and deletion serve compiled rebuilding. -/
  monotone : P.monotoneB = true
  /-- The source never computes with `min`: every expression builds. -/
  noMin : Program.OrderingFree P
  /-- Source function and variable names cannot collide with generated names. -/
  noAt : ∀ n ∈ P.names, ¬ "@".isPrefixOf n
  /-- Patterns supply constructor reads and key every variable. Flattening a bare literal
  pattern would otherwise erase its existence requirement. -/
  queryEncodable : P.QueriesEncodable
  /-- Either no action performs a union, or no literal can be built and handed to one. -/
  noLitUnion : (∀ c ∈ P.commands, c.ruleUnionFreeB = true) ∨
    ∀ c ∈ P.commands, c.litFreeB = true
  /-- Each source function has a unique arity. -/
  aritiesAgree : P.AritiesAgree
  /-- Every rule-head variable is query-bound, and a build action is an application.
  This excludes a bare unbound head that the compiler would otherwise silently erase. -/
  headsScoped : P.HeadsScoped

/-! #### Deciding the fragment -/

/-- A bare literal, computed. -/
def Expr.isLitB : Expr → Bool
  | .lit _ => true
  | _ => false

instance Expr.decidableIsLitFree (e : Expr) : Decidable (∀ l, e ≠ .lit l) :=
  decidable_of_iff (e.isLitB = false) (by cases e <;> simp [Expr.isLitB])

instance : ∀ p : Pattern, Decidable p.Grounded
  | .expr e => inferInstanceAs (Decidable (∀ l, e ≠ .lit l))
  | .eq e₁ e₂ => inferInstanceAs (Decidable ((∀ l, e₁ ≠ .lit l) ∨ ∀ l, e₂ ≠ .lit l))
  | .ne e₁ e₂ => inferInstanceAs (Decidable ((∀ l, e₁ ≠ .lit l) ∨ ∀ l, e₂ ≠ .lit l))

instance : ∀ p : Pattern, Decidable p.Scoped
  | .expr e => inferInstanceAs (Decidable e.IsApp)
  | .eq _ _ => .isTrue trivial
  | .ne _ _ => .isTrue trivial

/-- `Expr.var v ∈ args`, computed: `Expr` carries no `BEq`. -/
def Expr.memVarB (v : Var) : List Expr → Bool
  | [] => false
  | .var w :: es => w == v || Expr.memVarB v es
  | _ :: es => Expr.memVarB v es

theorem Expr.memVarB_iff (v : Var) : ∀ args : List Expr,
    Expr.memVarB v args = true ↔ Expr.var v ∈ args
  | [] => by simp [Expr.memVarB]
  | .lit _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es
  | .var w :: es => by
      simp only [Expr.memVarB, Bool.or_eq_true, beq_iff_eq, List.mem_cons, Expr.var.injEq,
        Expr.memVarB_iff v es]
      exact or_congr_left eq_comm
  | .app _ _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es
  | .min _ _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es

mutual

/-- `Expr.ArgVar`, computed. -/
def Expr.argVarB (v : Var) : Expr → Bool
  | .lit _ => false
  | .var _ => false
  | .app _ args => Expr.memVarB v args || Expr.argVarListB v args
  | .min a b => Expr.argVarB v a || Expr.argVarB v b

/-- `Expr.ArgVarList`, computed. -/
def Expr.argVarListB (v : Var) : List Expr → Bool
  | [] => false
  | e :: es => Expr.argVarB v e || Expr.argVarListB v es

end

mutual

theorem Expr.argVarB_iff (v : Var) : ∀ e : Expr, Expr.argVarB v e = true ↔ Expr.ArgVar v e
  | .lit _ => by simp [Expr.argVarB, Expr.ArgVar]
  | .var _ => by simp [Expr.argVarB, Expr.ArgVar]
  | .app _ args => by
      simp only [Expr.argVarB, Expr.ArgVar, Bool.or_eq_true, Expr.memVarB_iff,
        Expr.argVarListB_iff v args]
  | .min a b => by
      simp only [Expr.argVarB, Expr.ArgVar, Bool.or_eq_true, Expr.argVarB_iff v a,
        Expr.argVarB_iff v b]

theorem Expr.argVarListB_iff (v : Var) : ∀ es : List Expr,
    Expr.argVarListB v es = true ↔ Expr.ArgVarList v es
  | [] => by simp [Expr.argVarListB, Expr.ArgVarList]
  | e :: es => by
      simp only [Expr.argVarListB, Expr.ArgVarList, Bool.or_eq_true, Expr.argVarB_iff v e,
        Expr.argVarListB_iff v es]

end

/-- `Pattern.ArgVar`, computed. -/
def Pattern.argVarB (v : Var) : Pattern → Bool
  | .expr e => e.argVarB v
  | .eq e₁ e₂ => e₁.argVarB v || e₂.argVarB v
  | .ne e₁ e₂ => e₁.argVarB v || e₂.argVarB v

theorem Pattern.argVarB_iff (v : Var) (p : Pattern) :
    p.argVarB v = true ↔ Pattern.ArgVar v p := by
  cases p <;> simp [Pattern.argVarB, Pattern.ArgVar, Expr.argVarB_iff]

instance (v : Var) (p : Pattern) : Decidable (Pattern.ArgVar v p) :=
  decidable_of_iff (p.argVarB v = true) (Pattern.argVarB_iff v p)

instance (q : Query) : Decidable (Query.VarsKeyed q) :=
  inferInstanceAs (Decidable (∀ v ∈ Query.vars q, ∃ p ∈ q, Pattern.ArgVar v p))

instance (q : Query) : Decidable q.Encodable :=
  inferInstanceAs (Decidable ((∀ p ∈ q, p.Grounded ∧ p.Scoped) ∧ Query.VarsKeyed q))

instance (c : Cmd) : Decidable c.QueryEncodable :=
  inferInstanceAs (Decidable (∀ r ∈ c.rules, r.query.Encodable))

instance (P : Program) : Decidable P.QueriesEncodable :=
  inferInstanceAs (Decidable ((∀ c ∈ P.commands, c.QueryEncodable) ∧ P.check.Encodable))

instance instDecidableFragment (P : Program) : Decidable P.Fragment :=
  decidable_of_iff (P.monotoneB = true ∧ Program.OrderingFree P ∧
      (∀ n ∈ P.names, ¬ "@".isPrefixOf n) ∧
      P.QueriesEncodable ∧
      ((∀ c ∈ P.commands, c.ruleUnionFreeB = true) ∨ ∀ c ∈ P.commands, c.litFreeB = true) ∧
      P.AritiesAgree ∧ P.HeadsScoped)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
      fun h => ⟨h.monotone, h.noMin, h.noAt, h.queryEncodable, h.noLitUnion, h.aritiesAgree,
        h.headsScoped⟩⟩

end Egglog
