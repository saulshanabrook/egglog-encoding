import Batteries.Data.List.Basic

/-!
# Syntax of the modelled egglog fragment

```
Program = (Cmd ...)
Cmd     = Action | Rule | (run R) | (saturate R) | Decl
Decl    = (datatype ...) | (constructor ...) | (function ... :merge ...)
Rule    = (rule Query Actions :ruleset R)
Query   = (Pattern ...)
Pattern = expr | (= expr expr) | (= (values expr ...) (f expr ...))
Action  = expr | (let var expr) | (union expr expr) | (set (f expr ...) expr ...)
expr    = number | var | (f expr ...)
```
-/

namespace Egglog
/-- A variable, global or rule-local. -/
abbrev Var := String

/-- The name of a constructor or function. -/
abbrev FnName := String

/-- A base value. `Int` is the only one modelled. -/
inductive Lit where
  | int : Int → Lit
  deriving DecidableEq, Repr, Inhabited

/-- An expression. Evaluated against an environment to build a `Term`. -/
inductive Expr where
  | lit : Lit → Expr
  | var : Var → Expr
  | app : FnName → List Expr → Expr

/-- One conjunct of a rule's query: a pattern to match, an equality constraint, or an
entry to read. -/
inductive Pattern where
  | expr : Expr → Pattern
  | eq : Expr → Expr → Pattern
  /-- `f(a…, v…)`: read `f`'s entry at the key `a…` and bind its value columns `v…`.
  **The only read in the language.** -/
  | values : List Expr → FnName → List Expr → Pattern

/-- A rule's query, matched conjunctively. -/
abbrev Query := List Pattern

/-- An action: build a term, bind a variable, assert an equality, or record an entry. -/
inductive Action where
  | expr : Expr → Action
  | letBind : Var → Expr → Action
  | union : Expr → Expr → Action
  /-- `(set (f args…) out…)`: record `f args… ↦ out…`, one output expression per value
  column. -/
  | set : FnName → List Expr → List Expr → Action

/-- A ruleset name. A rule joins one with `:ruleset <name>`, and a run names the one it
fires. egglog's *unnamed* ruleset is the empty name: that is what a rule with no
`:ruleset` joins and what `(run 1)` runs (`egglog/src/ast/parse.rs:713`, `:849`); a named
one is declared with `(ruleset <name>)` (`:686`). -/
abbrev RulesetName := String

/-- A rule. Its actions run once per substitution satisfying its query, in the rounds of
the ruleset it joins. -/
structure Rule where
  query : Query
  actions : List Action
  /-- The ruleset this rule belongs to. Only a run naming it fires it. -/
  ruleset : RulesetName

/-- How two entries of a **merge function** colliding on one key combine: `merge body res`
runs `body` once with the two outputs bound by `mergeEnv`, then evaluates `res`, one
expression per value column; `noMerge` forbids a collision outright. -/
inductive MergeSpec where
  | merge : List Action → List Expr → MergeSpec
  | noMerge

/-- A function declaration: a constructor when `merge = none`, a merge function when not. -/
structure FnDecl where
  /-- The number of key columns. Read by `MergeStep`, which needs to know where a term's
  key ends and its value columns begin. -/
  arity : Nat
  /-- The number of value columns. One for a constructor. -/
  outArity : Nat
  /-- How collisions are resolved, or `none` for a constructor. -/
  merge : Option MergeSpec

/-- How many children a term recording an entry of this function carries: a constructor's
entry is `f(a…)`, a merge function's `f(a…, v…)`. -/
def FnDecl.entryWidth (d : FnDecl) : Nat :=
  if d.merge.isNone then d.arity else d.arity + d.outArity

/-- The declared functions. Undeclared names have no entry. -/
abbrev Signature := FnName → Option FnDecl

/-- How `f` resolves a collision; `none` for a constructor and an undeclared name alike. -/
def Signature.mergeOf (sig : Signature) (f : FnName) : Option MergeSpec :=
  (sig f).bind FnDecl.merge

/-- `f` is a **declared** constructor. An undeclared name is neither this nor a merge
function, and `Expr.eval` has no rule for it. -/
def Signature.IsCtor (sig : Signature) (f : FnName) : Prop :=
  ∃ d, sig f = some d ∧ d.merge = none

instance (sig : Signature) (f : FnName) : Decidable (sig.IsCtor f) :=
  decidable_of_iff (((sig f).map fun d => d.merge.isNone).getD false = true) (by
    unfold Signature.IsCtor
    cases h : sig f with
    | none => simp
    | some d => simp [Option.isNone_iff_eq_none])

/-- No declared function has a merge specification, which makes `MergeStep` vacuous. -/
def Signature.AllConstructors (sig : Signature) : Prop := ∀ f, sig.mergeOf f = none

/-! ### Variables and function names -/
mutual

/-- All variables occurring in `e`, deduplicated. -/
def Expr.vars : Expr → List Var
  | .lit _ => []
  | .var v => [v]
  | .app _ args => Expr.varsList args

def Expr.varsList : List Expr → List Var
  | [] => []
  | e :: es => e.vars ∪ Expr.varsList es

end

mutual

/-- Every function name applied anywhere in `e`. -/
def Expr.fns : Expr → List FnName
  | .lit _ => []
  | .var _ => []
  | .app f args => f :: Expr.fnsList args

def Expr.fnsList : List Expr → List FnName
  | [] => []
  | e :: es => e.fns ∪ Expr.fnsList es

end

def Pattern.vars : Pattern → List Var
  | .expr e => e.vars
  | .eq e₁ e₂ => e₁.vars ∪ e₂.vars
  | .values vs _ as => Expr.varsList vs ∪ Expr.varsList as

def Query.vars : Query → List Var
  | [] => []
  | p :: ps => p.vars ∪ Query.vars ps

/-- A top-level command. -/
inductive Cmd where
  | action : Action → Cmd
  | rule : Rule → Cmd
  /-- One round of a ruleset: egglog's `(run <ruleset> 1)`, which is `(repeat 1 (run
  <ruleset>))` (`egglog/src/ast/parse.rs:834-864`). -/
  | run : RulesetName → Cmd
  /-- Rounds of a ruleset until nothing changes: egglog's `(run-schedule (saturate
  <ruleset>))` (`egglog/src/ast/parse.rs:1073-1079`). -/
  | saturate : RulesetName → Cmd
  | decl : FnName → FnDecl → Cmd

abbrev Program := List Cmd

/-! ### The constructor-only fragment -/

/-- `c` declares only constructors. -/
def Cmd.CtorDecl : Cmd → Prop
  | .decl _ d => d.merge = none
  | _ => True

/-- Every declaration in the program declares a constructor, so every state it reaches is
`Signature.AllConstructors`. -/
def Program.CtorDecls (p : Program) : Prop := ∀ c ∈ p, c.CtorDecl

/-! ### The terminating fragment -/

/-- `c` is not a saturating run. A ruleset that keeps adding terms has no fixpoint, so
`Cmd.saturate` is the one command that may fail to reach a state at all. -/
def Cmd.NoSaturate : Cmd → Prop
  | .saturate _ => False
  | _ => True

/-- The program bounds its own running: every round count is written down. -/
def Program.NoSaturate (p : Program) : Prop := ∀ c ∈ p, c.NoSaturate

end Egglog
