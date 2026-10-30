import Batteries.Data.List.Basic
import Architect

/-!
# Syntax of the modelled egglog fragment

```
Program = (Cmd ...) (check Query)
Cmd     = (run Rule ...) | (saturate Rule ...)
Rule    = (rule Query Actions)
Query   = (Pattern ...)
Pattern = expr | (= expr expr) | (!= expr expr)
Action  = expr | (union expr expr) | (delete expr)
expr    = number | var | (f expr ...) | (min expr expr)
```

The language is untyped and has no declarations: applying any name to any arguments
builds a term, and a relation is a constructor whose rows are never nested. A run names
the rules it fires, so there are no rulesets and no rule store, and a program ends in the
one check that decides its outcome. egglog's named rulesets and its `rule` command are
resolved by the parser (`Tests/Parse.lean`): a run of a ruleset fires the rules registered
in it so far.
-/

namespace Egglog
/-- A variable bound by a query. -/
abbrev Var := String

/-- The name of a constructor. -/
abbrev FnName := String

/-- Mathematical integers, modelling egglog's integer literals without overflow. -/
inductive Lit where
  | int : Int → Lit
  deriving DecidableEq, Repr, Inhabited

/-- An expression. Evaluated against an environment to build a `Term`. -/
-- The paper displays the literal-free fragment; the model also supports integers.
@[blueprint "def:expressions"
  (statement := /--
  \syntaxline{Expressions}{e ::= x\mid f(e_1,\ldots,e_n)\mid\min(e,e)}
  -/)
  (latexEnv := "paperfragment")]
inductive Expr where
  | lit : Lit → Expr
  | var : Var → Expr
  | app : FnName → List Expr → Expr
  /-- The smaller term in the fixed order; the compiled rebuilding chooses representatives
  with it. -/
  | min : Expr → Expr → Expr

/-- One conjunct of a rule's query: a term to find, an equality, or a disequality. -/
@[blueprint "def:patterns"
  (statement := /-- \syntaxline{Patterns}{p ::= e\mid e=e\mid e\ne e} -/)
  (latexEnv := "paperfragment")]
inductive Pattern where
  | expr : Expr → Pattern
  | eq : Expr → Expr → Pattern
  /-- Both sides exist and are not congruent. Generated maintenance rules use it to fire
  only where a row actually changes. -/
  | ne : Expr → Expr → Pattern

/-- A rule's query, matched conjunctively. -/
@[blueprint "def:queries"
  (statement := /-- \syntaxline{Queries}{Q ::= p_1\land\cdots\land p_n} -/)
  (latexEnv := "paperfragment")]
abbrev Query := List Pattern

/-- An action: build a term, assert an equality, or delete a row. -/
@[blueprint "def:action-syntax"
  (statement := /--
  \syntaxline{Actions}{h ::= e\mid\kw{union}(e,e)\mid\kw{delete}(e)}
  \syntaxline{Sequences}{A ::= h_1;\ldots;h_n}
  -/)
  (latexEnv := "paperfragment")]
inductive Action where
  | expr : Expr → Action
  | union : Expr → Expr → Action
  /-- Remove the row the term denotes, in every congruent spelling. -/
  | delete : Expr → Action

/-- A rule. Its actions run once per substitution satisfying its query, in every round of
a run that names it. -/
@[blueprint "def:rules"
  (statement := /--
  \syntaxline{Rules}{\rho\in\mathit{Rule} ::= Q\Rightarrow A}
  -/)
  (latexEnv := "paperfragment")]
structure Rule where
  query : Query
  actions : List Action

/-! ### Variables and function names -/
mutual

/-- All variables occurring in `e`, deduplicated. -/
def Expr.vars : Expr → List Var
  | .lit _ => []
  | .var v => [v]
  | .app _ args => Expr.varsList args
  | .min a b => a.vars ∪ b.vars

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
  | .min a b => a.fns ∪ b.fns

def Expr.fnsList : List Expr → List FnName
  | [] => []
  | e :: es => e.fns ∪ Expr.fnsList es

end

def Pattern.vars : Pattern → List Var
  | .expr e => e.vars
  | .eq e₁ e₂ => e₁.vars ∪ e₂.vars
  | .ne e₁ e₂ => e₁.vars ∪ e₂.vars

def Query.vars : Query → List Var
  | [] => []
  | p :: ps => p.vars ∪ Query.vars ps

/-- A top-level command: one round of some rules, or rounds of them until nothing changes.
Initial facts are a run of an empty-query rule. -/
@[blueprint "def:commands"
  (statement := /--
  \syntaxline{Commands}{C ::= \kw{run}\ \bar\rho\mid\kw{saturate}\ \bar\rho}
  -/)
  (latexEnv := "paperfragment")]
inductive Cmd where
  /-- One round of the rules: egglog's `(run <ruleset> 1)` over the rules the ruleset holds
  (`egglog/src/ast/parse.rs:834-864`). -/
  | run : List Rule → Cmd
  /-- Rounds of the rules until nothing changes: egglog's `(run-schedule (saturate
  <ruleset>))` (`egglog/src/ast/parse.rs:1073-1079`). -/
  | saturate : List Rule → Cmd

/-- The rules a command fires. -/
def Cmd.rules : Cmd → List Rule
  | .run rs => rs
  | .saturate rs => rs

/-- A program: commands, then the one check that decides its outcome. The check is
existential and local: it exports no bindings and builds no terms. A program with nothing to
check ends in the empty query, which always holds. -/
@[blueprint "def:programs"
  (statement := /-- \syntaxline{Programs}{P ::= C_1;\ldots;C_n;\ \kw{check}\ Q} -/)
  (latexEnv := "paperfragment")]
structure Program where
  commands : List Cmd
  check : Query

/-- Every rule of the program, in command order. Proofs cite a rule by its position here. -/
def Program.rules (P : Program) : List Rule := P.commands.flatMap Cmd.rules

/-! ### The terminating fragment -/

/-- `c` is not a saturating run. Rules that keep adding terms have no fixpoint, so
`Cmd.saturate` is the one command that may fail to reach a state at all. -/
def Cmd.NoSaturate : Cmd → Prop
  | .saturate _ => False
  | _ => True

/-- The program bounds its own running: every round count is written down. -/
def Program.NoSaturate (P : Program) : Prop := ∀ c ∈ P.commands, c.NoSaturate

end Egglog
