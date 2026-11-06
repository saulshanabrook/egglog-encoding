import Batteries.Data.List.Basic
import Architect

/-!
# Syntax of the modelled egglog fragment

```
Program  = Schedule (check Query)
Schedule = (run Rule ...) | (saturate Schedule) | (seq Schedule Schedule)
Rule     = (rule Query Actions)
Query    = (Pattern ...)
Pattern  = expr | (= expr expr) | (!= expr expr)
Action   = expr | (union expr expr) | (subsume fn exprs)
expr     = number | var | (f expr ...) | (min expr expr)
```

The language is untyped and has no declarations: applying any name to any arguments
builds a term, and a relation is a constructor whose rows are never nested. A run names
the rules it fires, so there are no rulesets and no rule store; schedules nest as in
egglog's `run-schedule`; and a program ends in the one check that decides its outcome.
egglog's named rulesets and its `rule` command are resolved by the parser
(`Tests/Parse.lean`): a run of a ruleset fires the rules registered in it so far.
-/

namespace Egglog
/-- A variable bound by a query. -/
abbrev Var := String

/-- The name of a constructor. -/
abbrev FnName := String

/-- Mathematical integers, modelling egglog's integer literals without overflow. -/
inductive Lit where
  | int : Int → Lit
  | str : String → Lit
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
  (statement := /-- \syntaxline{Patterns}{p ::= e=e\mid e\ne e} -/)
  (latexEnv := "paperfragment")]
inductive Pattern where
  /-- The paper writes this pattern as a bare `e`, shorthand for `e = e`, which it matches
  exactly when. It stays a constructor because the compiler flattens it to one view atom. -/
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

/-- An action: build a term, assert an equality, or subsume a row. A row is named by its
symbol and its children, as in egglog's `(subsume (f args))`, so which spelling represents
a child's class never decides which row is subsumed. -/
@[blueprint "def:action-syntax"
  (statement := /--
  \syntaxline{Actions}{h ::= \kw{union}(e,e)\mid\kw{subsume}(f(e_1,\ldots,e_n))}
  -/)
  (latexEnv := "paperfragment")]
inductive Action where
  /-- The paper writes this action as a bare `e`, shorthand for `union(e,e)`, which adds
  the same fact. It stays a constructor because the compiled target must be union-free. -/
  | expr : Expr → Action
  | union : Expr → Expr → Action
  /-- Assert the row `f(ē)` and mark it subsumed: it stays, with its columns, and no query
  matches it or any spelling with congruent children again. -/
  | subsume : FnName → List Expr → Action

/-- A rule. Its actions run once per substitution satisfying its query, in every round of
a run that names it. Every action only adds to the state, so the actions commute and the
paper writes them as a set `H`; the list order plays no semantic role. -/
@[blueprint "def:rules"
  (statement := /--
  \syntaxline{Action sets}{H ::= \{h_1,\ldots,h_n\}}
  \syntaxline{Rules}{r\in\mathit{Rule} ::= Q\Rightarrow H}
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

/-- A schedule: one round of some rules, rounds of a schedule until nothing changes, or
one schedule after another. Initial facts are a run of an empty-query rule. -/
@[blueprint "def:commands"
  (statement := /--
  \syntaxline{Rule sets}{R ::= \{r_1,\ldots,r_n\}}
  \syntaxline{Schedules}{S ::= \kw{run}\ R\mid\kw{saturate}\ S\mid S;S}
  -/)
  (latexEnv := "paperfragment")]
inductive Schedule where
  /-- One round of the rules: egglog's `(run <ruleset>)` over the rules the ruleset holds
  (`egglog/src/ast/parse.rs:834-864`). The semantics reads the list as a set, which is how
  the paper writes it; the order only numbers the rules for certificates. -/
  | run : List Rule → Schedule
  /-- The schedule until a pass leaves congruence unchanged: egglog's `(saturate <schedule>)`
  (`egglog/src/ast/parse.rs:1073-1079`). -/
  | saturate : Schedule → Schedule
  /-- One schedule, then another: egglog's `(seq <schedule> <schedule>)`. -/
  | seq : Schedule → Schedule → Schedule

/-- The rules a schedule fires, in order of appearance. -/
def Schedule.rules : Schedule → List Rule
  | .run rs => rs
  | .saturate S => S.rules
  | .seq S₁ S₂ => S₁.rules ++ S₂.rules

/-- The rule lists of the runs inside a schedule, in order of appearance. -/
def Schedule.runs : Schedule → List (List Rule)
  | .run rs => [rs]
  | .saturate S => S.runs
  | .seq S₁ S₂ => S₁.runs ++ S₂.runs

/-- One schedule after another; none is a round of no rules, which changes nothing. -/
def Schedule.seqAll : List Schedule → Schedule
  | [] => .run []
  | [S] => S
  | S :: Ss => .seq S (seqAll Ss)

/-- A program: a schedule, then the one check that decides its outcome. The check is
existential and local: it exports no bindings and builds no terms. A program with nothing to
check ends in the empty query, which always holds. -/
@[blueprint "def:programs"
  (statement := /-- \syntaxline{Programs}{P ::= S;\ \kw{check}\ Q} -/)
  (latexEnv := "paperfragment")]
structure Program where
  schedule : Schedule
  check : Query

/-- Every rule of the program, in order of appearance. Proofs cite a rule by its position
here. -/
def Program.rules (P : Program) : List Rule := P.schedule.rules

/-- The rule lists of every run in the program. -/
def Program.runs (P : Program) : List (List Rule) := P.schedule.runs

/-! ### The terminating fragment -/

/-- `S` contains no saturation. Rules that keep adding terms have no fixpoint, so
`Schedule.saturate` is the one construct that may fail to reach a state at all. -/
def Schedule.NoSaturate : Schedule → Prop
  | .run _ => True
  | .saturate _ => False
  | .seq S₁ S₂ => S₁.NoSaturate ∧ S₂.NoSaturate

/-- The program bounds its own running: every round count is written down. -/
def Program.NoSaturate (P : Program) : Prop := P.schedule.NoSaturate

end Egglog
