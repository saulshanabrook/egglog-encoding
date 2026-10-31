import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names

/-!
# Congruence compilation

This pass implements an explicit union-find for the constructor source fragment using
rules only. Its one auxiliary table is the relation `@UF(key, parent)`, whose rows are
never nested; there are no proof columns and no proof expressions. Source terms serve as
their own ids: building `f(ā)` asserts the self-loop `@UF(f(ā), f(ā))`, and the term exists
in the target as that row's key.

The union-find changes only through rules. A maintenance rule matches a stale edge,
subsumes it, and writes its replacement; its disequality guard makes it fire only where the
replacement differs from the row, so no rule subsumes a row that it writes, and a self-loop
is never re-derived from itself. A collision of two parents keeps the smaller id, subsumes
the other edge, and links the larger id under the smaller. Congruence is one rule per
constructor: two applications whose children have the same parents link the larger of
their roots under the smaller. A subsumed row stays in its table, as in egglog, but no
query matches it again; a stale edge is never needed again, since leaders only move down
the term order.

A query matches the terms themselves and joins the union-find in between. Flattening is
left-to-right postorder: visit every child before emitting its parent's atoms. An
application becomes the application over fresh child variables followed by one edge from
each child variable to the child's id, where a child that is itself an application is given
a fresh root variable by an edge from that application. An equality visits its left side,
then its right side, then equates the resulting ids. Later resugaring traverses the
original query in this same order; no separate flattening tree is needed.

A source run becomes the run of the compiled rules followed by a saturation of the
maintenance rules, and sequences and saturations compile structurally, so every pass of a
compiled saturation is one source pass with a complete rebuild after each of its runs, as
in egglog's instrumented schedules. `compile` also returns one origin per compiled rule, in
the order of `Program.rules`; `encode` is the program alone. Origins do not affect
execution; they distinguish source rule firings from path compression, collisions and
congruence during later resugaring.

The view tables of the previous encoding, one row per application keyed by the parents of
its children, materialize the joins these queries perform; the paper presents them as an
optimization of this encoding.
-/

namespace Egglog.Congruence

/-- Generated maintenance rules. -/
inductive RebuildOrigin where
  | compress
  | collide
  | congruence (constructor : FnName)
  deriving DecidableEq, Repr

/-- A source rule is identified by its position in `Program.rules` of the original program. -/
inductive RuleOrigin where
  | source (ruleIndex : Nat)
  | rebuild (kind : RebuildOrigin)
  deriving DecidableEq, Repr

/-- The compiled program with one origin per rule, in the order of `Program.rules`. -/
structure Compiled where
  program : Program
  origins : List RuleOrigin

/-- A union-find row. -/
def ufRow (key parent : Expr) : Expr := .app ufName [key, parent]

/-- Subsume a union-find row. -/
def subsumeUf (key parent : Expr) : Action := .subsume ufName [key, parent]

/-- The id of a flattened expression: a value is its own id; an application's id is a fresh
root variable, reached by an edge from the application. -/
def idOf : Expr → Nat → Expr × Query × Nat
  | node@(.app _ _), n => (.var (freshVar n), [.expr (ufRow node (.var (freshVar n)))], n + 1)
  | e, n => (e, [], n)

mutual

/-- Flatten one expression, returning the expression that stands for it (a value, or the
application over fresh child variables), its ordered atoms, and the next fresh variable. -/
def encodeQueryExpr : Expr → Nat → Expr × Query × Nat
  | .app f args, n =>
      match encodeQueryArgs args n with
      | (xs, ps, next) =>
          let as := (List.range args.length).map fun i => Expr.var (freshVar (next + i))
          (.app f as,
            ps ++ .expr (.app f as) :: (as.zip xs).map (fun ax => .expr (ufRow ax.1 ax.2)),
            next + args.length)
  | e, n => (e, [], n)

/-- Visit arguments from left to right, each reduced to its id. Repeated subexpressions keep
distinct positions. -/
def encodeQueryArgs : List Expr → Nat → List Expr × Query × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeQueryExpr e n with
      | (node, ps, next) =>
          match idOf node next with
          | (x, rs, next') =>
              match encodeQueryArgs es next' with
              | (xs, qs, last) => (x :: xs, ps ++ rs ++ qs, last)

end

/-- The id of a whole expression: flatten it, then reach its root. -/
def encodeQueryId (e : Expr) (n : Nat) : Expr × Query × Nat :=
  match encodeQueryExpr e n with
  | (node, ps, next) =>
      match idOf node next with
      | (x, rs, last) => (x, ps ++ rs, last)

/-- A pattern that is an expression needs no id. Equality and disequality join the ids
produced by the two ordered traversals. -/
def encodePattern : Pattern → Nat → Query × Nat
  | .expr e, n => ((encodeQueryExpr e n).2.1, (encodeQueryExpr e n).2.2)
  | .eq lhs rhs, n =>
      match encodeQueryId lhs n with
      | (l, ps, next) =>
          match encodeQueryId rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.eq l r], last)
  | .ne lhs rhs, n =>
      match encodeQueryId lhs n with
      | (l, ps, next) =>
          match encodeQueryId rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.ne l r], last)

/-- Preserve source conjunct order. -/
def encodeQuery : Query → Nat → Query × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      match encodePattern p n with
      | (qs, next) =>
          match encodeQuery ps next with
          | (rest, last) => (qs ++ rest, last)

mutual

/-- Build children before their parent, and give every value a UF self-loop. A self-loop
for a value that already has a parent is stale and path compression removes it. -/
def encodeBuild : Expr → List Action
  | e@(.lit _) | e@(.var _) => [.expr (ufRow e e)]
  | .min a b => encodeBuild a ++ encodeBuild b
  | .app f args => encodeBuildArgs args ++ [.expr (ufRow (.app f args) (.app f args))]

/-- Build argument occurrences in the same left-to-right order as query flattening. -/
def encodeBuildArgs : List Expr → List Action
  | [] => []
  | e :: es => encodeBuild e ++ encodeBuildArgs es

end

/-- A source union links both ids to the smaller one; for the smaller one that is a
self-loop. Source subsumes are outside the fragment and compile to nothing. -/
def encodeAction : Action → List Action
  | .expr e => encodeBuild e
  | .union a b => encodeBuild a ++ encodeBuild b ++
      [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))]
  | .subsume _ _ => []

/-- No justification argument is needed for compiling a head. -/
def encodeActions (as : List Action) : List Action := as.flatMap encodeAction

/-- Variable supplies are local to a rule; source names cannot use the `@` namespace.
Query variables are bound to parents through union-find edges, which are roots once
rebuilding has completed, so the head needs no leader lookup. -/
def encodeRule (r : Rule) : Rule :=
  { query := (encodeQuery r.query 0).1, actions := encodeActions r.actions }

/-- Replace a parent edge by the edge to the parent's own parent. With `@a = @b` this
removes the stale self-loop of a value that acquired a parent. -/
def pathCompressRule : Rule :=
  { query := [.expr (ufRow (.var "@a") (.var "@b")),
              .expr (ufRow (.var "@b") (.var "@c")),
              .ne (.var "@b") (.var "@c")],
    actions := [subsumeUf (.var "@a") (.var "@b"),
                .expr (ufRow (.var "@a") (.var "@c"))] }

/-- Two parents of one key: keep the smaller, subsume the other edge, and link the larger
parent under the smaller. -/
def ufCollideRule : Rule :=
  { query := [.expr (ufRow (.var "@a") (.var "@b")),
              .expr (ufRow (.var "@a") (.var "@c")),
              .eq (.var "@b") (.min (.var "@b") (.var "@c")),
              .ne (.var "@b") (.var "@c")],
    actions := [subsumeUf (.var "@a") (.var "@c"),
                .expr (ufRow (.var "@c") (.var "@b"))] }

/-- `arity` generated variables with a common stem. -/
def congruenceVars (stem : String) (arity : Nat) : List Expr :=
  (List.range arity).map fun i => .var ("@" ++ stem ++ toString i)

/-- Two applications of `f` whose children have the same parents: link the larger of their
roots under the smaller. This is where congruence becomes an equation. -/
def congruenceRule (f : FnName) (arity : Nat) : Rule :=
  let as := congruenceVars "a" arity
  let bs := congruenceVars "b" arity
  let rs := congruenceVars "r" arity
  { query := [.expr (.app f as), .expr (.app f bs)] ++
      ((as.zip bs).zip rs).flatMap (fun abr =>
        [.expr (ufRow abr.1.1 abr.2), .expr (ufRow abr.1.2 abr.2)]) ++
      [.expr (ufRow (.app f as) (.var "@y")), .expr (ufRow (.app f bs) (.var "@z")),
       .eq (.var "@y") (.min (.var "@y") (.var "@z")), .ne (.var "@y") (.var "@z")],
    actions := [.expr (ufRow (.var "@z") (.var "@y"))] }

/-- The congruence rule of a constructor. A nullary constructor has one application and
needs none. -/
def rebuildRules (f : FnName) (arity : Nat) : List (Rule × RuleOrigin) :=
  if arity = 0 then [] else [(congruenceRule f arity, .rebuild (.congruence f))]

/-- The maintenance rules, with their origins. -/
def maintenanceRules (P : Program) : List (Rule × RuleOrigin) :=
  (pathCompressRule, .rebuild .compress) :: (ufCollideRule, .rebuild .collide) ::
    P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-- The compiled rules of a source command's rules, numbered from `index` in
`Program.rules` of the source. -/
def encodeRules (index : Nat) (rs : List Rule) : List (Rule × RuleOrigin) :=
  rs.zipIdx.map fun ri => (encodeRule ri.1, .source (index + ri.2))

/-- The maintenance saturation, with its origins. -/
def rebuild (P : Program) : Schedule × List RuleOrigin :=
  let m := maintenanceRules P
  (.saturate (.run (m.map Prod.fst)), m.map Prod.snd)

/-- Compile a schedule, numbering source rules from `index` in `Program.rules`. Every run
is followed by a rebuild, so a compiled saturation's body ends at a rebuild fixpoint and
each of its passes is one source pass. -/
def encodeSchedule (P : Program) : Schedule → Nat → Schedule × List RuleOrigin × Nat
  | .run rs, index =>
      let compiled := encodeRules index rs
      let (m, mo) := rebuild P
      (.seq (.run (compiled.map Prod.fst)) m, compiled.map Prod.snd ++ mo, index + rs.length)
  | .saturate S, index =>
      let (S', os, next) := encodeSchedule P S index
      (.saturate S', os, next)
  | .seq S₁ S₂, index =>
      let (T₁, o₁, next) := encodeSchedule P S₁ index
      let (T₂, o₂, last) := encodeSchedule P S₂ next
      (.seq T₁ T₂, o₁ ++ o₂, last)

/-- The congruence pass with origins for later proof resugaring. -/
def compile (P : Program) : Compiled :=
  let (S, os, _) := encodeSchedule P P.schedule 0
  { program := { schedule := S, check := (encodeQuery P.check 0).1 }, origins := os }

/-- The executable program, independent of all proof instrumentation. -/
def encode (P : Program) : Program := (compile P).program

end Egglog.Congruence
