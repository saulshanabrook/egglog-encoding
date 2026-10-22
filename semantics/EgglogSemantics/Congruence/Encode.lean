import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names

/-!
# Congruence compilation

This pass implements explicit union-find, rebuilding, and query flattening for the
constructor source fragment using rules only. Its auxiliary tables are the relations
`@UF(key, parent)` and `@fView(children…, id)`, applications whose last column is the id
and whose rows are never nested. There are no proof columns or proof expressions.
Structural constructor terms serve as ids.

Rows change only through rules. A maintenance rule matches a stale row, deletes it, and
writes its replacement. Its disequality guard makes it fire only where the replacement
differs from the row, so no rule deletes a row that it writes back, and a self-loop
`@UF(t, t)` is never re-derived from itself. A collision of two parents or two outputs
keeps the smaller id, deletes the other row, and links the larger id under the smaller.
A round applies every deletion before every write, so a row that one firing replaces and
another still derives survives, as in egglog.

Query flattening is left-to-right postorder: visit every child before emitting its
parent's view atom. An equality visits its left side, then its right side, then emits
an equality of the resulting ids. Later resugaring can traverse the original query in
this same order; no separate flattening tree is needed.

A source run becomes the run of the compiled rules followed by a saturation of the
maintenance rules; a source saturation runs its compiled rules together with the
maintenance rules, so rebuilding interleaves with every round, and is followed by the same
maintenance saturation. `compile` also returns one
origin per compiled rule, in the order of `Program.rules`; `encode` is the program alone.
Origins do not affect execution; they distinguish source rule firings from path
compression, collisions, e-class propagation, and child re-keying during later resugaring.
-/

namespace Egglog.Congruence

/-- Generated maintenance rules, including the position a child rule rewrites. -/
inductive RebuildOrigin where
  | compress
  | collide
  | eclass (constructor : FnName)
  | child (constructor : FnName) (index : Nat)
  | viewCollide (constructor : FnName)
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

/-- The two kinds of generated table; source constructors retain their names. -/
inductive TableRole where
  | unionFind
  | view (constructor : FnName)
  deriving DecidableEq, Repr

/-- Resolve generated table names against the original program. -/
def tableRole (P : Program) (f : FnName) : Option TableRole :=
  if f = ufName then some .unionFind else
    (P.ctors.find? fun fk => viewName fk.1 == f).map fun fk => .view fk.1

/-- A union-find row. -/
def ufRow (key parent : Expr) : Expr := .app ufName [key, parent]

/-- A view row of `f`. -/
def viewRow (f : FnName) (children : List Expr) (id : Expr) : Expr :=
  .app (viewName f) (children ++ [id])

mutual

/-- Flatten one expression, returning its id, ordered atoms, and next fresh variable. -/
def encodeQueryExpr : Expr → Nat → Expr × Query × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .min a b, n => (.min a b, [], n)
  | .app f args, n =>
      match encodeQueryArgs args n with
      | (es, ps, next) =>
          (.var (freshVar next),
            ps ++ [.expr (viewRow f es (.var (freshVar next)))], next + 1)

/-- Visit arguments from left to right. Repeated subexpressions keep distinct positions. -/
def encodeQueryArgs : List Expr → Nat → List Expr × Query × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeQueryExpr e n with
      | (e', ps, next) =>
          match encodeQueryArgs es next with
          | (es', qs, last) => (e' :: es', ps ++ qs, last)

end

/-- Equality and disequality join the ids produced by the two ordered traversals. -/
def encodePattern : Pattern → Nat → Query × Nat
  | .expr e, n => ((encodeQueryExpr e n).2.1, (encodeQueryExpr e n).2.2)
  | .eq lhs rhs, n =>
      match encodeQueryExpr lhs n with
      | (l, ps, next) =>
          match encodeQueryExpr rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.eq l r], last)
  | .ne lhs rhs, n =>
      match encodeQueryExpr lhs n with
      | (l, ps, next) =>
          match encodeQueryExpr rhs next with
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
  | .app f args =>
      encodeBuildArgs args ++
        [.expr (viewRow f args (.app f args)), .expr (ufRow (.app f args) (.app f args))]

/-- Build argument occurrences in the same left-to-right order as query flattening. -/
def encodeBuildArgs : List Expr → List Action
  | [] => []
  | e :: es => encodeBuild e ++ encodeBuildArgs es

end

/-- A source union links both ids to the smaller one; for the smaller one that is a
self-loop. Source deletes are outside the fragment and compile to nothing. -/
def encodeAction : Action → List Action
  | .expr e => encodeBuild e
  | .union a b => encodeBuild a ++ encodeBuild b ++
      [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))]
  | .delete _ => []

/-- No justification argument is needed for compiling a head. -/
def encodeActions (as : List Action) : List Action := as.flatMap encodeAction

/-- Variable supplies are local to a rule; source names cannot use the `@` namespace.
Query variables are bound through view rows, whose columns are canonical once rebuilding
has completed, so the head needs no leader lookup. -/
def encodeRule (r : Rule) : Rule :=
  { query := (encodeQuery r.query 0).1, actions := encodeActions r.actions }

/-- Replace a parent edge by the edge to the parent's own parent. With `@a = @b` this
removes the stale self-loop of a value that acquired a parent. -/
def pathCompressRule : Rule :=
  { query := [.expr (ufRow (.var "@a") (.var "@b")),
              .expr (ufRow (.var "@b") (.var "@c")),
              .ne (.var "@b") (.var "@c")],
    actions := [.delete (ufRow (.var "@a") (.var "@b")),
                .expr (ufRow (.var "@a") (.var "@c"))] }

/-- Two parents of one key: keep the smaller, delete the other edge, and link the larger
parent under the smaller. -/
def ufCollideRule : Rule :=
  { query := [.expr (ufRow (.var "@a") (.var "@b")),
              .expr (ufRow (.var "@a") (.var "@c")),
              .eq (.var "@b") (.min (.var "@b") (.var "@c")),
              .ne (.var "@b") (.var "@c")],
    actions := [.delete (ufRow (.var "@a") (.var "@c")),
                .expr (ufRow (.var "@c") (.var "@b"))] }

/-- The key variables of a generated view rule. -/
def rebuildVars (arity : Nat) : List Expr :=
  (List.range arity).map fun i => .var ("@c" ++ toString i)

/-- Move a view's output to its parent id. -/
def eclassRule (f : FnName) (arity : Nat) : Rule :=
  let cs := rebuildVars arity
  { query := [.expr (viewRow f cs (.var "@e")),
              .expr (ufRow (.var "@e") (.var "@x")),
              .ne (.var "@e") (.var "@x")],
    actions := [.delete (viewRow f cs (.var "@e")),
                .expr (viewRow f cs (.var "@x"))] }

/-- Move a view to the key with a child replaced by its parent id. -/
def childRule (f : FnName) (arity index : Nat) : Rule :=
  let cs := rebuildVars arity
  { query := [.expr (viewRow f cs (.var "@e")),
              .expr (ufRow (.var ("@c" ++ toString index)) (.var "@x")),
              .ne (.var ("@c" ++ toString index)) (.var "@x")],
    actions := [.delete (viewRow f cs (.var "@e")),
                .expr (viewRow f (cs.set index (.var "@x")) (.var "@e"))] }

/-- Two outputs at one key: keep the smaller, delete the other row, and link the larger
output under the smaller. This is where congruence becomes an equation. -/
def viewCollideRule (f : FnName) (arity : Nat) : Rule :=
  let cs := rebuildVars arity
  { query := [.expr (viewRow f cs (.var "@y")),
              .expr (viewRow f cs (.var "@z")),
              .eq (.var "@y") (.min (.var "@y") (.var "@z")),
              .ne (.var "@y") (.var "@z")],
    actions := [.delete (viewRow f cs (.var "@z")),
                .expr (ufRow (.var "@z") (.var "@y"))] }

/-- One output rule, one rule per key column, and the collision rule, in that order. -/
def rebuildRules (f : FnName) (arity : Nat) : List (Rule × RuleOrigin) :=
  (eclassRule f arity, .rebuild (.eclass f)) ::
    ((List.range arity).map (fun i => (childRule f arity i, .rebuild (.child f i)))
      ++ [(viewCollideRule f arity, .rebuild (.viewCollide f))])

/-- The maintenance rules, with their origins. -/
def maintenanceRules (P : Program) : List (Rule × RuleOrigin) :=
  (pathCompressRule, .rebuild .compress) :: (ufCollideRule, .rebuild .collide) ::
    P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-- The compiled rules of a source command's rules, numbered from `index` in
`Program.rules` of the source. -/
def encodeRules (index : Nat) (rs : List Rule) : List (Rule × RuleOrigin) :=
  rs.zipIdx.map fun ri => (encodeRule ri.1, .source (index + ri.2))

/-- Rebuild after every source command; inside a source saturation, also rebuild in every
round. The trailing rebuild after a saturation is not redundant: every round refires every
source rule, so a source rule can rewrite a stale row in the round that deletes it, and
writes win; only a round without source rules removes it. -/
def encodeCmd (P : Program) (index : Nat) : Cmd → List (Cmd × List RuleOrigin)
  | .run rs =>
      let compiled := encodeRules index rs
      let maintenance := maintenanceRules P
      [(.run (compiled.map Prod.fst), compiled.map Prod.snd),
       (.saturate (maintenance.map Prod.fst), maintenance.map Prod.snd)]
  | .saturate rs =>
      let all := encodeRules index rs ++ maintenanceRules P
      let maintenance := maintenanceRules P
      [(.saturate (all.map Prod.fst), all.map Prod.snd),
       (.saturate (maintenance.map Prod.fst), maintenance.map Prod.snd)]

/-- Compile the commands, numbering source rules by their position in `Program.rules`. -/
def encodeCmds (P : Program) : List Cmd → Nat → List (Cmd × List RuleOrigin)
  | [], _ => []
  | c :: cs, index => encodeCmd P index c ++ encodeCmds P cs (index + c.rules.length)

/-- The congruence pass with origins for later proof resugaring. -/
def compile (P : Program) : Compiled :=
  let cmds := encodeCmds P P.commands 0
  { program := { commands := cmds.map Prod.fst, check := (encodeQuery P.check 0).1 },
    origins := cmds.flatMap Prod.snd }

/-- The executable program, independent of all proof instrumentation. -/
def encode (P : Program) : Program := (compile P).program

end Egglog.Congruence
