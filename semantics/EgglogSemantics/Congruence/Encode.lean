import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names
import Architect

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
application becomes the application over fresh child variables, one edge from each child
variable to the child's id, and one edge from the application to a fresh root, which is
its id; a value is its own id. An equality visits its left side, then its right side,
then equates the resulting ids. Later resugaring traverses the original query in this same
order; no separate flattening tree is needed.

The paper displays the pass as inference rules; they are the `@[blueprint]` statements of
the definitions below, so the paper and the compiler change together.

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

/-- Generated maintenance rules: the union-find rules, the congruence rule of a constructor,
and the rules of its canonical node view when that optimization is on. -/
inductive RebuildOrigin where
  | compress
  | collide
  | congruence (constructor : FnName)
  /-- The naive view: derived from the terms and the union-find. -/
  | view (constructor : FnName)
  /-- A stale row of the naive view is subsumed. -/
  | stale (constructor : FnName)
  /-- The index of the view: one row per view row and column. -/
  | index (constructor : FnName)
  /-- A view row moves with the union-find edge of one of its columns, found through the
  index. -/
  | rekey (constructor : FnName) (column : Nat)
  /-- The congruence rule read over the view: two rows at one key. -/
  | viewCongruence (constructor : FnName)
  deriving DecidableEq, Repr

/-- How compiled queries read applications: the terms joined with the union-find, or a
canonical node view per constructor, maintained naively from the terms or through an
index from union-find edges. -/
inductive ViewMode where
  | none
  | naive
  | indexed
  deriving DecidableEq, Repr

/-- The optimizations of the pass. The defaults are the encoding the paper presents;
`phased` runs the union-find rules to a fixpoint before the term rules in every rebuild. -/
structure Options where
  views : ViewMode := .none
  phased : Bool := false
  deriving Repr

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

/-- A view row of `f`: the children's leaders and the node's leader. -/
def viewRow (f : FnName) (children : List Expr) (id : Expr) : Expr :=
  .app (viewName f) (children ++ [id])

/-- Subsume a view row of `f`. -/
def subsumeView (f : FnName) (children : List Expr) (id : Expr) : Action :=
  .subsume (viewName f) (children ++ [id])

mutual

/-- Flatten one expression, returning the expression that stands for it, its ordered atoms,
and the next fresh variable; see `encodeQueryExpr`. With a view, an application is read as
one view row over its children's ids, whose last column is its id. -/
def encodeQueryExprWith (o : Options) : Expr → Nat → Expr × Query × Nat
  | .app f args, n =>
      match encodeQueryArgsWith o args n with
      | (xs, ps, next) =>
          if o.views = .none then
            let as := (List.range args.length).map fun i => Expr.var (freshVar (next + i))
            let y := Expr.var (freshVar (next + args.length))
            (y,
              ps ++ .expr (.app f as) :: (as.zip xs).map (fun ax => .expr (ufRow ax.1 ax.2))
                ++ [.expr (ufRow (.app f as) y)],
              next + args.length + 1)
          else
            let y := Expr.var (freshVar next)
            (y, ps ++ [.expr (viewRow f xs y)], next + 1)
  | e, n => (e, [], n)

/-- Visit arguments from left to right. Repeated subexpressions keep distinct positions. -/
def encodeQueryArgsWith (o : Options) : List Expr → Nat → List Expr × Query × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeQueryExprWith o e n with
      | (x, ps, next) =>
          match encodeQueryArgsWith o es next with
          | (xs, qs, last) => (x :: xs, ps ++ qs, last)

end

/-- `e ⇝ Q; x`: flatten one expression into its id and its ordered atoms. A value is its own
id and needs no atom. An application becomes the application over fresh child variables,
one edge from each child variable to the child's id, and one edge from the application to
a fresh root, which is its id. A pattern written as a bare `e` is the paper's shorthand for
`e = e` and compiles to `Q` alone. -/
@[blueprint "def:compile-query"
  (statement := /--
  \begin{mathpar}
  \ir{Value}{x\in\mathit{Var}}{x\leadsto\top;\ x}
  \and
  \ir{App}{e_i\leadsto Q_i;\ x_i\ (\forall i)\\ a_1,\ldots,a_n,y\text{ fresh}}
    {f(e_1,\ldots,e_n)\leadsto Q_1\land\cdots\land Q_n\land f(a_1,\ldots,a_n)
      \land\textstyle\bigwedge_i\mathtt{UF}(a_i,x_i)\land\mathtt{UF}(f(a_1,\ldots,a_n),y);\ y}
  \and
  \ir{Compare}{e_1\leadsto Q_1;\ x_1\\e_2\leadsto Q_2;\ x_2}
    {(e_1\bowtie e_2)\leadsto Q_1\land Q_2\land x_1\bowtie x_2}
  \and
  \ir{Query}{p_i\leadsto Q_i\ (\forall i)}{p_1\land\cdots\land p_n\leadsto Q_1\land\cdots\land Q_n}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def encodeQueryExpr : Expr → Nat → Expr × Query × Nat := encodeQueryExprWith {}

/-- With a canonical node view, an application is one row. -/
@[blueprint "def:view-query"
  (statement := /--
  \begin{mathpar}
  \ir{App}{e_i\leadsto Q_i;\ x_i\ (\forall i)\\ y\text{ fresh}}
    {f(e_1,\ldots,e_n)\leadsto Q_1\land\cdots\land Q_n\land\mathtt{View}_f(x_1,\ldots,x_n,y);\ y}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def encodeQueryExprViews : Expr → Nat → Expr × Query × Nat :=
  encodeQueryExprWith { views := .indexed }

/-- A pattern that is an expression needs no id. Equality and disequality compare the ids
produced by the two ordered traversals. -/
def encodePatternWith (o : Options) : Pattern → Nat → Query × Nat
  | .expr e, n => ((encodeQueryExprWith o e n).2.1, (encodeQueryExprWith o e n).2.2)
  | .eq lhs rhs, n =>
      match encodeQueryExprWith o lhs n with
      | (l, ps, next) =>
          match encodeQueryExprWith o rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.eq l r], last)
  | .ne lhs rhs, n =>
      match encodeQueryExprWith o lhs n with
      | (l, ps, next) =>
          match encodeQueryExprWith o rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.ne l r], last)

/-- Preserve source conjunct order. -/
def encodeQueryWith (o : Options) : Query → Nat → Query × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      match encodePatternWith o p n with
      | (qs, next) =>
          match encodeQueryWith o ps next with
          | (rest, last) => (qs ++ rest, last)

def encodePattern : Pattern → Nat → Query × Nat := encodePatternWith {}
def encodeQuery : Query → Nat → Query × Nat := encodeQueryWith {}

mutual

/-- Build children before their parent, and give every value a UF self-loop. A self-loop
for a value that already has a parent is stale and path compression removes it. The
indexed view also gets the node's row, keyed by its children as built. -/
def encodeBuildWith (o : Options) : Expr → List Action
  | e@(.lit _) | e@(.var _) => [.expr (ufRow e e)]
  | .min a b => encodeBuildWith o a ++ encodeBuildWith o b
  | .app f args =>
      encodeBuildArgsWith o args ++
        (if o.views = .indexed then [.expr (viewRow f args (.app f args))] else []) ++
        [.expr (ufRow (.app f args) (.app f args))]

/-- Build argument occurrences in the same left-to-right order as query flattening. -/
def encodeBuildArgsWith (o : Options) : List Expr → List Action
  | [] => []
  | e :: es => encodeBuildWith o e ++ encodeBuildArgsWith o es

end

def encodeBuild : Expr → List Action := encodeBuildWith {}
def encodeBuildArgs : List Expr → List Action := encodeBuildArgsWith {}

/-- A source union links both ids to the smaller one; for the smaller one that is a
self-loop. A bare action `e` is the paper's shorthand for `union(e, e)`, whose extra edge
is the self-loop `exist(e)` already holds. Source subsumes are outside the fragment and
compile to nothing. -/
@[blueprint "def:compile-head"
  (statement := /--
  \[
  \operatorname{exist}(e)\triangleq\{\mathtt{UF}(e',e')\mid e'\text{ a subexpression of }e\}
  \]
  \begin{mathpar}
  \ir{Union}{ }{\kw{union}(e_1,e_2)\leadsto\operatorname{exist}(e_1)\cup\operatorname{exist}(e_2)
    \cup\{\mathtt{UF}(e_1,\min(e_1,e_2)),\ \mathtt{UF}(e_2,\min(e_1,e_2))\}}
  \and
  \ir{Head}{h_i\leadsto H_i\ (\forall i)}{\{h_1,\ldots,h_n\}\leadsto H_1\cup\cdots\cup H_n}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def encodeActionWith (o : Options) : Action → List Action
  | .expr e => encodeBuildWith o e
  | .union a b => encodeBuildWith o a ++ encodeBuildWith o b ++
      [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))]
  | .subsume _ _ => []

def encodeAction : Action → List Action := encodeActionWith {}

/-- No justification argument is needed for compiling a head. -/
def encodeActionsWith (o : Options) (as : List Action) : List Action :=
  as.flatMap (encodeActionWith o)

def encodeActions (as : List Action) : List Action := encodeActionsWith {} as

/-- Variable supplies are local to a rule; source names cannot use the `@` namespace.
Query variables are bound to parents through union-find edges, which are roots once
rebuilding has completed, so the head needs no leader lookup. -/
def encodeRuleWith (o : Options) (r : Rule) : Rule :=
  { query := (encodeQueryWith o r.query 0).1, actions := encodeActionsWith o r.actions }

def encodeRule (r : Rule) : Rule := encodeRuleWith {} r

/-- Replace a parent edge by the edge to the parent's own parent. With `@a = @b` this
removes the stale self-loop of a value that acquired a parent. -/
def pathCompressRule : Rule :=
  { query := [.expr (ufRow (.var "@a") (.var "@b")),
              .expr (ufRow (.var "@b") (.var "@c")),
              .ne (.var "@b") (.var "@c")],
    actions := [subsumeUf (.var "@a") (.var "@b"),
                .expr (ufRow (.var "@a") (.var "@c"))] }

/-- The rule form of a merge annotation `R(k₁,…,kₙ, v) :merge H; m(v, v′)` with `m = min`:
the last column of `R` depends on the others, two rows at one key keep the one whose value
is the minimum, subsume the other, and run `H` with the kept value `v` and the subsumed
value `v′`. egglog provides merge annotations natively; the compiler's two functional
dependencies, `ufCollideRule` and `viewCongruenceRule`, are instances of this rule. -/
@[blueprint "def:fd-syntax"
  (statement := /--
  \[
  R(k_1,\ldots,k_n,v)\ \kw{:merge}\ H;\ m(v,v')
  \]
  -/)
  (latexEnv := "paperfragment")]
def fdRule (R : FnName) (keys : List Expr) (v v' : Var) (extra : Expr → Expr → List Action) :
    Rule :=
  { query := [.expr (.app R (keys ++ [.var v])), .expr (.app R (keys ++ [.var v'])),
              .eq (.var v) (.min (.var v) (.var v')), .ne (.var v) (.var v')],
    actions := .subsume R (keys ++ [.var v']) :: extra (.var v) (.var v') }

/-- Two parents of one key: keep the smaller, subsume the other edge, and link the larger
parent under the smaller. The functional dependency of a term's parent on the term. -/
@[blueprint "def:fd-rule"
  (statement := /--
  \[
  R(k_1,\ldots,k_n,v)\land R(k_1,\ldots,k_n,v')\land v=m(v,v')\land v\ne v'
    \Rightarrow\kw{subsume}(R(k_1,\ldots,k_n,v')),\ H
  \]
  -/)
  (latexEnv := "paperfragment")]
def ufCollideRule : Rule :=
  fdRule ufName [.var "@a"] "@b" "@c" fun b c => [.expr (ufRow c b)]

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

/-! ### Canonical node views

An optimization of the pass: a row `View_f(a'₁, …, a'ₙ, c')` per application of `f`, holding
the leaders of its children and of itself, so that a compiled query reads one row per
application instead of the application and `n + 1` union-find edges, and a congruence is
two rows at one key. -/

/-- The key variables of a generated view rule. -/
def rebuildVars (arity : Nat) : List Expr :=
  (List.range arity).map fun i => .var ("@c" ++ toString i)

/-- The naive view: every application's row, from its children's and its own parents; a
row with a column that has a parent is stale; and the congruence rule, whose query is the
pattern the view caches, reads two rows at one key and retires the loser. -/
@[blueprint "def:view-naive"
  (statement := /--
  \[
  \begin{aligned}
  \textsc{View}_f&:\ f(a_1,\ldots,a_n)\land\textstyle\bigwedge_i\mathtt{UF}(a_i,a'_i)
    \land\mathtt{UF}(f(a_1,\ldots,a_n),c')\Rightarrow\mathtt{View}_f(a'_1,\ldots,a'_n,c')\\
  \textsc{Stale}_{f,i}&:\ \mathtt{View}_f(c_1,\ldots,c_{n+1})\land\mathtt{UF}(c_i,x)\land c_i\ne x
    \Rightarrow\kw{subsume}(\mathtt{View}_f(c_1,\ldots,c_{n+1}))\\
  \textsc{Cong}_f&:\ \mathtt{View}_f(a'_1,\ldots,a'_n,y)\land\mathtt{View}_f(a'_1,\ldots,a'_n,z)
    \land y=\min(y,z)\land y\ne z\\
    &\qquad\Rightarrow\kw{subsume}(\mathtt{View}_f(a'_1,\ldots,a'_n,z)),\ \mathtt{UF}(z,y)
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def viewRule (f : FnName) (arity : Nat) : Rule :=
  let as := congruenceVars "a" arity
  let rs := congruenceVars "r" arity
  { query := .expr (.app f as) :: (as.zip rs).map (fun ar => .expr (ufRow ar.1 ar.2))
      ++ [.expr (ufRow (.app f as) (.var "@y"))],
    actions := [.expr (viewRow f rs (.var "@y"))] }

/-- A naive view row with a column that has a parent is stale. `column` ranges over the
children and, at `arity`, the output. -/
def staleRule (f : FnName) (arity : Nat) (column : Nat) : Rule :=
  let cs := rebuildVars arity
  let key : Expr := if column < arity then .var ("@c" ++ toString column) else .var "@e"
  { query := [.expr (viewRow f cs (.var "@e")), .expr (ufRow key (.var "@x")),
              .ne key (.var "@x")],
    actions := [subsumeView f cs (.var "@e")] }

/-- The index of the view: a row per column, relating the view row to each value it
mentions, so that a union-find edge finds every row it moves by lookup. -/
@[blueprint "def:view-index"
  (statement := /--
  \[
  \begin{aligned}
  \textsc{Idx}_f&:\ \mathtt{View}_f(c_1,\ldots,c_{n+1})\\
    &\qquad\Rightarrow\mathtt{HasChild}(\mathtt{View}_f(c_1,\ldots,c_{n+1}),c_1),\ \ldots,\
    \mathtt{HasChild}(\mathtt{View}_f(c_1,\ldots,c_{n+1}),c_{n+1})
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def indexRule (f : FnName) (arity : Nat) : Rule :=
  let cs := rebuildVars arity ++ [Expr.var "@e"]
  let row := viewRow f (rebuildVars arity) (.var "@e")
  { query := [.expr row],
    actions := cs.map fun c => .expr (.app hasChildName [row, c]) }

/-- The indexed view: the index entry of column `i` of a row, joined with the union-find
edge of that column, moves the row to the column's parent. One binary join; builds write a
node's row with the node. -/
@[blueprint "def:view-indexed"
  (statement := /--
  \[
  \begin{aligned}
  \textsc{Rekey}_{f,i}&:\ \mathtt{HasChild}(\mathtt{View}_f(c_1,\ldots,c_{n+1}),c_i)\land\mathtt{UF}(c_i,x)\land c_i\ne x\\
    &\qquad\Rightarrow\kw{subsume}(\mathtt{View}_f(c_1,\ldots,c_{n+1})),\ \mathtt{View}_f(c_1,\ldots,x,\ldots,c_{n+1})\\
  \operatorname{exist}(f(e_1,\ldots,e_n))&\ni\mathtt{View}_f(e_1,\ldots,e_n,f(e_1,\ldots,e_n))
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def rekeyRule (f : FnName) (arity : Nat) (column : Nat) : Rule :=
  let cs := rebuildVars arity
  let key : Expr := if column < arity then .var ("@c" ++ toString column) else .var "@e"
  let moved := if column < arity then viewRow f (cs.set column (.var "@x")) (.var "@e")
    else viewRow f cs (.var "@x")
  { query := [.expr (.app hasChildName [viewRow f cs (.var "@e"), key]),
              .expr (ufRow key (.var "@x")), .ne key (.var "@x")],
    actions := [subsumeView f cs (.var "@e"), .expr moved] }

/-- The congruence rule read over the view: two rows at one key keep the smaller output,
subsume the other row, and link the larger output under the smaller. The functional
dependency of the view's output on its key. -/
@[blueprint "def:fd-instances"
  (statement := /--
  \[
  \mathtt{UF}(a,b)\ \kw{:merge}\ \mathtt{UF}(b',b);\ \min(b,b')\qquad
  \mathtt{View}_f(c_1,\ldots,c_n,y)\ \kw{:merge}\ \mathtt{UF}(y',y);\ \min(y,y')
  \]
  -/)
  (latexEnv := "paperfragment")]
def viewCongruenceRule (f : FnName) (arity : Nat) : Rule :=
  fdRule (viewName f) (rebuildVars arity) "@y" "@z" fun y z => [.expr (ufRow z y)]

/-- The rules that keep a constructor's view rows canonical, by mode. -/
def rekeyRules (o : Options) (f : FnName) (arity : Nat) : List (Rule × RuleOrigin) :=
  match o.views with
  | .none => []
  | .naive =>
      (viewRule f arity, .rebuild (.view f)) ::
        (List.range (arity + 1)).map fun i => (staleRule f arity i, .rebuild (.stale f))
  | .indexed =>
      (indexRule f arity, .rebuild (.index f)) ::
        (List.range (arity + 1)).map fun i => (rekeyRule f arity i, .rebuild (.rekey f i))

/-- The rule that detects a congruence of `f`, by mode. -/
def mergeRules (o : Options) (f : FnName) (arity : Nat) : List (Rule × RuleOrigin) :=
  match o.views with
  | .none => rebuildRules f arity
  | _ => [(viewCongruenceRule f arity, .rebuild (.viewCongruence f))]

/-- The maintenance rules in the groups a phased rebuild runs: the union-find rules, the
view maintenance, and the congruence detection. Empty groups are dropped. -/
def maintenanceGroups (o : Options) (P : Program) : List (List (Rule × RuleOrigin)) :=
  [[(pathCompressRule, .rebuild .compress), (ufCollideRule, .rebuild .collide)],
   P.ctors.flatMap fun fk => rekeyRules o fk.1 fk.2,
   P.ctors.flatMap fun fk => mergeRules o fk.1 fk.2].filter fun g => !g.isEmpty

/-- The maintenance rules, with their origins. -/
@[blueprint "def:maintenance"
  (statement := /--
  \[
  M_P\triangleq\{\textsc{Compress},\ \textsc{Collide}\}\cup\{\textsc{Cong}_f\mid f\text{ applied in }P\}
  \]
  \[
  \begin{aligned}
  \textsc{Compress}&:\ \mathtt{UF}(a,b)\land\mathtt{UF}(b,c)\land b\ne c
    \Rightarrow\kw{subsume}(\mathtt{UF}(a,b)),\ \mathtt{UF}(a,c)\\
  \textsc{Collide}&:\ \mathtt{UF}(a,b)\land\mathtt{UF}(a,c)\land b=\min(b,c)\land b\ne c
    \Rightarrow\kw{subsume}(\mathtt{UF}(a,c)),\ \mathtt{UF}(c,b)\\
  \textsc{Cong}_f&:\ f(a_1,\ldots,a_n)\land f(b_1,\ldots,b_n)
    \land\textstyle\bigwedge_i\bigl(\mathtt{UF}(a_i,r_i)\land\mathtt{UF}(b_i,r_i)\bigr)\\
  &\quad\land\ \mathtt{UF}(f(a_1,\ldots,a_n),y)\land\mathtt{UF}(f(b_1,\ldots,b_n),z)
    \land y=\min(y,z)\land y\ne z\Rightarrow\mathtt{UF}(z,y)
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def maintenanceRules (P : Program) : List (Rule × RuleOrigin) :=
  (pathCompressRule, .rebuild .compress) :: (ufCollideRule, .rebuild .collide) ::
    P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-- The compiled rules of a source command's rules, numbered from `index` in
`Program.rules` of the source. -/
def encodeRulesWith (o : Options) (index : Nat) (rs : List Rule) : List (Rule × RuleOrigin) :=
  rs.zipIdx.map fun ri => (encodeRuleWith o ri.1, .source (index + ri.2))

def encodeRules (index : Nat) (rs : List Rule) : List (Rule × RuleOrigin) :=
  encodeRulesWith {} index rs

/-- The maintenance saturation, with its origins. A phased rebuild saturates each group
but the last before the next, inside an outer saturation: the union-find settles before
the term rules read it, and the view settles before congruences are looked for. -/
@[blueprint "def:phased"
  (statement := /--
  \[
  \kw{saturate}\bigl(\kw{saturate}(\kw{run}\ \{\textsc{Compress},\textsc{Collide}\});\
    \kw{saturate}(\kw{run}\ \{\textsc{Idx}_f,\textsc{Rekey}_{f,i}\mid f,i\});\
    \kw{run}\ \{\textsc{Cong}_f\mid f\}\bigr)
  \]
  -/)
  (latexEnv := "paperfragment")]
def rebuildWith (o : Options) (P : Program) : Schedule × List RuleOrigin :=
  let groups := maintenanceGroups o P
  let origins := (groups.flatten).map Prod.snd
  if o.phased then
    let runs := groups.map fun g => Schedule.run (g.map Prod.fst)
    match runs.getLast? with
    | some last =>
        (.saturate (Schedule.seqAll (runs.dropLast.map Schedule.saturate ++ [last])), origins)
    | none => (.saturate (.run []), origins)
  else (.saturate (.run (groups.flatten.map Prod.fst)), origins)

def rebuild (P : Program) : Schedule × List RuleOrigin := rebuildWith {} P

/-- Compile a schedule, numbering source rules from `index` in `Program.rules`. Every run
is followed by a rebuild, so a compiled saturation's body ends at a rebuild fixpoint and
each of its passes is one source pass. -/
@[blueprint "def:compile-schedule"
  (statement := /--
  \begin{mathpar}
  \ir{Rule}{Q\leadsto Q'\\H\leadsto H'}{(Q\Rightarrow H)\leadsto(Q'\Rightarrow H')}
  \and
  \ir{Run}{r_i\leadsto r_i'\ (\forall i)}
    {\kw{run}\ \{r_1,\ldots,r_n\}\leadsto\kw{run}\ \{r_1',\ldots,r_n'\};\ \kw{saturate}\ (\kw{run}\ M_P)}
  \and
  \ir{Saturate}{S\leadsto S'}{\kw{saturate}\ S\leadsto\kw{saturate}\ S'}
  \and
  \ir{Seq}{S_1\leadsto S_1'\\S_2\leadsto S_2'}{S_1;S_2\leadsto S_1';S_2'}
  \and
  \ir{Program}{S\leadsto S'\\Q\leadsto Q'}{(S;\ \kw{check}\ Q)\leadsto(S';\ \kw{check}\ Q')}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def encodeScheduleWith (o : Options) (P : Program) :
    Schedule → Nat → Schedule × List RuleOrigin × Nat
  | .run rs, index =>
      let compiled := encodeRulesWith o index rs
      let (m, mo) := rebuildWith o P
      (.seq (.run (compiled.map Prod.fst)) m, compiled.map Prod.snd ++ mo, index + rs.length)
  | .saturate S, index =>
      let (S', os, next) := encodeScheduleWith o P S index
      (.saturate S', os, next)
  | .seq S₁ S₂, index =>
      let (T₁, o₁, next) := encodeScheduleWith o P S₁ index
      let (T₂, o₂, last) := encodeScheduleWith o P S₂ next
      (.seq T₁ T₂, o₁ ++ o₂, last)

def encodeSchedule (P : Program) : Schedule → Nat → Schedule × List RuleOrigin × Nat :=
  encodeScheduleWith {} P

/-- The congruence pass with origins for later proof resugaring, under the options. -/
def compileWith (o : Options) (P : Program) : Compiled :=
  let (S, os, _) := encodeScheduleWith o P P.schedule 0
  { program := { schedule := S, check := (encodeQueryWith o P.check 0).1 }, origins := os }

/-- The congruence pass the paper presents: no views, one maintenance set. -/
def compile (P : Program) : Compiled := compileWith {} P

/-- The executable program, independent of all proof instrumentation. -/
def encode (P : Program) : Program := (compile P).program

/-- The executable program under the options. -/
def encodeWith (o : Options) (P : Program) : Program := (compileWith o P).program

end Egglog.Congruence
