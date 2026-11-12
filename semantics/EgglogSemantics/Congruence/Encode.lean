import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names
import Architect

/-!
# Congruence compilation

The congruence pass compiles the constructor source fragment to rules over an explicit
union-find relation `@UF(key, parent)`. Source terms serve as ids. Without source
subsumption, builds assert only self-loops and congruence reads constructor rows directly;
maintenance consists of compression, collision and constructor congruence. This is the
encoding displayed in the paper.

For a program containing a source `subsume`, `Options.forProgram` enables `subsumption`:
builds also assert permanent `@Node_f(children, term)` rows, source subsumption records
`@Sub_f(children)` markers, and maintenance hides every congruent spelling. Congruence
reads the permanent node rows, so hidden applications still merge. Leaders decrease in
the term order; disequality guards protect canonical edges from subsumption.

Flattening visits children before parents, left to right. `Resugar.Query` consumes premise
proofs in this same order. Each compiled run is followed by a complete rebuild; sequences
and saturations preserve the source schedule's structure.

`compile` returns the program and one origin per rule in `Program.rules` order, for proof
lifting; `encode` returns the program alone. `Options` also selects canonical node views
and phased rebuilding. The default chooses subsumption from the source and uses no views
and one maintenance ruleset. The definitions'
`@[blueprint]` attributes display the pass as inference rules in the paper.
-/

namespace Egglog.Congruence

/-- Generated maintenance rules: the union-find rules, the congruence and subsumption rules
of a constructor, and the rules of its canonical node view when that optimization is on. -/
inductive RebuildOrigin where
  | compress
  | collide
  | congruence (constructor : FnName)
  /-- A spelling whose children are congruent to a marked, subsumed row's is subsumed. -/
  | subsume (constructor : FnName)
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

/-- Encoding options. The defaults give the paper's plain encoding on subsume-free
programs; `forProgram` enables subsumption when the source needs it. `phased` runs the
union-find rules to a fixpoint before the term rules in every rebuild. -/
structure Options where
  views : ViewMode := .none
  phased : Bool := false
  /-- Keep permanent nodes and propagate source subsumption between spellings. -/
  subsumption : Bool := false
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

/-- A node atom of `f`: the children and the node, `@Node_f(a₁, …, aₙ, k)`. -/
def nodeAtom (f : FnName) (children : List Expr) (id : Expr) : Expr :=
  .app (nodeName f) (children ++ [id])

/-- The node row a build writes for an application: its children and the application. -/
def nodeRow (f : FnName) (args : List Expr) : Expr := nodeAtom f args (.app f args)

/-- The marker row of a subsumed spelling: `@Sub_f(a₁, …, aₙ)`. -/
def subRow (f : FnName) (args : List Expr) : Expr := .app (subName f) args

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

def encodeQuery : Query → Nat → Query × Nat := encodeQueryWith {}

mutual

/-- Build children before their parent and give every value a union-find self-loop.
When subsumption is enabled, also record each application in its permanent node relation.
With indexed views, also write the node's view row, keyed by its children as built. -/
def encodeBuildWith (o : Options) : Expr → List Action
  | e@(.lit _) | e@(.var _) => [.expr (ufRow e e)]
  | .min a b => encodeBuildWith o a ++ encodeBuildWith o b
  | .app f args =>
      encodeBuildArgsWith o args ++
        (if o.views = .indexed then [.expr (viewRow f args (.app f args))] else []) ++
        (if o.subsumption then [.expr (nodeRow f args)] else []) ++
        [.expr (ufRow (.app f args) (.app f args))]

/-- Build argument occurrences in the same left-to-right order as query flattening. -/
def encodeBuildArgsWith (o : Options) : List Expr → List Action
  | [] => []
  | e :: es => encodeBuildWith o e ++ encodeBuildArgsWith o es

end

/-- A union links both ids to their minimum; a bare action builds its term and subterms; a
subsume builds its row and subsumes the spelling it built. With subsumption enabled it
also writes the marker from which `Sub_f` subsumes every congruent spelling. -/
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
  | .subsume f es => encodeBuildWith o (.app f es) ++ [.subsume f es] ++
      (if o.subsumption then [.expr (subRow f es)] else [])

/-- No justification argument is needed for compiling a head. -/
def encodeActionsWith (o : Options) (as : List Action) : List Action :=
  as.flatMap (encodeActionWith o)

/-- Compile a rule with a local fresh-variable supply. Source names must avoid `@`.
After rebuilding, query variables are bound to roots through union-find edges. Subsumption
affects heads and maintenance only; query compilation uses its fixed default setting. -/
def encodeRuleWith (o : Options) (r : Rule) : Rule :=
  { query := (encodeQueryWith { o with subsumption := false } r.query 0).1,
    actions := encodeActionsWith o r.actions }

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

/-- Resolve two parents of one key: keep the smaller, subsume the other edge, and link the
larger parent under the smaller. -/
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

/-- Link the larger root under the smaller for two applications with the same child
parents. Plain mode reads constructor rows directly. Subsumption mode reads permanent
node rows so that hidden applications still participate. -/
def congruenceRule (subsumption : Bool) (f : FnName) (arity : Nat) : Rule :=
  let as := congruenceVars "a" arity
  let bs := congruenceVars "b" arity
  let rs := congruenceVars "r" arity
  let k := if subsumption then Expr.var "@k" else .app f as
  let l := if subsumption then Expr.var "@l" else .app f bs
  { query := (if subsumption then
        [.expr (nodeAtom f as k), .expr (nodeAtom f bs l)]
      else [.expr (.app f as), .expr (.app f bs)]) ++
      ((as.zip bs).zip rs).flatMap (fun abr =>
        [.expr (ufRow abr.1.1 abr.2), .expr (ufRow abr.1.2 abr.2)]) ++
      [.expr (ufRow k (.var "@y")), .expr (ufRow l (.var "@z")),
       .eq (.var "@y") (.min (.var "@y") (.var "@z")), .ne (.var "@y") (.var "@z")],
    actions := [.expr (ufRow (.var "@z") (.var "@y"))] }

/-- Subsume a live application of `f` whose children have the same parents as a marked,
subsumed spelling's: at a rebuild fixpoint the parents agree exactly when the children are
congruent, so the compiled program subsumes the spellings the source considers subsumed,
including the ones built after the marker. -/
@[blueprint "def:subsume-encoding"
  (statement := /--
  For source programs with subsumption, extend the encoding by
  \[
  \operatorname{exist}(e)\mathrel{\gets}\operatorname{exist}(e)
    \cup\{\mathtt{Node}_f(\bar e',f(\bar e'))\mid f(\bar e')\in\operatorname{subexpr}(e)\}.
  \]
  \begin{mathpar}
  \ir{Subsume}{e=f(\bar e)}{\kw{subsume}(e)\leadsto\operatorname{exist}(e)
    \cup\{\kw{subsume}(e),\ \mathtt{Sub}_f(\bar e)\}}
  \end{mathpar}
  Add $\textsc{Sub}_f$ to $M_P$ and replace $\textsc{Cong}_f$ by
  \[
  \begin{aligned}
  \textsc{Sub}_f&:\ \mathtt{Sub}_f(\bar a)\land f(\bar b)
    \land\textstyle\bigwedge_i\bigl(\mathtt{UF}(a_i,r_i)\land\mathtt{UF}(b_i,r_i)\bigr)
    \Rightarrow\kw{subsume}(f(\bar b))\\
  \textsc{Cong}_f&:\ \mathtt{Node}_f(\bar a,k)\land\mathtt{Node}_f(\bar b,l)
    \land\textstyle\bigwedge_i\bigl(\mathtt{UF}(a_i,r_i)\land\mathtt{UF}(b_i,r_i)\bigr)\\
  &\quad\land\ \mathtt{UF}(k,y)\land\mathtt{UF}(l,z)
    \land y=\min(y,z)\land y\ne z\Rightarrow\mathtt{UF}(z,y).
  \end{aligned}
  \]
  Lifting reads a node row as its node: $\lceil\mathtt{Node}_f(\bar a,t)\rceil\triangleq(t=t)$.
  -/)
  (latexEnv := "paperfragment")]
def subsumeRule (f : FnName) (arity : Nat) : Rule :=
  let as := congruenceVars "a" arity
  let bs := congruenceVars "b" arity
  let rs := congruenceVars "r" arity
  { query := [.expr (subRow f as), .expr (.app f bs)] ++
      ((as.zip bs).zip rs).flatMap (fun abr =>
        [.expr (ufRow abr.1.1 abr.2), .expr (ufRow abr.1.2 abr.2)]),
    actions := [.subsume f bs] }

/-- Constructor congruence, plus subsumption propagation when enabled. A nullary
constructor has one application and needs no congruence rule. -/
def rebuildRules (subsumption : Bool) (f : FnName) (arity : Nat) : List (Rule × RuleOrigin) :=
  (if arity = 0 then [] else [(congruenceRule subsumption f arity, .rebuild (.congruence f))]) ++
    (if subsumption then [(subsumeRule f arity, .rebuild (.subsume f))] else [])

/-! ### Canonical node views

An optional view row holds the leaders of an application's children and of the application
itself. Compiled queries match these rows, and congruence detection compares rows at the
same key. -/

/-- The key variables of a generated view rule. -/
def rebuildVars (arity : Nat) : List Expr :=
  (List.range arity).map fun i => .var ("@c" ++ toString i)

/-- Derive a naive view row from an application's child parents and its own parent. -/
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

/-- Index a view row by each of its column values. -/
@[blueprint "def:view-index"
  (statement := /--
  \[
  \textsc{Idx}_f:\ \mathtt{View}_f(c_1,\ldots,c_{n+1})
    \Rightarrow\mathtt{HasChild}(\mathtt{View}_f(c_1,\ldots,c_{n+1}),c_1),\ldots,
    \mathtt{HasChild}(\mathtt{View}_f(c_1,\ldots,c_{n+1}),c_{n+1})
  \]
  -/)
  (latexEnv := "paperfragment")]
def indexRule (f : FnName) (arity : Nat) : Rule :=
  let cs := rebuildVars arity ++ [Expr.var "@e"]
  let row := viewRow f (rebuildVars arity) (.var "@e")
  { query := [.expr row],
    actions := cs.map fun c => .expr (.app hasChildName [row, c]) }

/-- Move an indexed view row to the parent of column `i`, subsuming the prior row.
`encodeBuildWith` supplies the initial rows. -/
@[blueprint "def:view-indexed"
  (statement := /--
  \[
  \begin{aligned}
  \textsc{Rekey}_{f,i}&:\ \mathtt{HasChild}(\mathtt{View}_f(c_1,\ldots,c_{n+1}),c_i)\land\mathtt{UF}(c_i,x)\land c_i\ne x\\
    &\qquad\Rightarrow\kw{subsume}(\mathtt{View}_f(c_1,\ldots,c_{n+1})),\ \mathtt{View}_f(c_1,\ldots,x,\ldots,c_{n+1})
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

/-- Resolve view rows at the same key: keep the smaller output, subsume the other row,
and link the larger output under the smaller. -/
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
  | .none => rebuildRules o.subsumption f arity
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
def maintenanceRules (subsumption : Bool) (P : Program) : List (Rule × RuleOrigin) :=
  (pathCompressRule, .rebuild .compress) :: (ufCollideRule, .rebuild .collide) ::
    P.ctors.flatMap fun fk => rebuildRules subsumption fk.1 fk.2

/-- The compiled rules of a source command's rules, numbered from `index` in
`Program.rules` of the source. -/
def encodeRulesWith (o : Options) (index : Nat) (rs : List Rule) : List (Rule × RuleOrigin) :=
  rs.zipIdx.map fun ri => (encodeRuleWith o ri.1, .source (index + ri.2))

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

/-- Compile a schedule, numbering source rules from `index` in `Program.rules` order and
following every run with a rebuild. -/
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

/-- Detect source subsumption automatically, enabling permanent nodes, markers and their
maintenance rules and selecting explicit reads. For subsume-free sources the requested
options are retained, so callers may also enable node rows explicitly. Phasing is retained. -/
def Options.forProgram (o : Options) (P : Program) : Options :=
  if P.schedule.subsumeFreeB then o
  else { o with views := .none, subsumption := true }

/-- The congruence pass with origins for later proof resugaring, under the options. -/
def compileWith (o : Options) (P : Program) : Compiled :=
  let o := o.forProgram P
  let (S, os, _) := encodeScheduleWith o P P.schedule 0
  let check := (encodeQueryWith { o with subsumption := false } P.check 0).1
  { program := { schedule := S, check := check }, origins := os }

/-- The default pass: select subsumption exactly when the source contains it, with no
views and one maintenance set. Subsume-free programs use the paper's plain encoding. -/
def compile (P : Program) : Compiled := compileWith {} P

/-- The executable program, independent of all proof instrumentation. -/
def encode (P : Program) : Program := (compile P).program

/-- The executable program under the options. -/
def encodeWith (o : Options) (P : Program) : Program := (compileWith o P).program

end Egglog.Congruence
