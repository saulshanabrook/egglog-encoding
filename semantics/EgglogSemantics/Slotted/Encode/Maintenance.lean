import EgglogSemantics.Slotted.Encode.Layout
import Architect

/-!
# Slotted maintenance

The unoriented relation `RenamesTo(a,m,b)` means `a = m * b`: `m` maps `b`'s
slots to `a`'s names. Reflexivity, inversion and composition include symmetry closure.
`FS` intersects node estimates and transports them through equations in both directions;
map restriction retires only strict shortenings. Migration and child update select their
smaller destination at use sites. All rules saturate together after a user round.

A replacement has the next generation and subsumes the old row. This distinguishes a
recreated spelling from its permanently subsumed predecessor. Dedup merges identical
spellings at different generations. No equation is retired merely because a union reverses
its endpoints. Finite `Orbit` witnesses make symmetry nonmembership an ordinary target
disequality, without a collected group value or a change to the target semantics.
-/

namespace Egglog.Slotted.Encode

open Target

/-! ### Shared variables and shorthands -/

private def va : Expr := .var "@a"
private def vb : Expr := .var "@b"
private def vc : Expr := .var "@c"
private def vm : Expr := .var "@m"
private def vn : Expr := .var "@n"
private def vk : Expr := .var "@k"
private def vA : Expr := .var "@A"
private def vB : Expr := .var "@B"
private def vC : Expr := .var "@C"
private def vp : Expr := .var "@p"
private def vI : Expr := .var "@I"

def pimg (m : Expr) : Expr := prim "@img" [m]
def pdom (m : Expr) : Expr := prim "@dom" [m]
def pinv (m : Expr) : Expr := prim "@inv" [m]
def pcomp (m m' : Expr) : Expr := prim "@comp" [m, m']
def prestrict (m A : Expr) : Expr := prim "@restrict" [m, A]
def pid (A : Expr) : Expr := prim "@id" [A]
def papply (m s : Expr) : Expr := prim "@apply" [m, s]
def punion (A B : Expr) : Expr := prim "@union" [A, B]
def pinter (A B : Expr) : Expr := prim "@inter" [A, B]
def pdiff (A B : Expr) : Expr := prim "@diff" [A, B]
def pset (ss : List Expr) : Expr := .app setName ss
def pisPerm (π A : Expr) : Expr := prim "@isPerm" [π, A]

/-- `id_A ∘ m ∘ id_B`: `m` spelled on the slot sets of its two classes. -/
def trimmed (A m B : Expr) : Expr := pcomp (pid A) (pcomp m (pid B))

/-- The union of a list of slot set expressions. -/
def unions : List Expr → Expr
  | [] => emptySet
  | [e] => e
  | e :: es => punion e (unions es)

def renamesTo (a m b : Expr) : Pattern := row renamesToName [a, m, b]
def fs (a A : Expr) : Pattern := row fsName [a, A]
def wRenamesTo (a m b : Expr) : Action := write renamesToName [a, m, b]
def wFS (a A : Expr) : Action := write fsName [a, A]

/-! ### Free slots -/

/-- `$0 ⇒ FS($0, {$0})`: the slot leaf depends on its one slot. -/
def leafFSRule : Rule :=
  { query := [.expr leafExpr], actions := [wFS leafExpr (pset [leafExpr])] }

/-- The generation of the matched row, and of its replacement. -/
def genVar : Expr := .var "@g"
def nextGen : Expr := .var "@g1"

/-- The pattern columns of a node of `f`: the generation `@g`, edge variables `@m_j`, child
variables `@c_j`, binder field variables `@b_j` and payload variables `@p_j`. -/
def nodeCols (L : Layout) (f : FnName) (n : Nat) : List Expr :=
  L.targetCols f n genVar (fun j => .var s!"@m{j}") fun j => match L.column f j with
    | .child => .var s!"@c{j}"
    | .binder => .var s!"@b{j}"
    | .payload => .var s!"@p{j}"

/-- The node pattern `@a = f(…)`. -/
def nodeAtom (L : Layout) (f : FnName) (n : Nat) : Pattern := .eq va (.app f (nodeCols L f n))

/-- The binder fields bound in child `j`, as a slot set expression. -/
def boundSet (L : Layout) (f : FnName) (j : Nat) : Expr :=
  pset ((L.boundIn f j).map fun k => .var s!"@b{k}")

/-- The node's own estimate of its free slots: the image of each child's edge less the names
bound in that child. -/
def nodeFSExpr (L : Layout) (f : FnName) (n : Nat) : Expr :=
  unions ((L.childPositions f n).map fun j =>
    if (L.boundIn f j).isEmpty then pimg (.var s!"@m{j}")
    else pdiff (pimg (.var s!"@m{j}")) (boundSet L f j))

/-- `NodeFS_f`: `a = f(ρ̄, c̄, s̄) ⇒ FS(a, ⋃ᵢ (img(ρᵢ) ∖ Bᵢ))`. -/
def nodeFSRule (L : Layout) (f : FnName) (n : Nat) : Rule :=
  if (L.childPositions f n).isEmpty then
    { query := [nodeAtom L f n], actions := [wFS va emptySet] }
  else
    { query := [nodeAtom L f n, bindP "@S" (nodeFSExpr L f n)], actions := [wFS va (.var "@S")] }

/-- The merge of `FS` by intersection: `FS(a, A) ∧ FS(a, B) ∧ C = A ∩ B ∧ C ≠ A ⇒ FS(a, C),
subsume(FS(a, A))`. -/
def intersectFSRule : Rule :=
  { query := [fs va vA, fs va vB, bindP "@C" (pinter vA vB), .ne vC vA],
    actions := [wFS va vC, .subsume fsName [va, vA]] }

/-- `RenamesTo(a, m, b) ∧ FS(a, A) ∧ FS(b, B) ⇒ FS(a, m[B]), FS(b, m⁻¹[A])`. -/
def transportFSRule : Rule :=
  { query := [renamesTo va vm vb, fs va vA, fs vb vB,
              bindP "@A'" (pimg (prestrict vm vB)), bindP "@B'" (pimg (prestrict (pinv vm) vA))],
    actions := [wFS va (.var "@A'"), wFS vb (.var "@B'")] }

/-! ### Renaming closure and finite membership witnesses -/

/-- Each support carries its finite identity self-equation. -/
def reflexiveRule : Rule :=
  { query := [fs va vA, bindP "@I" (pid vA)], actions := [wRenamesTo va vI va] }

/-- Inversion keeps both directions available, even after a native union. -/
def inverseRule : Rule :=
  { query := [renamesTo va vm vb, bindP "@n" (pinv vm)], actions := [wRenamesTo vb vn va] }

/-- Composition includes paths, multiple parents and symmetry composition. -/
def composeRule : Rule :=
  { query := [renamesTo va vm vb, renamesTo vb vn vc, bindP "@k" (pcomp vm vn)],
    actions := [wRenamesTo va vk vc] }

/-- Retire only a strictly shortened map. Transport reads its original entries in the same
pre-state. Self-equations use the same rule; at a fixpoint they are permutations of the
current support. -/
def restrictRenamesRule : Rule :=
  { query := [renamesTo va vm vb, fs va vA, fs vb vB,
              bindP "@n" (trimmed vA vm vB), .ne vn vm],
    actions := [wRenamesTo va vn vb, .subsume renamesToName [va, vm, vb]] }

/-- Materialize every finite permutation as a membership witness, including nonmembers.
These ordinary terms let a query test nonmembership without relational negation. -/
def orbitSeedRule : Rule :=
  { query := [fs va vA, .expr (.app memName [vp, prim "@perms" [vA]])],
    actions := [write orbitName [va, vp]] }

/-- A symmetry's witness is equal to the identity witness. The maps themselves are never
unioned, so primitive values retain structural equality. -/
def orbitMemberRule : Rule :=
  { query := [renamesTo va vp va, fs va vA, isTrue (pisPerm vp vA), bindP "@I" (pid vA)],
    actions := [.union (.app orbitName [va, vp]) (.app orbitName [va, vI])] }

/-! ### Term updates, per constructor -/

/-- `Collide_f`: two nodes with the same children and payloads are equal under the union of
the correspondences of their children, each read through a symmetry of the child, and the
alignment of their binders. Composition uses only entries where all steps are defined;
child maps and self-equations need not yet be restricted to the current free slots. -/
@[blueprint "def:slotted-collide"
  (statement := /--
  \[
  \begin{aligned}
   \textsc{Collide}:\quad
   &a=\mathtt{Mul}(g,\rho_1,c_1,\rho_2,c_2)
     \land a'=\mathtt{Mul}(g',\eta_1,c_1,\eta_2,c_2)\\
   &\land\mathtt{RenamesTo}(c_1,\pi_1,c_1)\land\mathtt{RenamesTo}(c_2,\pi_2,c_2)\\
   &\land m=\operatorname{align}(\rho_1\circ\pi_1\circ\eta_1^{-1},
     \rho_2\circ\pi_2\circ\eta_2^{-1})\\
   &\Rightarrow\mathtt{RenamesTo}(a,m,a').
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def collideRule (L : Layout) (f : FnName) (n : Nat) : Option Rule :=
  let children := L.childPositions f n
  let binders := L.binderPositions f n
  if children.isEmpty && binders.isEmpty then none else
  let cols' := L.targetCols f n (.var "@g'") (fun j => .var s!"@n{j}") fun j =>
    match L.column f j with
    | .child => .var s!"@c{j}"
    | .binder => .var s!"@d{j}"
    | .payload => .var s!"@p{j}"
  let perChild := children.flatMap fun j =>
    [renamesTo (.var s!"@c{j}") (.var s!"@pi{j}") (.var s!"@c{j}"),
     bindP s!"@k{j}" (pcomp (.var s!"@m{j}") (pcomp (.var s!"@pi{j}") (pinv (.var s!"@n{j}"))))]
  let perBinder := binders.map fun k =>
    bindP s!"@k{k}" (.app renName [.app pairName [.var s!"@d{k}", .var s!"@b{k}"]])
  let parts : List Expr := (children ++ binders).map fun j => .var s!"@k{j}"
  let query := [nodeAtom L f n, .eq (.var "@a'") (.app f cols')] ++ perChild ++ perBinder ++
    [bindP "@m" (prim "@align" parts)]
  some { query := query, actions := [wRenamesTo va vm (.var "@a'")] }

/-- The node's local slots: the images of its edges and its binder fields. -/
def localSlots (L : Layout) (f : FnName) (n : Nat) : Expr :=
  unions (((L.childPositions f n).map fun j => pimg (.var s!"@m{j}")) ++
    (if (L.binderPositions f n).isEmpty then []
     else [pset ((L.binderPositions f n).map fun k => .var s!"@b{k}")]))

/-- A term update: the query, which binds the replacement's generation `@g1 = @g + 1`, the
replacement's columns, and the rule `query ⇒ union(target, f(cols′)), subsume(f(cols))`. -/
def updateRule (L : Layout) (f : FnName) (n : Nat) (query : List Pattern) (target : Expr)
    (cols' : List Expr) : Rule :=
  { query := query ++ [bindP "@g1" (prim "@succ" [genVar])],
    actions := [.union target (.app f cols'), .subsume f (nodeCols L f n)] }

/-- `Migrate_f`: a node rebuilt in the smaller endpoint's names and unioned into it,
the restricted inverse map extended to the node's slots by `extend`. -/
def migrateRule (L : Layout) (f : FnName) (n : Nat) : Rule :=
  let cols' := L.targetCols f n nextGen (fun j => .var s!"@e{j}") fun j =>
    match L.column f j with
    | .child => .var s!"@c{j}"
    | .binder => .var s!"@w{j}"
    | .payload => .var s!"@p{j}"
  let query := [renamesTo va vm vb, fs va vA, fs vb vB, .eq vb (.min va vb), .ne vb va,
      nodeAtom L f n,
      bindP "@n" (trimmed vA vm vB),
      bindP "@L" (localSlots L f n), bindP "@h" (prim "@extend" [pinv vn, .var "@L", vB])] ++
    ((L.childPositions f n).map fun j => bindP s!"@e{j}" (pcomp (.var "@h") (.var s!"@m{j}"))) ++
    ((L.binderPositions f n).map fun k => bindP s!"@w{k}" (papply (.var "@h") (.var s!"@b{k}")))
  updateRule L f n query vb cols'

/-- `Child_{f,j}`: a node whose child `j` has a smaller equivalent endpoint points to it,
its edge composed with the restricted equation map. -/
def childRule (L : Layout) (f : FnName) (n : Nat) (j : Nat) : Rule :=
  let cols' := L.targetCols f n nextGen (fun i => if i = j then .var "@e" else .var s!"@m{i}")
    fun i => match L.column f i with
    | .child => if i = j then .var "@d" else .var s!"@c{i}"
    | .binder => .var s!"@b{i}"
    | .payload => .var s!"@p{i}"
  let c : Expr := .var s!"@c{j}"
  let query := [nodeAtom L f n, renamesTo c vm (.var "@d"), fs c vA, fs (.var "@d") vB,
      .ne c (.var "@d"),
      .eq (.var "@d") (.min c (.var "@d")), bindP "@n" (trimmed vA vm vB),
      bindP "@e" (pcomp (.var s!"@m{j}") vn)]
  updateRule L f n query va cols'

/-- `Restrict_{f,j}`: an edge restricted to the free slots of its child. -/
def restrictRule (L : Layout) (f : FnName) (n : Nat) (j : Nat) : Rule :=
  let cols' := L.targetCols f n nextGen (fun i => if i = j then .var "@e" else .var s!"@m{i}")
    fun i => match L.column f i with
    | .child => .var s!"@c{i}"
    | .binder => .var s!"@b{i}"
    | .payload => .var s!"@p{i}"
  let query := [nodeAtom L f n, fs (.var s!"@c{j}") vA,
      bindP "@e" (prestrict (.var s!"@m{j}") vA), .ne (.var "@e") (.var s!"@m{j}")]
  updateRule L f n query va cols'

/-- `Dedup_f`: two live rows with one spelling and different generations are one node: their
classes are unioned and the older row is retired. -/
def dedupRule (L : Layout) (f : FnName) (n : Nat) : Rule :=
  let cols' := L.targetCols f n (.var "@g'") (fun j => .var s!"@m{j}") fun j =>
    match L.column f j with
    | .child => .var s!"@c{j}"
    | .binder => .var s!"@b{j}"
    | .payload => .var s!"@p{j}"
  { query := [nodeAtom L f n, .eq (.var "@a'") (.app f cols'), .ne genVar (.var "@g'"),
              .eq genVar (.min genVar (.var "@g'"))],
    actions := [.union va (.var "@a'"), .subsume f (nodeCols L f n)] }

/-! ### The groups and the schedule -/

/-- The free-slot analysis: the leaf fact, `NodeFS_f` per constructor, the merge of `FS` by
intersection, and transport along equations. `B_i` is the set of binder fields bound in
child `i`; `g` is the row's generation, which every rule binds as a wildcard. -/
@[blueprint "def:slotted-fs-rules"
  (statement := /--
  \[
  \begin{aligned}
   &\$0\Rightarrow\mathtt{FS}(\$0,\{\$0\})
    \qquad a=\mathtt{Num}(g,k)\Rightarrow\mathtt{FS}(a,\varnothing)\\
   &a=\SumZeroTen(g,\$i,\rho,b)
     \Rightarrow\mathtt{FS}(a,\operatorname{img}(\rho)\setminus\{\$i\})\\
   \textsc{NodeFS}_f&:\ a=f(g,\bar\rho,\bar c,\bar s)
     \Rightarrow\mathtt{FS}\bigl(a,
       \textstyle\bigcup_i(\operatorname{img}(\rho_i)\setminus B_i)\bigr)\\
   \textsc{Intersect}&:\ \mathtt{FS}(a,A)\land\mathtt{FS}(a,B)\land C=A\cap B\land C\ne A
     \\
   &\quad\Rightarrow\mathtt{FS}(a,C),\ \kw{subsume}(\mathtt{FS}(a,A))\\
   \textsc{Transport}&:\ \mathtt{RenamesTo}(a,m,b)\land\mathtt{FS}(a,A)\land\mathtt{FS}(b,B)
     \\
   &\quad\Rightarrow\mathtt{FS}(a,m[B]),\ \mathtt{FS}(b,m^{-1}[A])
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def analysisRules (L : Layout) (ctors : List (FnName × Nat)) : List Rule :=
  leafFSRule :: (ctors.map fun fk => nodeFSRule L fk.1 fk.2) ++
    [intersectFSRule, transportFSRule]

/-- The single equation relation: finite identity, inversion, composition, and support
restriction. Collision discovers equations; finite witnesses support negative comparisons. -/
@[blueprint "def:slotted-renames-rules"
  (statement := /--
  \[
  \begin{gathered}
   \textsc{Identity}:\ \mathtt{FS}(a,A)\Rightarrow\mathtt{RenamesTo}(a,\mathrm{id}_A,a)
   \qquad
   \textsc{Reverse}:\ \mathtt{RenamesTo}(a,m,b)\Rightarrow\mathtt{RenamesTo}(b,m^{-1},a)\\
   \begin{aligned}
   \textsc{Compose}&:\ \mathtt{RenamesTo}(a,m,b)\land\mathtt{RenamesTo}(b,n,c)
     \Rightarrow\mathtt{RenamesTo}(a,m\circ n,c)\\
   \textsc{Trim}&:\ \mathtt{RenamesTo}(a,m,b)\land\mathtt{FS}(a,A)\land\mathtt{FS}(b,B)
     \land n=\mathrm{id}_A\circ m\circ\mathrm{id}_B\land n\ne m\\
   &\quad\Rightarrow\mathtt{RenamesTo}(a,n,b),\ \kw{subsume}(\mathtt{RenamesTo}(a,m,b))
   \end{aligned}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def renamingRules (L : Layout) (ctors : List (FnName × Nat)) : List Rule :=
  [reflexiveRule, inverseRule, composeRule, restrictRenamesRule,
   orbitSeedRule, orbitMemberRule] ++ ctors.filterMap fun fk => collideRule L fk.1 fk.2

/-- The children that binding position `k` of `f` covers. -/
def coveredBy (L : Layout) (f : FnName) (k : Nat) : List Nat :=
  ((L.bind f).filter fun ji => ji.1 = k).map Prod.snd

/-- Binder refresh: a bound name also used outside its scope is renamed, in the binder and
its covered children's edges, to a name the node does not use. `Refresh_{f,k,u}` fires when
the name of binding position `k` is in the image of the edge of a child `u` the binder does
not cover; a binder another binder of the same scope shadows is left to `Shadow`. -/
def refreshRule (L : Layout) (f : FnName) (n : Nat) (k : Nat) (u : Nat) : Rule :=
  let covered := coveredBy L f k
  let cols' := L.targetCols f n nextGen
    (fun i => if i ∈ covered then .var s!"@e{i}" else .var s!"@m{i}") fun i =>
      match L.column f i with
      | .child => .var s!"@c{i}"
      | .binder => if i = k then .var "@w" else .var s!"@b{i}"
      | .payload => .var s!"@p{i}"
  let peers := (L.binderPositions f n).filter fun k' => k' ≠ k && coveredBy L f k' = covered
  let query := [nodeAtom L f n, isTrue (prim "@elem" [.var s!"@b{k}", pimg (.var s!"@m{u}")])] ++
    (peers.map fun k' => .ne (.var s!"@b{k}") (.var s!"@b{k'}")) ++
    [bindP "@L" (localSlots L f n), bindP "@w" (prim "@mint" [.var "@L"])] ++
    (covered.flatMap fun i =>
      [bindP s!"@u{i}" (prim "@align" [.app renName [.app pairName [.var s!"@b{k}", .var "@w"]],
         pid (pdiff (pimg (.var s!"@m{i}")) (pset [.var s!"@b{k}"]))]),
       bindP s!"@e{i}" (pcomp (.var s!"@u{i}") (.var s!"@m{i}"))])
  updateRule L f n query va cols'

/-- Shadowed binders: two binding positions of one scope with one name, the earlier of which
binds nothing, the later shadowing it; the earlier is renamed to a name the node does not
use. -/
def shadowRule (L : Layout) (f : FnName) (n : Nat) (k k' : Nat) : Rule :=
  let cols' := L.targetCols f n nextGen (fun i => .var s!"@m{i}") fun i => match L.column f i with
    | .child => .var s!"@c{i}"
    | .binder => if i = k then .var "@w" else .var s!"@b{i}"
    | .payload => .var s!"@p{i}"
  let query := [nodeAtom L f n, .eq (.var s!"@b{k}") (.var s!"@b{k'}"),
    bindP "@L" (localSlots L f n), bindP "@w" (prim "@mint" [.var "@L"])]
  updateRule L f n query va cols'

/-- The refresh rules of a constructor: for every binding position, each uncovered child,
and each later binding position of the same scope. -/
def binderRules (L : Layout) (f : FnName) (n : Nat) : List Rule :=
  (L.binderPositions f n).flatMap fun k =>
    let covered := coveredBy L f k
    ((L.childPositions f n).filter (· ∉ covered)).map (refreshRule L f n k) ++
      ((L.binderPositions f n).filter fun k' => k < k' && coveredBy L f k' = covered).map
        (shadowRule L f n k)

/-- The term updates per constructor: Collide discovers equations between two nodes with
the same children through the children's symmetries and the alignment of the binders,
Migrate rebuilds a follower's node in its leader's names, Child points a node at its child's
leader, Restrict drops redundant entries from an edge, Refresh renames a bound name also
used outside its scope, and Dedup merges two rows with one spelling. Every update subsumes
the replaced row and writes its replacement at the replaced row's generation plus one, so
the replacement's key is new. -/
@[blueprint "def:slotted-term-updates"
  (statement := /--
  \[
  \begin{aligned}
   \textsc{Migrate}:\quad
   &a=\mathtt{Mul}(g,\rho_1,c_1,\rho_2,c_2)\land\mathtt{RenamesTo}(a,m,b)\land\mathtt{FS}(b,B)\\
   &\land b=\min(a,b)\land b\ne a
     \land\widehat m=\operatorname{extend}(m^{-1},\operatorname{img}(\rho_1)\cup\operatorname{img}(\rho_2),B)\\
   &\Rightarrow\kw{union}(b,\mathtt{Mul}(g{+}1,\widehat m\circ\rho_1,c_1,\widehat m\circ\rho_2,c_2)),\
     \kw{subsume}(a)\\[2pt]
   \textsc{Child}:\quad
   &a=\mathtt{Mul}(g,\rho_1,c_1,\rho_2,c_2)\land\mathtt{RenamesTo}(c_1,m,d)\land c_1\ne d\land d=\min(c_1,d)\\
   &\Rightarrow\kw{union}(a,\mathtt{Mul}(g{+}1,\rho_1\circ m,d,\rho_2,c_2)),\ \kw{subsume}(a)\\[2pt]
   \textsc{Restrict}:\quad
   &a=\mathtt{Mul}(g,\rho_1,c_1,\rho_2,c_2)\land\mathtt{FS}(c_1,A)\land\rho_1'=\rho_1|_A\land\rho_1'\ne\rho_1\\
   &\Rightarrow\kw{union}(a,\mathtt{Mul}(g{+}1,\rho_1',c_1,\rho_2,c_2)),\ \kw{subsume}(a)\\[2pt]
   \textsc{Dedup}_f:\quad
   &a=f(g,\bar t)\land a'=f(g',\bar t)\land g<g'
     \Rightarrow\kw{union}(a,a'),\ \kw{subsume}(a).
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def updateRulesAll (L : Layout) (ctors : List (FnName × Nat)) : List Rule :=
  ctors.flatMap fun fk =>
    binderRules L fk.1 fk.2 ++ [migrateRule L fk.1 fk.2] ++
      (L.childPositions fk.1 fk.2).flatMap (fun j =>
        [childRule L fk.1 fk.2 j, restrictRule L fk.1 fk.2 j]) ++
      [dedupRule L fk.1 fk.2]

/-- The maintenance rules `M`, in three groups: analyses, renaming closure,
and term updates. -/
def maintenanceGroups (L : Layout) (ctors : List (FnName × Nat)) : List (List Rule) :=
  [analysisRules L ctors, renamingRules L ctors, updateRulesAll L ctors]

/-- The rebuild that follows every compiled run: all maintenance rules saturate together. -/
@[blueprint "def:slotted-rebuild"
  (statement := /--
  \[
  M_P=M_{\mathrm{FS}}\cup M_{\mathrm{Rename}}\cup M_{\mathrm{Update}},
  \qquad M_{\mathrm{Rename}}\text{ includes }\textsc{Collide}_f.
  \]
  \[
  \kw{run}\ R\ \leadsto\ \kw{run}\ R';\ \kw{saturate}\ (\kw{run}\ M_P).
  \]
  Sequences and saturations compile structurally. Thus every user round is followed by
  joint maintenance saturation; nonleader rows are subsumed after replacement.
  -/)
  (latexEnv := "paperfragment")]
def rebuild (L : Layout) (ctors : List (FnName × Nat)) : Schedule :=
  .saturate (.run (maintenanceGroups L ctors).flatten)

end Egglog.Slotted.Encode
