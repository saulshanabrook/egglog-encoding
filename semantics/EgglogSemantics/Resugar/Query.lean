import EgglogSemantics.Resugar.Builder

/-!
# Source premises from compiled premises

A source rule's compiled query is its flattening (`Congruence.encodeQueryExpr`). Given the
lifted proofs of the compiled premises, in that order, this rebuilds one source proof per
source pattern by walking the pattern in the same order. A lifted compiled premise states
`b = x` for an edge `UF(b, x)`, and `t = t` for a matched application or for the value a
comparison compares, so nothing is evaluated: an application's rebuilt proof states
`y = instance` for its root `y`, and a comparison's the equation of its two sides.
-/

namespace Egglog.Resugar

open SourceProof (Proof)

/-- `cong` over every child in order. -/
def replaceChildren (P : Program) (children : List Proof) (parent : Proof) : Option Proof :=
  children.zipIdx.foldlM (fun acc child => congr P acc child.2 child.1) parent

mutual

/-- The children's proofs, then the application's own atom, one edge per child and the edge
to its root. Every child's proof runs from the matched child `b_i`: an application child's
proof, which ends at its root `x_i`, is extended along the edge `b_i = x_i` (Edge), and a
value child is proved by that edge itself, as a value side of a comparison is proved by the
comparison's own premise (Value). A reflexive proof is not chained in, which keeps lifted
proofs small; the claim is the same. A bare pattern `e` is the comparison `e = e` with one
shared derivation, whose proof is `trans(sym(π), π)`. -/
@[blueprint "def:lift-query"
  (statement := /--
  \begin{mathpar}
  \ir{Value}{x\in\mathit{Var}\\ \pi:s=\eval{x}}{x\Uparrow\pi:s=\eval{x}}
  \and
  \ir{Edge}{\pi':b=x\\ e\Uparrow\pi:x=\eval{e}}{e\Uparrow\kw{trans}(\pi',\pi):b=\eval{e}}
  \and
  \ir{App}{e_i\Uparrow\pi_i:b_i=\eval{e_i}\ (\forall i)\\
    \pi_0:f(b_1,\ldots,b_n)=f(b_1,\ldots,b_n)\\ \pi_r:f(b_1,\ldots,b_n)=y}
    {f(e_1,\ldots,e_n)\Uparrow\kw{trans}(\kw{sym}(\pi_r),\kw{cong}_n(\cdots\kw{cong}_1(\pi_0,\pi_1)\cdots,\pi_n))
      :y=\eval{f(e_1,\ldots,e_n)}}
  \and
  \ir{Compare}{e_1\Uparrow\pi_1:x=\eval{e_1}\\e_2\Uparrow\pi_2:x=\eval{e_2}}
    {(e_1=e_2)\Uparrow\kw{trans}(\kw{sym}(\pi_1),\pi_2):\eval{e_1}=\eval{e_2}}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def queryExpr (P : Program) : Expr → List Proof → Option (Proof × List Proof)
  | .app f args, remaining => do
    let (ids, rest) ← queryArgs P args remaining
    let node :: rest := rest | none
    let .app g bs := node.claim.rhs | none
    if g != f || bs.length != args.length || node.claim.lhs != node.claim.rhs then none else
    let edges := rest.take args.length
    if edges.length != args.length then none else
    let children ← (edges.zip ids).mapM fun ei =>
      match ei.2 with
      | some p => if p.claim.lhs == p.claim.rhs then some ei.1 else trans P ei.1 p
      | none => some ei.1
    let built ← replaceChildren P children node
    let root :: rest := rest.drop args.length | none
    if root.claim.lhs == root.claim.rhs then some (built, rest) else
    let rev ← symm P root
    let result ← trans P rev built
    some (result, rest)
  | _, _ => none

/-- The children left to right: an application's proof, or nothing for a value. -/
def queryArgs (P : Program) : List Expr → List Proof → Option (List (Option Proof) × List Proof)
  | [], remaining => some ([], remaining)
  | e :: es, remaining => do
    let (p, next) ← match e with
      | .app _ _ => do
        let (p, next) ← queryExpr P e remaining
        some (some p, next)
      | _ => some (none, remaining)
    let (ps, last) ← queryArgs P es next
    some (p :: ps, last)

end

/-- A comparison's side: an application's proof, or nothing for a value. -/
def querySide (P : Program) (e : Expr) (remaining : List Proof) :
    Option (Option Proof × List Proof) :=
  match e with
  | .app _ _ => do
    let (p, next) ← queryExpr P e remaining
    some (some p, next)
  | _ => some (none, remaining)

def queryPattern (P : Program) (p : Pattern) (remaining : List Proof) :
    Option (Proof × List Proof) := do
  match p with
  | .expr e =>
    -- A bare pattern is `e = e`: the instance's reflexivity, from `root = instance`.
    let (p, rest) ← queryExpr P e remaining
    if p.claim.lhs == p.claim.rhs then some (p, rest) else do
    let rev ← symm P p
    let result ← trans P rev p
    some (result, rest)
  | .eq lhs rhs =>
    let (a, next) ← querySide P lhs remaining
    let (z, next) ← querySide P rhs next
    let equality :: rest := next | none
    let a := a.getD equality
    let z := z.getD equality
    if a.claim.lhs != z.claim.lhs then none else
    if a.claim.lhs == a.claim.rhs then some (z, rest) else
    let rev ← symm P a
    let result ← trans P rev z
    some (result, rest)
  -- Source queries carry no disequality; the fragment excludes it.
  | .ne _ _ => none

def queryPatterns (P : Program) : Query → List Proof → Option (List Proof × List Proof)
  | [], remaining => some ([], remaining)
  | p :: ps, remaining => do
    let (a, next) ← queryPattern P p remaining
    let (as, last) ← queryPatterns P ps next
    some (a :: as, last)

/-- One source premise proof per original query conjunct, consuming every lifted premise. -/
def query (P : Program) (q : Query) (premises : List Proof) : Option (List Proof) := do
  let (ps, remaining) ← queryPatterns P q premises
  if remaining.isEmpty then some ps else none

end Egglog.Resugar
