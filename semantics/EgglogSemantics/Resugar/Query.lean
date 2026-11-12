import EgglogSemantics.Resugar.Builder

/-!
# Source premises from compiled premises

Reconstruct source premise proofs from lifted compiled premises, supplied in the order of
`Congruence.encodeQueryExpr`. An edge premise states `b = x`; an application premise states
`t = t`. An application's reconstructed proof states `root = instance`, and a comparison's
proof states the equation between its two instances.
-/

namespace Egglog.Resugar

open SourceProof (Proof)

/-- `cong` over every child in order. -/
def replaceChildren (P : Program) (children : List Proof) (parent : Proof) : Option Proof :=
  children.zipIdx.foldlM (fun acc child => congr P acc child.2 child.1) parent

mutual

/-- Consume an application's premise proofs in compiler order: its children's proofs,
its application atom, one edge per child, then its root edge. Return a proof of
`root = instance` and the unused premises, or `none` for a non-application or invalid
premises. A bare pattern `e` uses this derivation to prove the instance's reflexivity. -/
@[blueprint "def:lift-query"
  (statement := /--
  \begin{mathpar}
  \ir{Value}{x\in\mathit{Var}\\ \pi:s=\eval{x}}{x\Uparrow\pi:s=\eval{x}}
  \and
  \ir{Edge}{\pi':b=x\\ e\Uparrow\pi:x=\eval{e}}{e\Uparrow\kw{trans}(\pi',\pi):b=\eval{e}}
  \and
  \ir{Compare}{e_1\Uparrow\pi_1:x=\eval{e_1}\\e_2\Uparrow\pi_2:x=\eval{e_2}}
    {(e_1=e_2)\Uparrow\kw{trans}(\kw{sym}(\pi_1),\pi_2):\eval{e_1}=\eval{e_2}}
  \and
  \ir{App}{e_i\Uparrow\pi_i:b_i=\eval{e_i}\ (\forall i)\\
    \pi_0:f(b_1,\ldots,b_n)=f(b_1,\ldots,b_n)\\ \pi_r:f(b_1,\ldots,b_n)=y}
    {f(e_1,\ldots,e_n)\Uparrow\kw{trans}(\kw{sym}(\pi_r),\kw{cong}_n(\cdots\kw{cong}_1(\pi_0,\pi_1)\cdots,\pi_n))
      :y=\eval{f(e_1,\ldots,e_n)}}
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
  -- A lifted source query carries no disequality: the checker's fragment excludes it.
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
