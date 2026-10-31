import EgglogSemantics.Resugar.Builder

namespace Egglog.Resugar

open SourceProof (Proof)

def replaceChildren (P : Program) (children : List Proof) (parent : Proof) : Option Proof :=
  children.zipIdx.foldlM (fun acc child => congr P acc child.2 child.1) parent

/-- `id = instance` from `node = instance` and the node's root edge `node = id`. -/
def idForm (P : Program) (node root : Proof) : Option Proof := do
  if root.claim.lhs != node.claim.lhs then none else
  let rev ← symm P root
  trans P rev node

/-- An expression's proof in id form. An application's `node = instance` is turned around
through its root edge, the next premise; a value is already its id. -/
def rootStep (P : Program) (e : Expr) (p : Proof) (next : List Proof) :
    Option (Proof × List Proof) :=
  match e with
  | .app _ _ => do
    let root :: rest := next | none
    let q ← idForm P p root
    some (q, rest)
  | _ => some (p, next)

mutual

/-- The compiler's left-to-right postorder, repeated on the original expression: the
children, each followed by its root edge when it is an application, then the application's
own atom and one union-find edge per child. The result's claim is `node = instance`, where
`node` is the application the target matched and `instance` the source instance under `σ`;
a value is its own witness. The unconsumed premise proofs are threaded through in that
order. -/
def queryExpr (P : Program) (σ : Env) (allPremises : List Proof) :
    Expr → List Proof → Option (Proof × List Proof)
  | .app f args, remaining => do
    let (ids, rest) ← queryArgs P σ allPremises args remaining
    let node :: rest := rest | none
    let .app g bs := node.claim.rhs | none
    if g != f || bs.length != args.length || node.claim.lhs != node.claim.rhs then none else
    let edges := rest.take args.length
    if edges.length != args.length then none else
    let children ← (edges.zip ids).mapM fun ei =>
      if ei.2.claim.lhs == ei.2.claim.rhs then some ei.1 else trans P ei.1 ei.2
    let result ← replaceChildren P children node
    some (result, rest.drop args.length)
  | e, remaining => do
    let t ← e.eval σ
    let p ← witness P t allPremises
    some (p, remaining)

/-- The children in id form, left to right. -/
def queryArgs (P : Program) (σ : Env) (allPremises : List Proof) :
    List Expr → List Proof → Option (List Proof × List Proof)
  | [], remaining => some ([], remaining)
  | e :: es, remaining => do
    let (p, next) ← queryExpr P σ allPremises e remaining
    let (p', next') ← rootStep P e p next
    let (ps, last) ← queryArgs P σ allPremises es next'
    some (p' :: ps, last)

end

/-- An equation side: its proof in id form. -/
def queryId (P : Program) (σ : Env) (allPremises : List Proof) (e : Expr)
    (remaining : List Proof) : Option (Proof × List Proof) := do
  let (p, next) ← queryExpr P σ allPremises e remaining
  rootStep P e p next

def queryPattern (P : Program) (σ : Env) (allPremises : List Proof)
    (p : Pattern) (remaining : List Proof) : Option (Proof × List Proof) := do
  match p with
  | .expr e => queryExpr P σ allPremises e remaining
  | .eq lhs rhs =>
    let (a, next) ← queryId P σ allPremises lhs remaining
    let (z, last) ← queryId P σ allPremises rhs next
    let equality :: rest := last | none
    if equality.claim != (⟨a.claim.lhs, z.claim.lhs⟩ : SourceProof.Claim) then none else do
      let rev ← symm P a
      let left ← trans P rev equality
      let result ← trans P left z
      some (result, rest)
  -- Source queries carry no disequality; the fragment excludes it.
  | .ne _ _ => none

def queryPatterns (P : Program) (σ : Env) (allPremises : List Proof) :
    Query → List Proof → Option (List Proof × List Proof)
  | [], remaining => some ([], remaining)
  | p :: ps, remaining => do
    let (a, next) ← queryPattern P σ allPremises p remaining
    let (as, last) ← queryPatterns P σ allPremises ps next
    some (a :: as, last)

/-- One source premise proof per original query conjunct, consuming every lifted premise. -/
def query (P : Program) (σ : Env) (q : Query) (premises : List Proof) :
    Option (List Proof) := do
  let (ps, remaining) ← queryPatterns P σ premises q premises
  if remaining.isEmpty then some ps else none

end Egglog.Resugar
