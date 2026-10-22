import EgglogSemantics.Resugar.Builder

namespace Egglog.Resugar

open SourceProof (Proof)

def replaceChildren (P : Program) (children : List Proof) (parent : Proof) : Option Proof :=
  children.zipIdx.foldlM (fun acc child => congr P acc child.2 child.1) parent

mutual

/-- The compiler's left-to-right postorder, repeated on the original expression. The
unconsumed premise proofs are threaded through in that order. -/
def queryExpr (P : Program) (σ : Env) (allPremises : List Proof) :
    Expr → List Proof → Option (Proof × List Proof)
  | .app f args, remaining => do
    let (children, rest) ← queryArgs P σ allPremises args remaining
    let parent :: rest := rest | none
    if parent.claim.rhs != .app f (children.map (·.claim.lhs)) then none else do
      let result ← replaceChildren P children parent
      some (result, rest)
  | e, remaining => do
    let t ← e.eval σ
    let p ← witness P t allPremises
    some (p, remaining)

def queryArgs (P : Program) (σ : Env) (allPremises : List Proof) :
    List Expr → List Proof → Option (List Proof × List Proof)
  | [], remaining => some ([], remaining)
  | e :: es, remaining => do
    let (p, next) ← queryExpr P σ allPremises e remaining
    let (ps, last) ← queryArgs P σ allPremises es next
    some (p :: ps, last)

end

def queryPattern (P : Program) (σ : Env) (allPremises : List Proof)
    (p : Pattern) (remaining : List Proof) : Option (Proof × List Proof) := do
  match p with
  | .expr e => queryExpr P σ allPremises e remaining
  | .eq lhs rhs =>
    let (a, next) ← queryExpr P σ allPremises lhs remaining
    let (z, last) ← queryExpr P σ allPremises rhs next
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
