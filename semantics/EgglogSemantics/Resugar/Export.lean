import EgglogSemantics.Resugar.Fixtures
import EgglogSemantics.Tests.Egg
import Lean.Data.Json

/-! Source proofs as JSON, for checking the same proof with Rust egglog. A case carries its
program as `.egg` source, with every rule named `lean-rule-<index>` after its position in
`Program.rules`,
and one object per proof with the Lean verdict. A proof tree is written as its nodes in
postorder, sharing repeated subtrees, so every reference is to an earlier node. -/

namespace Egglog.Resugar.Export

open Lean (Json toJson)

mutual

/-- `["F", [args…]]` for an application; a literal is a tagged object. -/
def term : Term → Json
  | .lit (.int n) => Json.mkObj [("int", toJson n)]
  | .app f args => .arr #[toJson f, .arr (terms args).toArray]

def terms : List Term → List Json
  | [] => []
  | t :: ts => term t :: terms ts

end

def ruleName (i : Nat) : String := "lean-rule-" ++ toString i

structure Flat where
  nodes : Array Json := #[]
  shared : List (SourceProof.Proof × Nat) := []

/-- The node's index, reusing an identical subtree already written. -/
def emit (pf : SourceProof.Proof) (reason : Json) : StateM Flat Nat := do
  let s ← get
  match s.shared.find? (fun kv => kv.1 == pf) with
  | some kv => pure kv.2
  | none =>
    let i := s.nodes.size
    let n := Json.mkObj
      [("lhs", term pf.claim.lhs), ("rhs", term pf.claim.rhs), ("reason", reason)]
    set (⟨s.nodes.push n, (pf, i) :: s.shared⟩ : Flat)
    pure i

mutual

def flatten : SourceProof.Proof → StateM Flat Nat
  | p@(.symm _ q) => do
    let i ← flatten q
    emit p (Json.mkObj [("kind", "symm"), ("proof", toJson i)])
  | p@(.trans _ q r) => do
    let i ← flatten q
    let j ← flatten r
    emit p (Json.mkObj [("kind", "trans"), ("left", toJson i), ("right", toJson j)])
  | p@(.congr _ q k r) => do
    let i ← flatten q
    let j ← flatten r
    emit p (Json.mkObj [("kind", "congr"), ("base", toJson i), ("index", toJson k),
      ("child", toJson j)])
  | p@(.rule _ i σ qs) => do
    let is ← flattenAll qs
    emit p (Json.mkObj [("kind", "rule"), ("rule", ruleName i),
      ("subst", .arr (σ.map fun bnd => .arr #[toJson bnd.1, term bnd.2]).toArray),
      ("premises", toJson is)])

def flattenAll : List SourceProof.Proof → StateM Flat (List Nat)
  | [] => pure []
  | q :: qs => do
    let i ← flatten q
    let is ← flattenAll qs
    pure (i :: is)

end

def certificate (P : Program) (pf : SourceProof.Proof) : Json :=
  let (root, flat) := (flatten pf).run {}
  Json.mkObj [("nodes", .arr flat.nodes), ("root", toJson root),
    ("accepted", toJson (SourceProof.check P pf).isSome)]

/-- The program as `.egg` source with rules named by their position in `Program.rules`. -/
def program (P : Program) : Option String := do
  if !SourceProof.sourceOk P then none else
    some (P.renderWith fun k => some (ruleName k))

def caseJson (name : String) (P : Program) (cs : List SourceProof.Proof) :
    Option Json := do
  let source ← program P
  some (Json.mkObj [("case", name), ("program", source),
    ("certificates", .arr (cs.map (certificate P)).toArray)])

/-- The curated fixtures, which both checkers must judge alike. -/
def fixtures (_ : Unit) : Option (List Json) := do
  let fs ← Fixtures.all ()
  fs.mapM fun f => caseJson f.name f.program f.certificates

end Egglog.Resugar.Export
