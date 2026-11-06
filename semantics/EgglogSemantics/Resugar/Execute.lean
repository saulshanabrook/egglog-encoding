import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Impl.Interp

namespace Egglog.Resugar

open SourceProof (Proof)

/-- Run the instrumented compilation of `P` with `exec` and lift a proof of every row. -/
def certificates (exec : Program → Option FDatabase) (P : Program) :
    Option (List Proof) := do
  let annotated ← Provenance.encode (Congruence.encode P)
  let d ← exec annotated
  sourceProofs P d.terms

/-- A function name not used by the program: `base`, or `base` with the least number
appended that makes it new. -/
def freshName (P : Program) (base : String) : FnName :=
  ((List.range (P.names.length + 1)).map fun n => if n = 0 then base else base ++ toString n)
    |>.find? (fun s => !P.names.contains s) |>.getD base

/-- Prove the final check as egglog's `prove` does: a rule with the check as its query and
a fresh nullary goal as its head runs after the schedule, the goal's row gets its proof like
any other row, and the proofs of the check's conjuncts are the premises of that rule node,
each a proof about the original program. -/
def prove (exec : Program → Option FDatabase) (P : Program) : Option (List Proof) := do
  let goal : Term := .app (freshName P "prove") []
  let rule : Rule := ⟨P.check, [.expr goal.toExpr]⟩
  let certs ← certificates exec { schedule := .seq P.schedule (.run [rule]), check := P.check }
  let root ← certs.find? (·.claim == (⟨goal, goal⟩ : SourceProof.Claim))
  let .rule _ _ _ premises := root | none
  if premises.all (fun p => SourceProof.check P p == some p.claim) then some premises else none

end Egglog.Resugar
