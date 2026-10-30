import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Congruence.Encode

namespace Egglog.Resugar

open SourceProof (Claim)

/-- A view relates its id to its constructor application; UF records an equality; a source
value is itself. -/
def factClaim (P : Program) (t : Term) : Option Claim := do
  let .app f cols := t | some ⟨t, t⟩
  match Congruence.tableRole P f with
  | some .unionFind =>
    let [a, b] := cols | none
    some ⟨a, b⟩
  | some (.view ctor) => do
    let fk ← P.ctors.find? fun fk => fk.1 == ctor
    if cols.length != fk.2 + 1 then none else do
      let id ← cols[fk.2]?
      some ⟨id, .app ctor (cols.take fk.2)⟩
  | none => some ⟨t, t⟩

end Egglog.Resugar
