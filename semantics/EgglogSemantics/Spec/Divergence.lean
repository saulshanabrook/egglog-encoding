import EgglogSemantics.Spec.Step

/-! Divergence, used by the Lean statement of compiler correctness. The paper states
nontermination in prose instead. Rule firing remains an atomic `RunRules` step. -/

namespace Egglog

def InfiniteTrace (rel : Database → Database → Prop) (d : Database) : Prop :=
  ∃ trace : Nat → Database, trace 0 = d ∧ ∀ n, rel (trace n) (trace (n + 1))

/-- A run that changes congruence, so saturation continues past it. -/
def ChangingRun (rs : List Rule) (d e : Database) : Prop :=
  e = RunRules rs d ∧ Cong d ≠ Cong e

/-- Saturation diverges when every round changes congruence. -/
def SaturateDiverges (rs : List Rule) (d : Database) : Prop :=
  InfiniteTrace (ChangingRun rs) d

/-- Only saturations can diverge. -/
inductive CmdDiverges (d : Database) : Cmd → Prop where
  | saturate {rs : List Rule} : SaturateDiverges rs d → CmdDiverges d (.saturate rs)

/-- A command list diverges at a command after a successful finite prefix. -/
inductive ProgramDiverges : Database → List Cmd → Prop where
  | head {d : Database} {c : Cmd} {cs : List Cmd} :
      CmdDiverges d c → ProgramDiverges d (c :: cs)
  | tail {d mid : Database} {c : Cmd} {cs : List Cmd} :
      CmdStep d c mid → ProgramDiverges mid cs → ProgramDiverges d (c :: cs)

end Egglog
