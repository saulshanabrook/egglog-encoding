import EgglogSemantics.Spec.Step

/-! Divergence, used by the Lean statement of compiler correctness. The paper states
nontermination in prose instead. A round is an atomic `RunRules` step. -/

namespace Egglog

/-- Passes of `S` that each change the meaning of the state, forever. -/
def InfinitePasses (S : Schedule) (d : Database) : Prop :=
  ∃ trace : Nat → Database, trace 0 = d ∧
    ∀ n, Reach (trace n) S (trace (n + 1)) ∧ ¬ (trace n).SameMeaning (trace (n + 1))

/-- A schedule diverges when a saturation inside it never settles: its body diverges in
some pass, or every pass changes the meaning of the state. A run never diverges. -/
inductive Diverges : Database → Schedule → Prop where
  | seqLeft {d : Database} {S₁ S₂ : Schedule} : Diverges d S₁ → Diverges d (.seq S₁ S₂)
  | seqRight {d d' : Database} {S₁ S₂ : Schedule} :
      Reach d S₁ d' → Diverges d' S₂ → Diverges d (.seq S₁ S₂)
  | body {d : Database} {S : Schedule} : Diverges d S → Diverges d (.saturate S)
  | later {d d₁ : Database} {S : Schedule} :
      Reach d S d₁ → ¬ d.SameMeaning d₁ → Diverges d₁ (.saturate S) → Diverges d (.saturate S)
  | forever {d : Database} {S : Schedule} : InfinitePasses S d → Diverges d (.saturate S)

end Egglog
