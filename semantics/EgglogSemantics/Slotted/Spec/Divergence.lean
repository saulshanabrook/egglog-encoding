import EgglogSemantics.Slotted.Spec.Step

/-!
# Slotted divergence

`Egglog.Diverges` over the slotted round and the slotted fixpoint test, for the divergence
clause of the slotted pass's correctness statement.
-/

namespace Egglog.Slotted

/-- Slotted passes of `S` that each change the slotted meaning of the state, forever. -/
def SInfinitePasses (bind : Binders) (S : Schedule) (d : Database) : Prop :=
  ∃ trace : Nat → Database, trace 0 = d ∧
    ∀ n, SReach bind (trace n) S (trace (n + 1)) ∧
      ¬ SameMeaning' bind (trace n) (trace (n + 1))

/-- A slotted schedule diverges when a saturation inside it never settles. -/
inductive SDiverges (bind : Binders) : Database → Schedule → Prop where
  | seqLeft {d : Database} {S₁ S₂ : Schedule} : SDiverges bind d S₁ → SDiverges bind d (.seq S₁ S₂)
  | seqRight {d d' : Database} {S₁ S₂ : Schedule} :
      SReach bind d S₁ d' → SDiverges bind d' S₂ → SDiverges bind d (.seq S₁ S₂)
  | body {d : Database} {S : Schedule} : SDiverges bind d S → SDiverges bind d (.saturate S)
  | later {d d₁ : Database} {S : Schedule} :
      SReach bind d S d₁ → ¬ SameMeaning' bind d d₁ → SDiverges bind d₁ (.saturate S) →
      SDiverges bind d (.saturate S)
  | forever {d : Database} {S : Schedule} :
      SInfinitePasses bind S d → SDiverges bind d (.saturate S)

end Egglog.Slotted
