import EgglogSemantics.Source.Domain
import EgglogSemantics.Proofs.Step
import Mathlib.Data.List.Dedup

/-! Facts about the source fragment's definitions. -/

namespace Egglog

/-- Monotone source rules remove no rows. -/
theorem Rule.subsumeFree_of_monotone {r : Rule} (h : r.monotoneB = true) : r.SubsumeFree :=
  Actions.subsumeFree_of_all (Bool.and_eq_true_iff.mp h).2

theorem Schedule.subsumeFree_of_monotone {c : Schedule} (h : c.monotoneB = true) :
    ∀ r ∈ c.rules, r.SubsumeFree :=
  fun r hr => Rule.subsumeFree_of_monotone (List.all_eq_true.mp h r hr)

theorem Rule.subsumeFree_of_subsumeFreeB {r : Rule} (h : r.subsumeFreeB = true) : r.SubsumeFree :=
  Actions.subsumeFree_of_all h

theorem Schedule.subsumeFree_of_subsumeFreeB {S : Schedule} (h : S.subsumeFreeB = true) :
    ∀ r ∈ S.rules, r.SubsumeFree :=
  fun r hr => Rule.subsumeFree_of_subsumeFreeB (List.all_eq_true.mp h r hr)

end Egglog
