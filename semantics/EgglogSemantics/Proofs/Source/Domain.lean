import EgglogSemantics.Source.Domain
import EgglogSemantics.Proofs.Step
import Mathlib.Data.List.Dedup

/-! Facts about the source fragment's definitions. -/

namespace Egglog

@[inherit_doc Pattern.GroundedAt]
theorem Pattern.Grounded.groundedAt {src : Database} :
    ∀ {p : Pattern}, p.Grounded → p.GroundedAt src
  | .expr _, h => fun l he => absurd he (h l)
  | .eq _ _, h | .ne _ _, h => h.imp (fun h₁ l he => absurd he (h₁ l)) (fun h₂ l he => absurd he (h₂ l))

theorem Action.unionFreeB_iff (a : Action) : a.unionFreeB = true ↔ a.UnionFree := by
  cases a <;> simp [Action.unionFreeB, Action.UnionFree]

theorem Actions.unionFreeB_iff : ∀ as : List Action,
    as.all Action.unionFreeB = true ↔ Actions.UnionFree as
  | [] => by simp
  | a :: as => by
      simp only [List.all_cons, Bool.and_eq_true, Actions.UnionFree, Action.unionFreeB_iff,
        Actions.unionFreeB_iff as]

@[inherit_doc Schedule.ruleUnionFreeB]
theorem Schedule.ruleUnionFreeB_iff (c : Schedule) :
    c.ruleUnionFreeB = true ↔ c.UnionFree := by
  simp only [Schedule.ruleUnionFreeB, List.all_eq_true, Schedule.UnionFree]
  exact forall₂_congr (fun r _ => Actions.unionFreeB_iff r.actions)

/-- Monotone source rules remove no rows. -/
theorem Rule.subsumeFree_of_monotone {r : Rule} (h : r.monotoneB = true) : r.SubsumeFree :=
  Actions.subsumeFree_of_all (Bool.and_eq_true_iff.mp h).2

theorem Schedule.subsumeFree_of_monotone {c : Schedule} (h : c.monotoneB = true) :
    ∀ r ∈ c.rules, r.SubsumeFree :=
  fun r hr => Rule.subsumeFree_of_monotone (List.all_eq_true.mp h r hr)

end Egglog
