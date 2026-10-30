import EgglogSemantics.Proofs.Congruence.ActionExprs
import EgglogSemantics.Proofs.Source.Execution

/-! Extract expression-level premises from source rule-head conditions. -/

namespace Egglog.Congruence

theorem builds_exprs {sig : Signature} {as : List Action}
    (h : Actions.Builds as sig) : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.Evaluable sig := by
  induction as with
  | nil => simp
  | cons a as ih =>
      intro b hb e he
      rcases List.mem_cons.mp hb with rfl | hb
      · cases b with
        | expr x => obtain rfl := List.mem_singleton.mp he; exact h.1
        | union x y =>
            rcases List.mem_cons.mp he with rfl | he
            · exact h.1.1
            · obtain rfl := List.mem_singleton.mp he; exact h.1.2
      · exact ih h.2 b hb e he

theorem scoped_exprs {Γ : Scope} {as : List Action}
    (h : Actions.Scoped as Γ) : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ v ∈ e.vars, v ∈ Γ := by
  induction as with
  | nil => simp
  | cons a as ih =>
      intro b hb e he
      rcases List.mem_cons.mp hb with rfl | hb
      · cases b with
        | expr x => obtain rfl := List.mem_singleton.mp he; exact h.1.2
        | union x y =>
            rcases List.mem_cons.mp he with rfl | he
            · exact h.1.1
            · obtain rfl := List.mem_singleton.mp he; exact h.1.2
      · exact ih h.2 b hb e he

end Egglog.Congruence
