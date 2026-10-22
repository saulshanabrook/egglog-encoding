import EgglogSemantics.Proofs.Match

/-! Renaming the values of mathematical query substitutions. -/

namespace Egglog

/-- `σ` with every value rewritten by `w`. Domain and order untouched. -/
def Env.mapVals (w : Term → Term) (σ : Env) : Env := σ.map fun b => (b.1, w b.2)

theorem dom_mapVals (w : Term → Term) : ∀ σ : Env, Env.dom (Env.mapVals w σ) = Env.dom σ
  | [] => rfl
  | b :: σ => by
      show (b.1, w b.2).1 :: (Env.mapVals w σ).map Prod.fst = b.1 :: σ.map Prod.fst
      rw [show (Env.mapVals w σ).map Prod.fst = σ.map Prod.fst from dom_mapVals w σ]

theorem lookup_mapVals (w : Term → Term) (v : Var) : ∀ σ : Env,
    Env.lookup v (Env.mapVals w σ) = (Env.lookup v σ).map w
  | [] => rfl
  | (u, t) :: σ => by
      show (if v = u then some (w t) else Env.lookup v (Env.mapVals w σ)) =
        Option.map w (if v = u then some t else Env.lookup v σ)
      split
      · rfl
      · exact lookup_mapVals w v σ

theorem mem_mapVals {w : Term → Term} {b : Var × Term} : ∀ {σ : Env},
    b ∈ Env.mapVals w σ → ∃ a ∈ σ, b = (a.1, w a.2)
  | [], hb => by simp [Env.mapVals] at hb
  | a :: σ, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨a, List.mem_cons_self .., rfl⟩
      · obtain ⟨c, hc, rfl⟩ := mem_mapVals hb
        exact ⟨c, List.mem_cons_of_mem a hc, rfl⟩

theorem mapVals_append (w : Term → Term) (σ₁ σ₂ : Env) :
    Env.mapVals w (σ₁ ++ σ₂) = Env.mapVals w σ₁ ++ Env.mapVals w σ₂ := List.map_append

end Egglog
