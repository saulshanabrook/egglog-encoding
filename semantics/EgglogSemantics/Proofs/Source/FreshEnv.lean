import EgglogSemantics.Proofs.Source.FreshBindings
import EgglogSemantics.Impl.Interp

/-! Specialize fresh mathematical bindings to the executable matcher's value universe. -/

namespace Egglog

abbrev FreshEnv (d : FDatabase) := FreshBindings {t | t ∈ d.terms}

namespace FreshEnv

abbrev nil {d : FDatabase} {n m : Nat} : FreshEnv d n m [] := FreshBindings.nil

abbrev mono {d : FDatabase} {n m n' m' : Nat} {σ : Env} (h : FreshEnv d n m σ)
    (hn : n' ≤ n) (hm : m ≤ m') : FreshEnv d n' m' σ := FreshBindings.mono h hn hm

abbrev append {d : FDatabase} {n m k : Nat} {σ₁ σ₂ : Env}
    (h₁ : FreshEnv d n m σ₁) (h₂ : FreshEnv d m k σ₂) (hnm : n ≤ m) (hmk : m ≤ k) :
    FreshEnv d n k (σ₁ ++ σ₂) := FreshBindings.append h₁ h₂ hnm hmk

end FreshEnv
end Egglog
