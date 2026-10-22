import EgglogSemantics.Proofs.Match

/-! Positive queries preserve their matches when the mathematical state grows. -/

namespace Egglog

theorem congOn_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {ts : List Term} {a b : Term}
    (hc : StoredCongOn d₁ ts a b) : StoredCongOn d₂ ts a b :=
  StoredCong.mono (h.addTerms_mono ts) hc

theorem ValidEnv.mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => h.terms (hv.mem_terms b hb)⟩

/-- Positive patterns persist under assertion inclusion. -/
theorem ValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    {p : Pattern} {σ : Env}
    (hp : p.monotoneB = true) (h : ValidSubst d₁ p σ) :
    ValidSubst d₂ p σ := by
  refine ⟨h.1.mono hc, ?_⟩
  cases h.2 with
  | atom he hc' => exact .atom he (hc'.mono hc)
  | equal he₁ he₂ hc' =>
    exact .equal he₁ he₂ (hc'.mono hc)
  | unequal _ _ _ _ _ => simp [Pattern.monotoneB] at hp

theorem ValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    {q : Query} {σ : Env}
    (hq : ∀ p ∈ q, p.monotoneB = true) (h : ValidQuerySubst d₁ q σ) : ValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  refine ⟨σs, ?_, hu⟩
  clear hu
  induction hall with
  | nil => exact .nil
  | @cons p σ ps σs hp hs ih =>
    exact .cons (hp.mono hc (hq p (by simp)))
      (ih (fun p hp => hq p (List.mem_cons_of_mem _ hp)))

end Egglog
