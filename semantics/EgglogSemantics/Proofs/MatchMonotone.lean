import EgglogSemantics.Proofs.SourceMeaning

/-! Positive patterns persist under growth. A fixed substitution remains valid only
when its bindings remain representatives. -/

namespace Egglog

theorem congOn_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {ts : List Term} {a b : Term}
    (hc : StoredCongOn d₁ ts a b) : StoredCongOn d₂ ts a b :=
  StoredCong.mono (h.addTerms_mono ts) hc

theorem Matches.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hl : d₁.live ⊆ d₂.live)
    {p : Pattern} {σ : Env} (hp : p.monotoneB = true) (h : Matches d₁ p σ) :
    Matches d₂ p σ := by
  cases h with
  | atom hr =>
    obtain ⟨t, he⟩ := hr.eval_exists
    exact .atom (Lookup.mono_live hl ⟨he, hr⟩).2
  | equal hr₁ hr₂ he₁ he₂ hh =>
    exact .equal (Lookup.mono_live hl ⟨he₁, hr₁⟩).2 (Lookup.mono_live hl ⟨he₂, hr₂⟩).2
      he₁ he₂ (hh.mono hc)
  | unequal _ _ _ _ _ => simp [Pattern.monotoneB] at hp

theorem ValidEnv.mono {d₁ d₂ : Database} (h : d₁.reps ⊆ d₂.reps)
    {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => h (hv.mem_reps b hb)⟩

/-- Positive substitutions persist under assertion inclusion when their representatives persist. -/
theorem ValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hl : d₁.live ⊆ d₂.live)
    (hr : d₁.reps ⊆ d₂.reps)
    {p : Pattern} {σ : Env}
    (hp : p.monotoneB = true) (h : ValidSubst d₁ p σ) :
    ValidSubst d₂ p σ := by
  refine ⟨h.1.mono hr, ?_⟩
  exact h.2.mono hc hl hp

theorem ValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hl : d₁.live ⊆ d₂.live)
    (hr : d₁.reps ⊆ d₂.reps)
    {q : Query} {σ : Env}
    (hq : ∀ p ∈ q, p.monotoneB = true) (h : ValidQuerySubst d₁ q σ) : ValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  refine ⟨σs, ?_, hu⟩
  clear hu
  induction hall with
  | nil => exact .nil
  | @cons p σ ps σs hp hs ih =>
    exact .cons (hp.mono hc hl hr (hq p (by simp)))
      (ih (fun p hp => hq p (List.mem_cons_of_mem _ hp)))

open SourceMeaning InferredFacts

/-- Growth may change a representative, so transport chooses congruent bindings. -/
theorem ValidEnv.transport {d e : Database} (hc : d.Contained e) (he : e.WF)
    (hr : e.HasReps) {vars : List Var} {σ : Env} (hv : ValidEnv vars d σ) :
    ∃ τ, ValidEnv vars e τ ∧ EnvRelated e σ τ := by
  let w := representative e he
  have hw : ∀ t ∈ d.terms, w t ∈ e.reps ∧ e.Infers t (w t) :=
    fun t ht => representative_spec he hr (infers_of_held (hc.terms ht))
  refine ⟨Env.mapVals w σ, ⟨?_, ?_⟩,
    envRelated_map hv.mem_terms (fun t ht => (hw t ht).2)⟩
  · simpa [dom_mapVals] using hv.1
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
    exact (hw a.2 (hv.mem_terms a ha)).1

theorem Matches.transport {d e : Database} (hc : d.Contained e) (hl : d.live ⊆ e.live) (he : e.WF)
    {p : Pattern} {σ τ : Env} (hr : EnvRelated e σ τ)
    (hn : p.OrderingFree) (hp : p.monotoneB = true) (hm : Matches d p σ) :
    Matches e p τ :=
  matches_transport he he (.refl _) hr hn (hm.mono hc hl hp)

theorem ValidSubst.transport {d e : Database} (hc : d.Contained e) (hl : d.live ⊆ e.live) (he : e.WF)
    (hr : e.HasReps) {p : Pattern} {σ : Env}
    (hn : p.OrderingFree) (hp : p.monotoneB = true) (hm : ValidSubst d p σ) :
    ∃ τ, ValidSubst e p τ ∧ EnvRelated e σ τ := by
  obtain ⟨τ, hτ, hrel⟩ := hm.1.transport hc he hr
  exact ⟨τ, ⟨hτ, hm.2.transport hc hl he hrel hn hp⟩, hrel⟩

theorem QueryMatches.transport {d e : Database} (hc : d.Contained e) (hl : d.live ⊆ e.live) (he : e.WF)
    (hr : e.HasReps) {q : Query} {σ : Env}
    (hn : ∀ p ∈ q, p.OrderingFree) (hp : ∀ p ∈ q, p.monotoneB = true)
    (hm : QueryMatches d q σ) :
    ∃ τ, QueryMatches e q τ ∧ EnvRelated e σ τ := by
  obtain ⟨τ, hτ, hrel⟩ := hm.1.transport hc he hr
  exact ⟨τ, ⟨hτ, fun p h => (hm.2 p h).transport hc hl he hrel (hn p h) (hp p h)⟩, hrel⟩

theorem ValidQuerySubst.transport {d e : Database} (hc : d.Contained e) (hl : d.live ⊆ e.live) (he : e.WF)
    (hr : e.HasReps) {q : Query} {σ : Env}
    (hn : ∀ p ∈ q, p.OrderingFree) (hp : ∀ p ∈ q, p.monotoneB = true)
    (hm : ValidQuerySubst d q σ) :
    ∃ τ, ValidQuerySubst e q τ ∧ EnvRelated e σ τ := by
  obtain ⟨ρ, hρ, hag⟩ := hm.exists_queryMatches
  obtain ⟨τ, hτ, hrel⟩ := hρ.transport hc hl he hr hn hp
  obtain ⟨υ, hυ, hag'⟩ := hτ.exists_validQuerySubst
  refine ⟨υ, hυ, fun v t ht => ?_⟩
  obtain ⟨u, hu, hi⟩ := hrel v t ((hag v).trans ht)
  exact ⟨u, (hag' v).trans hu, hi⟩

theorem QueryHolds.mono {d e : Database} (hc : d.Contained e) (hl : d.live ⊆ e.live) (he : e.WF)
    (hr : e.HasReps) {q : Query}
    (hn : ∀ p ∈ q, p.OrderingFree) (hp : ∀ p ∈ q, p.monotoneB = true)
    (hm : QueryHolds d q) : QueryHolds e q := by
  obtain ⟨σ, hσ⟩ := hm
  obtain ⟨τ, hτ, _⟩ := hσ.transport hc hl he hr hn hp
  exact ⟨τ, hτ⟩

end Egglog
