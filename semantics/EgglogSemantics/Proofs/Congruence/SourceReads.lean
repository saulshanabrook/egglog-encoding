import EgglogSemantics.Proofs.Out
import EgglogSemantics.Proofs.Congruence.Correspond

/-! Monotone representation of source facts in mathematical target databases. -/

namespace Egglog.Congruence

mutual

/-- Readings persist when assertions grow at a fixed signature. -/
theorem ViewRepr.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig) :
    ∀ {a i : Term}, ViewRepr d₁ a i → ViewRepr d₂ a i
  | _, _, .lit => .lit
  | _, _, .app hs ho => .app (ViewReprList.mono h hsig hs) (ho.mono h hsig)

@[inherit_doc ViewRepr.mono]
theorem ViewReprList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig) :
    ∀ {as is : List Term}, ViewReprList d₁ as is → ViewReprList d₂ as is
  | _, _, .nil => .nil
  | _, _, .cons ha hs => .cons (ViewRepr.mono h hsig ha) (ViewReprList.mono h hsig hs)

end

/-- Head variables need a reading, which need not already be a canonical UF root. -/
def Env.Reads (d : Database) (σ ρ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t →
    ∃ i, Env.lookup v ρ = some i ∧ ViewRepr d t i

theorem Env.Reads.mono {d d' : Database} {σ ρ : Env} (h : Env.Reads d σ ρ)
    (hc : d.Contained d') (hsig : d.sig = d'.sig) : Env.Reads d' σ ρ := by
  intro v t ht
  obtain ⟨i, hi, hr⟩ := h v t ht
  exact ⟨i, hi, hr.mono hc hsig⟩

/-- Readings in a fixed snapshot. Persistence across merges uses `Live.Reads`. -/
structure SourceReads (d src : Database) : Prop where
  terms : ∀ t ∈ src.terms, ∃ i, ViewRepr d t i
  unions : UnionsJoined d src

theorem SourceReads.mono {d d' src : Database} (h : SourceReads d src)
    (hc : d.Contained d') (hsig : d.sig = d'.sig) : SourceReads d' src := by
  refine ⟨fun t ht => (h.terms t ht).imp fun _ hr => hr.mono hc hsig, ?_⟩
  intro a b hab hne
  obtain ⟨i, j, hi, hj, ho⟩ := h.unions a b hab hne
  exact ⟨i, j, hi.mono hc hsig, hj.mono hc hsig,
    ho.imp (Database.Out.mono hc hsig) (Database.Out.mono hc hsig)⟩

/-- A smaller source state only asks for a subset of the already represented facts. -/
theorem SourceReads.restrict {d src src' : Database} (h : SourceReads d src)
    (hc : src'.Contained src) : SourceReads d src' :=
  ⟨fun t ht => h.terms t (hc.terms ht), fun a b hab => h.unions a b (hc.eqs hab)⟩

theorem SourceReads.addTerm {d src : Database} (h : SourceReads d src) {t i : Term}
    (ht : ViewRepr d t i) : SourceReads d (src.addTerm t) := by
  refine ⟨?_, fun a b hab hne => ?_⟩
  · intro s hs
    rcases Database.addTerm_terms ▸ hs with hs | hs
    · exact h.terms s hs
    · exact ht.subterms s hs
  · rcases Database.addTerm_eqs ▸ hab with hab | ⟨s, _, heq⟩
    · exact h.unions a b hab hne
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact (hne rfl).elim

theorem SourceReads.addEq {d src : Database} (h : SourceReads d src) {a b i j : Term}
    (ha : ViewRepr d a i) (hb : ViewRepr d b j)
    (ho : d.Out ufName [i] [j] ∨ d.Out ufName [j] [i]) : SourceReads d (src.addEq a b) := by
  have hterms := (h.addTerm ha).addTerm hb
  refine ⟨?_, fun x y hxy hne => ?_⟩
  · intro t ht
    apply hterms.terms t
    simpa only [Database.addTerm_terms] using Database.addEq_terms ▸ ht
  · rcases Database.addEq_eqs ▸ hxy with heq | hxy
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨i, j, ha, hb, ho⟩
    · exact hterms.unions x y hxy hne

/-- Source facts from all firings can be read in one common target state. -/
theorem SourceReads.sUnion {d src : Database} {S : Set Database} (h : SourceReads d src)
    (hs : ∀ s ∈ S, SourceReads d s) : SourceReads d (src.sUnion S) := by
  refine ⟨fun t ht => ?_, fun a b hab hne => ?_⟩
  · rcases Database.sUnion_terms ▸ ht with ht | ht
    · exact h.terms t ht
    · obtain ⟨s, hs', ht⟩ := Set.mem_iUnion₂.mp ht
      exact (hs s hs').terms t ht
  · rcases Database.sUnion_eqs ▸ hab with hab | hab
    · exact h.unions a b hab hne
    · obtain ⟨s, hs', hab⟩ := Set.mem_iUnion₂.mp hab
      exact (hs s hs').unions a b hab hne

/-- One source round is represented when all of its rule results are represented. -/
theorem SourceReads.runRules {d src : Database} {R : RulesetName} (h : SourceReads d src)
    (hf : ∀ r ∈ src.rules, r.ruleset = R → ∀ post ∈ RuleResults src r, SourceReads d post) :
    SourceReads d (RunRules R src) := by
  apply h.sUnion
  rintro post ⟨r, hr, hR, hp⟩
  exact hf r hr hR post hp

end Egglog.Congruence
