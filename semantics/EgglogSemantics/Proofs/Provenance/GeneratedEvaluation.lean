import EgglogSemantics.Proofs.Lookup
import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Proofs.SourceProof.Actions

namespace Egglog.Provenance.Generated

theorem actionFacts_sound {db : Database} {σ : Env} {a : Action} {fs : List Term}
    (h : actionFacts σ a = some fs) :
    ∃ d, evalAction σ db a = some d ∧ ∀ t ∈ fs, t ∈ d.terms := by
  cases a with
  | union _ _ => simp [actionFacts] at h
  | expr e =>
      obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      refine ⟨db.addTerm t, by simp [evalAction, ht], ?_⟩
      intro s hs
      exact (db.addTerm t).subtermClosed t (Database.mem_addTerm t db)
        ((Term.mem_subtermList t).mp hs)
  | subsume f es =>
      obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact ⟨(db.addTerm (.app f ts)).addSubsumed {.app f ts},
        by simp [evalAction, hts], by simp⟩

/-- Sequential source heads retain every fact produced by an earlier action. -/
theorem actionsFacts_sound {db : Database} {σ : Env} {as : List Action} {fs : List Term}
    (hdf : Actions.SubsumeFree as) (h : actionsFacts σ as = some fs) :
    ∃ d, evalActions σ db as = some d ∧ ∀ t ∈ fs, t ∈ d.terms := by
  induction as generalizing db fs with
  | nil => cases Option.some.inj h; exact ⟨db, rfl, by simp⟩
  | cons a as ih =>
      obtain ⟨first, hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hr, heq⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj heq
      obtain ⟨d₁, hd₁, hm₁⟩ := actionFacts_sound (db := db) hf
      have htail := (Actions.subsumeFree_cons.mp hdf).2
      obtain ⟨d₂, hd₂, hm₂⟩ := ih (db := d₁) htail hr
      refine ⟨d₂, by simp [evalActions, hd₁, hd₂], ?_⟩
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact (evalActions_contained htail hd₂).terms (hm₁ t ht)
      · exact hm₂ t ht

theorem supported_sound {db : Database} {premises : List Term}
    (hp : ∀ t ∈ premises, t ∈ db.terms) {t : Term}
    (h : supported premises t = true) : t ∈ db.terms := by
  obtain ⟨p, hm, hs⟩ := List.any_eq_true.mp h
  exact db.subtermClosed p (hp p hm) ((Term.mem_subtermList p).mp (of_decide_eq_true hs))

/-- Structural disequality is semantic disequality in a relational (diagonal) state. -/
theorem premiseMatches_sound {db : Database} {σ : Env} {p : Pattern} {t : Term}
    {premises : List Term} (hX : db.subsumed = ∅) (ho : p.OrderingFree) (hd : ∀ a b, Cong db a b → a = b)
    (hp : ∀ u ∈ premises, u ∈ db.terms) (ht : t ∈ db.terms)
    (h : premiseMatches σ premises p t = true) : Matches db p σ := by
  cases p with
  | expr e =>
      exact .atom (Lookup.of_eval hX ho (beq_iff_eq.mp h)
        (Database.toCong ht)).2
  | eq a b =>
      simp only [premiseMatches, Bool.and_eq_true_iff, beq_iff_eq] at h
      exact .equal (Lookup.of_eval hX ho.1 h.1 (Database.toCong ht)).2
        (Lookup.of_eval hX ho.2 h.2 (Database.toCong ht)).2 h.1 h.2 (Database.toCong ht)
  | ne a b =>
      cases hx : a.eval σ with
      | none => simp [premiseMatches, hx] at h
      | some x =>
        cases hy : b.eval σ with
        | none => simp [premiseMatches, hx, hy] at h
        | some y =>
          simp only [premiseMatches, hx, hy, Bool.and_eq_true_iff, bne_iff_ne] at h
          exact .unequal
            (Lookup.of_eval hX ho.1 hx (Database.toCong (supported_sound hp h.1.2))).2
            (Lookup.of_eval hX ho.2 hy (Database.toCong (supported_sound hp h.2))).2
            hx hy (fun hc => h.1.1.2 (hd x y hc))

theorem premisesMatch_sound {db : Database} {σ : Env} {q : Query} {ts premises : List Term}
    (hX : db.subsumed = ∅) (ho : ∀ p ∈ q, p.OrderingFree)
    (hd : ∀ a b, Cong db a b → a = b) (hp : ∀ t ∈ premises, t ∈ db.terms)
    (ht : ∀ t ∈ ts, t ∈ db.terms) (h : premisesMatch σ premises q ts = true) :
    ∀ p ∈ q, Matches db p σ := by
  induction q generalizing ts with
  | nil => simp
  | cons p ps ih =>
      cases ts with
      | nil => simp [premisesMatch] at h
      | cons t ts =>
          simp only [premisesMatch, Bool.and_eq_true_iff] at h
          intro p' hp'
          rcases List.mem_cons.mp hp' with rfl | hp'
          · exact premiseMatches_sound hX (ho p' (by simp)) hd hp (ht t (by simp)) h.1
          · exact ih (fun p hp => ho p (by simp [hp])) (fun t ht' => ht t (by simp [ht'])) h.2 p' hp'

theorem actionsFacts_unionFree {σ : Env} {as : List Action} {fs : List Term}
    (h : actionsFacts σ as = some fs) : Actions.UnionFree as := by
  induction as generalizing fs with
  | nil => trivial
  | cons a as ih =>
      obtain ⟨first, hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hr, _⟩ := Option.bind_eq_some_iff.mp h
      refine ⟨?_, ih hr⟩
      cases a with
      | expr _ | subsume _ => trivial
      | union _ _ => simp [actionFacts] at hf

end Egglog.Provenance.Generated
