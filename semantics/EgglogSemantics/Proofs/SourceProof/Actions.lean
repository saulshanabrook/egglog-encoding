import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Proofs.Eval

namespace Egglog.SourceProof

def Claim.Holds (db : Database) (c : Claim) : Prop := StoredCong db c.lhs c.rhs

theorem Claim.Holds.mono {A B : Database} (h : A.Contained B) {c : Claim}
    (hc : c.Holds A) : c.Holds B := StoredCong.mono h hc

theorem reflClaims_sound {db : Database} {t : Term} {c : Claim}
    (hc : c ∈ reflClaims t) : c.Holds (db.addTerm t) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  exact StoredCong.subterm (Database.toStored (Database.mem_addTerm t db))
    ((Term.mem_subtermList t).mp hs)

/-- The source evaluator rejects subsumes, so successful fact production is additive. -/
theorem actionFacts_subsumeFree {σ : Env} {a : Action} {fs : List Claim}
    (h : actionFacts σ a = some fs) : a.SubsumeFree := by
  cases a with
  | expr _ | union _ _ => rfl
  | subsume _ => simp [actionFacts] at h

theorem actionsFacts_subsumeFree {σ : Env} {as : List Action} {fs : List Claim}
    (h : actionsFacts σ as = some fs) : Actions.SubsumeFree as := by
  induction as generalizing fs with
  | nil => simp
  | cons a as ih =>
      obtain ⟨first, hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hr, _⟩ := Option.bind_eq_some_iff.mp h
      exact Actions.subsumeFree_cons.mpr ⟨actionFacts_subsumeFree hf, ih hr⟩

theorem actionFacts_sound {db : Database} {σ : Env} {a : Action} {fs : List Claim}
    (h : actionFacts σ a = some fs) :
    ∃ d, evalAction σ db a = some d ∧ ∀ c ∈ fs, c.Holds d := by
  cases a with
  | expr e =>
      obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact ⟨db.addTerm t, by simp [evalAction, ht], fun _ hc => reflClaims_sound hc⟩
  | union e₁ e₂ =>
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · contradiction
      · rename_i hok
        cases Option.some.inj h
        refine ⟨db.addEq x y, by simp only [evalAction, hx, hy, Option.bind_some, if_neg hok], ?_⟩
        have hxy : StoredCong (db.addEq x y) x y := .direct (Set.mem_insert _ _)
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hxy
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hxy.symm
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
          exact StoredCong.subterm (hxy.trans hxy.symm) ((Term.mem_subtermList x).mp hs)
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
          exact StoredCong.subterm (hxy.symm.trans hxy) ((Term.mem_subtermList y).mp hs)
  | subsume _ => simp [actionFacts] at h

theorem actionsFacts_sound {db : Database} {σ : Env} {as : List Action} {fs : List Claim}
    (h : actionsFacts σ as = some fs) :
    ∃ d, evalActions σ db as = some d ∧ ∀ c ∈ fs, c.Holds d := by
  induction as generalizing db fs with
  | nil =>
      cases Option.some.inj h
      exact ⟨db, rfl, by simp⟩
  | cons a as ih =>
      obtain ⟨fs₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨fs₂, h₂, heq⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj heq
      obtain ⟨d₁, hd₁, hf₁⟩ := actionFacts_sound (db := db) h₁
      obtain ⟨d₂, hd₂, hf₂⟩ := ih (db := d₁) h₂
      refine ⟨d₂, by simp [evalActions, hd₁, hd₂], ?_⟩
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact (hf₁ c hc).mono (evalActions_contained (actionsFacts_subsumeFree h₂) hd₂)
      · exact hf₂ c hc

end Egglog.SourceProof
