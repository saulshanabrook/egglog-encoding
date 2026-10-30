import EgglogSemantics.Proofs.Database

/-! Query operands add existence without asserting new equalities. -/

namespace Egglog.Conservativity

/-- `addTerms` adds reflexive pairs and nothing else. This is the whole content of
conservativity's hypothesis. -/
theorem mem_addTerms_eqs : ∀ (ts : List Term) (db : Database) (p : Term × Term),
    p ∈ (db.addTerms ts).eqs → p ∈ db.eqs ∨ p.1 = p.2
  | [], _, _, h => Or.inl h
  | t :: ts, db, p, h => by
      rcases mem_addTerms_eqs ts (db.addTerm t) p h with h' | h'
      · rcases h' with rfl | h'
        · exact Or.inr rfl
        · exact Or.inl h'
      · exact Or.inr h'

end Egglog.Conservativity
