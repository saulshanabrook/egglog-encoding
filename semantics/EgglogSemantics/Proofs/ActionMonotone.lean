import EgglogSemantics.Proofs.Writes

namespace Egglog

theorem evalAction_mono {σ : Env} {db D d : Database} (hc : db.Contained D)
    {a : Action} (hdf : a.SubsumeFree) (h : evalAction σ db a = some d) :
    ∃ D', evalAction σ D a = some D' ∧ d.Contained D' := by
  rw [evalAction_eq_write _ _ _ hdf] at h ⊢
  obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨D.addEqs W, by simp [hW], ⟨Set.union_subset_union_left _ hc.eqs, hc.subsumed⟩⟩

theorem evalActions_mono {σ : Env} {db D d : Database} (hc : db.Contained D)
    {as : List Action} (hdf : Actions.SubsumeFree as) (h : evalActions σ db as = some d) :
    ∃ D', evalActions σ D as = some D' ∧ d.Contained D' := by
  rw [evalActions_eq_writes _ _ _ hdf] at h ⊢
  obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨D.addEqs W, by simp [hW], ⟨Set.union_subset_union_left _ hc.eqs, hc.subsumed⟩⟩

end Egglog
