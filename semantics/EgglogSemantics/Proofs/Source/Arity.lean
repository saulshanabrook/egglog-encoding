import EgglogSemantics.Source.Domain

/-! Source names, shared by the independent encoding passes. -/

namespace Egglog

/-- A source name is not in the generated namespace. -/
theorem noAt_of_mem_ctors {P : Program} (hdom : P.Fragment) {fk : FnName × Nat}
    (h : fk ∈ P.ctors) : ¬ "@".isPrefixOf fk.1 :=
  hdom.noAt fk.1 (by
    rw [Program.names]
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨fk, h, rfl⟩)))

end Egglog
