import EgglogSemantics.Proofs.Source.RebuildVars

/-! Fresh binding ranges compose independently of the allowed value universe. -/

namespace Egglog

/-- **The supply is injective**, so two blocks numbered apart bind different variables.
`toString_nat_inj` is the digits, and `String.append` cancels the `"@v"`. -/
theorem freshVar_inj {i j : Nat} (h : freshVar i = freshVar j) : i = j := by
  have h2 : (freshVar i).toList = (freshVar j).toList := by rw [h]
  rw [freshVar, freshVar, String.toList_append, String.toList_append] at h2
  exact toString_nat_inj (String.toList_inj.mp (List.append_cancel_left h2))

/-- A binding of an environment with distinct keys is the one `lookup` finds. -/
theorem Env.lookup_of_mem_nodup {σ : Env} {b : Var × Term} (hb : b ∈ σ)
    (hnd : (Env.dom σ).Nodup) : Env.lookup b.1 σ = some b.2 :=
  (Env.lookup_eq_some_iff_mem hnd).mpr hb

/-- Bindings generated inside one counter interval, with distinct names and values
in a chosen set. The interval makes independently flattened blocks compose. -/
structure FreshBindings (values : Set Term) (n m : Nat) (σ : Env) : Prop where
  /-- Every key is a generated variable of this block's stretch. -/
  fresh : ∀ b ∈ σ, ∃ k, n ≤ k ∧ k < m ∧ b.1 = freshVar k
  /-- No key twice. -/
  nodup : (Env.dom σ).Nodup
  /-- Every value belongs to the chosen universe. -/
  valued : ∀ b ∈ σ, b.2 ∈ values

theorem FreshBindings.nil {values : Set Term} {n m : Nat} : FreshBindings values n m [] :=
  ⟨by simp, by simp [Env.dom], by simp⟩

theorem FreshBindings.mono {values : Set Term} {n m n' m' : Nat} {σ : Env}
    (h : FreshBindings values n m σ)
    (hn : n' ≤ n) (hm : m ≤ m') : FreshBindings values n' m' σ :=
  ⟨fun b hb => (h.fresh b hb).imp fun _ hk =>
      ⟨Nat.le_trans hn hk.1, Nat.lt_of_lt_of_le hk.2.1 hm, hk.2.2⟩,
    h.nodup, h.valued⟩

/-- **Two adjacent blocks' bindings concatenate.** The `nodup` of the result is where
`freshVar_inj` is spent: the left block's keys are numbered below `m` and the right block's at
or above it, so no key of one is a key of the other. -/
theorem FreshBindings.append {values : Set Term} {n m k : Nat} {σ₁ σ₂ : Env}
    (h₁ : FreshBindings values n m σ₁) (h₂ : FreshBindings values m k σ₂)
    (hnm : n ≤ m) (hmk : m ≤ k) :
    FreshBindings values n k (σ₁ ++ σ₂) := by
  refine ⟨fun b hb => ?_, ?_, fun b hb => ?_⟩
  · rcases List.mem_append.mp hb with hb' | hb'
    · exact (h₁.mono (Nat.le_refl n) hmk).fresh b hb'
    · exact (h₂.mono hnm (Nat.le_refl k)).fresh b hb'
  · rw [Env.dom, List.map_append]
    refine List.Nodup.append h₁.nodup h₂.nodup ?_
    intro v hv₁ hv₂
    obtain ⟨b₁, hb₁, rfl⟩ := List.mem_map.mp hv₁
    obtain ⟨b₂, hb₂, hb₂'⟩ := List.mem_map.mp hv₂
    obtain ⟨k₁, -, hk₁, he₁⟩ := h₁.fresh b₁ hb₁
    obtain ⟨k₂, hk₂, -, he₂⟩ := h₂.fresh b₂ hb₂
    have : k₂ = k₁ := freshVar_inj (he₂.symm.trans (hb₂'.trans he₁))
    omega
  · rcases List.mem_append.mp hb with hb' | hb'
    · exact h₁.valued b hb'
    · exact h₂.valued b hb'

end Egglog
