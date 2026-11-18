import EgglogSemantics.Slotted.Spec.Congruence

/-!
# The slotted closure extends the plain one

Under the empty binder signature every argument position is a term child, so each plain
congruence rule is a slotted one: `Cong db ⊆ SCong Binders.none db`. The converse, that a
slot-free store gains nothing but the reflexivity of slot terms, is the other half of the
conservative-extension statement; `Slotted/Tests/Examples.lean` tests the whole statement on
slot-free programs, and `SLOTTED.md` records the proof left to phase 2.
-/

namespace Egglog.Slotted

/-- No position is a binding position under the empty signature. -/
theorem Binders.none_isBinding (f : FnName) (j : Nat) : Binders.none.isBinding f j = false := by
  simp [Binders.isBinding, Binders.none]

mutual

/-- Every plain derivation is a slotted one under the empty binder signature. -/
theorem scong_of_cong {db : Database} : ∀ {a b : Term}, Cong db a b → SCong Binders.none db a b
  | _, _, .direct h => .direct h
  | _, _, .child h hs => .child (scong_of_cong h) hs
  | _, _, .symm h => .symm (scong_of_cong h)
  | _, _, .trans h₁ h₂ => .trans (scong_of_cong h₁) (scong_of_cong h₂)
  | _, _, .congr h hl => .congr (scong_of_cong h) (scongArgs_of_congList hl)

/-- Pointwise plain congruence is slotted argument congruence at every position. -/
theorem scongArgs_of_congList {db : Database} {f : FnName} :
    ∀ {k : Nat} {as bs : List Term}, CongList db as bs → SCongArgs Binders.none db f k as bs
  | _, _, _, .nil => .nil
  | k, _, _, .cons h hl =>
    .cons (fun hb => by rw [Binders.none_isBinding] at hb; cases hb) (fun _ => scong_of_cong h)
      (scongArgs_of_congList hl)

end

/-- Plain existence is slotted existence, so the plain live terms are slotted live terms
when nothing is subsumed. -/
theorem mem_live'_of_mem_live {db : Database} (hX : db.subsumed = ∅) {t : Term}
    (h : t ∈ db.live) : t ∈ live' Binders.none db := by
  refine ⟨scong_of_cong h.1, ?_⟩
  rintro ⟨u, ⟨u₀, hu₀, -⟩, -⟩
  rw [hX] at hu₀
  exact hu₀

end Egglog.Slotted
