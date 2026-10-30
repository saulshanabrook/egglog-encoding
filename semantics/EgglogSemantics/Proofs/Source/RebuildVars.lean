import EgglogSemantics.Source.Names
import EgglogSemantics.Proofs.Bindings

/-! Distinct key variables shared by the rebuilding passes. -/

namespace Egglog

theorem toString_nat_inj {i j : Nat} (h : toString i = toString j) : i = j := by
  have hd : Nat.toDigits 10 i = Nat.toDigits 10 j := by
    rw [← Nat.toList_repr, ← Nat.toList_repr, ← Nat.toString_eq_repr, ← Nat.toString_eq_repr, h]
  have hi := Nat.ofDigitChars_toDigits (b := 10) (n := i) (by decide) (by decide)
  rw [hd, Nat.ofDigitChars_toDigits (by decide) (by decide)] at hi
  exact hi.symm

def rebuildVarNames (k : Nat) : List Var := (List.range k).map fun i => "@c" ++ toString i

theorem length_rebuildVarNames (k : Nat) : (rebuildVarNames k).length = k := by
  simp [rebuildVarNames]

theorem rebuildVarNames_nodup (k : Nat) : (rebuildVarNames k).Nodup := by
  refine (List.nodup_map_iff_inj_on List.nodup_range).mpr fun i _ j _ h => ?_
  have h2 : ("@c" ++ toString i).toList = ("@c" ++ toString j).toList := by rw [h]
  rw [String.toList_append, String.toList_append] at h2
  exact toString_nat_inj (String.toList_inj.mp (List.append_cancel_left h2))

theorem getElem_rebuildVarNames {k i : Nat} (hi : i < k) :
    (rebuildVarNames k)[i]'(by rw [length_rebuildVarNames]; exact hi) = "@c" ++ toString i := by
  simp [rebuildVarNames]

theorem not_mem_rebuildVarNames {v : Var} {c : Char} (hv : v.toList = ['@', c]) (hc : c ≠ 'c')
    (k : Nat) : v ∉ rebuildVarNames k := by
  intro h
  rw [rebuildVarNames, List.mem_map] at h
  obtain ⟨i, -, heq⟩ := h
  have h2 : v.toList = ['@', 'c'] ++ (toString i).toList := by
    rw [← heq, String.toList_append, show ("@c").toList = ['@', 'c'] from by decide]
  rw [hv] at h2
  exact hc (List.cons.inj (List.cons.inj h2).2).1

end Egglog
