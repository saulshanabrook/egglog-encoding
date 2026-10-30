import EgglogSemantics.Congruence.Read
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.NoUnions
import EgglogSemantics.Proofs.Source.Domain

/-!
# Reading the congruence target

A source term is represented by recursively joining view entries on its children's ids.
Two terms are equivalent when they have a common resulting id. This reads recorded entry
terms, including displaced rows, just as the specification's `Database.Out` does.

The executable reader is proved equivalent to that relation. Establishing that a compiled
execution represents exactly the source congruence additionally requires the rebuilding
and rule-simulation invariants; the reader theorem alone does not assert that result.
-/

namespace Egglog.Congruence

/-- Pointwise membership: `ks` picks, per column, one of the ids that column's child was
given. `false` at unequal lengths, which is what makes a view entry of the wrong width no
entry at all. -/
def memAll : List (List Term) → List Term → Bool
  | [], [] => true
  | r :: rs, k :: ks => decide (k ∈ r) && memAll rs ks
  | _, _ => false

/-- The id a view entry gives the source application `f a…`, or `none` where the entry is
not one: the head has to be `f`'s view, the width has to be the key plus the single value
column, and the key columns have to be ids of the children, which `rs` carries. -/
def viewIdOf (rs : List (List Term)) (f : FnName) (n : Nat) : Term → Option Term
  | .app g cs =>
      if g = viewName f ∧ cs.length = n + 1 ∧ memAll rs (cs.take n) = true then
        (cs.drop n).head?
      else none
  | .lit _ => none

/-- **What a reading found**: the entry term, split into its columns. Both directions of the
link read the table through this. -/
theorem viewIdOf_eq_some {rs : List (List Term)} {f : FnName} {n : Nat} {t e : Term} :
    viewIdOf rs f n t = some e ↔
      ∃ ks, t = .app (viewName f) (ks ++ [e]) ∧ ks.length = n ∧
        memAll rs ks = true := by
  match t with
  | .lit l => simp [viewIdOf]
  | .app g cs =>
    simp only [viewIdOf]
    constructor
    · intro h
      split at h
      · rename_i hcond
        obtain ⟨rfl, hlen, hall⟩ := hcond
        have hdlen : (cs.drop n).length = 1 := by rw [List.length_drop, hlen]; omega
        obtain ⟨e', hd⟩ := List.length_eq_one_iff.mp hdlen
        rw [hd] at h
        simp only [List.head?_cons, Option.some.injEq] at h
        subst h
        refine ⟨cs.take n, ?_, ?_, hall⟩
        · rw [← hd, List.take_append_drop]
        · rw [List.length_take, hlen]; omega
      · exact absurd h (by simp)
    · rintro ⟨ks, hteq, hklen, hall⟩
      simp only [Term.app.injEq] at hteq
      obtain ⟨rfl, rfl⟩ := hteq
      rw [List.take_left' hklen, List.drop_left' hklen,
        if_pos ⟨rfl, by simp [hklen], hall⟩]
      rfl

mutual

/-- The ids the target gives a source term: `ViewRepr d.toDatabase t`, computed.

A literal is its own id and nothing else's, whether the target holds it or not: `encodeBuild`
emits no action for a literal, so a literal never keys a view entry and the encoding owes it
no e-node. -/
def viewReprsF (d : FDatabase) : Term → List Term
  | .lit l => [Term.lit l]
  | .app f as => d.terms.filterMap (viewIdOf (viewReprsListF d as) f as.length)

/-- `viewReprsF` over an argument list, one id list per column. -/
def viewReprsListF (d : FDatabase) : List Term → List (List Term)
  | [] => []
  | t :: ts => viewReprsF d t :: viewReprsListF d ts

end

/-- `SameClass d.toDatabase`, computed: one id the target gives both terms. -/
def sameClassF (d : FDatabase) (a b : Term) : Bool :=
  (viewReprsF d a).any fun e => decide (e ∈ viewReprsF d b)

/-! ### The link, computed to stated

`SubtermClosed` is what this direction spends: `Database.Out` asks that the key columns be
terms the database holds, and they are subterms of the entry term the reading found. -/

mutual

theorem viewRepr_of_mem_viewReprsF {d : FDatabase} (hsc : d.SubtermClosed) :
    ∀ (t e : Term), e ∈ viewReprsF d t → ViewRepr d.toDatabase t e
  | .lit l, e, h => by
    rw [viewReprsF, List.mem_singleton] at h
    subst h
    exact .lit
  | .app f as, e, h => by
    simp only [viewReprsF, List.mem_filterMap] at h
    obtain ⟨t, ht, hid⟩ := h
    obtain ⟨ks, rfl, hklen, hall⟩ := viewIdOf_eq_some.mp hid
    have hmem : Term.app (viewName f) (ks ++ [e]) ∈ d.toDatabase.terms := by
      rw [FDatabase.toDatabase_terms]; exact ht
    refine .app (viewReprList_of_memAll hsc as ks hall) (Database.out_self hmem ?_)
    intro x hx
    rw [FDatabase.toDatabase_terms]
    exact hsc _ ht x ((Term.mem_subtermList _).mpr
      (Term.IsSubterm.arg (List.mem_append_left _ hx) (.refl x)))

theorem viewReprList_of_memAll {d : FDatabase} (hsc : d.SubtermClosed) :
    ∀ (as ks : List Term), memAll (viewReprsListF d as) ks = true →
      ViewReprList d.toDatabase as ks
  | [], [], _ => .nil
  | [], _ :: _, h => absurd h (by simp [viewReprsListF, memAll])
  | _ :: _, [], h => absurd h (by simp [viewReprsListF, memAll])
  | a :: as, k :: ks, h => by
    simp only [viewReprsListF, memAll, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cons (viewRepr_of_mem_viewReprsF hsc a k h.1) (viewReprList_of_memAll hsc as ks h.2)

end

/-! ### The link, stated to computed

`EqsRefl` is what this direction spends, and it is spent in exactly one place: `Out`'s
`CongList` premise reads the key up to congruence, and the reading found the entry keyed by
the ids themselves. -/

/-- `ViewReprList` reads one id per column. -/
theorem ViewReprList.length_eq {d : Database} : ∀ {as es : List Term},
    ViewReprList d as es → es.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ hl => by simp [ViewReprList.length_eq hl]

mutual

theorem mem_viewReprsF_of_viewRepr {d : FDatabase} (hr : d.EqsRefl) {t e : Term}
    (h : ViewRepr d.toDatabase t e) : e ∈ viewReprsF d t := by
  match h with
  | .lit => simp [viewReprsF]
  | @ViewRepr.app _ f as es e hl ho =>
    obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : es = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
    rw [FDatabase.toDatabase_terms] at hmem
    simp only [viewReprsF, List.mem_filterMap]
    exact ⟨_, hmem, viewIdOf_eq_some.mpr
      ⟨es, rfl, hl.length_eq, memAll_of_viewReprList hr as es hl⟩⟩

theorem memAll_of_viewReprList {d : FDatabase} (hr : d.EqsRefl) :
    ∀ (as es : List Term), ViewReprList d.toDatabase as es →
      memAll (viewReprsListF d as) es = true
  | _, _, .nil => by simp [viewReprsListF, memAll]
  | a :: as, e :: es, .cons hab hl => by
    simp only [viewReprsListF, memAll, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨mem_viewReprsF_of_viewRepr hr hab, memAll_of_viewReprList hr as es hl⟩

end

/-! ### The two links, joined

`sameClassF_iff` connects the executable comparison in `difftest congruence` with
the `SameClass` relation defined in this module. -/

/-- **`viewReprsF` decides `ViewRepr`.** -/
theorem mem_viewReprsF_iff {d : FDatabase} (hsc : d.SubtermClosed) (hr : d.EqsRefl)
    (t e : Term) : e ∈ viewReprsF d t ↔ ViewRepr d.toDatabase t e :=
  ⟨viewRepr_of_mem_viewReprsF hsc t e, mem_viewReprsF_of_viewRepr hr⟩

/-- **`sameClassF` decides `SameClass`.** -/
theorem sameClassF_iff {d : FDatabase} (hsc : d.SubtermClosed) (hr : d.EqsRefl)
    (a b : Term) :
    sameClassF d a b = true ↔ SameClass d.toDatabase a b := by
  simp only [sameClassF, List.any_eq_true, decide_eq_true_eq, SameClass]
  constructor
  · rintro ⟨e, hea, heb⟩
    exact ⟨e, (mem_viewReprsF_iff hsc hr a e).mp hea, (mem_viewReprsF_iff hsc hr b e).mp heb⟩
  · rintro ⟨e, hea, heb⟩
    exact ⟨e, (mem_viewReprsF_iff hsc hr a e).mpr hea, (mem_viewReprsF_iff hsc hr b e).mpr heb⟩

end Egglog.Congruence
