import EgglogSemantics.Proofs.Congruence.Relational
import EgglogSemantics.Proofs.Congruence.Descent
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite row-weight measure proves that every settled merging table has one output
per structural key. UF parents and constructor views share this argument. -/

namespace Egglog.Congruence

/-- Rank inside a fixed finite store; no well-founded ordering on all terms is needed. -/
def termRank (ts : List Term) (a : Term) : Nat :=
  (ts.filter fun t => Term.blt t a).length

theorem termRank_lt {ts : List Term} {a b : Term} (ha : a ∈ ts)
    (hab : Term.blt a b = true) : termRank ts a < termRank ts b := by
  have hsub : List.Sublist (ts.filter fun t => Term.blt t a)
      (ts.filter fun t => Term.blt t b) :=
    List.monotone_filter_right _ fun t ht => Term.blt_trans t a b ht hab
  have hin : a ∈ ts.filter fun t => Term.blt t b := List.mem_filter.mpr ⟨ha, hab⟩
  have hout : a ∉ ts.filter fun t => Term.blt t a := by
    intro h
    have haa := (List.mem_filter.mp h).2
    have hn := Term.blt_asymm a a haa
    simp [haa] at hn
  rcases Nat.lt_or_ge (termRank ts a) (termRank ts b) with hlt | hge
  · exact hlt
  · exact absurd (hsub.eq_of_length_le hge ▸ hin) hout

theorem termRank_le_length (ts : List Term) (a : Term) : termRank ts a ≤ ts.length :=
  List.length_filter_le _ _

/-- Removing a row and inserting two rows strictly decreases weight when either the first
inserted row is already present and the second is lighter than the removed one, or the two
together are lighter than it. -/
theorem sum_lt_of_erase_insert₂ {α : Type} [DecidableEq α] (w : α → Nat)
    {s t : Finset α} {r u v : α} (hr : r ∈ s)
    (ht : t ⊆ insert v (insert u (s.erase r)))
    (huv : (u ∈ s.erase r ∧ w v < w r) ∨ w u + w v < w r) :
    ∑ x ∈ t, w x < ∑ x ∈ s, w x := by
  have hsum : (∑ x ∈ s.erase r, w x) + w r = ∑ x ∈ s, w x :=
    Finset.sum_erase_add _ _ hr
  have ht' : (∑ x ∈ t, w x) ≤ ∑ x ∈ insert v (insert u (s.erase r)), w x :=
    Finset.sum_le_sum_of_subset ht
  have hv' : (∑ x ∈ insert v (insert u (s.erase r)), w x) ≤
      w v + ∑ x ∈ insert u (s.erase r), w x := by
    by_cases hv : v ∈ insert u (s.erase r)
    · rw [Finset.insert_eq_of_mem hv]; omega
    · rw [Finset.sum_insert hv]
  rcases huv with ⟨hu, hlt⟩ | hlt
  · rw [Finset.insert_eq_of_mem hu] at hv' ht'
    omega
  · have hu' : (∑ x ∈ insert u (s.erase r), w x) ≤ w u + ∑ x ∈ s.erase r, w x := by
      by_cases hu : u ∈ s.erase r
      · rw [Finset.insert_eq_of_mem hu]; omega
      · rw [Finset.sum_insert hu]
    omega

/-- Two rows below a rank together weigh less than one row at it. -/
private theorem two_pow_lt {a b n : Nat} (ha : a < n) (hb : b < n) :
    3 ^ (a + 1) + 3 ^ (b + 1) < 3 ^ (n + 1) := by
  have h1 : 3 ^ (a + 1) ≤ 3 ^ n := Nat.pow_le_pow_right (by decide) ha
  have h2 : 3 ^ (b + 1) ≤ 3 ^ n := Nat.pow_le_pow_right (by decide) hb
  have h3 : 0 < 3 ^ n := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

private theorem pow_succ_lt {a n : Nat} (ha : a < n) : 3 ^ (a + 1) < 3 ^ (n + 1) := by
  have h1 : 3 ^ (a + 1) ≤ 3 ^ n := Nat.pow_le_pow_right (by decide) ha
  have h3 : 0 < 3 ^ n := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

/-- UF keys use their structural rank, exponentially: a collision writes two links below
the key it rewrites, and together they must weigh less than the row they replace. Other
merging tables outweigh every UF key. -/
def rowWeight (ts : List Term) (sig : Signature) (r : Row) : Nat :=
  if sig.mergeOf r.fn = none then 0 else
    if r.fn = ufName then
      match r.args with
      | [a] => 3 ^ (termRank ts a + 1)
      | _ => 0
    else 3 ^ (ts.length + 2)

/-- Only merging rows participate in the measure; constructor-index rows weigh zero. -/
def tableRows (d : FDatabase) : Finset Row :=
  d.rows.toFinset.filter fun r => d.sig.mergeOf r.fn ≠ none

noncomputable def rowsWeight (ts : List Term) (d : FDatabase) : Nat :=
  ∑ r ∈ tableRows d, rowWeight ts d.sig r

@[simp] theorem mem_tableRows {d : FDatabase} {r : Row} :
    r ∈ tableRows d ↔ r ∈ d.rows ∧ d.sig.mergeOf r.fn ≠ none := by simp [tableRows]

@[simp] theorem tableRows_addTerm (d : FDatabase) (t : Term) :
    tableRows (d.addTerm t) = tableRows d := by
  ext r
  simp only [mem_tableRows, Egglog.FDatabase.addTerm_sig]
  constructor
  · rintro ⟨hr, hm⟩
    rcases Egglog.FDatabase.mem_addTerm_rows_imp hr with hr | hr
    · exact (hm (Egglog.FDatabase.mem_ctorRowList hr).2.1).elim
    · exact ⟨hr, hm⟩
  · rintro ⟨hr, hm⟩
    exact ⟨Egglog.FDatabase.mem_addTerm_rows_of_mem hr, hm⟩

/-- A collision can leave its survivor and the two new UF links, plus untouched old table
rows. -/
theorem mergeOneOriented_tableRows {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (huf : d.sig ufName = some (tableDecl 1))
    (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (run : d.mergeOneOriented cl r₁ r₂ = some e) :
    ∃ old new, r₂.out = [old] ∧ r₁.out = [new] ∧ r₁.fn = r₂.fn ∧
      r₁.args = r₂.args ∧ r₁ ∈ tableRows d ∧ r₂ ∈ tableRows d ∧
      ∀ r ∈ tableRows e,
        (r ∈ tableRows d ∧ r ≠ r₁ ∧ r ≠ r₂) ∨
        r = ⟨r₂.fn, r₂.args, [lowerId old new]⟩ ∨
        r = ⟨ufName, [old], [lowerId old new]⟩ ∨
        r = ⟨ufName, [new], [lowerId old new]⟩ := by
  obtain ⟨old, new, hold, hnew, hfn, hargs, hm₁, hm₂, hmg, he⟩ :=
    mergeOneOriented_single hshape hidx hcl hne run
  refine ⟨old, new, hold, hnew, hfn, hargs, mem_tableRows.mpr ⟨hm₁, hmg⟩,
    mem_tableRows.mpr ⟨hm₂, by rw [← hfn]; exact hmg⟩, ?_⟩
  intro r hr
  obtain ⟨hr, hmr⟩ := mem_tableRows.mp hr
  rw [he] at hr hmr
  obtain ⟨s, hs, hr⟩ := List.mem_map.mp hr
  obtain ⟨hs, hs₁⟩ := List.mem_filter.mp hs
  have hsr₁ : s ≠ r₁ := by simpa using hs₁
  by_cases hs₂ : s = r₂
  · exact Or.inr (Or.inl (by simpa [hs₂] using hr.symm))
  · obtain rfl : s = r := by simpa [hs₂] using hr
    have hmr' : d.sig.mergeOf s.fn ≠ none := hmr
    rcases Egglog.FDatabase.mem_addTerm_rows_imp hs with hs | hs
    · exact (hmr' (Egglog.FDatabase.mem_ctorRowList hs).2.1).elim
    · rcases mem_rows_mergeLinks (d := { d with env := mergeEnv ["old"] ["new"] [old] [new] }) huf
          (by simp [tableDecl]) rfl rfl hs hmr' with hs | hs | hs
      · exact Or.inr (Or.inr (Or.inl hs))
      · exact Or.inr (Or.inr (Or.inr hs))
      · exact Or.inl ⟨mem_tableRows.mpr ⟨hs, hmr'⟩, hsr₁, hs₂⟩

/-- Table columns stay inside one fixed finite store throughout a merge pass. -/
def TableColumnsIn (ts : List Term) (d : FDatabase) : Prop :=
  ∀ r ∈ tableRows d, ∀ t ∈ r.args ++ r.out, t ∈ ts

theorem tableColumnsIn_self {d : FDatabase} (hi : d.Inv) (hr : d.EqsRefl) :
    TableColumnsIn d.terms d := by
  intro r hm t ht
  obtain ⟨hm, hmg⟩ := mem_tableRows.mp hm
  exact FDatabase.mem_terms_of_column (Egglog.FDatabase.SubtermClosed.of_wf hi.wf)
    (mem_terms_of_indexOk hr hi.index hm hmg) ht

theorem mergeOneOriented_tableColumnsIn {ts : List Term} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (huf : d.sig ufName = some (tableDecl 1))
    (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂) (h : TableColumnsIn ts d)
    (run : d.mergeOneOriented cl r₁ r₂ = some e) : TableColumnsIn ts e := by
  obtain ⟨old, new, hold, hnew, _, _, hm₁, hm₂, hrows⟩ :=
    mergeOneOriented_tableRows hshape hidx huf hcl hne run
  have ho : old ∈ ts := h r₂ hm₂ old (by rw [hold]; simp)
  have hn : new ∈ ts := h r₁ hm₁ new (by rw [hnew]; simp)
  have hl : lowerId old new ∈ ts := by unfold lowerId; split <;> assumption
  intro r hr t ht
  rcases hrows r hr with ⟨hm, _, _⟩ | rfl | rfl | rfl
  · exact h r hm t ht
  · rcases List.mem_append.mp ht with ht | ht
    · exact h r₂ hm₂ t (List.mem_append_left _ ht)
    · exact List.mem_singleton.mp ht ▸ hl
  · simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> assumption
  · simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> assumption

/-- Every successful collision strictly decreases the total weight of live table rows: the
link from the larger id either already exists or ranks below the rewritten key, and the
self-loop at the smaller id ranks below both. -/
theorem mergeOneOriented_weight_lt {ts : List Term} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (huf : d.sig ufName = some (tableDecl 1)) (hdes : UFRowsDescend d)
    (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂) (hcols : TableColumnsIn ts d)
    (run : d.mergeOneOriented cl r₁ r₂ = some e) : rowsWeight ts e < rowsWeight ts d := by
  obtain ⟨old, new, hold, hnew, hfn, hargs, hm₁, hm₂, hrows⟩ :=
    mergeOneOriented_tableRows hshape hidx huf hcl hne run
  let lo : Row := ⟨r₂.fn, r₂.args, [lowerId old new]⟩
  let hi : Row := ⟨r₂.fn, r₂.args, [upperId old new]⟩
  let u : Row := ⟨ufName, [upperId old new], [lowerId old new]⟩
  let s : Row := ⟨ufName, [lowerId old new], [lowerId old new]⟩
  have he₁ : r₁ = ⟨r₂.fn, r₂.args, [new]⟩ := by
    cases r₁; cases r₂; simp_all
  have he₂ : r₂ = ⟨r₂.fn, r₂.args, [old]⟩ := by
    cases r₂; simp_all
  have hon : old ≠ new := by
    intro h
    apply hne
    rw [he₁, he₂, h]
  have hpairs : (hi = r₁ ∧ lo = r₂) ∨ (hi = r₂ ∧ lo = r₁) := by
    rcases ids_paired old new with ⟨hu, hl⟩ | ⟨hu, hl⟩
    · exact Or.inr ⟨by simpa [hi, hu] using he₂.symm, by simpa [lo, hl] using he₁.symm⟩
    · exact Or.inl ⟨by simpa [hi, hu] using he₁.symm, by simpa [lo, hl] using he₂.symm⟩
  have hhi : hi ∈ tableRows d := hpairs.elim (fun h => h.1 ▸ hm₁) (fun h => h.1 ▸ hm₂)
  have hlo : lo ∈ tableRows d := hpairs.elim (fun h => h.2 ▸ hm₂) (fun h => h.2 ▸ hm₁)
  have hlh : lo ≠ hi := by
    intro h
    rcases hpairs with ⟨hh, hl⟩ | ⟨hh, hl⟩
    · exact hne (hh.symm.trans (h.symm.trans hl))
    · exact hne (hl.symm.trans (h.trans hh))
  have hlink : ∀ r : Row, r = ⟨ufName, [old], [lowerId old new]⟩ ∨
      r = ⟨ufName, [new], [lowerId old new]⟩ → r = u ∨ r = s := by
    intro r hr
    rcases ids_paired old new with ⟨hu, hl⟩ | ⟨hu, hl⟩
    · rcases hr with rfl | rfl
      · exact Or.inl (by simp [u, hu])
      · exact Or.inr (by simp [s, hl])
    · rcases hr with rfl | rfl
      · exact Or.inr (by simp [s, hl])
      · exact Or.inl (by simp [u, hu])
  have hsub : tableRows e ⊆ insert s (insert u ((tableRows d).erase hi)) := by
    intro r hr
    rcases hrows r hr with ⟨hm, hn₁, hn₂⟩ | hr | hr
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      exact ⟨hpairs.elim (fun h => h.1 ▸ hn₁) (fun h => h.1 ▸ hn₂), hm⟩
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hr ▸ hlh, hr ▸ hlo⟩))
    · rcases hlink r hr with rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_self _ _
  have hum : d.sig.mergeOf ufName ≠ none := by simp [Signature.mergeOf, huf, tableDecl]
  have him : d.sig.mergeOf hi.fn ≠ none := (mem_tableRows.mp hhi).2
  have huweight : rowWeight ts d.sig u = 3 ^ (termRank ts (upperId old new) + 1) := by
    simp [rowWeight, u, hum]
  have hsweight : rowWeight ts d.sig s = 3 ^ (termRank ts (lowerId old new) + 1) := by
    simp [rowWeight, s, hum]
  have hlts : lowerId old new ∈ ts := hcols lo hlo _ (by simp [lo])
  have huts : upperId old new ∈ ts := hcols hi hhi _ (by simp [hi])
  have hrank : termRank ts (lowerId old new) < termRank ts (upperId old new) :=
    termRank_lt hlts (lowerId_lt_upperId hon)
  have hbound : (u ∈ (tableRows d).erase hi ∧ rowWeight ts d.sig s < rowWeight ts d.sig hi) ∨
      rowWeight ts d.sig u + rowWeight ts d.sig s < rowWeight ts d.sig hi := by
    by_cases hf : r₂.fn = ufName
    · have hk := (hidx.width hi (mem_tableRows.mp hhi).1 (tableDecl 1)
        (by simpa [hi, hf] using huf) him).1
      obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hk
      change r₂.args = [k] at hk
      have hhiweight : rowWeight ts d.sig hi = 3 ^ (termRank ts k + 1) := by
        simp [rowWeight, hi, hf, hk, hum]
      have hedge : (⟨ufName, [k], [upperId old new]⟩ : Row) ∈ d.rows := by
        simpa [hi, hf, hk] using (mem_tableRows.mp hhi).1
      rcases ufRowsDescend_iff.mp hdes k (upperId old new) hedge with hu | hu
      · have heq : u = lo := by simp [u, lo, hf, hk, hu]
        refine Or.inl ⟨Finset.mem_erase.mpr ⟨heq ▸ hlh, heq ▸ hlo⟩, ?_⟩
        rw [hsweight, hhiweight, ← hu]
        exact pow_succ_lt hrank
      · have hrank' : termRank ts (upperId old new) < termRank ts k := termRank_lt huts hu
        right
        rw [huweight, hsweight, hhiweight]
        exact two_pow_lt hrank' (hrank.trans hrank')
    · right
      have hhiweight : rowWeight ts d.sig hi = 3 ^ (ts.length + 2) := by
        simp [rowWeight, him, hi, hf]
      rw [huweight, hsweight, hhiweight]
      exact two_pow_lt (Nat.lt_succ_of_le (termRank_le_length ts _))
        (Nat.lt_succ_of_le (termRank_le_length ts _))
  have hsig := (Egglog.FDatabase.mergeOneOriented_confined run).2.2.1
  change (∑ r ∈ tableRows e, rowWeight ts e.sig r) < _
  rw [hsig]
  exact sum_lt_of_erase_insert₂ _ hhi hsub hbound

/-- Folding steps which either leave the state alone or decrease its weight. -/
theorem foldl_preserves_or_decreases {α β : Type} {P : α → Prop} {m : α → Nat}
    {step : α → β → α}
    (hstep : ∀ a b, P a → P (step a b) ∧ (step a b = a ∨ m (step a b) < m a)) :
    ∀ (l : List β) (a : α), P a → P (l.foldl step a) ∧
      (l.foldl step a = a ∨ m (l.foldl step a) < m a) := by
  intro l
  induction l with
  | nil => intro a ha; exact ⟨ha, Or.inl rfl⟩
  | cons b bs ih =>
      intro a ha
      obtain ⟨hb, hcases⟩ := hstep a b ha
      obtain ⟨hbs, hcases'⟩ := ih (step a b) hb
      refine ⟨hbs, ?_⟩
      rcases hcases with he | hlt
      · simpa only [List.foldl_cons, he] using hcases'
      · rcases hcases' with he | hlt'
        · exact Or.inr (he ▸ hlt)
        · exact Or.inr (hlt'.trans hlt)

/-- If such a fold preserves weight, every visited step was inert at the initial state. -/
theorem foldl_steps_of_weight_eq {α β : Type} {P : α → Prop} {m : α → Nat}
    {step : α → β → α}
    (hstep : ∀ a b, P a → P (step a b) ∧ (step a b = a ∨ m (step a b) < m a)) :
    ∀ (l : List β) (a : α), P a → m (l.foldl step a) = m a →
      ∀ b ∈ l, step a b = a := by
  intro l
  induction l with
  | nil => simp
  | cons b bs ih =>
      intro a ha he c hc
      obtain ⟨hb, hcases⟩ := hstep a b ha
      have hbEq : step a b = a := by
        rcases hcases with hbEq | hlt
        · exact hbEq
        · obtain ⟨_, htail⟩ := foldl_preserves_or_decreases hstep bs (step a b) hb
          change m (bs.foldl step (step a b)) = m a at he
          rcases htail with heq | hlt'
          · rw [heq] at he
            omega
          · omega
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hbEq
      · exact ih a ha (by simpa only [List.foldl_cons, hbEq] using he) c hc

/-- State facts preserved by every collision in one pass. -/
structure MergeState (ts : List Term) (sig : Signature) (d : FDatabase) : Prop where
  inv : d.Inv
  noUnions : d.NoUnions
  signature : d.sig = sig
  descend : UFTermsDescend d
  columns : TableColumnsIn ts d

def mergePair (cl : Finset (Term × Term)) (d : FDatabase) (pair : Row × Row) : FDatabase :=
  if pair.1 == pair.2 then d else (d.mergeOneWith cl pair.1 pair.2).getD d

theorem mergePair_step {ts : List Term} {sig : Signature} {cl : Finset (Term × Term)}
    (hshape : MergeShape sig) (huf : sig ufName = some (tableDecl 1))
    (hcl : ∀ p ∈ cl, p.1 = p.2) (d : FDatabase) (pair : Row × Row)
    (h : MergeState ts sig d) : MergeState ts sig (mergePair cl d pair) ∧
      (mergePair cl d pair = d ∨ rowsWeight ts (mergePair cl d pair) < rowsWeight ts d) := by
  unfold mergePair
  split
  · exact ⟨h, Or.inl rfl⟩
  next hne =>
    have hne : pair.1 ≠ pair.2 := by simpa using hne
    cases hm : d.mergeOneWith cl pair.1 pair.2 with
    | none => exact ⟨h, Or.inl rfl⟩
    | some e =>
      have hs : MergeShape d.sig := h.signature ▸ hshape
      have hu : d.sig ufName = some (tableDecl 1) := h.signature ▸ huf
      have hmg : d.sig.mergeOf ufName ≠ none := by simp [Signature.mergeOf, hu, tableDecl]
      have hc := Egglog.FDatabase.mergeOneWith_confined hm
      have hdes := mergeOneWith_ufTermsDescend hs h.noUnions.eqsRefl
        (Egglog.FDatabase.SubtermClosed.of_wf h.inv.wf) h.inv.index hcl hne h.descend hm
      have hcol : TableColumnsIn ts e := by
        rcases Egglog.FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d)
          pair.1 pair.2 with he | he
        · exact mergeOneOriented_tableColumnsIn hs h.inv.index hu hcl hne.symm h.columns (he ▸ hm)
        · exact mergeOneOriented_tableColumnsIn hs h.inv.index hu hcl hne h.columns (he ▸ hm)
      refine ⟨⟨Egglog.FDatabase.mergeOneWith_inv h.inv hs.mergesLegal hm,
        mergeOneWith_noUnions h.noUnions hm, hc.2.2.1.trans h.signature, hdes, hcol⟩, Or.inr ?_⟩
      rcases Egglog.FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d)
        pair.1 pair.2 with he | he
      · exact mergeOneOriented_weight_lt hs h.inv.index hu
          (h.descend.rows h.inv.index h.noUnions.eqsRefl hmg) hcl hne.symm h.columns (he ▸ hm)
      · exact mergeOneOriented_weight_lt hs h.inv.index hu
          (h.descend.rows h.inv.index h.noUnions.eqsRefl hmg) hcl hne h.columns (he ▸ hm)

theorem mergeOneWith_weight_lt {ts : List Term} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (huf : d.sig ufName = some (tableDecl 1)) (hdes : UFRowsDescend d)
    (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂) (hcols : TableColumnsIn ts d)
    (run : d.mergeOneWith cl r₁ r₂ = some e) : rowsWeight ts e < rowsWeight ts d := by
  rcases Egglog.FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he
  · exact mergeOneOriented_weight_lt hshape hidx huf hdes hcl hne.symm hcols (he ▸ run)
  · exact mergeOneOriented_weight_lt hshape hidx huf hdes hcl hne hcols (he ▸ run)

/-- An inert pair at a merge state could not have fired a successful collision. -/
theorem mergeOneWith_none_of_pair_eq {ts : List Term} {sig : Signature}
    {cl : Finset (Term × Term)} (hshape : MergeShape sig)
    (huf : sig ufName = some (tableDecl 1)) (hcl : ∀ p ∈ cl, p.1 = p.2)
    {d : FDatabase} (h : MergeState ts sig d) {r₁ r₂ : Row} (hne : r₁ ≠ r₂)
    (he : mergePair cl d (r₁, r₂) = d) : d.mergeOneWith cl r₁ r₂ = none := by
  simp only [mergePair, beq_iff_eq, if_neg hne] at he
  cases hm : d.mergeOneWith cl r₁ r₂ with
  | none => rfl
  | some e =>
      rw [hm] at he
      have hd : e = d := he
      have hu : d.sig ufName = some (tableDecl 1) := h.signature ▸ huf
      have hmg : d.sig.mergeOf ufName ≠ none := by simp [Signature.mergeOf, hu, tableDecl]
      have hlt := mergeOneWith_weight_lt (h.signature ▸ hshape) h.inv.index hu
        (h.descend.rows h.inv.index h.noUnions.eqsRefl hmg) hcl hne h.columns hm
      rw [hd] at hlt
      exact (Nat.lt_irrefl _ hlt).elim

/-- The nested row scan is a fold over its ordered pairs. -/
theorem mergeRound_pairs {d : FDatabase} (hhas : d.hasMergeRow = true) :
    let e := FDatabase.rebuild d.closureF d
    d.mergeRound = (e.rows.flatMap fun r₁ => e.rows.map fun r₂ => (r₁, r₂)).foldl
      (mergePair d.closureF) e := by
  simp only [FDatabase.mergeRound, hhas, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    List.foldl_flatMap, List.foldl_map]
  apply congrArg (fun f => (FDatabase.rebuild d.closureF d).rows.foldl f
    (FDatabase.rebuild d.closureF d))
  funext acc r₁
  apply congrArg (fun f => (FDatabase.rebuild d.closureF d).rows.foldl f acc)
  funext acc' r₂
  unfold mergePair
  dsimp only
  split
  · rfl
  · cases acc'.mergeOneWith d.closureF r₁ r₂ <;> rfl

/-- At a settled state, the row scan can perform no successful collision. -/
theorem noMerge_of_settled {d : FDatabase} (hset : d.settled = true)
    (hshape : MergeShape d.sig) (huf : d.sig ufName = some (tableDecl 1))
    (hi : d.Inv) (hn : d.NoUnions) (hdes : UFTermsDescend d)
    (hhas : d.hasMergeRow = true) {r₁ r₂ : Row} (hr₁ : r₁ ∈ d.rows) (hr₂ : r₂ ∈ d.rows)
    (hne : r₁ ≠ r₂) :
    (FDatabase.rebuild d.closureF d).mergeOneWith d.closureF r₁ r₂ = none := by
  let e := FDatabase.rebuild d.closureF d
  have heq : e = { d with rows := d.rows.dedup } := by
    dsimp [e]
    rw [← Relational.diagonal_eq_closure hn.eqsRefl, Relational.rebuild_diagonal]
  have he : MergeState d.terms d.sig e := by
    refine ⟨Egglog.FDatabase.Inv.rebuild hi Egglog.FDatabase.closureSound_closureF,
      rebuild_noUnions hn, rfl, hdes, ?_⟩
    intro r hr t ht
    have hr' : r ∈ tableRows d := by simpa [heq, tableRows] using hr
    exact tableColumnsIn_self hi hn.eqsRefl r hr' t ht
  have hcl : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have hweight : rowsWeight d.terms d.mergeRound = rowsWeight d.terms e := by
    have hrows := Egglog.FDatabase.settled_rows hset
    have hsig := Egglog.FDatabase.mergeRound_confined (d := d)
    have hdedup : d.rows.dedup.toFinset = d.rows.toFinset := by ext r; simp
    simp [rowsWeight, tableRows, hrows, hsig.2.2.1, heq, hdedup]
  have hfixed := foldl_steps_of_weight_eq (mergePair_step hshape huf hcl)
    (e.rows.flatMap fun r₁ => e.rows.map fun r₂ => (r₁, r₂)) e he
    (by rw [← mergeRound_pairs hhas]; exact hweight)
  apply mergeOneWith_none_of_pair_eq hshape huf hcl he hne
  apply hfixed
  exact List.mem_flatMap.mpr ⟨r₁, by simpa [heq] using hr₁,
    List.mem_map.mpr ⟨r₂, by simpa [heq] using hr₂, rfl⟩⟩

/-- Equal-key rows run their merge successfully once UF is declared. -/
theorem mergeOneWith_isSome_of_collide {cl : Finset (Term × Term)} {d : FDatabase}
    {r₁ r₂ : Row} {dc : FnDecl} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (huf : d.sig ufName = some (tableDecl 1)) (hdecl : d.sig r₁.fn = some dc)
    (hdc : dc.merge = some (.merge ["old"] ["new"] mergeBody mergeResult))
    (hm₁ : r₁ ∈ d.rows) (hm₂ : r₂ ∈ d.rows) (hfn : r₁.fn = r₂.fn)
    (hargs : r₁.args = r₂.args) (hkeys : FDatabase.congrKeys cl r₁.args r₂.args = true) :
    (d.mergeOneWith cl r₁ r₂).isSome = true := by
  have hout := (hshape r₁.fn dc hdecl mergeBody mergeResult hdc).2.2.2.1
  have hmg : d.sig.mergeOf r₁.fn = some (.merge ["old"] ["new"] mergeBody mergeResult) := by
    simp [Signature.mergeOf, hdecl, hdc]
  have hmg₂ : d.sig.mergeOf r₂.fn ≠ none := by rw [← hfn, hmg]; simp
  have hswap : FDatabase.swapForCanon cl d r₁ r₂ = false := by
    rw [FDatabase.swapForCanon, hmg]
    simp [hargs]
  obtain ⟨new, hnew⟩ := List.length_eq_one_iff.mp
    ((hidx.width r₁ hm₁ dc hdecl (by rw [hmg]; simp)).2.trans hout)
  obtain ⟨old, hold⟩ := List.length_eq_one_iff.mp
    ((hidx.width r₂ hm₂ dc (by rw [← hfn]; exact hdecl) hmg₂).2.trans hout)
  have henv : ({ d with env := mergeEnv ["old"] ["new"] r₂.out r₁.out } : FDatabase).env =
      mergeEnv ["old"] ["new"] [old] [new] := by rw [hold, hnew]
  have hbody := execActions_mergeBody henv
  simp only [huf, Option.isSome_some, ↓reduceIte] at hbody
  have hguard : (decide (r₁.fn = r₂.fn) && FDatabase.congrKeys cl r₁.args r₂.args
      && d.rows.contains r₁ && d.rows.contains r₂) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
    exact ⟨⟨⟨hfn, hkeys⟩, hm₁⟩, hm₂⟩
  rw [FDatabase.mergeOneWith, if_neg (by simp [hswap]), FDatabase.mergeOneOriented]
  simp only [hmg]
  rw [if_pos hguard]
  split
  · simp
  · rw [hbody, Option.bind_some]
    change (Option.map _ (Expr.evalList d.sig mergeResult (mergeEnv ["old"] ["new"]
      r₂.out r₁.out))).isSome = true
    rw [hold, hnew, evalList_mergeResult]
    rfl

/-- Every merging table has a unique row at each structural key after settling. -/
theorem tableRows_unique_of_settled {d : FDatabase} (hset : d.settled = true)
    (hshape : MergeShape d.sig) (huf : d.sig ufName = some (tableDecl 1))
    (hi : d.Inv) (hn : d.NoUnions) (hdes : UFTermsDescend d)
    {r₁ r₂ : Row} {dc : FnDecl} (hdecl : d.sig r₁.fn = some dc)
    (hdc : dc.merge = some (.merge ["old"] ["new"] mergeBody mergeResult))
    (hm₁ : r₁ ∈ d.rows) (hm₂ : r₂ ∈ d.rows) (hfn : r₁.fn = r₂.fn)
    (hargs : r₁.args = r₂.args) : r₁ = r₂ := by
  by_contra hne
  have hmg : d.sig.mergeOf r₁.fn = some (.merge ["old"] ["new"] mergeBody mergeResult) := by
    simp [Signature.mergeOf, hdecl, hdc]
  have hhas : d.hasMergeRow = true := by
    apply List.any_eq_true.mpr
    exact ⟨r₁, hm₁, by rw [hmg]⟩
  have hnone := noMerge_of_settled hset hshape huf hi hn hdes hhas hm₁ hm₂ hne
  have heq : FDatabase.rebuild d.closureF d = { d with rows := d.rows.dedup } := by
    rw [← Relational.diagonal_eq_closure hn.eqsRefl, Relational.rebuild_diagonal]
  have hkeys : FDatabase.congrKeys d.closureF r₁.args r₂.args = true := by
    rw [← hargs]
    apply congrKeys_self
    intro a ha
    apply Egglog.FDatabase.mem_closureF_iff.mpr
    apply Egglog.FDatabase.mem_toDatabase_terms.mpr
    exact FDatabase.mem_terms_of_column (Egglog.FDatabase.SubtermClosed.of_wf hi.wf)
      (mem_terms_of_indexOk hn.eqsRefl hi.index hm₁ (by rw [hmg]; simp))
      (List.mem_append_left _ ha)
  have hsome := mergeOneWith_isSome_of_collide (d := FDatabase.rebuild d.closureF d) hshape
    (Egglog.FDatabase.Inv.rebuild hi Egglog.FDatabase.closureSound_closureF).index huf
    hdecl hdc (by simpa [heq] using hm₁) (by simpa [heq] using hm₂) hfn hargs hkeys
  rw [hnone] at hsome
  contradiction

/-- In particular, every live UF node has at most one parent. -/
theorem ufRowsForest_of_settled {d : FDatabase} (hset : d.settled = true)
    (hshape : MergeShape d.sig) (huf : d.sig ufName = some (tableDecl 1))
    (hi : d.Inv) (hn : d.NoUnions) (hdes : UFTermsDescend d) : UFRowsForest d := by
  intro a b c hb hc
  have he := tableRows_unique_of_settled hset hshape huf hi hn hdes huf rfl hb.1 hc.1 rfl rfl
  simpa using congrArg Row.out he

/-- A successful merge phase returns a functional UF graph. -/
theorem mergeSaturateF_ufRowsForest {n : Nat} {d e : FDatabase}
    (hshape : MergeShape d.sig) (huf : d.sig ufName = some (tableDecl 1))
    (hi : d.Inv) (hn : d.NoUnions) (hdes : UFTermsDescend d)
    (run : d.mergeSaturateF n = some e) : UFRowsForest e := by
  have hsig := (Egglog.FDatabase.mergeSaturateF_fields run).1
  exact ufRowsForest_of_settled (Egglog.FDatabase.mergeSaturateF_settled n run)
    (hsig ▸ hshape) (by rw [hsig]; exact huf)
    (hi.mergeSaturateF hshape.mergesLegal run) (mergeSaturateF_noUnions n hn run)
    (mergeSaturateF_ufTermsDescend n hshape hi hn hdes run)

/-- At the end of a merge phase, every id has exactly one reachable live root. -/
theorem mergeSaturateF_unique_root {n : Nat} {d e : FDatabase}
    (hshape : MergeShape d.sig) (huf : d.sig ufName = some (tableDecl 1))
    (hi : d.Inv) (hn : d.NoUnions) (hdes : UFTermsDescend d)
    (run : d.mergeSaturateF n = some e) (a : Term) :
    ∃ r, UFRowReach e a r ∧ UFRowRoot e r ∧
      ∀ s, UFRowReach e a s → UFRowRoot e s → s = r := by
  have hi' := hi.mergeSaturateF hshape.mergesLegal run
  have hn' := mergeSaturateF_noUnions n hn run
  have hdes' := mergeSaturateF_ufTermsDescend n hshape hi hn hdes run
  have huf' : e.sig.mergeOf ufName ≠ none := by
    simp [Signature.mergeOf, (Egglog.FDatabase.mergeSaturateF_fields run).1, huf, tableDecl]
  obtain ⟨r, hr, hrr⟩ := exists_ufRowRoot (hdes'.rows hi'.index hn'.eqsRefl huf') a
  exact ⟨r, hr, hrr, fun s hs hsr =>
    ufRowRoot_unique (mergeSaturateF_ufRowsForest hshape huf hi hn hdes run) hs hsr hr hrr⟩

/-- Retained UF paths connect ids to the same live root after a merge phase. -/
theorem mergeSaturateF_joined_root {n : Nat} {d e : FDatabase}
    (hshape : MergeShape d.sig) (huf : d.sig ufName = some (tableDecl 1))
    (hi : d.Inv) (hn : d.NoUnions) (hdes : UFTermsDescend d) (hbr : EntryRowsUF d)
    (run : d.mergeSaturateF n = some e) {a b : Term} (hab : UFReach e a b) :
    ∃ r, UFRowReach e a r ∧ UFRowReach e b r ∧ UFRowRoot e r := by
  obtain ⟨r, har, hrr, _⟩ := mergeSaturateF_unique_root hshape huf hi hn hdes run a
  obtain ⟨s, hbs, hsr, _⟩ := mergeSaturateF_unique_root hshape huf hi hn hdes run b
  have hi' := hi.mergeSaturateF hshape.mergesLegal run
  have hn' := mergeSaturateF_noUnions n hn run
  have hdes' := mergeSaturateF_ufTermsDescend n hshape hi hn hdes run
  have huf' : e.sig ufName = some (tableDecl 1) := by
    rw [(Egglog.FDatabase.mergeSaturateF_fields run).1]
    exact huf
  have hmg : e.sig.mergeOf ufName ≠ none := by simp [Signature.mergeOf, huf', tableDecl]
  have heq := ufRowRoot_of_ufReach (mergeSaturateF_entryRowsUF n hshape hi hn hbr run)
    huf' (hdes'.rows hi'.index hn'.eqsRefl hmg)
    (mergeSaturateF_ufRowsForest hshape huf hi hn hdes run) hdes' hab r s har hrr hbs hsr
  exact ⟨r, har, heq ▸ hbs, hrr⟩

end Egglog.Congruence
