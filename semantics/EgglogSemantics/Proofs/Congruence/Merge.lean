import EgglogSemantics.Proofs.Congruence.IdOrder
import EgglogSemantics.Proofs.Congruence.State
import EgglogSemantics.Proofs.Congruence.Signature
import EgglogSemantics.Proofs.Entries

/-! The writes of a generated table merge: retain the smaller id and link both ids to it.
The link from the smaller id is a self-loop row, not a union-find edge. No proof payload
participates in any of them. -/

namespace Egglog.Congruence

/-- The state the merge body leaves: both ids linked to the smaller one, the larger
first. -/
def mergeLinks (d : FDatabase) (old new : Term) : FDatabase :=
  (d.addAtom (.app ufName [old, lowerId old new])).addAtom (.app ufName [new, lowerId old new])

/-- Indexing an atom changes nothing but the rows; its terms are the atom's and the old ones. -/
theorem mem_addAtom_terms {d : FDatabase} (hc : d.SubtermClosed) {t s : Term} :
    s ∈ (d.addAtom t).terms ↔ s ∈ t.subtermList ∨ s ∈ d.terms :=
  Egglog.FDatabase.mem_addTerm_terms hc

@[simp] theorem mergeLinks_sig (d : FDatabase) (old new : Term) :
    (mergeLinks d old new).sig = d.sig := rfl

@[simp] theorem mergeLinks_env (d : FDatabase) (old new : Term) :
    (mergeLinks d old new).env = d.env := rfl

theorem mem_terms_mergeLinks_imp {d : FDatabase} {old new t : Term}
    (h : t ∈ (mergeLinks d old new).terms) :
    t ∈ (Term.app ufName [new, lowerId old new]).subtermList ∨
      t ∈ (Term.app ufName [old, lowerId old new]).subtermList ∨ t ∈ d.terms := by
  rcases Egglog.FDatabase.mem_addTerm_terms_imp h with h | h
  · exact Or.inl h
  · exact Or.inr (Egglog.FDatabase.mem_addTerm_terms_imp h)

theorem mem_terms_mergeLinks {d : FDatabase} (hc : d.SubtermClosed) {old new t : Term} :
    t ∈ (mergeLinks d old new).terms ↔
      t ∈ (Term.app ufName [new, lowerId old new]).subtermList ∨
        t ∈ (Term.app ufName [old, lowerId old new]).subtermList ∨ t ∈ d.terms := by
  rw [mergeLinks, mem_addAtom_terms (d := d.addAtom (.app ufName [old, lowerId old new]))
    (hc.addTerm _), mem_addAtom_terms hc]

theorem mem_terms_of_mergeLinks {d : FDatabase} {old new t : Term} (h : t ∈ d.terms) :
    t ∈ (mergeLinks d old new).terms :=
  Egglog.FDatabase.mem_addTerm_of_mem (Egglog.FDatabase.mem_addTerm_of_mem h)

/-- Both links are recorded as entry terms. -/
theorem mergeLinks_links (d : FDatabase) (old new : Term) :
    Term.app ufName [old, lowerId old new] ∈ (mergeLinks d old new).terms ∧
      Term.app ufName [new, lowerId old new] ∈ (mergeLinks d old new).terms :=
  ⟨Egglog.FDatabase.mem_addTerm_of_mem (Egglog.FDatabase.self_mem_addTerm d _),
    Egglog.FDatabase.self_mem_addTerm _ _⟩

theorem mem_rows_of_mergeLinks {d : FDatabase} {old new : Term} {r : Row} (h : r ∈ d.rows) :
    r ∈ (mergeLinks d old new).rows :=
  mem_addAtom_rows (mem_addAtom_rows h)

/-- With UF declared at its generated shape, both links are live rows. -/
theorem mergeLinks_rows {d : FDatabase} {dc : FnDecl} (huf : d.sig ufName = some dc)
    (hm : dc.merge.isSome = true) (ha : dc.arity = 1) (hv : dc.outArity = 1) (old new : Term) :
    (⟨ufName, [old], [lowerId old new]⟩ : Row) ∈ (mergeLinks d old new).rows ∧
      (⟨ufName, [new], [lowerId old new]⟩ : Row) ∈ (mergeLinks d old new).rows := by
  have e₁ := Egglog.FDatabase.addAtom_eq_addRow (d := d) (as := [old])
    (vs := [lowerId old new]) huf hm (by simp [ha]) (by simp [hv])
  have e₂ := Egglog.FDatabase.addAtom_eq_addRow
    (d := d.addAtom (.app ufName [old, lowerId old new])) (as := [new])
    (vs := [lowerId old new]) huf hm (by simp [ha]) (by simp [hv])
  constructor
  · apply mem_addAtom_rows
    change _ ∈ (d.addAtom (.app ufName ([old] ++ [lowerId old new]))).rows
    rw [e₁]
    simp [FDatabase.addRow]
  · change _ ∈ ((d.addAtom _).addAtom (.app ufName ([new] ++ [lowerId old new]))).rows
    rw [e₂]
    simp [FDatabase.addRow]

/-- Conversely, a merging row of the result is one of the two links or an old row. -/
theorem mem_rows_mergeLinks {d : FDatabase} {dc : FnDecl} (huf : d.sig ufName = some dc)
    (hm : dc.merge.isSome = true) (ha : dc.arity = 1) (hv : dc.outArity = 1)
    {old new : Term} {r : Row} (hr : r ∈ (mergeLinks d old new).rows)
    (hmg : d.sig.mergeOf r.fn ≠ none) :
    r = ⟨ufName, [old], [lowerId old new]⟩ ∨ r = ⟨ufName, [new], [lowerId old new]⟩ ∨
      r ∈ d.rows := by
  have e₁ := Egglog.FDatabase.addAtom_eq_addRow (d := d) (as := [old])
    (vs := [lowerId old new]) huf hm (by simp [ha]) (by simp [hv])
  have e₂ := Egglog.FDatabase.addAtom_eq_addRow
    (d := d.addAtom (.app ufName [old, lowerId old new])) (as := [new])
    (vs := [lowerId old new]) huf hm (by simp [ha]) (by simp [hv])
  change r ∈ ((d.addAtom _).addAtom (.app ufName ([new] ++ [lowerId old new]))).rows at hr
  rw [e₂] at hr
  simp only [FDatabase.addRow, List.mem_dedup, List.mem_cons] at hr
  rcases hr with hr | hr
  · exact Or.inr (Or.inl hr)
  rcases Egglog.FDatabase.mem_addTerm_rows_imp hr with hr | hr
  · exact (hmg (Egglog.FDatabase.mem_ctorRowList hr).2.1).elim
  change r ∈ (d.addAtom (.app ufName ([old] ++ [lowerId old new]))).rows at hr
  rw [e₁] at hr
  simp only [FDatabase.addRow, List.mem_dedup, List.mem_cons] at hr
  rcases hr with hr | hr
  · exact Or.inl hr
  rcases Egglog.FDatabase.mem_addTerm_rows_imp hr with hr | hr
  · exact (hmg (Egglog.FDatabase.mem_ctorRowList hr).2.1).elim
  · exact Or.inr (Or.inr hr)

/-- This equation also describes failure when UF has not been declared. -/
theorem execActions_mergeBody {m : FDatabase} {old new : Term}
    (henv : m.env = mergeEnv ["old"] ["new"] [old] [new]) :
    execActions m mergeBody =
      if (m.sig ufName).isSome then some (mergeLinks m old new) else none := by
  have hsig : ∀ t, (m.addAtom t).sig = m.sig := fun _ => rfl
  have henv' : ∀ t, (m.addAtom t).env = m.env := fun _ => rfl
  by_cases huf : (m.sig ufName).isSome = true
  · simp [mergeBody, execActions, execAction, Expr.evalAtom, huf, hsig, henv', henv,
      mergeEnv_pair, Env.lookup, lowerId, Term.least, mergeLinks]
  · simp [mergeBody, execActions, execAction, Expr.evalAtom, huf]

theorem execActions_mergeBody_inv {m m' : FDatabase} {old new : Term}
    (henv : m.env = mergeEnv ["old"] ["new"] [old] [new])
    (h : execActions m mergeBody = some m') : m' = mergeLinks m old new := by
  rw [execActions_mergeBody henv] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

theorem evalList_mergeResult {sig : Signature} {old new : Term} :
    Expr.evalList sig mergeResult (mergeEnv ["old"] ["new"] [old] [new]) = some [lowerId
      old new] := by
  simp [mergeResult, Expr.evalList, Expr.eval, mergeEnv_pair, Env.lookup, lowerId, Term.least]

/-- Two colliding views justify equality of their output ids through existing source
applications at congruent children. -/
theorem EntrySound.collide {src : Database} {f : FnName} {cs : List Term} {a b : Term}
    (ha : EntrySound src f cs a) (hb : EntrySound src f cs b) : Cong src a b := by
  obtain ⟨as, ham, hal, hae⟩ := ha
  obtain ⟨bs, hbm, hbl, hbe⟩ := hb
  exact hae.symm.trans ((Cong.congr ham hbm (hal.trans hbl.symm)).trans hbe)

theorem EntrySound.select_lower {src : Database} {f : FnName} {cs : List Term} {a b : Term}
    (ha : EntrySound src f cs a) (hb : EntrySound src f cs b) :
    EntrySound src f cs (lowerId a b) := by
  unfold lowerId
  split <;> assumption

/-- Linking two congruent held ids to the smaller one adds only justified edges. -/
theorem SoundTerms.mergeLinks {src : Database} {d : FDatabase} (hsc : d.SubtermClosed)
    (h : SoundTerms d src) {old new : Term} (ho : old ∈ d.terms) (hn : new ∈ d.terms)
    (hc : Cong src old new) : SoundTerms (mergeLinks d old new) src := by
  have hl : lowerId old new ∈ d.terms := by
    rcases lowerId_eq_or old new with heq | heq <;> rw [heq] <;> assumption
  exact (h.addUF hsc ho hl (cong_lowerId_left hc)).addUF (hsc.addTerm _)
    (Egglog.FDatabase.mem_addTerm_of_mem hn) (Egglog.FDatabase.mem_addTerm_of_mem hl)
    (cong_lowerId_right hc)

/-- With one output and structural keys, ignoring a collision is possible only when
its two rows are identical. Merge rounds already skip such pairs. -/
theorem noConflict_iff_eq {arity : Nat} {r₁ r₂ : Row}
    (hfn : r₁.fn = r₂.fn) (hargs : r₁.args = r₂.args)
    (h₁ : r₁.out.length = 1) (h₂ : r₂.out.length = 1) :
    FDatabase.noConflict ((tableDecl arity).unchangedWidth mergeBody) r₁ r₂ = true ↔
      r₁ = r₂ := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h₁
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp h₂
  simp only [tableDecl, FnDecl.unchangedWidth, mergeBody, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte, FDatabase.noConflict, ha, hb]
  cases r₁
  cases r₂
  simp_all

/-- A table collision creates only one new source equality: the UF edge connecting
its two already justified output ids. The surviving entry is one of the inputs. -/
theorem mergeOneOriented_soundTerms {src : Database} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (h : SoundTerms d src)
    (hfire : d.mergeOneOriented cl r₁ r₂ = some e) : SoundTerms e src := by
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
    obtain ⟨dc, hdc, hmergedc⟩ := Option.bind_eq_some_iff.mp hms
    obtain ⟨hname, rfl, rfl, hout, huf, -, rfl, rfl⟩ := hshape r₁.fn dc hdc body res hmergedc
    split at hfire
    next hg =>
      obtain ⟨⟨⟨hfn, hkeys⟩, hmem₁⟩, hmem₂⟩ : ((r₁.fn = r₂.fn ∧
          FDatabase.congrKeys cl r₁.args r₂.args = true) ∧ r₁ ∈ d.rows) ∧ r₂ ∈ d.rows := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] using hg
      have hmg₁ : d.sig.mergeOf r₁.fn ≠ none := by rw [hms]; simp
      have hmg₂ : d.sig.mergeOf r₂.fn ≠ none := by rw [← hfn]; exact hmg₁
      have hE₁ := mem_terms_of_indexOk hr hidx hmem₁ hmg₁
      have hE₂ := mem_terms_of_indexOk hr hidx hmem₂ hmg₂
      have hargs : r₁.args = r₂.args := eq_of_congrKeys hcl hkeys
      obtain ⟨hk₁, hw₁⟩ := hidx.width r₁ hmem₁ dc hdc hmg₁
      obtain ⟨-, hw₂⟩ := hidx.width r₂ hmem₂ dc (by rw [← hfn]; exact hdc) hmg₂
      rw [hout] at hw₁ hw₂
      obtain ⟨new, hnew⟩ := List.length_eq_one_iff.mp hw₁
      obtain ⟨old, hold⟩ := List.length_eq_one_iff.mp hw₂
      have hn : new ∈ d.terms := FDatabase.mem_terms_of_column hsc hE₁ (by rw [hnew]; simp)
      have ho : old ∈ d.terms := FDatabase.mem_terms_of_column hsc hE₂ (by rw [hold]; simp)
      have hE₁' : Term.app r₂.fn (r₂.args ++ [new]) ∈ d.terms := by
        rw [← hfn, ← hargs, ← hnew]; exact hE₁
      have hE₂' : Term.app r₂.fn (r₂.args ++ [old]) ∈ d.terms := by
        rw [← hold]; exact hE₂
      have hc : Cong src old new := by
        rcases hname with hu | ⟨f, hv⟩
        · obtain ⟨key, hkey⟩ : ∃ key, r₁.args = [key] := by
            rw [huf hu] at hk₁
            exact List.length_eq_one_iff.mp hk₁
          have hn' : Cong src key new := h.2 key new (by
            simpa [← hfn, hu, ← hargs, hkey] using hE₁')
          have ho' : Cong src key old := h.2 key old (by
            simpa [← hfn, hu, ← hargs, hkey] using hE₂')
          exact ho'.symm.trans hn'
        · exact EntrySound.collide
            (h.1 f r₂.args old (by simpa [← hfn, hv] using hE₂'))
            (h.1 f r₂.args new (by simpa [← hfn, hv] using hE₁'))
      split at hfire
      next =>
        obtain rfl := Option.some.inj hfire
        exact h.mono_terms (fun _ ht => ht)
      next =>
        obtain ⟨m, hm, hfire⟩ := Option.bind_eq_some_iff.mp hfire
        obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hfire
        have henv : ({ d with env := mergeEnv ["old"] ["new"] r₂.out r₁.out } : FDatabase).env =
            mergeEnv ["old"] ["new"] [old] [new] := by rw [hnew, hold]
        obtain rfl := execActions_mergeBody_inv henv hm
        have henv' : (mergeLinks { d with env := mergeEnv ["old"] ["new"] r₂.out r₁.out } old new).env =
            mergeEnv ["old"] ["new"] [old] [new] := henv
        rw [henv', evalList_mergeResult, Option.some.injEq] at hvs
        subst vs
        have hsurv : Term.app r₂.fn (r₂.args ++ [lowerId old new]) ∈ d.terms := by
          unfold lowerId; split <;> assumption
        have hstep : SoundTerms (mergeLinks d old new) src := h.mergeLinks hsc ho hn hc
        have hsc' : (mergeLinks d old new).SubtermClosed :=
          (hsc.addTerm (.app ufName [old, lowerId old new])).addTerm
            (.app ufName [new, lowerId old new])
        exact SoundTerms.mono_terms (fun _ ht => ht)
          (hstep.addTerm_of_mem hsc' (mem_terms_of_mergeLinks hsurv))
    next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)

theorem mergeOneWith_soundTerms {src : Database} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (h : SoundTerms d src)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) : SoundTerms e src := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he <;>
    exact mergeOneOriented_soundTerms hshape hr hsc hidx hcl h (he ▸ hm)

/-- **A merge pass preserves the invariant.** The rebuild writes `rows` only, so it costs
nothing; every firing is `mergeOneWith_soundTerms`. -/
theorem mergeRound_soundTerms {src : Database} {d : FDatabase}
    (hshape : MergeShape d.sig)
    (hinv : d.Inv) (hn : d.NoUnions) (h : SoundTerms d src) :
    SoundTerms d.mergeRound src := by
  have hlegal := hshape.mergesLegal
  have hdiag : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      SoundTerms d.mergeRound src := by
    refine FDatabase.mergeRound_induction
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ SoundTerms x src)
      ⟨hinv, rfl, hn, h⟩
      ⟨FDatabase.Inv.rebuild hinv FDatabase.closureSound_closureF, rfl, rebuild_noUnions hn,
        h.mono_terms (fun t ht => ht)⟩ ?_
    intro x y r₁ r₂ hx hy
    refine ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      ((FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1,
      mergeOneWith_noUnions hx.2.2.1 hy, ?_⟩
    exact mergeOneWith_soundTerms (by rw [hx.2.1]; exact hshape) hx.2.2.1.eqsRefl
      (FDatabase.SubtermClosed.of_wf hx.1.wf) hx.1.index hdiag hx.2.2.2 hy
  exact key.2.2.2

/-- **The whole merge phase preserves the invariant**, which is what `FDatabase.execCmdM` runs
after every top-level action and at the end of every round. -/
theorem mergeSaturateF_soundTerms {src : Database} : ∀ (n : Nat) {d e : FDatabase},
    MergeShape d.sig → d.Inv → d.NoUnions →
    SoundTerms d src → FDatabase.mergeSaturateF n d = some e → SoundTerms e src
  | 0, d, e, _, _, _, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · exact absurd hrun (by simp)
  | n + 1, d, e, hshape, hinv, hn, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · have hsig : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
        exact mergeSaturateF_soundTerms n (by rw [hsig]; exact hshape)
          (FDatabase.Inv.mergeRound_of_legalMerges hinv hshape.mergesLegal)
          (mergeRound_noUnions hn) (mergeRound_soundTerms hshape hinv hn h) hrun

end Egglog.Congruence
