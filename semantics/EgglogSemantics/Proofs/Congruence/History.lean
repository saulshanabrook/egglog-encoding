import EgglogSemantics.Proofs.Congruence.Merge
import EgglogSemantics.Proofs.Congruence.UnionFind
import EgglogSemantics.Proofs.Congruence.Relational
import EgglogSemantics.Proofs.Entries

/-! Retained entries reach a live output through explicit, recorded UF edges. -/

namespace Egglog.Congruence

variable {oldVars newVars : List Var}

/-- Historical edges remain recorded even when a merge replaces their live row. -/
def UFStep (d : FDatabase) (a b : Term) : Prop := Term.app ufName [a, b] ∈ d.terms

def UFReach (d : FDatabase) (a b : Term) : Prop := Relation.ReflTransGen (UFStep d) a b

theorem UFReach.mono {d e : FDatabase} (ht : ∀ t ∈ d.terms, t ∈ e.terms)
    {a b : Term} (h : UFReach d a b) : UFReach e a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (ht _ hs)

/-- Reflexive reachability needs a separate existence premise when read as a source proof. -/
theorem UFReach.sound {d : FDatabase} {src : Database} (hs : SoundTerms d src)
    {a b : Term} (ha : a ∈ src.terms) (h : UFReach d a b) : Cong src a b := by
  induction h with
  | refl => exact ha
  | tail _ hedge ih => exact ih.trans (hs.2 _ _ hedge)

/-- Every retained function entry has a live row at its original key, possibly with a
new output reached by explicit UF links. -/
def EntryRowsUF (d : FDatabase) : Prop :=
  ∀ f dc, d.sig f = some dc → ∀ {oldVars newVars : List Var} body res,
    dc.merge = some (.merge oldVars newVars body res) →
    ∀ cs x, cs.length = dc.arity → Term.app f (cs ++ [x]) ∈ d.terms →
      ∃ v, (⟨f, cs, [v]⟩ : Row) ∈ d.rows ∧ UFReach d x v

/-- Row replacement preserves the key and connects the displaced output to its survivor. -/
def RowsCarryUF (d e : FDatabase) : Prop :=
  ∀ f cs x, (⟨f, cs, [x]⟩ : Row) ∈ d.rows →
    ∃ v, (⟨f, cs, [v]⟩ : Row) ∈ e.rows ∧ UFReach e x v

theorem RowsCarryUF.of_subset {d e : FDatabase} (h : ∀ r ∈ d.rows, r ∈ e.rows) :
    RowsCarryUF d e := fun _ _ x hr => ⟨x, h _ hr, .refl⟩

theorem RowsCarryUF.trans {d e g : FDatabase} (h₁ : RowsCarryUF d e)
    (h₂ : RowsCarryUF e g) (ht : ∀ t ∈ e.terms, t ∈ g.terms) : RowsCarryUF d g := by
  intro f cs x hr
  obtain ⟨y, hy, hxy⟩ := h₁ f cs x hr
  obtain ⟨z, hz, hyz⟩ := h₂ f cs y hy
  exact ⟨z, hz, (hxy.mono ht).trans hyz⟩

theorem EntryRowsUF.out {d : FDatabase} (h : EntryRowsUF d) (hr : d.EqsRefl)
    {f : FnName} {dc : FnDecl} (hdc : d.sig f = some dc) {body : List Action} {res : List Expr}
    (hm : dc.merge = some (.merge oldVars newVars body res)) {cs : List Term} {x : Term}
    (hlen : cs.length = dc.arity) (ho : d.toDatabase.Out f cs [x]) :
    ∃ v, (⟨f, cs, [v]⟩ : Row) ∈ d.rows ∧ UFReach d x v := by
  obtain ⟨bs, hcl, ht⟩ := ho
  obtain rfl : cs = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
  exact h f dc hdc body res hm cs x hlen
    (by rw [Egglog.FDatabase.toDatabase_terms] at ht; exact ht)

theorem entryShaped_of_mergeShape {sig : Signature} (hshape : MergeShape sig)
    {f : FnName} {dc : FnDecl} (hdc : sig f = some dc) {body : List Action} {res : List Expr}
    (hm : dc.merge = some (.merge oldVars newVars body res)) {cs : List Term} {x : Term}
    (hlen : cs.length = dc.arity) : EntryShaped (.app f (cs ++ [x])) := by
  obtain ⟨hn, -, -, -, huf, -⟩ := hshape f dc hdc body res hm
  rcases hn with rfl | ⟨g, rfl⟩
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (hlen.trans (huf rfl))
    exact Or.inr ⟨a, x, rfl⟩
  · exact Or.inl ⟨g, cs, x, rfl⟩

/-- Old entries are handled by row transport; only newly recorded entries remain. -/
theorem EntryRowsUF.step {d e : FDatabase} (h : EntryRowsUF d) (hsig : e.sig = d.sig)
    (ht : ∀ t ∈ d.terms, t ∈ e.terms) (hc : RowsCarryUF d e)
    (hnew : ∀ f dc, d.sig f = some dc → ∀ {oldVars newVars : List Var} body res,
      dc.merge = some (.merge oldVars newVars body res) → ∀ cs x, cs.length = dc.arity →
      Term.app f (cs ++ [x]) ∈ e.terms → Term.app f (cs ++ [x]) ∈ d.terms ∨
        ∃ v, (⟨f, cs, [v]⟩ : Row) ∈ e.rows ∧ UFReach e x v) : EntryRowsUF e := by
  intro f dc hdc oldVars newVars body res hm cs x hlen hmem
  rw [hsig] at hdc
  rcases hnew f dc hdc body res hm cs x hlen hmem with hold | hdone
  · obtain ⟨v, hv, hreach⟩ := h f dc hdc body res hm cs x hlen hold
    obtain ⟨w, hw, hreach'⟩ := hc f cs v hv
    exact ⟨w, hw, (hreach.mono ht).trans hreach'⟩
  · exact hdone

/-- Atom insertion supplies its own live row. Entry-shaped proper subterms must already
be held; source builds and maintenance writes establish this independently. -/
theorem EntryRowsUF.addAtom {d : FDatabase} (hshape : MergeShape d.sig)
    (h : EntryRowsUF d) {t : Term}
    (hsub : ∀ s ∈ t.subtermList, s ≠ t → EntryShaped s → s ∈ d.terms) :
    EntryRowsUF (d.addAtom t) := by
  refine h.step rfl (fun s hs => FDatabase.mem_addTerm_of_mem hs)
    (RowsCarryUF.of_subset fun r hr => mem_addAtom_rows hr) ?_
  intro f dc hd oldVars newVars body res hm cs x hlen hmem
  rcases Egglog.FDatabase.mem_addTerm_terms_imp hmem with hsubterm | hold
  · by_cases he : Term.app f (cs ++ [x]) = t
    · subst t
      have hout := (hshape f dc hd body res hm).2.2.2.1
      refine Or.inr ⟨x, ?_, .refl⟩
      rw [Egglog.FDatabase.addAtom_eq_addRow hd (by simp [hm]) hlen (by simp [hout])]
      simp [FDatabase.addRow]
    · exact Or.inl (hsub _ hsubterm he (entryShaped_of_mergeShape hshape hd hm hlen))
  · exact Or.inl hold

theorem EntryRowsUF.union {d e : FDatabase} (hd : EntryRowsUF d) (he : EntryRowsUF e)
    (hsig : e.sig = d.sig) : EntryRowsUF (d.union e) := by
  intro f dc hdc oldVars newVars body res hm cs x hlen hmem
  rcases Egglog.FDatabase.mem_terms_union.mp hmem with hm' | hm'
  · obtain ⟨v, hv, hreach⟩ := hd f dc hdc body res hm cs x hlen hm'
    exact ⟨v, Egglog.FDatabase.mem_rows_union.mpr (Or.inl hv),
      hreach.mono fun _ ht => Egglog.FDatabase.mem_terms_union.mpr (Or.inl ht)⟩
  · obtain ⟨v, hv, hreach⟩ := he f dc (by rw [hsig]; exact hdc) body res hm cs x hlen hm'
    exact ⟨v, Egglog.FDatabase.mem_rows_union.mpr (Or.inr hv),
      hreach.mono fun _ ht => Egglog.FDatabase.mem_terms_union.mpr (Or.inr ht)⟩

/-- The exact single-output collision. Distinct rows at the same key must have distinct
outputs, so the merge executes its UF writes rather than taking the no-change branch. -/
theorem mergeOneOriented_single {d e : FDatabase} {cl : Finset (Term × Term)}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (run : d.mergeOneOriented cl r₁ r₂ = some e) :
    ∃ old new, r₂.out = [old] ∧ r₁.out = [new] ∧ r₁.fn = r₂.fn ∧
      r₁.args = r₂.args ∧ r₁ ∈ d.rows ∧ r₂ ∈ d.rows ∧ d.sig.mergeOf r₁.fn ≠ none ∧
      let m :=
        mergeLinks ({ d with env := mergeEnv ["old"] ["new"] [old] [new] } : FDatabase) old new
      let m' := m.addTerm (.app r₂.fn (r₂.args ++ [lowerId old new]))
      e = { m' with
        rows := (m'.rows.filter fun r => r ≠ r₁).map (fun r =>
          if r = r₂ then ⟨r₂.fn, r₂.args, [lowerId old new]⟩ else r)
        env := d.env
        rules := d.rules } := by
  rw [FDatabase.mergeOneOriented] at run
  split at run
  next body res hms =>
    obtain ⟨dc, hdc, hmerge⟩ := Option.bind_eq_some_iff.mp hms
    obtain ⟨-, rfl, rfl, hout, -, hid, rfl, rfl⟩ := hshape r₁.fn dc hdc body res hmerge
    split at run
    next hg =>
      obtain ⟨⟨⟨hfn, hkeys⟩, hm₁⟩, hm₂⟩ : ((r₁.fn = r₂.fn ∧
          FDatabase.congrKeys cl r₁.args r₂.args = true) ∧ r₁ ∈ d.rows) ∧ r₂ ∈ d.rows := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] using hg
      have hargs := eq_of_congrKeys hcl hkeys
      have hmg : d.sig.mergeOf r₁.fn ≠ none := by
        simp [Signature.mergeOf, hdc, hmerge]
      have hdc₂ : d.sig r₂.fn = some dc := by rw [← hfn]; exact hdc
      obtain ⟨new, hnew⟩ := List.length_eq_one_iff.mp
        ((hidx.width r₁ hm₁ dc hdc hmg).2.trans hout)
      obtain ⟨old, hold⟩ := List.length_eq_one_iff.mp
        ((hidx.width r₂ hm₂ dc hdc₂ (by rw [← hfn]; exact hmg)).2.trans hout)
      have hskip : FDatabase.noConflict ((d.sig r₁.fn).bind (·.unchangedWidth mergeBody))
          r₁ r₂ = false := by
        rw [hdc]
        simp only [Option.bind_some, FnDecl.unchangedWidth, hid,
          mergeBody, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hout]
        exact Bool.eq_false_iff.mpr fun hc =>
          hne ((noConflict_iff_eq (arity := dc.arity) hfn hargs
            (by simp [hnew]) (by simp [hold])).mp hc)
      rw [hskip] at run
      simp only [Bool.false_eq_true, ↓reduceIte] at run
      obtain ⟨m, hm, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨vs, hvs, he⟩ := Option.map_eq_some_iff.mp run
      have henv : ({ d with env := mergeEnv ["old"] ["new"] r₂.out r₁.out } : FDatabase).env =
          mergeEnv ["old"] ["new"] [old] [new] := by rw [hold, hnew]
      obtain rfl := execActions_mergeBody_inv henv hm
      change Expr.evalList d.sig mergeResult (mergeEnv ["old"] ["new"] r₂.out r₁.out) =
        some vs at hvs
      rw [hold, hnew, evalList_mergeResult, Option.some.injEq] at hvs
      subst vs
      refine ⟨old, new, hold, hnew, hfn, hargs, hm₁, hm₂, hmg, ?_⟩
      simpa only [hold, hnew] using he.symm
    next => exact absurd run (by simp)
  next => exact absurd run (by simp)

/-- Both displaced outputs reach the row that the collision leaves at their shared key:
each is linked to the smaller id by its own recorded entry. -/
theorem mergeOneOriented_survivorUF {d e : FDatabase} {cl : Finset (Term × Term)}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (run : d.mergeOneOriented cl r₁ r₂ = some e) :
    ∃ old new v, r₂.out = [old] ∧ r₁.out = [new] ∧ r₁.fn = r₂.fn ∧
      r₁.args = r₂.args ∧ (⟨r₂.fn, r₂.args, [v]⟩ : Row) ∈ e.rows ∧
      UFReach e old v ∧ UFReach e new v := by
  obtain ⟨old, new, hold, hnew, hfn, hargs, hm₁, hm₂, hmg, he⟩ :=
    mergeOneOriented_single hshape hidx hcl hne run
  have hlinks :=
    mergeLinks_links ({ d with env := mergeEnv ["old"] ["new"] [old] [new] } : FDatabase) old new
  have hreach : UFReach e old (lowerId old new) ∧ UFReach e new (lowerId old new) := by
    rw [he]
    exact ⟨.single (FDatabase.mem_addTerm_of_mem hlinks.1),
      .single (FDatabase.mem_addTerm_of_mem hlinks.2)⟩
  refine ⟨old, new, lowerId old new, hold, hnew, hfn, hargs, ?_, hreach⟩
  rw [he]
  refine List.mem_map.mpr ⟨r₂, List.mem_filter.mpr ⟨?_, by simpa using hne.symm⟩, by simp⟩
  exact Egglog.FDatabase.mem_addTerm_rows_of_mem ((mem_rows_of_mergeLinks hm₂))

theorem mergeOneOriented_rowsCarryUF {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hidx : d.IndexOk)
    (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (run : d.mergeOneOriented cl r₁ r₂ = some e) : RowsCarryUF d e := by
  obtain ⟨old, new, v, hold, hnew, hfn, hargs, hrow, hov, hnv⟩ :=
    mergeOneOriented_survivorUF hshape hidx hcl hne run
  intro f cs x hm
  by_cases h₁ : (⟨f, cs, [x]⟩ : Row) = r₁
  · have hf : f = r₂.fn := (congrArg Row.fn h₁).trans hfn
    have hc : cs = r₂.args := (congrArg Row.args h₁).trans hargs
    have hx : x = new := by simpa [hnew] using congrArg Row.out h₁
    exact ⟨v, by rw [hf, hc]; exact hrow, by rw [hx]; exact hnv⟩
  · by_cases h₂ : (⟨f, cs, [x]⟩ : Row) = r₂
    · have hf : f = r₂.fn := congrArg Row.fn h₂
      have hc : cs = r₂.args := congrArg Row.args h₂
      have hx : x = old := by simpa [hold] using congrArg Row.out h₂
      exact ⟨v, by rw [hf, hc]; exact hrow, by rw [hx]; exact hov⟩
    · exact ⟨x, mem_rows_of_mergeOneOriented run hm h₁ h₂, .refl⟩

/-- The survivor's term was already an input. The only potentially new entries are the two
UF links; if a link's row coincides with a collided row, its term was already recorded. -/
theorem mergeOneOriented_newEntryRow {d e : FDatabase} {cl : Finset (Term × Term)}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (run : d.mergeOneOriented cl r₁ r₂ = some e) :
    ∀ f dc, d.sig f = some dc → ∀ {oldVars newVars : List Var} body res,
      dc.merge = some (.merge oldVars newVars body res) →
      ∀ cs x, cs.length = dc.arity → Term.app f (cs ++ [x]) ∈ e.terms →
        Term.app f (cs ++ [x]) ∈ d.terms ∨
          ∃ v, (⟨f, cs, [v]⟩ : Row) ∈ e.rows ∧ UFReach e x v := by
  obtain ⟨old, new, hold, hnew, hfn, hargs, hm₁, hm₂, hmg, he⟩ :=
    mergeOneOriented_single hshape hidx hcl hne run
  have ht₁ := mem_terms_of_indexOk hr hidx hm₁ hmg
  have ht₂ := mem_terms_of_indexOk hr hidx hm₂ (by rw [← hfn]; exact hmg)
  have hnewmem : new ∈ d.terms := FDatabase.mem_terms_of_column hsc ht₁
    (by rw [hnew]; simp)
  have holdmem : old ∈ d.terms := FDatabase.mem_terms_of_column hsc ht₂
    (by rw [hold]; simp)
  have hsurv : Term.app r₂.fn (r₂.args ++ [lowerId old new]) ∈ d.terms := by
    unfold lowerId
    split
    · simpa only [hnew, hfn, hargs] using ht₁
    · simpa only [hold] using ht₂
  have hlow : lowerId old new ∈ d.terms := by unfold lowerId; split <;> assumption
  intro f dc hdc oldVars newVars body res hmerge cs x hlen hmem
  -- One link `(@uf a m)` with `a` held: either the sought entry was held, or it is this
  -- link's own row, which the collision neither removes nor replaces.
  have hlink : ∀ a ∈ [old, new], Term.app f (cs ++ [x]) ∈
        (Term.app ufName [a, lowerId old new]).subtermList →
      Term.app f (cs ++ [x]) ∈ d.terms ∨
        ∃ v, (⟨f, cs, [v]⟩ : Row) ∈ e.rows ∧ UFReach e x v := by
    intro a hamem hm
    have ha : a ∈ d.terms := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hamem
      rcases hamem with rfl | rfl <;> assumption
    have hcols : ∀ t ∈ [a, lowerId old new], t ∈ d.terms := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> assumption
    by_cases ht : Term.app f (cs ++ [x]) = Term.app ufName [a, lowerId old new]
    · by_cases hheld : Term.app ufName [a, lowerId old new] ∈ d.terms
      · exact Or.inl (ht ▸ hheld)
      · obtain ⟨rfl, hcol⟩ := Term.app.inj ht
        obtain ⟨rfl, hx⟩ := List.append_inj'
          (show cs ++ [x] = [a] ++ [lowerId old new] from hcol) rfl
        obtain rfl : x = lowerId old new := by simpa using hx
        let u : Row := ⟨ufName, [a], [lowerId old new]⟩
        have hu₁ : u ≠ r₁ := by
          intro hu
          apply hheld
          have hterm := congrArg (fun r : Row => Term.app r.fn (r.args ++ r.out)) hu
          exact hterm.symm ▸ ht₁
        have hu₂ : u ≠ r₂ := by
          intro hu
          apply hheld
          have hterm := congrArg (fun r : Row => Term.app r.fn (r.args ++ r.out)) hu
          exact hterm.symm ▸ ht₂
        refine Or.inr ⟨lowerId old new, ?_, .refl⟩
        rw [he]
        refine List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨?_, by simpa using hu₁⟩,
          by simp [hu₂, u]⟩
        apply Egglog.FDatabase.mem_addTerm_rows_of_mem
        have hrows := mergeLinks_rows (d := { d with env := mergeEnv ["old"] ["new"] [old] [new] })
          hdc (by simp [hmerge]) (by simpa using hlen.symm)
          (hshape _ dc hdc body res hmerge).2.2.2.1 old new
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hamem
        rcases hamem with rfl | rfl
        · exact hrows.1
        · exact hrows.2
    · exact Or.inl (FDatabase.subterms_of_columns hsc hcols _ hm ht)
  rw [he] at hmem
  rcases Egglog.FDatabase.mem_addTerm_terms_imp hmem with hm | hm
  · exact Or.inl (hsc _ hsurv _ hm)
  · rcases mem_terms_mergeLinks_imp hm with hm | hm | hm
    · exact hlink new (by simp) hm
    · exact hlink old (by simp) hm
    · exact Or.inl hm

/-- Merging preserves the retained-entry/live-row bridge. -/
theorem mergeOneOriented_entryRowsUF {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (h : EntryRowsUF d) (run : d.mergeOneOriented cl r₁ r₂ = some e) : EntryRowsUF e := by
  obtain ⟨ht, _, hsig, _⟩ := Egglog.FDatabase.mergeOneOriented_confined run
  exact h.step hsig ht (mergeOneOriented_rowsCarryUF hshape hidx hcl hne run)
    (mergeOneOriented_newEntryRow hshape hr hsc hidx hcl hne run)

theorem mergeOneWith_entryRowsUF {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (h : EntryRowsUF d) (run : d.mergeOneWith cl r₁ r₂ = some e) : EntryRowsUF e := by
  rcases Egglog.FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he
  · exact mergeOneOriented_entryRowsUF hshape hr hsc hidx hcl hne.symm h (he ▸ run)
  · exact mergeOneOriented_entryRowsUF hshape hr hsc hidx hcl hne h (he ▸ run)

/-- A merge round preserves the bridge, including the runtime's inert rebuilding step. -/
theorem mergeRound_entryRowsUF {d : FDatabase} (hshape : MergeShape d.sig)
    (hinv : d.Inv) (hn : d.NoUnions) (h : EntryRowsUF d) : EntryRowsUF d.mergeRound := by
  have hdiag : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have hreb : EntryRowsUF (FDatabase.rebuild d.closureF d) := by
    rw [← Relational.diagonal_eq_closure hn.eqsRefl, Relational.rebuild_diagonal]
    intro f dc hd oldVars newVars body res hm cs x hlen hmem
    obtain ⟨v, hv, hreach⟩ := h f dc hd body res hm cs x hlen hmem
    exact ⟨v, List.mem_dedup.mpr hv, hreach⟩
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      EntryRowsUF d.mergeRound := by
    refine Egglog.FDatabase.mergeRound_induction_ne
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ EntryRowsUF x)
      ⟨hinv, rfl, hn, h⟩
      ⟨Egglog.FDatabase.Inv.rebuild hinv Egglog.FDatabase.closureSound_closureF,
        rfl, rebuild_noUnions hn, hreb⟩ ?_
    intro x y r₁ r₂ hne hx hy
    refine ⟨Egglog.FDatabase.mergeOneWith_inv hx.1
        (by rw [hx.2.1]; exact hshape.mergesLegal) hy,
      ((Egglog.FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1,
      mergeOneWith_noUnions hx.2.2.1 hy, ?_⟩
    exact mergeOneWith_entryRowsUF (by rw [hx.2.1]; exact hshape) hx.2.2.1.eqsRefl
      (Egglog.FDatabase.SubtermClosed.of_wf hx.1.wf) hx.1.index hdiag hne hx.2.2.2 hy
  exact key.2.2.2

/-- Every retained entry still reaches a live row after a successful merge phase. -/
theorem mergeSaturateF_entryRowsUF : ∀ (n : Nat) {d e : FDatabase},
    MergeShape d.sig → d.Inv → d.NoUnions → EntryRowsUF d →
      Egglog.FDatabase.mergeSaturateF n d = some e → EntryRowsUF e
  | 0, d, e, _, _, _, h, run => by
      rw [Egglog.FDatabase.mergeSaturateF] at run
      split at run
      · obtain rfl := Option.some.inj run; exact h
      · exact absurd run (by simp)
  | n + 1, d, e, hshape, hinv, hn, h, run => by
      rw [Egglog.FDatabase.mergeSaturateF] at run
      split at run
      · obtain rfl := Option.some.inj run; exact h
      · have hsig : d.mergeRound.sig = d.sig := Egglog.FDatabase.mergeRound_confined.2.2.1
        exact mergeSaturateF_entryRowsUF n (by rw [hsig]; exact hshape)
          (Egglog.FDatabase.Inv.mergeRound_of_legalMerges hinv hshape.mergesLegal)
          (mergeRound_noUnions hn) (mergeRound_entryRowsUF hshape hinv hn h) run

end Egglog.Congruence
