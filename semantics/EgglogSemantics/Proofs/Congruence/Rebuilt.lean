import EgglogSemantics.Proofs.Congruence.Forest
import EgglogSemantics.Proofs.Congruence.RebuildFiring

namespace Egglog.Congruence

/-- Data invariants at a completed rebuilding phase. Execution preservation and the
fixed-point test establish these independently of any proof instrumentation. -/
structure Rebuilt (d : FDatabase) : Prop where
  inv : d.Inv
  noUnions : d.NoUnions
  shape : MergeShape d.sig
  uf : d.sig ufName = some (tableDecl 1)
  descend : UFTermsDescend d
  history : EntryRowsUF d
  settled : d.settled = true
  closed : d.RoundClosed rebuildRuleset

theorem Rebuilt.forest {d : FDatabase} (h : Rebuilt d) : UFRowsForest d :=
  ufRowsForest_of_settled h.settled h.shape h.uf h.inv h.noUnions h.descend

/-- A live view's output cannot still have a nontrivial parent after rebuilding.
Firing output propagation would retain a smaller output at the same key. The history
bridge and unique live row would then force an upward historical UF path. -/
theorem Rebuilt.view_root {d : FDatabase} (h : Rebuilt d) {src : Database}
    (hs : SoundTerms d src) (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e : Term}
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hrule : eclassRule f cs.length ∈ d.rules)
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows) : UFRowRoot d e := by
  intro x hx
  have huf : d.sig.mergeOf ufName ≠ none := by simp [Signature.mergeOf, h.uf, tableDecl]
  have hvf : d.sig.mergeOf (viewName f) ≠ none := by simp [Signature.mergeOf, hf, tableDecl]
  have hcols := viewRow_valueColumns h.noUnions.eqsRefl h.inv hs hb hc hvf hr
  have hxs := (ufRow_valueColumns h.noUnions.eqsRefl h.inv hs hb hc huf hx.1).2
  obtain ⟨σ, d', hm, hfire, ht⟩ := eclassRule_fires hf h.uf hr hx.1
    (fun t ht => hcols t (List.mem_append_left _ ht)) (hcols e (by simp)) hxs
  have hist : Term.app (viewName f) (cs ++ [x]) ∈ d.terms :=
    h.closed.fired hrule rfl hm hfire ht
  obtain ⟨v, hv, hxv⟩ := h.history (viewName f) (tableDecl cs.length) hf mergeBody
    mergeResult rfl cs x rfl hist
  have heq := tableRows_unique_of_settled h.settled h.shape h.uf h.inv h.noUnions
    h.descend hf rfl hr hv rfl rfl
  have hve : v = e := by simpa using (congrArg Row.out heq).symm
  subst v
  have hxe := h.descend.rows h.inv.index h.noUnions.eqsRefl huf e x hx
  rcases UFReach.le h.descend hxv with he | hex
  · exact hx.2 he.symm
  · rw [Term.blt_asymm x e hxe] at hex
    contradiction

/-- A re-keying firing is retained at a rebuilding fixed point. -/
theorem Rebuilt.child_entry {d : FDatabase} (h : Rebuilt d) {src : Database}
    (hs : SoundTerms d src) (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e x : Term} {i : Nat} (hi : i < cs.length)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hrule : childRule f cs.length i ∈ d.rules)
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hx : (⟨ufName, [cs[i]], [x]⟩ : Row) ∈ d.rows) :
    Term.app (viewName f) (cs.set i x ++ [e]) ∈ d.terms := by
  have huf : d.sig.mergeOf ufName ≠ none := by simp [Signature.mergeOf, h.uf, tableDecl]
  have hvf : d.sig.mergeOf (viewName f) ≠ none := by simp [Signature.mergeOf, hf, tableDecl]
  have hcols := viewRow_valueColumns h.noUnions.eqsRefl h.inv hs hb hc hvf hr
  have hxs := (ufRow_valueColumns h.noUnions.eqsRefl h.inv hs hb hc huf hx).2
  obtain ⟨σ, d', hm, hfire, ht⟩ := childRule_fires hi hf h.uf hr hx
    (fun t ht => hcols t (List.mem_append_left _ ht)) (hcols e (by simp)) hxs
  exact h.closed.fired hrule rfl hm hfire ht

/-- Re-keying preserves the live output: both the old and new live outputs are roots,
and the retained entry connects them by a historical path. -/
theorem Rebuilt.child_row {d : FDatabase} (h : Rebuilt d) {src : Database}
    (hs : SoundTerms d src) (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e x : Term} {i : Nat} (hi : i < cs.length)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (houtput : eclassRule f cs.length ∈ d.rules)
    (hchild : childRule f cs.length i ∈ d.rules)
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hx : (⟨ufName, [cs[i]], [x]⟩ : Row) ∈ d.rows) :
    (⟨viewName f, cs.set i x, [e]⟩ : Row) ∈ d.rows := by
  have ht := h.child_entry hs hb hc hi hf hchild hr hx
  obtain ⟨v, hv, hev⟩ := h.history (viewName f) (tableDecl cs.length) hf mergeBody
    mergeResult rfl (cs.set i x) e (by simp [tableDecl]) ht
  have heroot := h.view_root hs hb hc hf houtput hr
  have hvroot := h.view_root hs hb hc (by simpa using hf) (by simpa using houtput) hv
  have heq : e = v := ufRowRoot_of_ufReach h.history h.uf
    (h.descend.rows h.inv.index h.noUnions.eqsRefl (by simp [Signature.mergeOf, h.uf, tableDecl]))
    h.forest h.descend hev e v .refl heroot .refl hvroot
  exact heq ▸ hv

/-- Follow an entire UF chain in one key column. -/
theorem Rebuilt.child_path {d : FDatabase} (h : Rebuilt d) {src : Database}
    (hs : SoundTerms d src) (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e x : Term} {i : Nat} (hi : i < cs.length)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (houtput : eclassRule f cs.length ∈ d.rules)
    (hchild : childRule f cs.length i ∈ d.rules)
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hx : UFRowReach d cs[i] x) :
    (⟨viewName f, cs.set i x, [e]⟩ : Row) ∈ d.rows := by
  induction hx with
  | refl => simpa only [List.set_getElem_self hi] using hr
  | @tail b x _ hedge ih =>
      have hh := h.child_row hs hb hc (by simpa using hi)
        (by simpa using hf) (by simpa using houtput) (by simpa using hchild) ih
        (by simpa [List.getElem_set_self] using hedge.1)
      simpa only [List.set_set] using hh

/-- A well-formed live row has the declared key width. -/
theorem Rebuilt.view_width {d : FDatabase} (h : Rebuilt d) {f : FnName} {k : Nat}
    (hf : d.sig (viewName f) = some (tableDecl k)) {cs : List Term} {e : Term}
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows) : cs.length = k :=
  (h.inv.index.width _ hr _ hf (by simp [Signature.mergeOf, hf, tableDecl])).1

/-- Normalize any number of child columns, retaining the same live output. -/
theorem Rebuilt.keys_paths {d : FDatabase} (h : Rebuilt d) {src : Database}
    (hs : SoundTerms d src) (hb : src.TermsBuild)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {k : Nat} (hf : d.sig (viewName f) = some (tableDecl k))
    (houtput : eclassRule f k ∈ d.rules)
    (hchildren : ∀ i < k, childRule f k i ∈ d.rules)
    {cs bs : List Term} {e : Term} (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hx : List.Forall₂ (UFRowReach d) cs bs) :
    (⟨viewName f, bs, [e]⟩ : Row) ∈ d.rows := by
  have walk : ∀ (as bs : List Term), List.Forall₂ (UFRowReach d) as bs →
      ∀ ps, (⟨viewName f, ps ++ as, [e]⟩ : Row) ∈ d.rows →
        (⟨viewName f, ps ++ bs, [e]⟩ : Row) ∈ d.rows := by
    intro as bs hab
    induction hab with
    | nil => exact fun _ hr => hr
    | @cons a b as bs hab _ ih =>
        intro ps hr
        have hlen := h.view_width hf hr
        have hi : ps.length < (ps ++ a :: as).length := by simp
        have hf' : d.sig (viewName f) = some (tableDecl (ps ++ a :: as).length) := hlen ▸ hf
        have hout' : eclassRule f (ps ++ a :: as).length ∈ d.rules := hlen ▸ houtput
        have hchild' : childRule f (ps ++ a :: as).length ps.length ∈ d.rules :=
          hlen ▸ hchildren ps.length (hlen ▸ hi)
        have hm := h.child_path hs hb hc hi hf' hout' hchild' hr (by simpa using hab)
        have hm' : (⟨viewName f, (ps ++ [b]) ++ as, [e]⟩ : Row) ∈ d.rows := by
          simpa using hm
        have hh := ih (ps ++ [b]) hm'
        simpa using hh
  simpa using walk cs bs hx [] (by simpa using hr)

end Egglog.Congruence
