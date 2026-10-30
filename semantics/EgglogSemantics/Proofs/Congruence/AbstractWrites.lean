import EgglogSemantics.Proofs.Congruence.SourceSafe
import EgglogSemantics.Proofs.Congruence.SourceWrites
import EgglogSemantics.Proofs.Congruence.AbstractState

/-! Mathematical soundness of source-justified constructor and union writes. -/

namespace Egglog.Congruence.Abstract

private theorem sourceAtom_columns {src : Database} (hw : src.WF) {t : Term}
    (h : SourceAtom src t) :
    ∃ f cs, t = .app f cs ∧ ∀ c ∈ cs, c ∈ src.terms := by
  cases h with
  | view ht =>
      refine ⟨_, _, rfl, ?_⟩
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact Database.mem_terms_of_arg hw ht hc
      · exact List.mem_singleton.mp hc ▸ ht
  | uf hc _ =>
      refine ⟨_, _, rfl, ?_⟩
      intro c hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hc.mem_left
      · exact List.mem_singleton.mp hm ▸ hc.mem_right

private theorem sourceAtom_subterms {src : Database} (hw : src.WF) (hs : SourceSafe src)
    {t : Term} (h : SourceAtom src t) {s : Term} (hm : s ∈ t.subterms) (hn : s ≠ t) :
    ¬ EntryShaped s := by
  obtain ⟨f, cs, rfl, hc⟩ := sourceAtom_columns hw h
  exact sourceSubterms hw hs hc s ((Term.mem_subtermList _).mpr hm) hn

private theorem sourceAtom_view {src : Database} (hw : src.WF) {t : Term}
    (h : SourceAtom src t) {f : FnName} {cs : List Term} {e : Term}
    (he : t = .app (viewName f) (cs ++ [e])) : EntrySound src f cs e := by
  cases h with
  | @view g ks ht =>
      obtain ⟨hname, hcols⟩ := Term.app.inj he
      obtain rfl := viewName_inj hname
      obtain ⟨hk, ho⟩ := List.append_inj' hcols rfl
      have ho' : Term.app g ks = e := by simpa using ho
      rw [← hk, ← ho']
      exact ⟨ks, ht, StoredCongList.refl (fun _ hc => Database.mem_terms_of_arg hw ht hc), Database.toStored ht⟩
  | uf _ _ => exact (viewName_ne_ufName (Term.app.inj he).1.symm).elim

private theorem sourceAtom_edge {src : Database} {t a b : Term} (h : SourceAtom src t)
    (he : t = .app ufName [a, b]) : StoredCong src a b ∧ (b = a ∨ Term.blt b a = true) := by
  cases h with
  | view _ => exact (viewName_ne_ufName (Term.app.inj he).1).elim
  | uf hc hd =>
      obtain ⟨rfl, rfl⟩ := by simpa using (Term.app.inj he).2
      exact ⟨hc, hd⟩

/-- A generated write is justified by its source fact, including all recorded subterms. -/
theorem sourceAtom_preserves {src d : Database} {t : Term} (hw : src.WF)
    (hsafe : SourceSafe src) (hs : SoundTerms d src) (hd : Descending d)
    (ht : SourceAtom src t) : SoundTerms (d.addTerm t) src ∧ Descending (d.addTerm t) := by
  constructor
  · apply hs.addTerm
    · intro f cs e hm
      by_cases he : Term.app (viewName f) (cs ++ [e]) = t
      · exact sourceAtom_view hw ht he.symm
      · exact (sourceAtom_subterms hw hsafe ht hm he (Or.inl ⟨f, cs, e, rfl⟩)).elim
    · intro a b hm
      by_cases he : Term.app ufName [a, b] = t
      · exact (sourceAtom_edge ht he.symm).1
      · exact (sourceAtom_subterms hw hsafe ht hm he (Or.inr ⟨a, b, rfl⟩)).elim
  · intro a b hm
    rcases Database.addTerm_terms ▸ hm with hm | hm
    · exact hd a b hm
    · by_cases he : Term.app ufName [a, b] = t
      · exact (sourceAtom_edge ht he.symm).2
      · exact (sourceAtom_subterms hw hsafe ht hm he (Or.inr ⟨a, b, rfl⟩)).elim

/-- Every atom in a justified action block preserves sound entries and descending edges. -/
theorem sourceWrites_preserves {src d e : Database} {as : List Action}
    (hw : src.WF) (hsafe : SourceSafe src) (hs : SoundTerms d src) (hd : Descending d)
    (hwrites : SourceWrites src d.sig d.env as) (run : evalActions d as = some e) :
    SoundTerms e src ∧ Descending e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj run; exact ⟨hs, hd⟩
  | cons a as ih =>
      obtain ⟨ea, t, rfl, hev, ht⟩ := hwrites a List.mem_cons_self
      have ha : evalAction d (.expr ea) = some (d.addTerm t) := by simp [evalAction, hev]
      rw [evalActions, ha, Option.bind_some] at run
      obtain ⟨hs', hd'⟩ := sourceAtom_preserves hw hsafe hs hd ht
      exact ih hs' hd' (fun a ha => hwrites a (List.mem_cons_of_mem _ ha)) run

/-- Rule-local write justifications use the firing environment and any fixed source model. -/
theorem sourceWrites_local_preserves {src d e : Database} {as : List Action} {ρ : Env}
    (hw : src.WF) (hsafe : SourceSafe src) (hs : SoundTerms d src) (hd : Descending d)
    (hwrites : SourceWrites src d.sig (ρ) as)
    (run : evalLocalActions d as ρ = some e) : SoundTerms e src ∧ Descending e := by
  obtain ⟨post, hp, rfl⟩ := Option.map_eq_some_iff.mp run
  have hi := sourceWrites_preserves (d := { d with env := ρ }) hw hsafe
    (by simpa only [SoundTerms, Database.terms_setEnv] using hs)
    (by simpa only [Descending, Database.terms_setEnv] using hd) hwrites hp
  simpa only [SoundTerms, Descending, Database.terms_setEnvRules] using hi

/-- A completed source model can justify target heads without a paired source firing. -/
theorem encodeActions_preserves_of_justified {src d e : Database} {as : List Action}
    (hw : src.WF) (hsafe : SourceSafe src) (hs : SoundTerms d src) (hdesc : Descending d)
    (hp : ∀ a ∈ as, ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (hsource : ∀ a ∈ as, SourceAction src d.sig d.env a)
    (run : evalActions d (encodeActions as) = some e) : SoundTerms e src ∧ Descending e :=
  sourceWrites_preserves hw hsafe hs hdesc
    (encodeActions_sourceWrites_of_justified hw hp hd huf hsource) run

theorem encodeLocalActions_preserves_of_justified {src d e : Database}
    {as : List Action} {ρ : Env}
    (hw : src.WF) (hsafe : SourceSafe src) (hs : SoundTerms d src) (hdesc : Descending d)
    (hp : ∀ a ∈ as, ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (hsource : ∀ a ∈ as, SourceAction src d.sig (ρ) a)
    (run : evalLocalActions d (encodeActions as) ρ = some e) :
    SoundTerms e src ∧ Descending e :=
  sourceWrites_local_preserves hw hsafe hs hdesc
    (encodeActions_sourceWrites_of_justified hw hp hd huf hsource) run

/-- Executing the compiled source block is sound in the source block's final state. -/
theorem encodeActions_preserves {src post d e : Database} {as : List Action}
    (hw : src.WF) (hsafe : SourceSafe post) (hcs : src.sig.AllConstructors)
    (hs : SoundTerms d src) (hdesc : Descending d)
    (hp : ∀ a ∈ as, ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (heval : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ t,
      x.eval src.sig src.env = some t → x.eval d.sig d.env = some t)
    (hsrc : evalActions src as = some post)
    (htgt : evalActions d (encodeActions as) = some e) : SoundTerms e post ∧ Descending e :=
  sourceWrites_preserves (evalActions_wf hw hsrc) hsafe
    (hs.mono_src (evalActions_contained hsrc).eqs) hdesc
    (encodeActions_sourceWrites hw hcs hp hd huf heval hsrc) htgt

end Egglog.Congruence.Abstract
