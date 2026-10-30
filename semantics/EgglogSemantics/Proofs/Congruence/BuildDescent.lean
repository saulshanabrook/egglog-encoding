import EgglogSemantics.Proofs.Congruence.Build
import EgglogSemantics.Proofs.Congruence.Descent

/-! Source builds cannot introduce UF edges through their children; explicit unions
write only descending edges. -/

namespace Egglog.Congruence

theorem UFTermsDescend.addAtom_source {src : Database} {d : FDatabase}
    (hw : src.WF) (hs : SourceSafe src) (h : UFTermsDescend d)
    {f : FnName} {cols : List Term} (hc : ∀ t ∈ cols, t ∈ src.terms)
    (hu : ∀ a b, Term.app f cols = Term.app ufName [a, b] → b = a ∨ Term.blt b a = true) :
    UFTermsDescend (d.addAtom (.app f cols)) := by
  apply h.addTerm
  intro a b hm
  rw [Term.subtermList, List.mem_cons] at hm
  rcases hm with he | hm
  · exact hu a b he.symm
  · obtain ⟨t, ht, hst⟩ := (Term.mem_subtermListL cols).mp hm
    exact (hs _ (hw.subtermClosed t (hc t ht) hst) (Or.inr ⟨a, b, rfl⟩)).elim

private theorem viewWrites_ufTermsDescend {src : Database} (hw : src.WF)
    (hs : SourceSafe src) : ViewWritesPreserve src UFTermsDescend := by
  intro d f cs ht h
  apply h.addAtom_source hw hs
  · intro t hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hw.subtermClosed _ ht (Term.arg_subterms hm (Term.self_mem_subterms t))
    · exact List.mem_singleton.mp hm ▸ ht
  · intro a b he
    exact (viewName_ne_ufName (Term.app.inj he).1).elim

theorem encodeBuild_ufTermsDescend {src : Database} (hw : src.WF) (hs : SourceSafe src)
    (e : Expr) {d d' : FDatabase} {t : Term}
    (hp : e.OrderingFree)
    (he : e.eval d.sig d.env = some t) (ht : t ∈ src.terms) (h : UFTermsDescend d)
    (run : execActions d (encodeBuild e) = some d') : UFTermsDescend d' :=
  encodeBuild_preserves hw (viewWrites_ufTermsDescend hw hs) e hp he ht h run

theorem encodeUnion_ufTermsDescend {src : Database} (hw : src.WF) (hs : SourceSafe src)
    {d d' : FDatabase} {a b : Expr} {ta tb : Term}
    (hpa : a.OrderingFree) (hpb : b.OrderingFree)
    (ha : a.eval d.sig d.env = some ta) (hb : b.eval d.sig d.env = some tb)
    (hc : Cong src ta tb) (h : UFTermsDescend d)
    (run : execActions d (encodeAction (.union a b)) = some d') : UFTermsDescend d' := by
  refine encodeUnion_preserves hw (viewWrites_ufTermsDescend hw hs) ?_
    hpa hpb ha hb hc h run
  intro d a b hab hle h
  apply h.addAtom_source hw hs
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hab.mem_of.1
    · exact hab.mem_of.2
  · intro x y he
    obtain ⟨rfl, rfl⟩ : a = x ∧ b = y := by simpa using he
    exact hle

/-- Source action execution supplies the columns for descending UF writes. -/
theorem encodeAction_ufTermsDescend {src post : Database} {d d' : FDatabase} {a : Action}
    (hw : post.WF) (hs : SourceSafe post) (hctors : src.sig.AllConstructors)
    (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (heval : ∀ e ∈ actionExprs a, e.eval d.sig d.env = e.eval src.sig src.env)
    (h : UFTermsDescend d) (hsrc : evalAction src a = some post)
    (htgt : execActions d (encodeAction a) = some d') : UFTermsDescend d' := by
  rcases evalAction_eq_some hsrc with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, -, rfl⟩
  · rw [Expr.evalAtom_eq_eval hctors] at he
    apply encodeBuild_ufTermsDescend hw hs e (hp e (by simp [actionExprs]))
      ((heval e (by simp [actionExprs])).trans he) _ h htgt
    rw [Database.addTerm_terms]
    exact Or.inr (Term.self_mem_subterms t)
  · apply encodeUnion_ufTermsDescend hw hs (hp a (by simp [actionExprs]))
      (hp b (by simp [actionExprs])) ((heval a (by simp [actionExprs])).trans ha)
      ((heval b (by simp [actionExprs])).trans hb) _ h htgt
    exact Cong.direct (Set.mem_insert _ _)

/-- Historical descent survives an entire compiled source action block. -/
theorem encodeActions_ufTermsDescend {src post : Database} {d d' : FDatabase} {as : List Action}
    (hw : src.WF) (hs : SourceSafe post) (hctors : src.sig.AllConstructors)
    (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (heval : ∀ a ∈ as, ∀ e ∈ actionExprs a,
      e.eval d.sig d.env = e.eval src.sig src.env)
    (h : UFTermsDescend d) (hsrc : evalActions src as = some post)
    (htgt : execActions d (encodeActions as) = some d') : UFTermsDescend d' := by
  induction as generalizing src d with
  | nil =>
      obtain rfl := Option.some.inj htgt
      exact h
  | cons a as ih =>
      obtain ⟨mid, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp hsrc
      obtain ⟨m, htfirst, htrest⟩ := execActions_append htgt
      have hmid : SourceSafe mid := fun t ht => hs t ((evalActions_contained hrest).terms ht)
      have hdes := encodeAction_ufTermsDescend (evalAction_wf hw hfirst) hmid hctors
        (hp a List.mem_cons_self) (heval a List.mem_cons_self) h hfirst htfirst
      apply ih (evalAction_wf hw hfirst) (by rw [evalAction_sig hfirst]; exact hctors)
        (fun a ha => hp a (List.mem_cons_of_mem _ ha)) _ hdes hrest htrest
      intro a ha e he
      rw [Egglog.FDatabase.execActions_sig htfirst, Egglog.FDatabase.execActions_env htfirst,
        evalAction_sig hfirst, evalAction_env hfirst]
      exact heval a (List.mem_cons_of_mem _ ha) e he

end Egglog.Congruence
