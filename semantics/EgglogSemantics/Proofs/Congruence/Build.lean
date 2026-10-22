import EgglogSemantics.Proofs.Congruence.SourceSafe
import EgglogSemantics.Proofs.Congruence.ActionExprs
import EgglogSemantics.Proofs.Congruence.History
import EgglogSemantics.Proofs.Congruence.SourceState
import EgglogSemantics.Proofs.Entries
import EgglogSemantics.Proofs.Signature

/-! Source actions justify each compiled view and union-find write. Source values
contain no generated entries, so their children need no instrumentation invariant. -/

namespace Egglog.Congruence

/-- A source constructor creates a view entry for its own structural id. -/
theorem SoundTerms.addView_source {src : Database} {d : FDatabase}
    (hw : src.WF) (hs : SourceSafe src) (h : SoundTerms d src) {f : FnName}
    {cs : List Term} (ht : Term.app f cs ∈ src.terms) :
    SoundTerms (d.addAtom (.app (viewName f) (cs ++ [.app f cs]))) src := by
  have hc : ∀ c ∈ cs, c ∈ src.terms := fun c hc =>
    hw.subtermClosed _ ht (Term.arg_subterms hc (Term.self_mem_subterms c))
  apply SoundTerms.mono_terms
    (d := d.addTerm (.app (viewName f) (cs ++ [Term.app f cs]))) (fun _ ht => ht)
  refine h.addTerm_top (fun s hm hn hshape => ?_) (fun g ks out he => ?_)
    (fun a b he => ?_)
  · have hcols : ∀ c ∈ cs ++ [Term.app f cs], c ∈ src.terms := by
      intro c hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hc c hmem
      · obtain rfl := List.mem_singleton.mp hmem
        exact ht
    exact (sourceSubterms hw hs hcols s hm hn hshape).elim
  · obtain ⟨hf, hcols⟩ := Term.app.inj he
    obtain rfl := viewName_inj hf
    obtain ⟨hk, ho⟩ := List.append_inj' hcols rfl
    have ho' : Term.app f cs = out := by simpa using ho
    rw [← hk, ← ho']
    exact ⟨cs, ht, CongList.refl hc, ht⟩
  · exact (viewName_ne_ufName (Term.app.inj he).1).elim

/-- A source equation creates an edge; neither endpoint can hide another table entry. -/
theorem SoundTerms.addUF_source {src : Database} {d : FDatabase}
    (hw : src.WF) (hs : SourceSafe src) (h : SoundTerms d src) {a b : Term}
    (hc : Cong src a b) : SoundTerms (d.addAtom (.app ufName [a, b])) src := by
  apply SoundTerms.mono_terms (d := d.addTerm (.app ufName [a, b])) (fun _ ht => ht)
  refine h.addTerm_top (fun s hm hn hshape => ?_) (fun f cs e he => ?_)
    (fun x p he => ?_)
  · have hcols : ∀ c ∈ [a, b], c ∈ src.terms := by
      intro c hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hc.mem_of.1
      · exact hc.mem_of.2
    exact (sourceSubterms hw hs hcols s hm hn hshape).elim
  · exact (viewName_ne_ufName (Term.app.inj he).1.symm).elim
  · obtain ⟨rfl, rfl⟩ : a = x ∧ b = p := by simpa using (Term.app.inj he).2
    exact hc

/-- One source constructor write preserves the chosen target invariant. -/
def ViewWritesPreserve (src : Database) (Φ : FDatabase → Prop) : Prop :=
  ∀ {d : FDatabase} {f : FnName} {cs : List Term}, Term.app f cs ∈ src.terms → Φ d →
    Φ (d.addAtom (.app (viewName f) (cs ++ [.app f cs])))

mutual

/-- A property preserved by source view writes is preserved by recursive building. -/
theorem encodeBuild_preserves {src : Database} (hw : src.WF)
    {Φ : FDatabase → Prop} (hwrite : ViewWritesPreserve src Φ) :
    ∀ (e : Expr) {d d' : FDatabase} {t : Term},
      e.OrderingFree →
      e.eval d.sig d.env = some t → t ∈ src.terms → Φ d →
      execActions d (encodeBuild e) = some d' → Φ d'
  | .lit _, _, _, _, _, _, _, h, run
  | .var _, _, _, _, _, _, _, h, run => by
      obtain rfl := Option.some.inj run
      exact h
  | .min _ _, _, _, _, hp, _, _, _, _ => (Expr.not_orderingFree_min hp).elim
  | .ite _ _ _ _, _, _, _, hp, _, _, _, _ => (Expr.not_orderingFree_ite hp).elim
  | .app f args, d, d', t, hp, he, ht, h, run => by
      have hctor : d.sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hn] at he
        contradiction
      rw [Expr.eval_app_ctor hctor] at he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨m, hm, hr⟩ := execActions_append run
      have hsound := encodeBuildArgs_preserves hw hwrite args (Expr.orderingFree_app hp) hts
        (fun t ht' => hw.subtermClosed _ ht
          (Term.arg_subterms ht' (Term.self_mem_subterms t))) h hm
      have hsig := Egglog.FDatabase.execActions_sig hm
      have henv := Egglog.FDatabase.execActions_env hm
      have hts' : Expr.evalList m.sig args m.env = some ts := by rw [hsig, henv]; exact hts
      have he' : (Expr.app f args).eval m.sig m.env = some (.app f ts) := by
        rw [hsig, henv, Expr.eval_app_ctor hctor, hts]; rfl
      have ha : execAction m (.expr (.app (viewName f) (args ++ [.app f args]))) =
          some d' := by simpa [execActions] using hr
      obtain ⟨ks, vs, hk, hv, rfl⟩ := execAction_entry ha
      obtain rfl : ts = ks := Option.some.inj (hts'.symm.trans hk)
      obtain ⟨v, hval, rfl⟩ := Expr.evalList_singleton hv
      obtain rfl : Term.app f ts = v := Option.some.inj (he'.symm.trans hval)
      exact hwrite ht hsound

/-- Argument builders carry the same property from left to right. -/
theorem encodeBuildArgs_preserves {src : Database} (hw : src.WF)
    {Φ : FDatabase → Prop} (hwrite : ViewWritesPreserve src Φ) :
    ∀ (es : List Expr) {d d' : FDatabase} {ts : List Term},
      Expr.OrderingFreeList es →
      Expr.evalList d.sig es d.env = some ts → (∀ t ∈ ts, t ∈ src.terms) →
      Φ d → execActions d (encodeBuildArgs es) = some d' → Φ d'
  | [], _, _, _, _, _, _, h, run => by
      obtain rfl := Option.some.inj run
      exact h
  | e :: es, d, d', ts, hp, he, ht, h, run => by
      obtain ⟨t, hev, hr⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨m, hm, hr⟩ := execActions_append run
      have hsound := encodeBuild_preserves hw hwrite e (Expr.orderingFreeList_cons hp).1 hev
        (ht t List.mem_cons_self) h hm
      apply encodeBuildArgs_preserves hw hwrite es (Expr.orderingFreeList_cons hp).2 _
        (fun t ht' => ht t (List.mem_cons_of_mem _ ht')) hsound hr
      rw [Egglog.FDatabase.execActions_sig hm, Egglog.FDatabase.execActions_env hm]
      exact hts

end

/-- Every write performed while building an existing source value is sound. -/
theorem encodeBuild_soundTerms {src : Database} (hw : src.WF) (hs : SourceSafe src)
    (e : Expr) {d d' : FDatabase} {t : Term}
    (hp : e.OrderingFree)
    (he : e.eval d.sig d.env = some t) (ht : t ∈ src.terms) (h : SoundTerms d src)
    (run : execActions d (encodeBuild e) = some d') : SoundTerms d' src :=
  encodeBuild_preserves hw (Φ := fun d => SoundTerms d src)
    (fun ht h => h.addView_source hw hs ht) e hp he ht h run

/-- A compiled union builds its operands, then links each of them to the smaller id;
both writes are justified descending edges. -/
theorem encodeUnion_preserves {src : Database} (hw : src.WF)
    {Φ : FDatabase → Prop} (hview : ViewWritesPreserve src Φ)
    (huf : ∀ {d : FDatabase} {a b : Term}, Cong src a b →
      (b = a ∨ Term.blt b a = true) → Φ d → Φ (d.addAtom (.app ufName [a, b])))
    {d d' : FDatabase} {a b : Expr} {ta tb : Term}
    (hpa : a.OrderingFree) (hpb : b.OrderingFree)
    (ha : a.eval d.sig d.env = some ta) (hb : b.eval d.sig d.env = some tb)
    (hc : Cong src ta tb) (h : Φ d)
    (run : execActions d (encodeAction (.union a b)) = some d') : Φ d' := by
  obtain ⟨m, hbuild, hwrite⟩ := execActions_append run
  obtain ⟨n, hleft, hright⟩ := execActions_append hbuild
  have hn := encodeBuild_preserves hw hview a hpa ha hc.mem_of.1 h hleft
  have hb' : b.eval n.sig n.env = some tb := by
    rw [Egglog.FDatabase.execActions_sig hleft, Egglog.FDatabase.execActions_env hleft]
    exact hb
  have hm := encodeBuild_preserves hw hview b hpb hb' hc.mem_of.2 hn hright
  have ha' : a.eval m.sig m.env = some ta := by
    rw [Egglog.FDatabase.execActions_sig hbuild, Egglog.FDatabase.execActions_env hbuild]
    exact ha
  have hb'' : b.eval m.sig m.env = some tb := by
    rw [Egglog.FDatabase.execActions_sig hbuild, Egglog.FDatabase.execActions_env hbuild]
    exact hb
  have hmin : (Expr.min a b).eval m.sig m.env = some (lowerId ta tb) := eval_min_ids ha' hb''
  change execActions m ([_] ++ [_]) = some d' at hwrite
  obtain ⟨m₁, hw₁, hw₂⟩ := execActions_append hwrite
  have hw₁' : execAction m (.expr (.app ufName ([a] ++ [.min a b]))) = some m₁ := by
    simpa [execActions] using hw₁
  obtain ⟨ks, vs, hk, hv, rfl⟩ := execAction_entry hw₁'
  obtain ⟨k, hkv, rfl⟩ := Expr.evalList_singleton hk
  obtain ⟨v, hvv, rfl⟩ := Expr.evalList_singleton hv
  obtain rfl : ta = k := Option.some.inj (ha'.symm.trans hkv)
  obtain rfl : lowerId ta tb = v := Option.some.inj (hmin.symm.trans hvv)
  have hm₁ := huf (cong_lowerId_left hc) (lowerId_le_left ta tb) hm
  have hw₂' : execAction (m.addAtom (.app ufName [ta, lowerId ta tb]))
      (.expr (.app ufName ([b] ++ [.min a b]))) = some d' := by
    simpa [execActions] using hw₂
  obtain ⟨ks, vs, hk, hv, rfl⟩ := execAction_entry hw₂'
  obtain ⟨k, hkv, rfl⟩ := Expr.evalList_singleton hk
  obtain ⟨v, hvv, rfl⟩ := Expr.evalList_singleton hv
  obtain rfl : tb = k := Option.some.inj (hb''.symm.trans hkv)
  obtain rfl : lowerId ta tb = v := Option.some.inj (hmin.symm.trans hvv)
  exact huf (cong_lowerId_right hc) (lowerId_le_right ta tb) hm₁

/-- A compiled union builds its operands, then writes their justified links. -/
theorem encodeUnion_soundTerms {src : Database} (hw : src.WF) (hs : SourceSafe src)
    {d d' : FDatabase} {a b : Expr} {ta tb : Term}
    (hpa : a.OrderingFree) (hpb : b.OrderingFree)
    (ha : a.eval d.sig d.env = some ta) (hb : b.eval d.sig d.env = some tb)
    (hc : Cong src ta tb) (h : SoundTerms d src)
    (run : execActions d (encodeAction (.union a b)) = some d') : SoundTerms d' src :=
  encodeUnion_preserves hw (Φ := fun d => SoundTerms d src)
    (fun ht h => h.addView_source hw hs ht)
    (fun hc _ h => h.addUF_source hw hs hc) hpa hpb ha hb hc h run

/-- One source action and its compiled writes add only facts justified by the source
post-state. The evaluation premise concerns only expressions the action actually uses. -/
theorem encodeAction_soundTerms {src post : Database} {d d' : FDatabase} {a : Action}
    (hw : post.WF) (hs : SourceSafe post) (hctors : src.sig.AllConstructors)
    (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (heval : ∀ e ∈ actionExprs a, e.eval d.sig d.env = e.eval src.sig src.env)
    (h : SoundTerms d src) (hsrc : evalAction src a = some post)
    (htgt : execActions d (encodeAction a) = some d') : SoundTerms d' post := by
  have hpost := h.mono_src (evalAction_contained hsrc).eqs
  rcases evalAction_eq_some hsrc with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, -, rfl⟩
  · rw [Expr.evalAtom_eq_eval hctors] at he
    apply encodeBuild_soundTerms hw hs e (hp e (by simp [actionExprs]))
      ((heval e (by simp [actionExprs])).trans he) _ hpost htgt
    rw [Database.addTerm_terms]
    exact Or.inr (Term.self_mem_subterms t)
  · apply encodeUnion_soundTerms hw hs (hp a (by simp [actionExprs]))
      (hp b (by simp [actionExprs])) ((heval a (by simp [actionExprs])).trans ha)
      ((heval b (by simp [actionExprs])).trans hb) _ hpost htgt
    exact Cong.direct (Set.mem_insert _ _)

/-- Action blocks use the same variable environment throughout. Each successive source
post-state supplies the existence and equality needed by its compiled writes. -/
theorem encodeActions_soundTerms {src post : Database} {d d' : FDatabase} {as : List Action}
    (hw : src.WF) (hs : SourceSafe post) (hctors : src.sig.AllConstructors)
    (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (heval : ∀ a ∈ as, ∀ e ∈ actionExprs a,
      e.eval d.sig d.env = e.eval src.sig src.env)
    (h : SoundTerms d src) (hsrc : evalActions src as = some post)
    (htgt : execActions d (encodeActions as) = some d') : SoundTerms d' post := by
  induction as generalizing src d with
  | nil =>
      obtain rfl := Option.some.inj hsrc
      obtain rfl := Option.some.inj htgt
      exact h
  | cons a as ih =>
      obtain ⟨mid, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp hsrc
      obtain ⟨m, htfirst, htrest⟩ := execActions_append htgt
      have hmid : SourceSafe mid := fun t ht => hs t ((evalActions_contained hrest).terms ht)
      have hsound := encodeAction_soundTerms (evalAction_wf hw hfirst) hmid hctors
        (hp a List.mem_cons_self) (heval a List.mem_cons_self) h hfirst htfirst
      apply ih (evalAction_wf hw hfirst) (by rw [evalAction_sig hfirst]; exact hctors)
        (fun a ha => hp a (List.mem_cons_of_mem _ ha)) _ hsound hrest htrest
      intro a ha e he
      rw [Egglog.FDatabase.execActions_sig htfirst, Egglog.FDatabase.execActions_env htfirst,
        evalAction_sig hfirst, evalAction_env hfirst]
      exact heval a (List.mem_cons_of_mem _ ha) e he

/-- Source columns contain no generated entry, so indexing their enclosing atom
preserves the bridge without any extra requirement on target-held subterms. -/
theorem EntryRowsUF.addAtom_source {src : Database} {d : FDatabase} (hw : src.WF)
    (hs : SourceSafe src) (hshape : MergeShape d.sig) (h : EntryRowsUF d)
    {f : FnName} {cols : List Term} (hc : ∀ t ∈ cols, t ∈ src.terms) :
    EntryRowsUF (d.addAtom (.app f cols)) :=
  h.addAtom hshape fun s hm hn hentry => (sourceSubterms hw hs hc s hm hn hentry).elim

private theorem viewWrites_entryRowsUF {src : Database} (hw : src.WF) (hs : SourceSafe src) :
    ViewWritesPreserve src (fun d => MergeShape d.sig ∧ EntryRowsUF d) := by
  intro d f cs ht h
  refine ⟨h.1, h.2.addAtom_source hw hs h.1 ?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hw.subtermClosed _ ht (Term.arg_subterms hc (Term.self_mem_subterms c))
  · obtain rfl := List.mem_singleton.mp hc; exact ht

theorem encodeBuild_entryRowsUF {src : Database} (hw : src.WF) (hs : SourceSafe src)
    (e : Expr) {d d' : FDatabase} {t : Term}
    (hp : e.OrderingFree)
    (he : e.eval d.sig d.env = some t) (ht : t ∈ src.terms)
    (hshape : MergeShape d.sig) (h : EntryRowsUF d)
    (run : execActions d (encodeBuild e) = some d') : EntryRowsUF d' :=
  (encodeBuild_preserves hw (Φ := fun d => MergeShape d.sig ∧ EntryRowsUF d)
    (viewWrites_entryRowsUF hw hs) e hp he ht ⟨hshape, h⟩ run).2

theorem encodeUnion_entryRowsUF {src : Database} (hw : src.WF) (hs : SourceSafe src)
    {d d' : FDatabase} {a b : Expr} {ta tb : Term}
    (hpa : a.OrderingFree) (hpb : b.OrderingFree)
    (ha : a.eval d.sig d.env = some ta) (hb : b.eval d.sig d.env = some tb)
    (hc : Cong src ta tb) (hshape : MergeShape d.sig) (h : EntryRowsUF d)
    (run : execActions d (encodeAction (.union a b)) = some d') : EntryRowsUF d' := by
  refine (encodeUnion_preserves hw (Φ := fun d => MergeShape d.sig ∧ EntryRowsUF d)
    (viewWrites_entryRowsUF hw hs) ?_
    hpa hpb ha hb hc ⟨hshape, h⟩ run).2
  intro d a b hc _ h
  refine ⟨h.1, h.2.addAtom_source hw hs h.1 ?_⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact hc.mem_of.1
  · exact hc.mem_of.2

/-- Source action execution supplies the columns for the retained-entry bridge. -/
theorem encodeAction_entryRowsUF {src post : Database} {d d' : FDatabase} {a : Action}
    (hw : post.WF) (hs : SourceSafe post) (hctors : src.sig.AllConstructors)
    (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (heval : ∀ e ∈ actionExprs a, e.eval d.sig d.env = e.eval src.sig src.env)
    (hshape : MergeShape d.sig) (h : EntryRowsUF d)
    (hsrc : evalAction src a = some post)
    (htgt : execActions d (encodeAction a) = some d') : EntryRowsUF d' := by
  rcases evalAction_eq_some hsrc with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, -, rfl⟩
  · rw [Expr.evalAtom_eq_eval hctors] at he
    apply encodeBuild_entryRowsUF hw hs e (hp e (by simp [actionExprs]))
      ((heval e (by simp [actionExprs])).trans he) _ hshape h htgt
    rw [Database.addTerm_terms]
    exact Or.inr (Term.self_mem_subterms t)
  · apply encodeUnion_entryRowsUF hw hs (hp a (by simp [actionExprs]))
      (hp b (by simp [actionExprs])) ((heval a (by simp [actionExprs])).trans ha)
      ((heval b (by simp [actionExprs])).trans hb) _ hshape h htgt
    exact Cong.direct (Set.mem_insert _ _)

/-- The bridge survives a compiled source action block. -/
theorem encodeActions_entryRowsUF {src post : Database} {d d' : FDatabase} {as : List Action}
    (hw : src.WF) (hs : SourceSafe post) (hctors : src.sig.AllConstructors)
    (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (heval : ∀ a ∈ as, ∀ e ∈ actionExprs a,
      e.eval d.sig d.env = e.eval src.sig src.env)
    (hshape : MergeShape d.sig) (h : EntryRowsUF d)
    (hsrc : evalActions src as = some post)
    (htgt : execActions d (encodeActions as) = some d') : EntryRowsUF d' := by
  induction as generalizing src d with
  | nil =>
      obtain rfl := Option.some.inj htgt
      exact h
  | cons a as ih =>
      obtain ⟨mid, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp hsrc
      obtain ⟨m, htfirst, htrest⟩ := execActions_append htgt
      have hmid : SourceSafe mid := fun t ht => hs t ((evalActions_contained hrest).terms ht)
      have hhistory := encodeAction_entryRowsUF (evalAction_wf hw hfirst) hmid hctors
        (hp a List.mem_cons_self) (heval a List.mem_cons_self) hshape h hfirst htfirst
      apply ih (evalAction_wf hw hfirst) (by rw [evalAction_sig hfirst]; exact hctors)
        (fun a ha => hp a (List.mem_cons_of_mem _ ha)) _
        (by rw [Egglog.FDatabase.execActions_sig htfirst]; exact hshape) hhistory hrest htrest
      intro a ha e he
      rw [Egglog.FDatabase.execActions_sig htfirst, Egglog.FDatabase.execActions_env htfirst,
        evalAction_sig hfirst, evalAction_env hfirst]
      exact heval a (List.mem_cons_of_mem _ ha) e he

end Egglog.Congruence
