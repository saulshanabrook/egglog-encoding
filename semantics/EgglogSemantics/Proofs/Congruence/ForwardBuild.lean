import EgglogSemantics.Proofs.Congruence.Build
import EgglogSemantics.Proofs.Congruence.SourceReads

/-! Forward execution of compiled source heads, preserving existence and recorded unions. -/

namespace Egglog.Congruence

private theorem out_addAtom {d : FDatabase} (hsc : d.SubtermClosed) (f : FnName)
    (cs : List Term) (i : Term) : (d.addAtom (.app f (cs ++ [i]))).toDatabase.Out f cs [i] := by
  apply Database.out_self
  · change Term.app f (cs ++ [i]) ∈ (d.addTerm (.app f (cs ++ [i]))).toDatabase.terms
    rw [Egglog.FDatabase.toDatabase_terms]
    exact Egglog.FDatabase.self_mem_addTerm _ _
  · intro t ht
    change t ∈ (d.addTerm (.app f (cs ++ [i]))).toDatabase.terms
    rw [Egglog.FDatabase.toDatabase_terms]
    exact (Egglog.FDatabase.mem_addTerm_terms hsc).mpr (Or.inl ((Term.mem_subtermList _).mpr
      (Term.IsSubterm.arg (List.mem_append_left _ ht) (.refl t))))

mutual

/-- A source build executes at a reading substitution and represents its source result.
The target id is the head expression evaluated at target ids, not the source term itself. -/
theorem encodeBuild_reads {sig : Signature} {σ : Env} :
    ∀ (e : Expr) {t : Term} {d : FDatabase}, d.SubtermClosed →
      e.OrderingFree →
      (∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true) →
      Env.Reads d.toDatabase σ d.env → e.eval sig σ = some t →
      ∃ i d', e.eval d.sig d.env = some i ∧
        execActions d (encodeBuild e) = some d' ∧ ViewRepr d'.toDatabase t i
  | .lit l, _, d, _, _, _, _, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨.lit l, d, rfl, rfl, .lit⟩
  | .var v, t, d, _, _, _, _, hρ, he => by
      obtain ⟨i, hi, hr⟩ := hρ v t he
      exact ⟨i, d, hi, rfl, hr⟩
  | .min _ _, _, _, _, hp, _, _, _, _ => (Expr.not_orderingFree_min hp).elim
  | .ite _ _ _ _, _, _, _, hp, _, _, _, _ => (Expr.not_orderingFree_ite hp).elim
  | .app f args, t, d, hsc, hp, hc, hd, hρ, he => by
      have hctor : sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hn] at he
        contradiction
      rw [Expr.eval_app_ctor hctor] at he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨is, m, his, hm, hviews⟩ := encodeBuildArgs_reads args hsc
        (Expr.orderingFree_app hp)
        (fun g hg => hc g (by simp [Expr.fns, hg]))
        (fun fk hk => hd fk (List.mem_cons_of_mem _ hk)) hρ hts
      have htarget : (Expr.app f args).eval d.sig d.env = some (.app f is) := by
        rw [Expr.eval_app_ctor (hc f (by simp [Expr.fns]) hctor), his]; rfl
      have hsig := Egglog.FDatabase.execActions_sig hm
      have henv := Egglog.FDatabase.execActions_env hm
      have hcols : Expr.evalList m.sig (args ++ [.app f args]) m.env =
          some (is ++ [.app f is]) := by
        rw [hsig, henv]
        exact Expr.evalList_append_eq his (by
          simp only [Expr.evalList, htarget, Option.bind_some, Option.map_some])
      have hwrite := execAction_atom_of_eval
        (by rw [hsig]; exact hd (f, args.length) List.mem_cons_self) hcols
      refine ⟨.app f is, m.addAtom (.app (viewName f) (is ++ [.app f is])),
        htarget, execActions_append_eq hm ?_, ?_⟩
      · simp only [execActions, hwrite, Option.bind_some]
      · exact .app (hviews.mono (Egglog.FDatabase.execAction_contained hwrite))
          (out_addAtom (execActions_subtermClosed hsc hm) (viewName f) is (.app f is))

@[inherit_doc encodeBuild_reads]
theorem encodeBuildArgs_reads {sig : Signature} {σ : Env} :
    ∀ (es : List Expr) {ts : List Term} {d : FDatabase}, d.SubtermClosed →
      Expr.OrderingFreeList es →
      (∀ f ∈ Expr.fnsList es, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ Expr.ctorsList es, (d.sig (viewName fk.1)).isSome = true) →
      Env.Reads d.toDatabase σ d.env → Expr.evalList sig es σ = some ts →
      ∃ is d', Expr.evalList d.sig es d.env = some is ∧
        execActions d (encodeBuildArgs es) = some d' ∧ ViewReprList d'.toDatabase ts is
  | [], _, d, _, _, _, _, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨[], d, rfl, rfl, .nil⟩
  | e :: es, _, d, hsc, hp, hc, hd, hρ, he => by
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨i, m, hi, hm, hv⟩ := encodeBuild_reads e hsc (Expr.orderingFreeList_cons hp).1
        (fun f hf => hc f (by simp [Expr.fnsList, hf]))
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) hρ ht
      have hsig := Egglog.FDatabase.execActions_sig hm
      have henv := Egglog.FDatabase.execActions_env hm
      obtain ⟨is, d', his, hr, hvs⟩ := encodeBuildArgs_reads (d := m) es
        (execActions_subtermClosed hsc hm) (Expr.orderingFreeList_cons hp).2
        (fun f hf hctor => by rw [hsig]; exact hc f (by simp [Expr.fnsList, hf]) hctor)
        (fun fk hk => by rw [hsig]; exact hd fk (by simp [Expr.ctorsList, hk]))
        (by rw [henv]; exact hρ.mono (Egglog.FDatabase.execActions_contained hm)) hts
      rw [hsig, henv] at his
      refine ⟨i :: is, d', ?_, execActions_append_eq hm hr,
        .cons (hv.mono (Egglog.FDatabase.execActions_contained hr)) hvs⟩
      simp only [Expr.evalList, hi, Option.bind_some, his, Option.map_some]

end

/-- The endpoint readings of an encoded union are joined by an explicit UF entry: the link
from the larger id, the other link being a self-loop. -/
theorem encodeUnion_reads {sig : Signature} {σ : Env} {a b : Expr} {ta tb : Term}
    {d : FDatabase} (hsc : d.SubtermClosed)
    (hp : ∀ e ∈ [a, b], e.OrderingFree)
    (hc : ∀ e ∈ [a, b], ∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ [a, b], ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d.toDatabase σ d.env)
    (ha : a.eval sig σ = some ta) (hb : b.eval sig σ = some tb) :
    ∃ i j d', execActions d (encodeAction (.union a b)) = some d' ∧
      ViewRepr d'.toDatabase ta i ∧ ViewRepr d'.toDatabase tb j ∧
      (d'.toDatabase.Out ufName [i] [j] ∨ d'.toDatabase.Out ufName [j] [i]) := by
  obtain ⟨i, m, hi, hm, hia⟩ := encodeBuild_reads a hsc
    (hp a (by simp)) (hc a (by simp)) (hd a (by simp)) hρ ha
  have hsig := Egglog.FDatabase.execActions_sig hm
  have henv := Egglog.FDatabase.execActions_env hm
  obtain ⟨j, n, hj, hn, hjb⟩ := encodeBuild_reads (d := m) b (execActions_subtermClosed hsc hm)
    (hp b (by simp))
    (fun f hf hctor => by rw [hsig]; exact hc b (by simp) f hf hctor)
    (fun fk hk => by rw [hsig]; exact hd b (by simp) fk hk)
    (by rw [henv]; exact hρ.mono (Egglog.FDatabase.execActions_contained hm)) hb
  have hbuild := execActions_append_eq hm hn
  rw [hsig, henv] at hj
  have hsig' := Egglog.FDatabase.execActions_sig hbuild
  have henv' := Egglog.FDatabase.execActions_env hbuild
  have hi' : a.eval n.sig n.env = some i := by rw [hsig', henv']; exact hi
  have hj' : b.eval n.sig n.env = some j := by rw [hsig', henv']; exact hj
  have hmin := eval_min_ids hi' hj'
  have hcols₁ : Expr.evalList n.sig [a, .min a b] n.env = some [i, lowerId i j] := by
    simp only [Expr.evalList, hi', hmin, Option.bind_some, Option.map_some]
  have huf' : (n.sig ufName).isSome = true := by rw [hsig']; exact huf
  have hwrite₁ := execAction_atom_of_eval huf' hcols₁
  have hcols₂ : Expr.evalList (n.addAtom (.app ufName [i, lowerId i j])).sig [b, .min a b]
      (n.addAtom (.app ufName [i, lowerId i j])).env = some [j, lowerId i j] := by
    change Expr.evalList n.sig [b, .min a b] n.env = _
    simp only [Expr.evalList, hj', hmin, Option.bind_some, Option.map_some]
  have hwrite₂ := execAction_atom_of_eval (d := n.addAtom (.app ufName [i, lowerId i j]))
    huf' hcols₂
  refine ⟨i, j, (n.addAtom (.app ufName [i, lowerId i j])).addAtom (.app ufName [j, lowerId i j]),
    execActions_append_eq hbuild ?_, ?_, ?_, ?_⟩
  · simp only [execActions, hwrite₁, Option.bind_some, hwrite₂]
  · exact ((hia.mono (Egglog.FDatabase.execActions_contained hn)).mono
      (Egglog.FDatabase.execAction_contained hwrite₁)).mono
      (Egglog.FDatabase.execAction_contained hwrite₂)
  · exact (hjb.mono (Egglog.FDatabase.execAction_contained hwrite₁)).mono
      (Egglog.FDatabase.execAction_contained hwrite₂)
  · have hscn : n.SubtermClosed := execActions_subtermClosed hsc hbuild
    have ho₁ := (out_addAtom hscn ufName [i] (lowerId i j)).mono
      (Egglog.FDatabase.execAction_contained hwrite₂)
    have ho₂ := out_addAtom (d := n.addAtom (.app ufName [i, lowerId i j])) (hscn.addAtom _)
      ufName [j] (lowerId i j)
    rcases ids_paired i j with ⟨-, hl⟩ | ⟨-, hl⟩
    · exact Or.inl (by simpa only [List.cons_append, List.nil_append, hl] using ho₁)
    · exact Or.inr (by simpa only [List.cons_append, List.nil_append, hl] using ho₂)

/-- Every successful source action has a successful compiled execution carrying its
new existence and union facts. This does not require rebuilding until the block ends. -/
theorem encodeAction_reads {src post : Database} {d : FDatabase} {a : Action}
    (hcs : src.sig.AllConstructors) (hsc : d.SubtermClosed)
    (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d.toDatabase src.env d.env)
    (h : SourceReads d.toDatabase src) (run : evalAction src a = some post) :
    ∃ d', execActions d (encodeAction a) = some d' ∧ SourceReads d'.toDatabase post := by
  rcases evalAction_eq_some run with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, _, rfl⟩
  · rw [Expr.evalAtom_eq_eval hcs] at he
    obtain ⟨i, d', _, hr, hv⟩ := encodeBuild_reads e hsc (hp e (by simp [actionExprs]))
      (hc e (by simp [actionExprs])) (hd e (by simp [actionExprs])) hρ he
    exact ⟨d', hr, (h.mono (Egglog.FDatabase.execActions_contained hr)).addTerm hv⟩
  · obtain ⟨i, j, d', hr, hi, hj, ho⟩ := encodeUnion_reads hsc hp hc hd huf hρ ha hb
    exact ⟨d', hr, (h.mono (Egglog.FDatabase.execActions_contained hr)).addEq hi hj ho⟩

/-- Rule heads and global action blocks execute while retaining all source facts. -/
theorem encodeActions_reads {src post : Database} {d : FDatabase} {as : List Action}
    (hcs : src.sig.AllConstructors) (hsc : d.SubtermClosed)
    (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d.toDatabase src.env d.env)
    (h : SourceReads d.toDatabase src) (run : evalActions src as = some post) :
    ∃ d', execActions d (encodeActions as) = some d' ∧ SourceReads d'.toDatabase post := by
  induction as generalizing src d with
  | nil =>
      obtain rfl := Option.some.inj run
      exact ⟨d, rfl, h⟩
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨m, hfirst, hmid⟩ := encodeAction_reads hcs hsc (hp a List.mem_cons_self)
        (hc a List.mem_cons_self) (hd a List.mem_cons_self) huf hρ h hm
      have hsig := Egglog.FDatabase.execActions_sig hfirst
      have henv := Egglog.FDatabase.execActions_env hfirst
      have hsrcsig := evalAction_sig hm
      have hsrcenv := evalAction_env hm
      obtain ⟨d', hrest, hpost⟩ := ih
        (by rw [hsrcsig]; exact hcs) (execActions_subtermClosed hsc hfirst)
        (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun a ha e he f hf hctor => by
          rw [hsig]; exact hc a (List.mem_cons_of_mem _ ha) e he f hf (hsrcsig ▸ hctor))
        (fun a ha e he fk hk => by
          rw [hsig]; exact hd a (List.mem_cons_of_mem _ ha) e he fk hk)
        (by rw [hsig]; exact huf)
        (by rw [hsrcenv, henv]; exact hρ.mono (Egglog.FDatabase.execActions_contained hfirst))
        hmid hr
      exact ⟨d', execActions_append_eq hfirst hrest, hpost⟩

end Egglog.Congruence
