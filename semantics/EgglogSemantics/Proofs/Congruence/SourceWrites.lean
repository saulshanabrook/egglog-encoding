import EgglogSemantics.Proofs.Congruence.ActionExprs

/-! Source justifications for the individual writes in a compiled action. -/

namespace Egglog.Congruence

/-- A top-level compiled write has an original constructor value or union justification. -/
inductive SourceAtom (src : Database) : Term → Prop where
  | view {f : FnName} {cs : List Term} : Term.app f cs ∈ src.terms →
      SourceAtom src (.app (viewName f) (cs ++ [.app f cs]))
  | uf {a b : Term} : StoredCong src a b → (b = a ∨ Term.blt b a = true) →
      SourceAtom src (.app ufName [a, b])

/-- The values of a compiled action block depend only on its signature and environment,
so merge phases can be interleaved without changing its original write justifications. -/
def SourceWrites (src : Database) (sig : Signature) (ρ : Env) (as : List Action) : Prop :=
  ∀ a ∈ as, ∃ e t, a = .expr e ∧ e.evalAtom sig ρ = some t ∧ SourceAtom src t

private theorem evalAtom_uf {sig : Signature} {ρ : Env} {a b : Expr} {ta tb : Term}
    (huf : sig ufName = some (tableDecl 1))
    (ha : a.eval sig ρ = some ta) (hb : b.eval sig ρ = some tb) :
    (Expr.app ufName [a, b]).evalAtom sig ρ = some (.app ufName [ta, tb]) := by
  rw [Expr.evalAtom_app_decl huf (Or.inr rfl)]
  simp only [Expr.evalList, ha, hb, Option.bind_some, Option.map_some]

private theorem ufSelf_sourceWrites {src : Database} {sig : Signature} {ρ : Env}
    {e : Expr} {t : Term} (huf : sig ufName = some (tableDecl 1))
    (he : e.eval sig ρ = some t) (ht : t ∈ src.terms) :
    SourceWrites src sig ρ [.expr (.app ufName [e, e])] := by
  intro a ha
  obtain rfl := List.mem_singleton.mp ha
  exact ⟨_, _, rfl, evalAtom_uf huf he he, .uf ht (Or.inl rfl)⟩

mutual

/-- Every atom emitted by a global build is justified by a subterm of the source result. -/
theorem encodeBuild_sourceWrites {src : Database} (hw : src.WF) {sig : Signature} {ρ : Env}
    (huf : sig ufName = some (tableDecl 1)) :
    ∀ (e : Expr) {t : Term}, e.OrderingFree →
      (∀ fk ∈ e.ctors, sig (viewName fk.1) = some (tableDecl fk.2)) →
      e.eval sig ρ = some t → t ∈ src.terms → SourceWrites src sig ρ (encodeBuild e)
  | .lit _, _, _, _, he, ht => ufSelf_sourceWrites huf he ht
  | .var _, _, _, _, he, ht => ufSelf_sourceWrites huf he ht
  | .min _ _, _, hp, _, _, _ => (Expr.not_orderingFree_min hp).elim
  | .ite _ _ _ _, _, hp, _, _, _ => (Expr.not_orderingFree_ite hp).elim
  | .app f args, _, hp, hd, he, ht => by
      have hctor : sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hn] at he
        contradiction
      rw [Expr.eval_app_ctor hctor] at he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      have hl := encodeBuildArgs_sourceWrites hw huf args (Expr.orderingFree_app hp)
        (fun fk hk => hd fk (List.mem_cons_of_mem _ hk)) hts
        (fun t ht' => hw.subtermClosed _ ht (Term.arg_subterms ht' (Term.self_mem_subterms t)))
      have hval : (Expr.app f args).eval sig ρ = some (.app f ts) := by
        rw [Expr.eval_app_ctor hctor, hts]; rfl
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hl a ha
      · rcases List.mem_cons.mp ha with rfl | ha
        · refine ⟨_, .app (viewName f) (ts ++ [.app f ts]), rfl, ?_, .view ht⟩
          have hcols : Expr.evalList sig (args ++ [.app f args]) ρ =
              some (ts ++ [.app f ts]) := by
            rw [Expr.evalList_append_map, hts]
            simp only [Expr.evalList, hval, Option.bind_some, Option.map_some]
          rw [Expr.evalAtom_app_decl (hd (f, args.length) List.mem_cons_self)
            (Or.inr (by simp [tableDecl, FnDecl.entryWidth])), hcols]
          rfl
        · exact ufSelf_sourceWrites huf hval ht a ha

@[inherit_doc encodeBuild_sourceWrites]
theorem encodeBuildArgs_sourceWrites {src : Database} (hw : src.WF)
    {sig : Signature} {ρ : Env} (huf : sig ufName = some (tableDecl 1)) :
    ∀ (es : List Expr) {ts : List Term}, Expr.OrderingFreeList es →
      (∀ fk ∈ Expr.ctorsList es, sig (viewName fk.1) = some (tableDecl fk.2)) →
      Expr.evalList sig es ρ = some ts → (∀ t ∈ ts, t ∈ src.terms) →
      SourceWrites src sig ρ (encodeBuildArgs es)
  | [], _, _, _, _, _ => by intro a ha; cases ha
  | e :: es, _, hp, hd, he, ht => by
      obtain ⟨t, ht', he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      have hfirst := encodeBuild_sourceWrites hw huf e (Expr.orderingFreeList_cons hp).1
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) ht' (ht t List.mem_cons_self)
      have hrest := encodeBuildArgs_sourceWrites hw huf es (Expr.orderingFreeList_cons hp).2
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) hts
        (fun t ht' => ht t (List.mem_cons_of_mem _ ht'))
      intro a ha
      exact (List.mem_append.mp ha).elim (hfirst a) (hrest a)

end

theorem SourceWrites.append {src : Database} {sig : Signature} {ρ : Env} {as bs : List Action}
    (ha : SourceWrites src sig ρ as) (hb : SourceWrites src sig ρ bs) :
    SourceWrites src sig ρ (as ++ bs) := fun a h => (List.mem_append.mp h).elim (ha a) (hb a)

/-- Both UF links and all operand builds come from the asserted source union. -/
theorem encodeUnion_sourceWrites {src : Database} (hw : src.WF) {sig : Signature} {ρ : Env}
    {a b : Expr} {ta tb : Term}
    (hp : ∀ e ∈ [a, b], e.OrderingFree)
    (hd : ∀ e ∈ [a, b], ∀ fk ∈ e.ctors, sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : sig ufName = some (tableDecl 1))
    (ha : a.eval sig ρ = some ta) (hb : b.eval sig ρ = some tb) (hc : StoredCong src ta tb) :
    SourceWrites src sig ρ (encodeAction (.union a b)) := by
  apply SourceWrites.append
    ((encodeBuild_sourceWrites hw huf a (hp a (by simp)) (hd a (by simp)) ha hc.mem_of.1).append
      (encodeBuild_sourceWrites hw huf b (hp b (by simp)) (hd b (by simp)) hb hc.mem_of.2))
  intro act hact
  have hmin := eval_min_ids ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hact
  rcases hact with rfl | rfl
  · refine ⟨_, .app ufName [ta, lowerId ta tb], rfl, ?_,
      .uf (cong_lowerId_left hc) (lowerId_le_left ..)⟩
    exact evalAtom_uf huf ha hmin
  · refine ⟨_, .app ufName [tb, lowerId ta tb], rfl, ?_,
      .uf (cong_lowerId_right hc) (lowerId_le_right ..)⟩
    exact evalAtom_uf huf hb hmin

/-- Ground source facts justify compiled actions independently of a source execution. -/
def SourceAction (src : Database) (sig : Signature) (ρ : Env) : Action → Prop
  | .expr e => ∃ t, e.eval sig ρ = some t ∧ t ∈ src.terms
  | .union a b => ∃ ta tb, a.eval sig ρ = some ta ∧ b.eval sig ρ = some tb ∧ StoredCong src ta tb

theorem SourceAction.mono {src post : Database} {sig : Signature} {ρ : Env} {a : Action}
    (hc : src.Contained post) (h : SourceAction src sig ρ a) : SourceAction post sig ρ a := by
  cases a with
  | expr e => obtain ⟨t, he, ht⟩ := h; exact ⟨t, he, hc.terms ht⟩
  | union a b => obtain ⟨ta, tb, ha, hb, he⟩ := h; exact ⟨ta, tb, ha, hb, he.mono hc⟩

theorem sourceAction_of_evalAction {src post : Database} {a : Action}
    (hc : src.sig.AllConstructors) (hr : evalAction src a = some post) :
    SourceAction post src.sig src.env a := by
  rcases evalAction_eq_some hr with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, _, rfl⟩
  · exact ⟨t, by simpa only [Expr.evalAtom_eq_eval hc] using he, Database.mem_addTerm t src⟩
  · exact ⟨ta, tb, ha, hb, .direct (Set.mem_insert _ _)⟩

theorem sourceActions_of_evalActions {src post : Database} {as : List Action}
    (hc : src.sig.AllConstructors) (hr : evalActions src as = some post) :
    ∀ a ∈ as, SourceAction post src.sig src.env a := by
  induction as generalizing src with
  | nil => simp
  | cons a as ih =>
      obtain ⟨mid, hm, ht⟩ := Option.bind_eq_some_iff.mp hr
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (sourceAction_of_evalAction hc hm).mono (evalActions_contained ht)
      · have hs : mid.sig = src.sig := evalAction_sig hm
        have he : mid.env = src.env := evalAction_env hm
        simpa only [hs, he] using ih (by rw [hs]; exact hc) ht b hb

theorem encodeAction_sourceWrites_of_justified {src : Database} {sig : Signature} {ρ : Env}
    (hw : src.WF) {a : Action} (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : sig ufName = some (tableDecl 1)) (hs : SourceAction src sig ρ a) :
    SourceWrites src sig ρ (encodeAction a) := by
  cases a with
  | expr e =>
      obtain ⟨t, he, ht⟩ := hs
      exact encodeBuild_sourceWrites hw huf e (hp e (by simp [actionExprs]))
        (hd e (by simp [actionExprs])) he ht
  | union a b =>
      obtain ⟨ta, tb, ha, hb, hc⟩ := hs
      exact encodeUnion_sourceWrites hw hp hd huf ha hb hc

theorem encodeActions_sourceWrites_of_justified {src : Database} {sig : Signature} {ρ : Env}
    (hw : src.WF) {as : List Action}
    (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hd : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : sig ufName = some (tableDecl 1)) (hs : ∀ a ∈ as, SourceAction src sig ρ a) :
    SourceWrites src sig ρ (encodeActions as) := by
  intro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  exact encodeAction_sourceWrites_of_justified hw (hp b hb) (hd b hb) huf (hs b hb) a ha

/-- An original action's successful result justifies every atom of its compiled block. -/
theorem encodeAction_sourceWrites {src post : Database} {sig : Signature} {ρ : Env}
    (hw : post.WF) (hcs : src.sig.AllConstructors) {a : Action}
    (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : sig ufName = some (tableDecl 1))
    (heval : ∀ e ∈ actionExprs a, ∀ t, e.eval src.sig src.env = some t → e.eval sig ρ = some t)
    (run : evalAction src a = some post) : SourceWrites post sig ρ (encodeAction a) := by
  rcases evalAction_eq_some run with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, _, rfl⟩
  · rw [Expr.evalAtom_eq_eval hcs] at he
    exact encodeBuild_sourceWrites hw huf e (hp e (by simp [actionExprs]))
      (hd e (by simp [actionExprs])) (heval e (by simp [actionExprs]) _ he)
      (Database.mem_addTerm t src)
  · exact encodeUnion_sourceWrites hw hp hd huf
      (heval a (by simp [actionExprs]) _ ha)
      (heval b (by simp [actionExprs]) _ hb) (StoredCong.direct (Set.mem_insert _ _))

theorem SourceAtom.mono {src post : Database} (hc : src.Contained post) {t : Term}
    (h : SourceAtom src t) : SourceAtom post t := by
  cases h with
  | view ht => exact .view (hc.terms ht)
  | uf he hd => exact .uf (he.mono hc) hd

theorem SourceWrites.mono {src post : Database} {sig : Signature} {ρ : Env}
    {as : List Action} (hc : src.Contained post) (h : SourceWrites src sig ρ as) :
    SourceWrites post sig ρ as := by
  intro a ha
  obtain ⟨e, t, rfl, hev, ht⟩ := h a ha
  exact ⟨e, t, rfl, hev, ht.mono hc⟩

/-- A source block's final state justifies all generated writes, including earlier actions. -/
theorem encodeActions_sourceWrites {src post : Database} {sig : Signature} {ρ : Env}
    (hw : src.WF) (hcs : src.sig.AllConstructors) {as : List Action}
    (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hd : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : sig ufName = some (tableDecl 1))
    (heval : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ t,
      e.eval src.sig src.env = some t → e.eval sig ρ = some t)
    (run : evalActions src as = some post) : SourceWrites post sig ρ (encodeActions as) := by
  induction as generalizing src with
  | nil => intro a ha; cases ha
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp run
      have hsig := evalAction_sig hm
      have henv := evalAction_env hm
      have hwm := evalAction_wf hw hm
      have hfirst := encodeAction_sourceWrites hwm hcs (hp a List.mem_cons_self)
        (hd a List.mem_cons_self) huf (heval a List.mem_cons_self) hm
      apply (hfirst.mono (evalActions_contained hr)).append
      apply ih hwm (by rw [hsig]; exact hcs)
        (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun a ha => hd a (List.mem_cons_of_mem _ ha))
      · intro a ha e he t ht
        rw [hsig, henv] at ht
        exact heval a (List.mem_cons_of_mem _ ha) e he t ht
      · exact hr

end Egglog.Congruence
