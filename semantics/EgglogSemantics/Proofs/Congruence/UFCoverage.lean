import EgglogSemantics.Proofs.Congruence.AbstractRuntime
import EgglogSemantics.Proofs.Congruence.AbstractWrites
import EgglogSemantics.Proofs.Congruence.AbstractMerge
import EgglogSemantics.Proofs.Congruence.LiveCoverage
import EgglogSemantics.Proofs.Congruence.AbstractMaintenanceDescent

/-! Complete source writes give every held value a current UF parent. -/

namespace Egglog.Congruence.Live

open Abstract

def HasUF (d : Database) (t : Term) : Prop := ∃ u, ufEntry t u ∈ d.entries

def UFTotal (d : Database) : Prop := ∀ t ∈ d.values, HasUF d t

theorem UFTotal.out {d : Database} (h : UFTotal d) (hs : d.StoreOk) :
    ∀ t ∈ d.values, ∃ u, d.Out ufName [t] [u] := by
  intro t ht
  obtain ⟨u, hu⟩ := h t ht
  exact ⟨u, out_of_current hs hu⟩

theorem HasUF.mono {d e : Database} (hc : d.entries ⊆ e.entries) {t : Term}
    (h : HasUF d t) : HasUF e t := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, hc hu⟩

theorem Covers.hasUF {d e : Database} (h : Covers d e) {t : Term}
    (ht : HasUF d t) : HasUF e t := by
  obtain ⟨u, hu⟩ := ht
  obtain ⟨v, hv, _⟩ := h.rows ufName [t] u hu
  exact ⟨v, hv⟩

theorem UFTotal.of_covers {d e : Database} (h : UFTotal d) (hc : Covers d e)
    (hv : e.values ⊆ d.values) : UFTotal e := fun t ht => hc.hasUF (h t (hv ht))

theorem values_addTerm_bound {d ref : Database} {t : Term} (hsig : d.sig = ref.sig)
    (hd : d.values ⊆ ref.values)
    (ht : ∀ s ∈ t.subterms, s.IsValue ref.sig → s ∈ ref.terms) :
    (d.addTerm t).values ⊆ ref.values := by
  intro s hs
  have hv : s.IsValue ref.sig := hsig ▸ hs.2
  rcases Database.addTerm_terms ▸ hs.1 with hm | hm
  · exact hd ⟨hm, hs.2⟩
  · exact ⟨ht s hm hv, hv⟩

theorem row_value_subterms {ref : Database} (hw : ref.WF) {row : Entry}
    (hv : row.Valid ref.sig) (hc : ∀ c ∈ row.columns, c ∈ ref.terms) :
    ∀ s ∈ row.atom.subterms, s.IsValue ref.sig → s ∈ ref.terms := by
  intro s hs hv'
  apply subterms_of_columns hw hc hs
  intro he
  exact hv.atom_not_value (by simpa only [Entry.atom, he] using hv')

theorem mergeStep_values_subset {d e : Database} (h : Runtime d)
    (hshape : MergeShape d.sig) (hm : MergeStep d e) : e.values ⊆ d.values := by
  obtain ⟨f, cs, a, b, hra, hrb, _, rfl⟩ :=
    mergeStep_form hshape h.noUnions.diag h.state.uf hm
  have ha := h.storeOk.columns _ hra a (by simp [Entry.columns])
  have hb := h.storeOk.columns _ hrb b (by simp [Entry.columns])
  have hva := (h.storeOk.entry_valid hra).output_values a (by simp)
  have hvb := (h.storeOk.entry_valid hrb).output_values b (by simp)
  have hvmin : (lowerId a b).IsValue d.sig := hva.least hvb
  have hmin : lowerId a b ∈ d.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  have hbase : ((d.eraseEntry ⟨f, cs, [a]⟩).eraseEntry ⟨f, cs, [b]⟩).values ⊆ d.values := by
    intro t ht
    refine ⟨Database.terms_eraseEntry_subset (h.storeOk.columns _ hra) (?_) , ht.2⟩
    exact Database.terms_eraseEntry_subset (fun s hs =>
      Database.mem_terms_eraseEntry_of_value (h.storeOk.entry_valid hra)
        ((h.storeOk.entry_valid hrb).column_values s hs)
        (h.storeOk.columns _ hrb s hs)) ht.1
  have hlink (x : Term) (hx : x ∈ d.terms) (hvx : x.IsValue d.sig) :
      ∀ t ∈ (Term.app ufName [x, lowerId a b]).subterms,
        t.IsValue d.sig → t ∈ d.terms := by
    apply row_value_subterms h.wf (ufEntry_valid h.state.uf hvx hvmin)
    simpa [ufEntry, Entry.columns] using And.intro hx hmin
  let base := (d.eraseEntry ⟨f, cs, [a]⟩).eraseEntry ⟨f, cs, [b]⟩
  have h₁ := values_addTerm_bound (d := base) (ref := d) rfl hbase (hlink a ha hva)
  have h₂ := values_addTerm_bound (d := base.addTerm (.app ufName [a, lowerId a b]))
    (ref := d) rfl h₁ (hlink b hb hvb)
  apply values_addTerm_bound (d := mergeLinks base a b) (ref := d) rfl h₂
  intro t ht _
  apply h.wf.subtermClosed _ ?_ ht
  rcases lowerId_eq_or a b with he | he
  · rw [he]; exact (StoredCong.direct hra.2).toHeld
  · rw [he]; exact (StoredCong.direct hrb.2).toHeld

theorem mergeClosure_values_subset {d e : Database} (h : Runtime d)
    (hshape : MergeShape d.sig) (hm : MergeClosure d e) : e.values ⊆ d.values := by
  induction hm with
  | refl => exact Set.Subset.refl _
  | tail hc hs ih =>
      exact (mergeStep_values_subset (h.merge hc)
        (by rw [MergeClosure.sig hc]; exact hshape) hs).trans ih

theorem UFTotal.merge {d e : Database} (h : UFTotal d) (hr : Runtime d)
    (hshape : MergeShape d.sig) (hm : MergeClosure d e) : UFTotal e :=
  h.of_covers (Covers.mergeClosure hr.state hr.noUnions.diag hm)
    (mergeClosure_values_subset hr hshape hm)

private theorem entries_addTerm (d : Database) (t : Term) :
    d.entries ⊆ (d.addTerm t).entries :=
  fun _ hr => Database.mem_addTerm_entries.mpr (Or.inl hr)

private theorem value_subterm_row {sig : Signature} {row : Entry} (hr : row.Valid sig)
    {s : Term} (hs : s ∈ row.atom.subterms) (hv : s.IsValue sig) :
    ∃ c ∈ row.columns, s ∈ c.subterms := by
  change Term.IsSubterm s (.app row.name row.columns) at hs
  cases hs with
  | refl => exact (hr.atom_not_value hv).elim
  | arg hc hs => exact ⟨_, hc, hs⟩

private theorem complete_self {base d : Database} {t : Term}
    (_hsig : base.sig = d.sig) (hc : base.entries ⊆ d.entries) (h : UFTotal base)
    (huf : d.sig ufName = some (tableDecl 1)) (hv : t.IsValue d.sig)
    (hd : d.values ⊆ insert t base.values)
    (hp : ∀ s ∈ t.subterms, s = t ∨ s ∈ base.values) :
    UFTotal (d.addTerm (ufEntry t t).atom) ∧
      t ∈ (d.addTerm (ufEntry t t).atom).values := by
  have hrow : ufEntry t t ∈ (d.addTerm (ufEntry t t).atom).entries :=
    Database.mem_addTerm_entries.mpr (Or.inr ⟨(ufEntry_valid huf hv hv).shape, .refl _⟩)
  have hcover : ∀ s, s = t ∨ s ∈ base.values → HasUF (d.addTerm (ufEntry t t).atom) s := by
    intro s hs
    rcases hs with rfl | hs
    · exact ⟨_, hrow⟩
    · exact (h s hs).mono (hc.trans (entries_addTerm _ _))
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases Database.addTerm_terms ▸ hs.1 with hs' | hs'
    · exact hcover s (hd ⟨hs', hs.2⟩)
    · obtain ⟨c, hc', hs'⟩ := value_subterm_row (ufEntry_valid huf hv hv) hs' hs.2
      have he : c = t := by simpa [ufEntry, Entry.columns] using hc'
      exact hcover s (hp s (he ▸ hs'))
  · refine ⟨?_, hv⟩
    rw [Database.addTerm_terms]
    exact Or.inr (Term.arg_subterms (by simp [ufEntry, Entry.columns]) (.refl t))

private theorem self_write {d : Database} {x : Expr} {t : Term}
    (huf : d.sig ufName = some (tableDecl 1)) (he : x.eval d.sig d.env = some t) :
    evalActions d [.expr (.app ufName [x, x])] = some (d.addTerm (ufEntry t t).atom) := by
  have hev := Expr.evalAtom_app_decl (cols := [x, x]) (σ := d.env) huf (Or.inr rfl)
  simp only [Expr.evalList, he, Option.bind_some, Option.map_some] at hev
  simp only [evalActions, evalAction, hev, Option.map_some, Option.bind_some]
  rfl

private theorem evalActions_append_build {d m e : Database} {as bs : List Action}
    (ha : evalActions d as = some m) (hb : evalActions m bs = some e) :
    evalActions d (as ++ bs) = some e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj ha; exact hb
  | cons a as ih =>
      obtain ⟨n, hn, ha⟩ := Option.bind_eq_some_iff.mp ha
      simpa only [List.cons_append, evalActions, hn, Option.bind_some] using ih ha

mutual

theorem encodeBuild_ufTotal : ∀ (x : Expr) {d : Database} {t : Term},
    d.WF → (∀ b ∈ d.env, b.2.IsValue d.sig) → UFTotal d → x.OrderingFree →
    (∀ fk ∈ x.ctors, d.sig (viewName fk.1) = some (tableDecl fk.2)) →
    d.sig ufName = some (tableDecl 1) → x.eval d.sig d.env = some t →
    ∃ e, evalActions d (encodeBuild x) = some e ∧ UFTotal e ∧ t ∈ e.values
  | .lit l, d, t, _, _, hu, _, _, huf, he => by
      obtain rfl := Option.some.inj he
      refine ⟨_, self_write huf rfl, complete_self rfl (Set.Subset.refl _) hu huf
        (.lit _ l) (fun _ ht => Or.inr ht) ?_⟩
      intro s hs
      exact Or.inl (by simpa using hs)
  | .var v, d, t, hw, hv, hu, _, _, huf, he => by
      have ht := hw.envInTerms (v, t) (Env.mem_of_lookup he)
      have hv := Expr.eval_isValue hv he
      refine ⟨_, self_write huf he, complete_self rfl (Set.Subset.refl _) hu huf hv
        (fun _ ht => Or.inr ht) ?_⟩
      exact fun s hs => Or.inr ⟨hw.subtermClosed _ ht hs, hv.subterm hs⟩
  | .min _ _, _, _, _, _, _, hp, _, _, _ => (Expr.not_orderingFree_min hp).elim
  | .ite _ _ _ _, _, _, _, _, _, hp, _, _, _ => (Expr.not_orderingFree_ite hp).elim
  | .app f xs, d, t, hw, hv, hu, hp, hd, huf, he => by
      have hctor : d.sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hn] at he
        contradiction
      rw [Expr.eval_app_ctor hctor] at he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨m, hm, hum, hheld⟩ := encodeBuildArgs_ufTotal xs hw hv hu
        (Expr.orderingFree_app hp) (fun fk hk => hd fk (List.mem_cons_of_mem _ hk)) huf hts
      have hsig := evalActions_sig hm
      have henv := evalActions_env hm
      have hwm := evalActions_wf hw hm
      have hval : (Term.app f ts).IsValue m.sig := by
        rw [hsig]; exact .app hctor (Expr.evalList_isValue hv hts)
      have hproper : ∀ s ∈ (Term.app f ts).subterms,
          s = .app f ts ∨ s ∈ m.values := by
        intro s hs
        cases hs with
        | refl => exact Or.inl rfl
        | arg hc hs => exact Or.inr ⟨hwm.subtermClosed _ (hheld _ hc).1 hs,
            (hheld _ hc).2.subterm hs⟩
      have hview : m.sig (viewName f) = some (tableDecl ts.length) := by
        rw [hsig, Expr.evalList_length hts]
        exact hd (f, xs.length) List.mem_cons_self
      let row : Entry := ⟨viewName f, ts, [.app f ts]⟩
      have hrow : row.Valid m.sig := by
        refine ⟨tableDecl ts.length, hview, by simp [tableDecl], rfl, rfl, ?_⟩
        intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · exact (hheld s hs).2
        · exact List.mem_singleton.mp hs ▸ hval
      have htarget : (Expr.app f xs).eval m.sig m.env = some (.app f ts) := by
        rw [hsig, henv, Expr.eval_app_ctor hctor, hts]; rfl
      have hcols : Expr.evalList m.sig (xs ++ [.app f xs]) m.env =
          some (ts ++ [.app f ts]) := by
        rw [Expr.evalList_append_map, hsig, henv, hts]
        simp only [Expr.evalList, hsig, henv] at htarget ⊢
        simp only [htarget, Option.bind_some, Option.map_some]
      have hwrite : evalAction m (.expr (.app (viewName f) (xs ++ [.app f xs]))) =
          some (m.addTerm row.atom) := by
        rw [evalAction, Expr.evalAtom_app_decl hview (Or.inr (by
          simp [tableDecl, FnDecl.entryWidth, Expr.evalList_length hts])), hcols]
        rfl
      have hbound : (m.addTerm row.atom).values ⊆ insert (.app f ts) m.values := by
        intro s hs
        rcases Database.addTerm_terms ▸ hs.1 with hs' | hs'
        · exact Or.inr ⟨hs', hs.2⟩
        · obtain ⟨c, hc, hsc⟩ := value_subterm_row hrow hs' hs.2
          apply hproper s
          apply Term.subterms_subset_of_mem (t := .app f ts) ?_ hsc
          rcases List.mem_append.mp hc with hc | hc
          · exact .arg hc (.refl c)
          · exact List.mem_singleton.mp hc ▸ Term.self_mem_subterms _
      have huf' : m.sig ufName = some (tableDecl 1) := by rw [hsig]; exact huf
      have hself := self_write (d := m.addTerm row.atom) huf' htarget
      refine ⟨_, evalActions_append_build hm ?_,
        complete_self (base := m) (d := m.addTerm row.atom) rfl
          (entries_addTerm _ _) hum huf' hval hbound hproper⟩
      change evalActions m
        ([.expr (.app (viewName f) (xs ++ [.app f xs]))] ++
          [.expr (.app ufName [.app f xs, .app f xs])]) = _
      exact evalActions_append_build (by simp only [evalActions, hwrite, Option.bind_some]) hself

theorem encodeBuildArgs_ufTotal : ∀ (xs : List Expr) {d : Database} {ts : List Term},
    d.WF → (∀ b ∈ d.env, b.2.IsValue d.sig) → UFTotal d → Expr.OrderingFreeList xs →
    (∀ fk ∈ Expr.ctorsList xs, d.sig (viewName fk.1) = some (tableDecl fk.2)) →
    d.sig ufName = some (tableDecl 1) → Expr.evalList d.sig xs d.env = some ts →
    ∃ e, evalActions d (encodeBuildArgs xs) = some e ∧
      UFTotal e ∧ ∀ t ∈ ts, t ∈ e.values
  | [], d, _, _, _, hu, _, _, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨d, rfl, hu, by simp⟩
  | x :: xs, d, _, hw, hv, hu, hp, hd, huf, he => by
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨m, hm, hum, htm⟩ := encodeBuild_ufTotal x hw hv hu
        (Expr.orderingFreeList_cons hp).1 (fun fk hk => hd fk (by simp [Expr.ctorsList, hk]))
        huf ht
      have hsig := evalActions_sig hm
      have henv := evalActions_env hm
      obtain ⟨e, hr, hue, hheld⟩ := encodeBuildArgs_ufTotal xs (evalActions_wf hw hm)
        (by simpa only [hsig, henv] using hv) hum
        (Expr.orderingFreeList_cons hp).2
        (fun fk hk => by rw [hsig]; exact hd fk (by simp [Expr.ctorsList, hk]))
        (by rw [hsig]; exact huf) (by rw [hsig, henv]; exact hts)
      refine ⟨e, evalActions_append_build hm hr, hue, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨(evalActions_contained hr).terms htm.1, by rw [evalActions_sig hr]; exact htm.2⟩
      · exact hheld s hs

end

theorem UFTotal.addRow {d : Database} (h : UFTotal d) (hw : d.WF) {row : Entry}
    (hv : row.Valid d.sig) (hc : ∀ t ∈ row.columns, t ∈ d.terms) :
    UFTotal (d.addTerm row.atom) :=
  h.of_covers (Covers.of_entries rfl (entries_addTerm _ _))
    (values_addTerm_bound (d := d) (ref := d) rfl (Set.Subset.refl _)
      (row_value_subterms hw hv hc))

private theorem uf_write {d : Database} {x y : Expr} {a b : Term}
    (huf : d.sig ufName = some (tableDecl 1))
    (hx : x.eval d.sig d.env = some a) (hy : y.eval d.sig d.env = some b) :
    evalAction d (.expr (.app ufName [x, y])) = some (d.addTerm (ufEntry a b).atom) := by
  have hev := Expr.evalAtom_app_decl (cols := [x, y]) (σ := d.env) huf (Or.inr rfl)
  simp only [Expr.evalList, hx, hy, Option.bind_some, Option.map_some] at hev
  rw [evalAction, hev]
  rfl

private theorem evalActions_append_uf (d : Database) (as bs : List Action) :
    evalActions d (as ++ bs) = (evalActions d as).bind (fun e => evalActions e bs) := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, evalActions, ih]
      cases evalAction d a <;> rfl

theorem encodeAction_ufTotal {d e : Database} {a : Action}
    (hw : d.WF) (hv : ∀ b ∈ d.env, b.2.IsValue d.sig) (hu : UFTotal d)
    (hp : ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (heval : ∀ x ∈ actionExprs a, ∃ t, x.eval d.sig d.env = some t)
    (hr : evalActions d (encodeAction a) = some e) : UFTotal e := by
  cases a with
  | expr x =>
      obtain ⟨t, ht⟩ := heval x (by simp [actionExprs])
      obtain ⟨post, hp', hu', _⟩ := encodeBuild_ufTotal x hw hv hu
        (hp x (by simp [actionExprs])) (hd x (by simp [actionExprs])) huf ht
      obtain rfl := Option.some.inj (hp'.symm.trans hr)
      exact hu'
  | union x y =>
      obtain ⟨tx, hx⟩ := heval x (by simp [actionExprs])
      obtain ⟨ty, hy⟩ := heval y (by simp [actionExprs])
      obtain ⟨m, hm, hum, htx⟩ := encodeBuild_ufTotal x hw hv hu
        (hp x (by simp [actionExprs])) (hd x (by simp [actionExprs])) huf hx
      have hsig := evalActions_sig hm
      have henv := evalActions_env hm
      obtain ⟨n, hn, hun, hty⟩ := encodeBuild_ufTotal y (evalActions_wf hw hm)
        (by simpa only [hsig, henv] using hv) hum
        (hp y (by simp [actionExprs]))
        (fun fk hk => by rw [hsig]; exact hd y (by simp [actionExprs]) fk hk)
        (by rw [hsig]; exact huf) (by rw [hsig, henv]; exact hy)
      have hb := evalActions_append_build hm hn
      have hs := evalActions_sig hb
      have he := evalActions_env hb
      have hxn : x.eval n.sig n.env = some tx := by rw [hs, he]; exact hx
      have hyn : y.eval n.sig n.env = some ty := by rw [hs, he]; exact hy
      have hmin := eval_min_ids hxn hyn
      have huf' : n.sig ufName = some (tableDecl 1) := by rw [hs]; exact huf
      have ht : tx ∈ n.values := ⟨(evalActions_contained hn).terms htx.1,
        by rw [evalActions_sig hn]; exact htx.2⟩
      have hl : lowerId tx ty ∈ n.values := by
        rcases lowerId_eq_or tx ty with heq | heq <;> rw [heq] <;> assumption
      have hwrite₁ := uf_write huf' hxn hmin
      have hwrite₂ := uf_write (d := n.addTerm (ufEntry tx (lowerId tx ty)).atom) huf' hyn hmin
      rw [encodeAction, evalActions_append_uf, hb, Option.bind_some,
        evalActions, hwrite₁, Option.bind_some, evalActions, hwrite₂, Option.bind_some,
        evalActions] at hr
      obtain rfl := Option.some.inj hr
      have hwn := evalActions_wf hw hb
      have hu₁ := hun.addRow hwn (ufEntry_valid huf' ht.2 hl.2)
        (by simpa [ufEntry, Entry.columns] using And.intro ht.1 hl.1)
      exact hu₁.addRow (hwn.addTerm _) (ufEntry_valid huf' hty.2 hl.2) (by
        intro t ht'
        have ht'' : t = ty ∨ t = lowerId tx ty := by
          simpa [ufEntry, Entry.columns] using ht'
        exact (Database.Contained.addTerm _ _).terms
          (ht''.elim (fun heq => heq ▸ hty.1) (fun heq => heq ▸ hl.1)))

theorem encodeActions_ufTotal {d e : Database} {as : List Action}
    (hw : d.WF) (hv : ∀ b ∈ d.env, b.2.IsValue d.sig) (hu : UFTotal d)
    (hp : ∀ a ∈ as, ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (heval : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∃ t, x.eval d.sig d.env = some t)
    (hr : evalActions d (encodeActions as) = some e) : UFTotal e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj hr; exact hu
  | cons a as ih =>
      change evalActions d (encodeAction a ++ encodeActions as) = some e at hr
      rw [evalActions_append_uf] at hr
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp hr
      have hum := encodeAction_ufTotal hw hv hu (hp a List.mem_cons_self)
        (hd a List.mem_cons_self) huf (heval a List.mem_cons_self) hm
      have hs := evalActions_sig hm
      have he := evalActions_env hm
      exact ih (evalActions_wf hw hm)
        (by simpa only [evalActions_sig hm, evalActions_env hm] using hv) hum
        (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun a ha x hx fk hk => hs ▸ hd a (List.mem_cons_of_mem _ ha) x hx fk hk)
        (hs ▸ huf)
        (fun a ha x hx => by rw [hs, he]; exact heval a (List.mem_cons_of_mem _ ha) x hx) hr

theorem encodeLocalActions_ufTotal {d e : Database} {as : List Action} {ρ : Env}
    (hw : d.WF) (hu : UFTotal d)
    (hρ : ∀ b ∈ ρ, b.2 ∈ d.terms)
    (hρv : ∀ b ∈ ρ, b.2.IsValue d.sig)
    (hp : ∀ a ∈ as, ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (heval : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∃ t, x.eval d.sig (ρ) = some t)
    (hr : evalLocalActions d (encodeActions as) ρ = some e) : UFTotal e := by
  obtain ⟨post, hp', rfl⟩ := Option.map_eq_some_iff.mp hr
  have hi := encodeActions_ufTotal (d := { d with env := ρ })
    (hw.appendEnv hρ)
    hρv
    (by simpa only [UFTotal, HasUF, Database.values,
      Database.terms_setEnv, Database.entries] using hu) hp hd huf heval hp'
  simpa only [UFTotal, HasUF, Database.values, Database.terms_setEnvRules,
    Database.entries] using hi

theorem UFTotal.localFlat {d e : Database} {q : Query} {ρ : Env}
    {f : FnName} {xs : List Expr} (h : UFTotal d) (hw : d.WF)
    (hf : ¬ d.sig.IsCtor f) (hvars : ∀ x ∈ xs, ∃ v, x = Expr.var v)
    (hρ : ValidQuerySubst d q ρ)
    (hr : evalLocalActions d [.expr (.app f xs)] ρ = some e) : UFTotal e := by
  obtain ⟨ts, us, hts, hus, hterms⟩ := evalLocalActions_entry (args := xs) (out := [])
    (by simpa using hr)
  obtain rfl : us = [] := (Option.some.inj hus).symm
  have henv : ∀ b ∈ ρ, b.2 ∈ d.terms := hρ.mem_terms
  have hcols := evalList_vars_held henv xs hvars hts
  apply h.of_covers (Covers.of_entries (evalLocalActions_sig hr).symm
    (evalLocalActions_entries_subset hr))
  intro t ht
  have hv : t.IsValue d.sig := (evalLocalActions_sig hr) ▸ ht.2
  have hm := hterms ht.1
  rw [Database.addTerm_terms] at hm
  rcases hm with hm | hm
  · exact ⟨hm, hv⟩
  · have hm' : t ∈ (Term.app f ts).subterms := by simpa using hm
    cases hm' with
    | refl => exact (hf (Term.isValue_app_iff.mp hv).1).elim
    | arg hc hs => exact ⟨hw.subtermClosed _ (hcols _ hc) hs, hv⟩

private theorem notCtor_of_table {sig : Signature} {f g : FnName} {k : Nat}
    {xs ys : List Expr} (hd : sig f = some (tableDecl k))
    (he : [Action.expr (.app f xs)] = [.expr (.app g ys)]) : ¬ sig.IsCtor g := by
  obtain ⟨hf, _⟩ := Expr.app.inj (Action.expr.inj (List.cons.inj he).1)
  subst g
  rintro ⟨decl, hdecl, hm⟩
  obtain rfl := Option.some.inj (hdecl.symm.trans hd)
  simp [tableDecl] at hm

theorem maintenance_head_notCtor {P : Program} (hp : P.Fragment) {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r)
    {f : FnName} {xs : List Expr} (ha : r.actions = [.expr (.app f xs)]) :
    ¬ (encodeSig P).IsCtor f := by
  have base : ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r →
      ∀ f xs, r.actions = [.expr (.app f xs)] → ¬ (encodeSig P).IsCtor f := by
    intro c hc r hr f xs ha
    simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
    rcases hc with rfl | ⟨⟨g, k⟩, hk, hc⟩
    · obtain rfl := Cmd.rule.inj hr
      exact notCtor_of_table (encodeSig_ufName hp) ha
    · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨i, _, rfl⟩
      · obtain rfl := Cmd.rule.inj hr
        exact notCtor_of_table (encodeSig_tables hp hk).2 ha
      · obtain rfl := Cmd.rule.inj hr
        exact notCtor_of_table (encodeSig_tables hp hk).2 ha
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact base c hc r hr f xs ha
  · unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact base c hc s hs f xs ha
    next => exact base c hc r hr f xs ha

theorem maintenance_ufTotal {P : Program} (hp : P.Fragment) {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r)
    {d e : Database} {ρ : Env} (hsig : d.sig = encodeSig P) (hw : d.WF) (h : UFTotal d)
    (hρ : ValidQuerySubst d r.query ρ) (he : evalLocalActions d r.actions ρ = some e) :
    UFTotal e := by
  obtain ⟨f, xs, ha, hv, _⟩ := maintenance_headShape hc hr
  rw [ha] at he
  exact h.localFlat hw (hsig ▸ maintenance_head_notCtor hp hc hr ha) hv hρ he

theorem UFTotal.runRules {d : Database} {R : RulesetName} (h : UFTotal d)
    (hf : ∀ r ∈ d.rules, r.ruleset = R → ∀ ρ post,
      ValidQuerySubst d r.query ρ → evalLocalActions d r.actions ρ = some post → UFTotal post) :
    UFTotal (RunRules R d) := by
  intro t ht
  have hv : t.IsValue d.sig := ht.2
  have hm := ht.1
  rw [RunRules.eq_sUnion, Database.sUnion_terms] at hm
  rcases hm with hm | hm
  · exact (h t ⟨hm, hv⟩).mono RunRules.entries_subset
  · obtain ⟨post, ⟨r, hr, hR, ρ, hρ, he⟩, hm⟩ := Set.mem_iUnion₂.mp hm
    obtain ⟨u, hu⟩ := hf r hr hR ρ post hρ he t
      ⟨hm, by rw [evalLocalActions_sig he]; exact hv⟩
    rw [RunRules.eq_sUnion]
    refine ⟨u, ?_, Or.inr ?_⟩
    · simpa only [evalLocalActions_sig he, Database.sUnion_sig] using hu.1
    · exact Set.mem_iUnion₂.mpr ⟨post, ⟨r, hr, hR, ρ, hρ, he⟩, hu.2⟩

theorem UFTotal.runStep {d e : Database} {R : RulesetName} (h : UFTotal d)
    (hr : Runtime d) (hshape : MergeShape d.sig)
    (hf : ∀ r ∈ d.rules, r.ruleset = R → ∀ ρ post,
      ValidQuerySubst d r.query ρ → evalLocalActions d r.actions ρ = some post → UFTotal post)
    (he : RunStep R d e) : UFTotal e :=
  (h.runRules hf).merge (hr.runRules R) hshape he.1

theorem UFTotal.runReach {d e : Database} {R : RulesetName} (h : UFTotal d)
    (hr : Runtime d) (hshape : MergeShape d.sig)
    (hf : ∀ mid, Runtime mid → mid.sig = d.sig → mid.rules = d.rules → mid.env = d.env →
      UFTotal mid → ∀ r ∈ mid.rules, r.ruleset = R → ∀ ρ post,
      ValidQuerySubst mid r.query ρ → evalLocalActions mid r.actions ρ = some post →
      UFTotal post)
    (he : Relation.ReflTransGen (RunStep R) d e) : UFTotal e := by
  have hi : Runtime e ∧ e.sig = d.sig ∧ e.rules = d.rules ∧ e.env = d.env ∧ UFTotal e := by
    apply RunReach.induction (P := fun mid => Runtime mid ∧ mid.sig = d.sig ∧
      mid.rules = d.rules ∧ mid.env = d.env ∧ UFTotal mid) _ he ⟨hr, rfl, rfl, rfl, h⟩
    rintro mid post ⟨hm, hsig, hrules, henv, hu⟩ hstep
    exact ⟨hm.runStep hstep, (RunStep.sig hstep).trans hsig,
      hstep.1.envRules.2.trans hrules, (RunStep.env hstep).trans henv,
      hu.runStep hm (by rw [hsig]; exact hshape)
        (hf mid hm hsig hrules henv hu) hstep⟩
  exact hi.2.2.2.2

theorem UFTotal.rebuild {P : Program} (hp : P.Fragment) {d e : Database} (h : UFTotal d)
    (hr : Runtime d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (he : Relation.ReflTransGen (RunStep rebuildRuleset) d e) : UFTotal e := by
  apply h.runReach hr (hsig ▸ encodeSig_mergeShape P) ?_ he
  intro mid hm hs hrules _ hu r hmem hR ρ post hρ hfire
  obtain ⟨c, hc, hcr⟩ := honly r (hrules ▸ hmem) hR
  exact maintenance_ufTotal hp hc hcr (hs.trans hsig) hm.wf hu hρ hfire

theorem prelude_ufTotal {P : Program} {d : Database}
    (h : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) : UFTotal d := by
  intro t ht
  have he := (prelude_empty h).2.1
  exact (he ▸ ht.1).elim

private theorem self_write_evaluates {d e : Database} {x : Expr}
    (hr : evalActions d [.expr (.app ufName [x, x])] = some e) :
    ∃ t, x.eval d.sig d.env = some t := by
  obtain ⟨mid, hm, _⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨t, ht, _⟩ := Option.map_eq_some_iff.mp hm
  obtain ⟨ts, hts, _⟩ := Expr.evalAtom_app_inv ht
  obtain ⟨t, ht, _⟩ := Option.bind_eq_some_iff.mp hts
  exact ⟨t, ht⟩

theorem encodeBuild_evaluates {d e : Database} {x : Expr} (hp : x.OrderingFree)
    (hr : evalActions d (encodeBuild x) = some e) : ∃ t, x.eval d.sig d.env = some t := by
  cases x with
  | lit l => exact ⟨.lit l, rfl⟩
  | var v => exact self_write_evaluates hr
  | min a b => exact (Expr.not_orderingFree_min hp).elim
  | ite => exact (Expr.not_orderingFree_ite hp).elim
  | app f xs =>
      rw [encodeBuild, evalActions_append_uf] at hr
      obtain ⟨m, hm, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨n, hn, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨t, ht⟩ := self_write_evaluates hr
      rw [evalAction_sig hn, evalAction_env hn, evalActions_sig hm, evalActions_env hm] at ht
      exact ⟨t, ht⟩

theorem encodeAction_evaluates {d e : Database} {a : Action}
    (hp : ∀ x ∈ actionExprs a, x.OrderingFree)
    (hr : evalActions d (encodeAction a) = some e) :
    ∀ x ∈ actionExprs a, ∃ t, x.eval d.sig d.env = some t := by
  cases a with
  | expr x =>
      intro y hy
      obtain rfl : y = x := List.mem_singleton.mp hy
      exact encodeBuild_evaluates (hp y (by simp [actionExprs])) hr
  | union x y =>
      rw [encodeAction, evalActions_append_uf] at hr
      obtain ⟨n, hn, _⟩ := Option.bind_eq_some_iff.mp hr
      rw [evalActions_append_uf] at hn
      obtain ⟨m, hm, hn⟩ := Option.bind_eq_some_iff.mp hn
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact encodeBuild_evaluates (hp z (by simp [actionExprs])) hm
      · obtain rfl := List.mem_singleton.mp hz
        simpa only [evalActions_sig hm, evalActions_env hm] using
          encodeBuild_evaluates (hp z (by simp [actionExprs])) hn

theorem encodeActions_ufTotal_of_run {d e : Database} {as : List Action}
    (hw : d.WF) (hv : ∀ b ∈ d.env, b.2.IsValue d.sig) (hu : UFTotal d)
    (hp : ∀ a ∈ as, ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (hr : evalActions d (encodeActions as) = some e) : UFTotal e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj hr; exact hu
  | cons a as ih =>
      change evalActions d (encodeAction a ++ encodeActions as) = some e at hr
      rw [evalActions_append_uf] at hr
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp hr
      have hum := encodeAction_ufTotal hw hv hu (hp a List.mem_cons_self)
        (hd a List.mem_cons_self) huf (encodeAction_evaluates (hp a List.mem_cons_self) hm) hm
      have hs := evalActions_sig hm
      exact ih (evalActions_wf hw hm)
        (by simpa only [evalActions_sig hm, evalActions_env hm] using hv) hum
        (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun a ha x hx fk hk => hs ▸ hd a (List.mem_cons_of_mem _ ha) x hx fk hk)
        (hs ▸ huf) hr

theorem encodeLocalActions_ufTotal_of_run {d e : Database} {as : List Action} {ρ : Env}
    (hw : d.WF) (hu : UFTotal d)
    (hρ : ∀ b ∈ ρ, b.2 ∈ d.terms)
    (hρv : ∀ b ∈ ρ, b.2.IsValue d.sig)
    (hp : ∀ a ∈ as, ∀ x ∈ actionExprs a, x.OrderingFree)
    (hd : ∀ a ∈ as, ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1))
    (hr : evalLocalActions d (encodeActions as) ρ = some e) : UFTotal e := by
  obtain ⟨post, hp', rfl⟩ := Option.map_eq_some_iff.mp hr
  have hi := encodeActions_ufTotal_of_run (d := { d with env := ρ })
    (hw.appendEnv hρ)
    hρv
    (by simpa only [UFTotal, HasUF, Database.values,
      Database.terms_setEnv, Database.entries] using hu) hp hd huf hp'
  simpa only [UFTotal, HasUF, Database.values, Database.terms_setEnvRules,
    Database.entries] using hi

end Egglog.Congruence.Live
