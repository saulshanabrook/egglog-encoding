import EgglogSemantics.Proofs.Congruence.AbstractFiniteRows
import EgglogSemantics.Proofs.Congruence.EntryShape
import EgglogSemantics.Proofs.ActionMonotone
import EgglogSemantics.Proofs.Bindings

/-! Encoded source heads only write generated rows. Soundness of the completed head
therefore bounds every new row and every newly constructed value by one source state. -/

namespace Egglog.Congruence.Abstract

theorem SoundTerms.mem_soundRows {d src : Database} (h : SoundTerms d src)
    {t : Term} (ht : t ∈ d.terms) (hshape : EntryShaped t) : t ∈ SoundRows src := by
  rcases hshape with ⟨f, cs, e, rfl⟩ | ⟨a, b, rfl⟩
  · exact Or.inl ⟨f, cs, e, rfl, h.1 f cs e ht⟩
  · exact Or.inr ⟨a, b, rfl, h.2 a b ht⟩

/-- Every successful evaluation of this action adds a generated row. -/
def RowAction (a : Action) : Prop :=
  ∀ d e, evalAction d a = some e → ∃ t, EntryShaped t ∧ e = d.addTerm t

private theorem RowAction.expr {x : Expr}
    (h : ∀ sig ρ t, x.evalAtom sig ρ = some t → EntryShaped t) :
    RowAction (.expr x) := by
  intro d e he
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp he
  exact ⟨t, h d.sig d.env t ht, rfl⟩

theorem RowAction.view (f : FnName) (args : List Expr) (out : Expr) :
    RowAction (.expr (.app (viewName f) (args ++ [out]))) := by
  apply RowAction.expr
  intro sig ρ t ht
  obtain ⟨cols, hc, rfl⟩ := Expr.evalAtom_app_inv ht
  obtain ⟨cs, es, _, he, rfl⟩ := Expr.evalList_append hc
  obtain ⟨e, _, rfl⟩ := Expr.evalList_singleton he
  exact Or.inl ⟨f, cs, e, rfl⟩

theorem RowAction.uf (a b : Expr) : RowAction (.expr (.app ufName [a, b])) := by
  apply RowAction.expr
  intro sig ρ t ht
  obtain ⟨cols, hc, rfl⟩ := Expr.evalAtom_app_inv ht
  obtain ⟨x, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨y, _, rfl⟩ := Expr.evalList_singleton hxs
  exact Or.inr ⟨x, y, rfl⟩

mutual

theorem encodeBuild_rowActions : ∀ e a, a ∈ encodeBuild e → RowAction a
  | .lit l, a, h => by
      obtain rfl := List.mem_singleton.mp h
      exact RowAction.uf (.lit l) (.lit l)
  | .var v, a, h => by
      obtain rfl := List.mem_singleton.mp h
      exact RowAction.uf (.var v) (.var v)
  | .min x y, a, h =>
      (List.mem_append.mp h).elim (encodeBuild_rowActions x a) (encodeBuild_rowActions y a)
  | .ite _ _ _ _, _, h => by cases h
  | .app f args, a, h => by
      rcases List.mem_append.mp h with h | h
      · exact encodeBuildArgs_rowActions args a h
      · rcases List.mem_cons.mp h with rfl | h
        · exact RowAction.view f args (.app f args)
        · obtain rfl := List.mem_singleton.mp h
          exact RowAction.uf (.app f args) (.app f args)

theorem encodeBuildArgs_rowActions : ∀ es a, a ∈ encodeBuildArgs es → RowAction a
  | [], _, h => by cases h
  | e :: es, a, h =>
      (List.mem_append.mp h).elim (encodeBuild_rowActions e a) (encodeBuildArgs_rowActions es a)

end

theorem encodeAction_rowActions (a : Action) : ∀ b ∈ encodeAction a, RowAction b := by
  intro b hb
  cases a with
  | expr e => exact encodeBuild_rowActions e b hb
  | union x y =>
      rcases List.mem_append.mp hb with hb | hb
      · exact (List.mem_append.mp hb).elim
          (encodeBuild_rowActions x b) (encodeBuild_rowActions y b)
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact RowAction.uf x (.min x y)
        · obtain rfl := List.mem_singleton.mp hb
          exact RowAction.uf y (.min x y)

theorem encodeActions_rowActions (as : List Action) :
    ∀ b ∈ encodeActions as, RowAction b := by
  intro b hb
  obtain ⟨a, _, hb⟩ := List.mem_flatMap.mp hb
  exact encodeAction_rowActions a b hb

/-- A sound row-writing block adds only source values and source-sound rows. -/
theorem evalActions_rows_newTerms {src d e : Database} {as : List Action}
    (hw : src.WF) (hs : SoundTerms e src) (ha : ∀ a ∈ as, RowAction a)
    (hr : evalActions d as = some e) :
    e.terms ⊆ d.terms ∪ (src.terms ∪ SoundRows src) := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj hr; exact Set.subset_union_left
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨t, ht, rfl⟩ := ha a List.mem_cons_self d mid hm
      have hsound : t ∈ SoundRows src := hs.mem_soundRows
        ((evalActions_contained hr).terms (Database.mem_addTerm t d)) ht
      have htail := ih (fun a ha' => ha a (List.mem_cons_of_mem _ ha')) hr
      intro s hmem
      rcases htail hmem with hmem | hmem
      · rw [Database.addTerm_terms] at hmem
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · by_cases he : s = t
          · exact Or.inr (Or.inr (he ▸ hsound))
          · exact Or.inr (Or.inl (SoundRows.subterms_subset hw hsound hmem he))
      · exact Or.inr hmem

/-- Rule-local environments do not affect the row bound. -/
theorem evalLocalActions_rows_newTerms {src d e : Database} {as : List Action} {ρ : Env}
    (hw : src.WF) (hs : SoundTerms e src) (ha : ∀ a ∈ as, RowAction a)
    (hr : evalLocalActions d as ρ = some e) :
    e.terms ⊆ d.terms ∪ (src.terms ∪ SoundRows src) := by
  obtain ⟨mid, hm, rfl⟩ := Option.map_eq_some_iff.mp hr
  have hs' : SoundTerms mid src := hs.congr_terms
    (d := { mid with env := d.env, rules := d.rules }) (e := mid)
    (Database.terms_eq_of_eqs_eq rfl)
  have hb := evalActions_rows_newTerms hw hs' ha hm
  simpa only [Database.terms_setEnvRules, Database.terms_setEnv] using hb

end Egglog.Congruence.Abstract
