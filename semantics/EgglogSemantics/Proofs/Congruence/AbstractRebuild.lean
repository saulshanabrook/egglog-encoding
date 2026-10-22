import Mathlib.Order.WellFoundedSet
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.Order
import EgglogSemantics.Proofs.Congruence.Correspond

/-! Rebuilding over mathematical databases. Closure refers to current rows and must
be established after a completed maintenance round and destructive normalization. -/

namespace Egglog.Congruence.Abstract

/-- A parent step also permits keeping the current id. -/
def Parent (d : Database) (a b : Term) : Prop := a = b ∨ d.Out ufName [a] [b]

/-- The consequences of the generated merge and maintenance fixed points. -/
structure Closed (d : Database) : Prop where
  compress : ∀ a b c, d.Out ufName [a] [b] → d.Out ufName [b] [c] →
    d.Out ufName [a] [c]
  ufJoin : ∀ a b c, d.Out ufName [a] [b] → d.Out ufName [a] [c] →
    ∃ e, Parent d b e ∧ Parent d c e
  viewJoin : ∀ f cs a b, d.Out (viewName f) cs [a] → d.Out (viewName f) cs [b] →
    ∃ e, Parent d a e ∧ Parent d b e
  output : ∀ f cs a b, d.Out (viewName f) cs [a] → d.Out ufName [a] [b] →
    d.Out (viewName f) cs [b]
  keys : ∀ f cs ds e, d.Out (viewName f) cs [e] → List.Forall₂ (Parent d) cs ds →
    d.Out (viewName f) ds [e]

theorem Parent.refl (d : Database) (a : Term) : Parent d a a := Or.inl rfl

theorem Parent.trans {d : Database} (h : Closed d) {a b c : Term}
    (hab : Parent d a b) (hbc : Parent d b c) : Parent d a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  exact Or.inr (h.compress a b c hab hbc)

theorem Parent.join {d : Database} (h : Closed d) {a b c : Term}
    (hab : Parent d a b) (hac : Parent d a c) :
    ∃ e, Parent d b e ∧ Parent d c e := by
  rcases hab with rfl | hab
  · exact ⟨c, hac, .refl d c⟩
  rcases hac with rfl | hac
  · exact ⟨b, .refl d b, Or.inr hab⟩
  exact h.ufJoin a b c hab hac

def Root (d : Database) (a : Term) : Prop := ∀ b, Parent d a b → b = a

/-- These are proof invariants, not extra premises of compiler correctness. Finiteness
comes from `ProgramStep.finite_from_empty`; closure must come from actual rebuilding. -/
structure Rebuilt (d : Database) : Prop where
  wf : d.WF
  finite : d.terms.Finite
  closed : Closed d
  descend : ∀ a b, d.Out ufName [a] [b] → b = a ∨ Term.blt b a = true

private instance : IsStrictOrder Term (fun a b => Term.blt a b = true) where
  irrefl := fun a h => by simp at h
  trans := fun a b c => Term.blt_trans a b c

theorem Rebuilt.exists_root {d : Database} (h : Rebuilt d) (a : Term) :
    ∃ b, Parent d a b ∧ Root d b := by
  have hf : {b | Parent d a b}.Finite := by
    apply (h.finite.insert a).subset
    intro b hb
    rcases hb with rfl | ⟨cs, _, ht⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _
        (Database.mem_terms_of_arg h.wf (StoredCong.direct ht.2).mem_left (by simp [Entry.columns]))
  have hw := Set.wellFoundedOn_iff.mp
    (hf.wellFoundedOn (r := fun x y => Term.blt x y = true))
  obtain ⟨b, hb, hmin⟩ := hw.has_min {b | Parent d a b} ⟨a, .refl d a⟩
  refine ⟨b, hb, fun c hbc => ?_⟩
  rcases hbc with rfl | hbc
  · rfl
  rcases h.descend b c hbc with heq | hlt
  · exact heq
  have hac := hb.trans h.closed (Or.inr hbc)
  exact (hmin c hac ⟨hlt, hac, hb⟩).elim

noncomputable def Rebuilt.root {d : Database} (h : Rebuilt d) (a : Term) : Term :=
  (h.exists_root a).choose

theorem Rebuilt.root_spec {d : Database} (h : Rebuilt d) (a : Term) :
    Parent d a (h.root a) ∧ Root d (h.root a) := (h.exists_root a).choose_spec

theorem Rebuilt.root_unique {d : Database} (h : Rebuilt d) {a b c : Term}
    (hab : Parent d a b) (hb : Root d b) (hac : Parent d a c) (hc : Root d c) : b = c := by
  obtain ⟨e, hbe, hce⟩ := hab.join h.closed hac
  exact (hb e hbe).symm.trans (hc e hce)

theorem Rebuilt.root_eq {d : Database} (h : Rebuilt d) {a : Term} (ha : Root d a) :
    h.root a = a := ha _ (h.root_spec a).1

@[simp] theorem Rebuilt.root_idem {d : Database} (h : Rebuilt d) (a : Term) :
    h.root (h.root a) = h.root a := h.root_eq (h.root_spec a).2

theorem Rebuilt.root_parent {d : Database} (h : Rebuilt d) {a b : Term}
    (hab : Parent d a b) : h.root a = h.root b :=
  h.root_unique (h.root_spec a).1 (h.root_spec a).2
    (hab.trans h.closed (h.root_spec b).1) (h.root_spec b).2

theorem Rebuilt.root_lit {d src : Database} (h : Rebuilt d) (hs : EdgesSound d src)
    (hw : src.WF) (l : Lit) : h.root (.lit l) = .lit l := by
  apply h.root_eq
  intro b hb
  rcases hb with rfl | hb
  · rfl
  · exact ((hs _ _ hb).eq_of_isLit hw.litsIsolated (Or.inl rfl)).symm

theorem Rebuilt.out_normalized {d : Database} (h : Rebuilt d) {f : FnName}
    {cs : List Term} {e : Term} (ho : d.Out (viewName f) cs [e]) :
    d.Out (viewName f) (cs.map h.root) [h.root e] := by
  have hkeys : List.Forall₂ (Parent d) cs (cs.map h.root) := by
    clear ho
    induction cs with
    | nil => exact .nil
    | cons c cs ih => exact .cons (h.root_spec c).1 ih
  have hn := h.closed.keys f cs (cs.map h.root) e ho hkeys
  rcases (h.root_spec e).1 with heq | he
  · exact heq ▸ hn
  · exact h.closed.output f _ e _ hn he

theorem Rebuilt.outputs_equal {d : Database} (h : Rebuilt d) {f : FnName}
    {cs : List Term} {a b : Term}
    (ha : d.Out (viewName f) cs [a]) (hb : d.Out (viewName f) cs [b]) :
    h.root a = h.root b := by
  obtain ⟨e, hae, hbe⟩ := h.closed.viewJoin f cs a b ha hb
  exact (h.root_parent hae).trans (h.root_parent hbe).symm

mutual

theorem Rebuilt.normalize_view {d src : Database} (h : Rebuilt d)
    (hs : EdgesSound d src) (hw : src.WF) : ∀ (t : Term) {e : Term},
    ViewRepr d t e → ViewRepr d t (h.root e)
  | .lit l, _, .lit => by rw [h.root_lit hs hw l]; exact .lit
  | .app _ as, _, .app hl ho =>
      .app (h.normalize_views hs hw as hl) (h.out_normalized ho)

theorem Rebuilt.normalize_views {d src : Database} (h : Rebuilt d)
    (hs : EdgesSound d src) (hw : src.WF) : ∀ (ts : List Term) {es : List Term},
    ViewReprList d ts es → ViewReprList d ts (es.map h.root)
  | [], _, .nil => .nil
  | t :: ts, _, .cons ht hts =>
      .cons (h.normalize_view hs hw t ht) (h.normalize_views hs hw ts hts)

end

mutual

theorem Rebuilt.unique_view {d : Database} (h : Rebuilt d) : ∀ (t : Term) {a b : Term},
    ViewRepr d t a → ViewRepr d t b → h.root a = h.root b
  | .lit _, _, _, .lit, .lit => rfl
  | .app _ ts, _, _, .app ha hoa, .app hb hob => by
      have hkeys := h.unique_views ts ha hb
      have hna := h.out_normalized hoa
      have hnb := h.out_normalized hob
      rw [← hkeys] at hnb
      simpa only [h.root_idem] using h.outputs_equal hna hnb

theorem Rebuilt.unique_views {d : Database} (h : Rebuilt d) :
    ∀ (ts : List Term) {as bs : List Term}, ViewReprList d ts as → ViewReprList d ts bs →
      as.map h.root = bs.map h.root
  | [], _, _, .nil, .nil => rfl
  | t :: ts, _, _, .cons ha has, .cons hb hbs =>
      congrArg₂ List.cons (h.unique_view t ha hb) (h.unique_views ts has hbs)

end

theorem Rebuilt.viewLeader {d src : Database} (h : Rebuilt d) (hs : EdgesSound d src)
    (hw : src.WF) : ViewLeader d :=
  ⟨h.root, fun t _ ht => h.normalize_view hs hw t ht,
    fun t _ _ ha hb => h.unique_view t ha hb, fun _ _ hu => h.root_parent (Or.inr hu)⟩

theorem Rebuilt.share_keys {d src : Database} (h : Rebuilt d) (hs : EdgesSound d src)
    (hw : src.WF) {as bs es : List Term} (ha : ViewReprList d as es)
    (hab : List.Forall₂ (SameClass d) as bs) :
    ViewReprList d as (es.map h.root) ∧ ViewReprList d bs (es.map h.root) := by
  refine ⟨h.normalize_views hs hw as ha, ?_⟩
  induction hab generalizing es with
  | nil => cases ha; exact .nil
  | @cons a b as bs hab _ ih =>
      cases ha with
      | @cons _ e _ es hae has =>
          obtain ⟨x, hax, hbx⟩ := hab
          exact .cons (h.unique_view a hae hax ▸ h.normalize_view hs hw b hbx) (ih has)

theorem Rebuilt.viewsCover {d src : Database} (h : Rebuilt d) (hs : EdgesSound d src)
    (hw : src.WF) (hex : ∀ t ∈ src.terms, ∃ e, ViewRepr d t e) : ViewsCover d src := by
  constructor
  intro f as bs ha hab
  obtain ⟨e, he⟩ := hex (.app f as) ha
  cases he with
  | app hl ho =>
      obtain ⟨hleft, hright⟩ := h.share_keys hs hw hl hab
      exact ⟨_, h.root e, hleft, hright, h.out_normalized ho⟩

theorem Rebuilt.corresponds {d src : Database} (h : Rebuilt d) (he : EdgesSound d src)
    (hv : ViewsSound d src) (hw : src.WF)
    (hex : ∀ t ∈ src.terms, ∃ e, ViewRepr d t e) (hun : UnionsJoined d src)
    (a b : Term) (ha : a ∈ src.terms) (hb : b ∈ src.terms) :
    StoredCong src a b ↔ SameClass d a b :=
  corresponds_of_invariants hw (h.viewLeader he hw) (h.viewsCover he hw hex) hun hv a b ha hb

end Egglog.Congruence.Abstract
