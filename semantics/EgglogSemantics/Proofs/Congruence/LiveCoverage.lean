import EgglogSemantics.Proofs.Congruence.LiveRead
import EgglogSemantics.Proofs.Congruence.AbstractRuntime

/-! Sequential merging retains the readings of a block evaluated without merges. -/

namespace Egglog.Congruence.Live

structure Covers (d e : Database) : Prop where
  sig : d.sig = e.sig
  rows : ∀ f cs a, Entry.mk f cs [a] ∈ d.entries →
    ∃ b, Entry.mk f cs [b] ∈ e.entries ∧ Joined e a b

theorem Covers.refl (d : Database) : Covers d d :=
  ⟨rfl, fun _ _ a ha => ⟨a, ha, .refl a⟩⟩

theorem Covers.joined {d e : Database} (h : Covers d e)
    {a b : Term} (hj : Joined d a b) : Joined e a b := by
  induction hj with
  | refl a => exact .refl a
  | edge hr =>
      obtain ⟨c, hc, hbc⟩ := h.rows ufName [_] _ hr
      exact (Joined.edge hc).trans hbc.symm
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Covers.trans {d e f : Database} (h : Covers d e) (h' : Covers e f) :
    Covers d f := by
  refine ⟨h.sig.trans h'.sig, fun g cs a ha => ?_⟩
  obtain ⟨b, hb, hab⟩ := h.rows g cs a ha
  obtain ⟨c, hc, hbc⟩ := h'.rows g cs b hb
  exact ⟨c, hc, (h'.joined hab).trans hbc⟩

theorem Covers.of_entries {d e : Database} (hsig : d.sig = e.sig)
    (h : d.entries ⊆ e.entries) : Covers d e :=
  ⟨hsig, fun _ _ a ha => ⟨a, h ha, .refl a⟩⟩

theorem Covers.repr {d e : Database} (h : Covers d e)
    {t i : Term} (hr : Repr d t i) : Repr e t i :=
  hr.transport h.rows (fun _ _ hj => h.joined hj)

theorem Covers.reads {d e src : Database} (h : Covers d e) (hr : Reads d src) :
    Reads e src := hr.transport (fun _ _ ht => h.repr ht)

theorem Covers.mergeClosure {d e : Database} (h : State d) (hd : d.Diag)
    (hc : MergeClosure d e) : Covers d e :=
  ⟨hc.sig.symm, fun _ _ _ hr => by
    obtain ⟨b, hb, hj, _⟩ := row_closure h hd hc hr
    exact ⟨b, hb, hj⟩⟩

theorem Covers.addTerm {d e : Database} (h : Covers d e) (t : Term) :
    Covers (d.addTerm t) (e.addTerm t) := by
  refine ⟨h.sig, fun f cs a ha => ?_⟩
  rcases Database.mem_addTerm_entries.mp ha with ha | ⟨hv, ht⟩
  · obtain ⟨b, hb, hj⟩ := h.rows f cs a ha
    exact ⟨b, Database.mem_addTerm_entries.mpr (Or.inl hb),
      hj.mono (fun _ hr => Database.mem_addTerm_entries.mpr (Or.inl hr))⟩
  · exact ⟨a, Database.mem_addTerm_entries.mpr (Or.inr ⟨h.sig ▸ hv, ht⟩), .refl a⟩

theorem Covers.addEq {d e : Database} (h : Covers d e) (a b : Term) :
    Covers (d.addEq a b) (e.addEq a b) := by
  refine ⟨h.sig, fun f cs t ht => ?_⟩
  rcases ht.2 with he | he
  · exact ⟨t, ⟨h.sig ▸ ht.1, Or.inl he⟩, .refl t⟩
  · obtain ⟨u, hu, hj⟩ := h.rows f cs t ⟨ht.1, he⟩
    exact ⟨u, ⟨hu.1, Or.inr hu.2⟩,
      Joined.mono (d := e) (e := e.addEq a b) (fun _ hr => ⟨hr.1, Or.inr hr.2⟩) hj⟩

theorem evalAction_covers {d e post : Database} (h : Covers d e) (henv : d.env = e.env)
    {a : Action} (hf : evalAction d a = some post) :
    ∃ out, evalAction e a = some out ∧ Covers post out ∧ post.env = out.env := by
  rcases evalAction_eq_some hf with ⟨exp, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, hl, rfl⟩
  · exact ⟨e.addTerm t, by simp [evalAction, ← h.sig, ← henv, he], h.addTerm t, henv⟩
  · refine ⟨e.addEq ta tb, ?_, ?_, henv⟩
    · simp only [not_or, Bool.not_eq_true] at hl
      simp [evalAction, ← h.sig, ← henv, ha, hb, hl.1, hl.2]
    · exact h.addEq ta tb

end Egglog.Congruence.Live
