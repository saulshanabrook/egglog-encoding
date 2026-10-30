import EgglogSemantics.Proofs.Congruence.LiveNormalization
import EgglogSemantics.Proofs.Congruence.IdOrder
import EgglogSemantics.Proofs.DiagonalPreservation

/-! Destructive merging preserves rows up to smaller, UF-connected outputs. -/

namespace Egglog.Congruence.Live

/-- Connectivity uses current UF rows, allowing traversal in either direction. -/
inductive Joined (d : Database) : Term → Term → Prop where
  | refl (a : Term) : Joined d a a
  | edge {a b : Term} : ufEntry a b ∈ d.entries → Joined d a b
  | symm {a b : Term} : Joined d a b → Joined d b a
  | trans {a b c : Term} : Joined d a b → Joined d b c → Joined d a c

theorem Joined.mono {d e : Database} (h : d.entries ⊆ e.entries)
    {a b : Term} (hj : Joined d a b) : Joined e a b := by
  induction hj with
  | refl a => exact .refl a
  | edge hr => exact .edge (h hr)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- On a diagonal store, a genuine collision has different singleton outputs. -/
theorem mergeStep_entries {d e : Database} (h : State d) (hd : d.Diag)
    (hs : MergeStep d e) :
    ∃ f key a b, Entry.mk f key [a] ∈ d.entries ∧ Entry.mk f key [b] ∈ d.entries ∧
      a ≠ b ∧ e.entries = insert ⟨f, key, [Term.least a b]⟩
        (insert (ufEntry b (Term.least a b)) (insert (ufEntry a (Term.least a b))
          ((d.entries \ {⟨f, key, [a]⟩}) \ {⟨f, key, [b]⟩}))) := by
  obtain ⟨old, new, decl, mid, vs, ho, hn, hne, hname, hdecl, hkeys, hm, rfl⟩ := mergeStep_iff.mp hs
  have hold := h.rows old ho
  have hnew := h.rows new hn
  have he : decl = tableDecl old.key.length := Option.some.inj (hdecl.symm.trans hold.declared)
  subst decl
  obtain ⟨a, ha⟩ := hold.output
  obtain ⟨b, hb⟩ := hnew.output
  have hva := (h.typed old ho).output_values a (by simp [ha])
  have hvb := (h.typed new hn).output_values b (by simp [hb])
  have hk := CongList.eq_of_diag hd hkeys
  have hea : old = ⟨old.name, old.key, [a]⟩ := by
    cases old; exact congrArg (Entry.mk _ _) ha
  have heb : new = ⟨old.name, old.key, [b]⟩ := by
    rw [hname, hk]
    cases new; exact congrArg (Entry.mk _ _) hb
  have hab : a ≠ b := by
    intro hab
    exact hne (hea.trans (hab ▸ heb.symm))
  rw [ha, hb] at hm
  obtain ⟨hsig, hvs, heffects⟩ :=
    mergeValues_effects (d := (d.eraseEntry old).eraseEntry new) h.uf hva hvb hm
  have hresult : (Entry.mk old.name old.key [Term.least a b]).Valid mid.sig := by
    rw [hsig]
    exact (h.typed old ho).with_value (by simp [ha]) (by simpa using hva.least hvb)
  refine ⟨old.name, old.key, a, b, hea ▸ ho, heb ▸ hn, hab, ?_⟩
  rw [hvs, Database.putEntry_entries hresult, heffects,
    Database.eraseEntry_entries (by simpa using h.typed new hn),
    Database.eraseEntry_entries (h.typed old ho),
    hea, heb]

theorem row_step {d e : Database} (h : State d) (hd : d.Diag)
    (hs : MergeStep d e) {f : FnName} {key : List Term} {a : Term}
    (hr : Entry.mk f key [a] ∈ d.entries) :
    ∃ b, Entry.mk f key [b] ∈ e.entries ∧ Joined e a b ∧ IdLe b a := by
  obtain ⟨g, cs, x, y, _, _, _, he⟩ := mergeStep_entries h hd hs
  by_cases hx : Entry.mk f key [a] = ⟨g, cs, [x]⟩
  · cases hx
    refine ⟨Term.least a y, ?_, .edge ?_, lowerId_le_left a y⟩
    · rw [he]; exact Set.mem_insert _ _
    · rw [he]; exact Or.inr (Or.inr (Or.inl rfl))
  by_cases hy : Entry.mk f key [a] = ⟨g, cs, [y]⟩
  · cases hy
    refine ⟨Term.least x a, ?_, .edge ?_, lowerId_le_right x a⟩
    · rw [he]; exact Set.mem_insert _ _
    · rw [he]; exact Or.inr (Or.inl rfl)
  refine ⟨a, ?_, .refl a, .refl a⟩
  rw [he]
  exact Or.inr (Or.inr (Or.inr ⟨⟨hr, hx⟩, hy⟩))

theorem Joined.mergeStep {d e : Database} (h : State d) (hd : d.Diag)
    (hs : MergeStep d e) {a b : Term} (hj : Joined d a b) : Joined e a b := by
  induction hj with
  | refl a => exact .refl a
  | edge hr =>
    obtain ⟨c, hc, hbc, _⟩ := row_step h hd hs hr
    exact (Joined.edge hc).trans hbc.symm
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem row_closure {d e : Database} (h : State d) (hd : d.Diag)
    (hs : MergeClosure d e) {f : FnName} {key : List Term} {a : Term}
    (hr : Entry.mk f key [a] ∈ d.entries) :
    ∃ b, Entry.mk f key [b] ∈ e.entries ∧ Joined e a b ∧ IdLe b a := by
  induction hs with
  | refl => exact ⟨a, hr, .refl a, .refl a⟩
  | @tail mid post hcl hs ih =>
    have hm := (state_closure h (outputsIn_self d) hcl).1
    have hdiag := mergeClosure_diag h hd hcl
    obtain ⟨b, hb, hj, hle⟩ := ih
    obtain ⟨c, hc, hjc, hcle⟩ := row_step hm hdiag hs hb
    exact ⟨c, hc, (hj.mergeStep hm hdiag hs).trans hjc, hcle.trans hle⟩

theorem Joined.mergeClosure {d e : Database} (h : State d) (hd : d.Diag)
    (hs : MergeClosure d e) {a b : Term} (hj : Joined d a b) : Joined e a b := by
  induction hj with
  | refl a => exact .refl a
  | edge hr =>
    obtain ⟨c, hc, hbc, _⟩ := row_closure h hd hs hr
    exact (Joined.edge hc).trans hbc.symm
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Egglog.Congruence.Live
