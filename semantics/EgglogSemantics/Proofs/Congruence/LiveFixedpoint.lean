import EgglogSemantics.Proofs.Congruence.LivePersistence
import EgglogSemantics.Proofs.Congruence.LiveState
import EgglogSemantics.Proofs.Congruence.LiveLeaders
import EgglogSemantics.Proofs.Congruence.AbstractRebuild
import EgglogSemantics.Proofs.Congruence.AbstractRuntime
import EgglogSemantics.Proofs.DiagonalRound

/-! Completed maintenance fixed points absorb writes through actual minimum merges. -/

namespace Egglog.Congruence.Live

theorem ruleResult_row {d post : Database} {R : RulesetName} {r : Rule}
    (hr : r ∈ d.rules) (hR : r.ruleset = R) (hf : post ∈ RuleResults d r)
    {row : Entry} (hrow : row ∈ post.entries) : row ∈ (RunRules R d).entries := by
  rw [RunRules.eq_sUnion]
  refine ⟨?_, Or.inr ?_⟩
  · simpa only [Database.sUnion_sig, ← RuleResults.sig hf] using hrow.1
  · exact Set.mem_iUnion₂.mpr ⟨post, ⟨r, hr, hR, hf⟩, hrow.2⟩

/-- A head row may be consumed, but its current replacement is connected and no larger. -/
theorem firing_row_bound {d post : Database} {R : RulesetName}
    (h : State d) (hg : GeneratedTables d.sig) (hn : d.NoUnions)
    (hstore : d.StoreOk) (hqs : d.RulesSafe) (hs : RunSaturated R d) {r : Rule}
    (hr : r ∈ d.rules) (hR : r.ruleset = R)
    (hf : post ∈ RuleResults d r) {f : FnName} {key : List Term} {a : Term}
    (hrow : Entry.mk f key [a] ∈ post.entries) :
    ∃ b, Entry.mk f key [b] ∈ d.entries ∧ Joined d a b ∧ IdLe b a := by
  obtain ⟨out, hstep, heq⟩ := hs.2
  have hentries := hstore.entries_eq_of_terms_eq
    (hstep.storeOk hstore hqs (hg.mergesWidthOk h.uf)) heq.sig
    (heq.terms_eq_of_diag hn.diag (hstep.noUnions hn).diag)
  obtain ⟨b, hb, hj, hle⟩ := row_closure (h.runRules hg hstore hqs R) (RunRules.diag hn)
    hstep.1 (ruleResult_row hr hR hf hrow)
  exact ⟨b, hentries.symm ▸ hb, hj.mono (fun _ hr => hentries.symm ▸ hr), hle⟩

end Egglog.Congruence.Live

namespace Egglog.Congruence.Abstract

theorem out_of_current {d : Database} (hs : d.StoreOk) {f : FnName}
    {cs vs : List Term} (hr : Entry.mk f cs vs ∈ d.entries) : d.Out f cs vs :=
  ⟨cs, CongList.refl fun t ht => hs.columns _ hr t (List.mem_append_left _ ht), hr⟩

theorem Parent.trans_of_compress {d : Database}
    (hc : ∀ a b c, d.Out ufName [a] [b] → d.Out ufName [b] [c] →
      d.Out ufName [a] [c]) {a b c : Term}
    (hab : Parent d a b) (hbc : Parent d b c) : Parent d a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  exact Or.inr (hc a b c hab hbc)

theorem Parent.join_of_normal {d : Database} (hn : MergeNormal d) {a b c : Term}
    (hab : Parent d a b) (hac : Parent d a c) :
    ∃ e, Parent d b e ∧ Parent d c e := by
  rcases hab with rfl | hab
  · exact ⟨c, hac, .refl d c⟩
  rcases hac with rfl | hac
  · exact ⟨b, .refl d b, Or.inr hab⟩
  have he := List.singleton_inj.mp (hn.out_unique hab hac)
  exact ⟨b, .refl d b, Or.inl he.symm⟩

/-- Compression and functional UF rows make every connected pair share a parent. -/
theorem joined_common_parent {d : Database} (hs : d.StoreOk) (hn : MergeNormal d)
    (hc : ∀ a b c, d.Out ufName [a] [b] → d.Out ufName [b] [c] →
      d.Out ufName [a] [c]) {a b : Term} (hj : Live.Joined d a b) :
    ∃ r, Parent d a r ∧ Parent d b r := by
  induction hj with
  | refl a => exact ⟨a, .refl d a, .refl d a⟩
  | edge hr => exact ⟨_, Or.inr (out_of_current hs hr), .refl d _⟩
  | symm _ ih => obtain ⟨r, ha, hb⟩ := ih; exact ⟨r, hb, ha⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨r, ha, hb⟩ := ih₁
    obtain ⟨s, hbs, hcs⟩ := ih₂
    obtain ⟨t, hrt, hst⟩ := hb.join_of_normal hn hbs
    exact ⟨t, ha.trans_of_compress hc hrt, hcs.trans_of_compress hc hst⟩

theorem joined_roots_eq {d : Database} (hs : d.StoreOk) (hn : MergeNormal d)
    (hc : ∀ a b c, d.Out ufName [a] [b] → d.Out ufName [b] [c] →
      d.Out ufName [a] [c]) {a b : Term} (hj : Live.Joined d a b)
    (ha : Root d a) (hb : Root d b) : a = b := by
  obtain ⟨r, har, hbr⟩ := joined_common_parent hs hn hc hj
  exact (ha r har).symm.trans (hb r hbr)

theorem Rebuilt.root_joined {d : Database} (h : Rebuilt d) (hs : d.StoreOk)
    {a b : Term} (hj : Live.Joined d a b) : h.root a = h.root b := by
  induction hj with
  | refl => rfl
  | edge hr => exact h.root_parent (Or.inr (out_of_current hs hr))
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Egglog.Congruence.Abstract
