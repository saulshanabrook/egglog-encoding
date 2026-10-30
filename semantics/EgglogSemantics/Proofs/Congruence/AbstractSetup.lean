import EgglogSemantics.Proofs.Congruence.AbstractBoundary
import EgglogSemantics.Proofs.Congruence.SourceSetup
import EgglogSemantics.Proofs.Out

/-! Boundary preservation for source declarations, rule registrations, and checks. -/

namespace Egglog.Congruence.Abstract

theorem Rebuilt.setRules {d : Database} (h : Rebuilt d) (rules : Set Rule) :
    Rebuilt { d with rules := rules } := by
  let e : Database := { d with rules := rules }
  have hto {f cs vs} (ho : d.Out f cs vs) : e.Out f cs vs :=
    Database.Out.mono (d₁ := d) (d₂ := e) ⟨Set.Subset.refl _⟩ rfl ho
  have hfrom {f cs vs} (ho : e.Out f cs vs) : d.Out f cs vs :=
    Database.Out.mono (d₁ := e) (d₂ := d) ⟨Set.Subset.refl _⟩ rfl ho
  have pto {a b} (hp : Parent d a b) : Parent e a b := hp.imp id hto
  have pfrom {a b} (hp : Parent e a b) : Parent d a b := hp.imp id hfrom
  refine ⟨h.wf.congr rfl rfl, ?_, ?_, fun a b ho => h.descend a b (hfrom ho)⟩
  · simpa only [Database.terms_setRules] using h.finite
  · constructor
    · intro a b c hab hbc
      exact hto (h.closed.compress a b c (hfrom hab) (hfrom hbc))
    · intro a b c hab hac
      obtain ⟨z, hb, hc⟩ := h.closed.ufJoin a b c (hfrom hab) (hfrom hac)
      exact ⟨z, pto hb, pto hc⟩
    · intro f cs a b ha hb
      obtain ⟨z, ha', hb'⟩ := h.closed.viewJoin f cs a b (hfrom ha) (hfrom hb)
      exact ⟨z, pto ha', pto hb'⟩
    · intro f cs a b ha hb
      exact hto (h.closed.output f cs a b (hfrom ha) (hfrom hb))
    · intro f cs ds z hz hl
      exact hto (h.closed.keys f cs ds z (hfrom hz) (hl.imp fun _ _ hp => pfrom hp))

/-- A source declaration is already hoisted into the target prelude. -/
theorem Boundary.decl {src post d e : Database} (h : Boundary src d)
    (hcs : src.sig.AllConstructors) {f : FnName} {dc : FnDecl}
    (hdecl : (Cmd.decl f dc).CtorDecl) (hs : CmdStep src (.decl f dc) post) {i : Nat}
    (ht : ProgramStep d ((encodeCmd i (.decl f dc)).map Command.command) e) :
    Boundary post e := by
  obtain rfl := ht.nil_inv
  have heq := source_setup_eqs hcs (c := .decl f dc) trivial hdecl hs
  exact ⟨h.sound.mono_src (completion_mono ⟨heq.symm.subset⟩).eqs, h.descend,
    h.reads.restrict ⟨heq.subset⟩, h.rebuilt, h.total⟩

/-- Registering a rule leaves current rows and their readings unchanged. -/
theorem Boundary.rule {src post d e : Database} (h : Boundary src d)
    (hcs : src.sig.AllConstructors) (hnormal : MergeNormal d) {r : Rule}
    (hs : CmdStep src (.rule r) post) {i : Nat}
    (ht : ProgramStep d ((encodeCmd i (.rule r)).map Command.command) e) :
    Boundary post e := by
  change ProgramStep d [.rule (encodeRule r)] e at ht
  obtain ⟨m, hm, hnil⟩ := ht.cons_inv
  obtain rfl := hnil.nil_inv
  obtain ⟨n, hn, hcl⟩ := hm.reach
  change n = { d with rules := insert (encodeRule r) d.rules } at hn
  subst n
  have hnormal' := hnormal.setRules (insert (encodeRule r) d.rules)
  rw [hcl.eq_of_mergeNormal hnormal']
  have heq := source_setup_eqs hcs (c := .rule r) trivial trivial hs
  refine ⟨?_, ?_, ?_, h.rebuilt.setRules _, ?_⟩
  · exact (h.sound.mono_src (completion_mono ⟨heq.symm.subset⟩).eqs).congr_terms
      Database.terms_setRules
  · exact h.descend.mono_terms Database.terms_setRules.subset
  · exact (h.reads.restrict (src' := post) ⟨heq.subset⟩).mono (Set.Subset.refl _)
  · simpa only [Live.UFTotal, Live.HasUF, Database.values, Database.terms_setRules,
      Database.entries] using h.total

/-- Successful checks preserve the boundary relation. -/
theorem Boundary.check {src post d e : Database} (h : Boundary src d) {q : Query}
    (hs : CmdStep src (.check q) post) {i : Nat}
    (ht : ProgramStep d ((encodeCmd i (.check q)).map Command.command) e) :
    Boundary post e := by
  obtain ⟨_, rfl⟩ := hs
  change ProgramStep d [.check (encodeQuery q 0).1] e at ht
  obtain ⟨m, hm, hnil⟩ := ht.cons_inv
  obtain rfl := hnil.nil_inv
  obtain ⟨_, rfl⟩ := hm
  exact h

end Egglog.Congruence.Abstract
