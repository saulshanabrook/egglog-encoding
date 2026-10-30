import EgglogSemantics.Proofs.Congruence.AbstractSoundRounds
import EgglogSemantics.Proofs.Congruence.LiveRead
import EgglogSemantics.Proofs.Congruence.UFCoverage
import EgglogSemantics.Proofs.ActionProgram

/-! Data invariants at boundaries between original source commands. -/

namespace Egglog

/-- Commands other than declarations retain merge normality. -/
theorem CmdStep.mergeNormal {d e : Database} {c : Cmd} (h : CmdStep d c e)
    (hn : MergeNormal d) (hc : Congruence.NoDecl c) : MergeNormal e := by
  cases c with
  | check q => obtain ⟨_, rfl⟩ := h; exact hn
  | rule r =>
    have h : e = { d with rules := insert r d.rules } := h
    subst h
    exact hn.setRules _
  | run R => exact MergeNormalize.normal h
  | saturate R => exact SaturateReach.mergeNormal h
  | decl => exact hc.elim

theorem ProgramStep.mergeNormal {d e : Database} {p : Program}
    (h : ProgramStep d p e) (hn : MergeNormal d) (hp : ∀ c ∈ p, Congruence.NoDecl c) :
    MergeNormal e := by
  induction h with
  | nil => exact hn
  | cons hc _ ih =>
    exact ih (hc.mergeNormal hn (hp _ List.mem_cons_self))
      (fun c hm => hp c (List.mem_cons_of_mem _ hm))

/-- A compiled prefix ends merge-normal: its declarations all run on empty data. -/
theorem Congruence.prefix_mergeNormal {P pre : Program} {d : Database}
    (h : ProgramStep Database.empty
      ((Congruence.encodePrelude P ++ Congruence.encodeCmds pre 0).map
        Congruence.Command.command) d) :
    MergeNormal d := by
  rw [List.map_append] at h
  obtain ⟨m, hm, hrest⟩ := h.append_inv
  have hme : m.eqs = ∅ := hm.eqs_empty_of_declOrRule (Congruence.prelude_setup P) rfl
  refine hrest.mergeNormal ?_ (Congruence.cmds_noDecl pre 0)
  intro row hr
  exact (hme ▸ hr.2).elim

namespace Congruence.Abstract

/-- The relation maintained between corresponding successful command prefixes. -/
structure Boundary (src d : Database) : Prop where
  sound : SoundTerms d src.completion
  descend : Descending d
  reads : Live.Reads d src
  rebuilt : Rebuilt d
  total : Live.UFTotal d

theorem prelude_boundary {P : Program} {d : Database} (hp : P.Fragment)
    (ht : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) :
    Boundary Database.empty d := by
  obtain ⟨_, hterms, _⟩ := Live.prelude_empty ht
  have hr := Live.prelude_runtime hp ht
  have hnone {f : FnName} {cs vs : List Term} (ho : d.Out f cs vs) : False := by
    have hm := ho.term hr.noUnions.diag
    simp only [hterms, Set.mem_empty_iff_false] at hm
  have hfinite : d.terms.Finite := hterms ▸ Set.finite_empty
  refine ⟨?_, ?_, ?_, ⟨hr.wf, hfinite, ?_, ?_⟩,
    Live.prelude_ufTotal ht⟩
  · constructor <;> intros <;> simp_all
  · intro a b hm
    simp [hterms] at hm
  · constructor
    · intro t ht
      simp at ht
    · intro a b hab _
      cases hab
  · constructor
    · intro a b c ho _; exact (hnone ho).elim
    · intro a b c ho _; exact (hnone ho).elim
    · intro f cs a b ho _; exact (hnone ho).elim
    · intro f cs a b ho _; exact (hnone ho).elim
    · intro f cs ds e ho _; exact (hnone ho).elim
  · intro a b ho; exact (hnone ho).elim

end Congruence.Abstract
end Egglog
