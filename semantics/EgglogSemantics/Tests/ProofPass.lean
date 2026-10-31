import EgglogSemantics.Congruence.Relational
import EgglogSemantics.Proofs.Resugar.Soundness

namespace Egglog.Tests.ProofPass

set_option linter.hashCommand false

def a : Term := .app "A" []
def b : Term := .app "B" []
def seed : Rule := ⟨[], [.union a.toExpr b.toExpr]⟩
def program : Program := ⟨Schedule.seqAll [.run [seed]], [.eq a.toExpr b.toExpr]⟩

/-- Execute the actual firing-log instrumentation of the congruence compilation. -/
def run : Option FDatabase := do
  let annotated ← Provenance.encode (Congruence.encode program)
  Relational.execSchedule runFuel FDatabase.empty annotated.schedule

def proofs : Option (List SourceProof.Proof) := do
  let d ← run
  Resugar.extractAll program d.terms

#guard run.isSome
#guard run.any fun d => d.terms.any fun t => match t with
  | .app f _ => (Provenance.fireIndex f).isSome
  | .lit _ => false
#guard proofs.any fun ps => !ps.isEmpty && ps.all fun p =>
  SourceProof.check program p == some p.claim
#guard proofs.any fun ps => ps.any fun p =>
  p.claim == (⟨a, b⟩ : SourceProof.Claim) || p.claim == (⟨b, a⟩ : SourceProof.Claim)
-- With the firing log removed, extraction cannot justify any of the data rows.
#guard run.any fun d =>
  (Provenance.extract (Congruence.encode program) (Provenance.eraseLog d.terms)).isNone

/-- The computed extraction is subject to the general checked-output guarantee. -/
theorem proofs_checked {ps : List SourceProof.Proof} (h : proofs = some ps) :
    ∀ p ∈ ps, SourceProof.check program p = some p.claim := by
  obtain ⟨_, _, he⟩ := Option.bind_eq_some_iff.mp h
  exact Resugar.extractAll_checked he

private def registered : Database :=
  Database.empty
def reached : Database := RunRules [seed] registered

theorem source_reached : Reach Database.empty program.schedule reached :=
  .run

private theorem registered_subsumeFree : ∀ r ∈ [seed], r.SubsumeFree := by
  intro r hr
  have he : r = seed := List.mem_singleton.mp hr
  subst r
  simp [Rule.SubsumeFree, Actions.SubsumeFree, seed, Action.SubsumeFree, Action.monotoneB]

private theorem equality_asserted : (a, b) ∈ reached.eqs := by
  have hf : registered.addEq a b ∈ RuleResults registered seed :=
    ⟨[], ⟨[], .nil, .nil⟩, rfl⟩
  have hc := SourceMeaning.firing_contained_round registered_subsumeFree
    (by simp) hf
  exact hc.eqs (Set.mem_insert _ _)

theorem source_saturated (rs : List Rule) (hc : rs ∈ program.runs) :
    RunSaturated rs reached := by
  have hc : rs = [seed] := List.mem_singleton.mp hc
  subst rs
  have hfixed : RunRules [seed] reached = reached := by
    apply (runRules_eq_self_iff [seed] reached registered_subsumeFree).mpr
    intro r hr out hout
    have he : r = seed := List.mem_singleton.mp hr
    subst r
    obtain ⟨σ, _, hf⟩ := hout
    have he : evalActions σ reached seed.actions = some (reached.addEq a b) := rfl
    rw [he] at hf
    obtain rfl := Option.some.inj hf
    refine ⟨?_, Set.Subset.rfl⟩
    rintro p (rfl | hp)
    · exact equality_asserted
    · exact hp
  rw [RunSaturated, hfixed]
  exact Database.SameMeaning.refl _

/-- The actual instrumented run's extracted certificates infer their source claims. -/
theorem extracted_claim_infers {ps : List SourceProof.Proof} (h : proofs = some ps) :
    ∀ p ∈ ps, reached.Infers p.claim.lhs p.claim.rhs := by
  obtain ⟨_, _, he⟩ := Option.bind_eq_some_iff.mp h
  exact Resugar.extractAll_infers source_reached (source_reached.wf Database.WF.empty)
    source_saturated he

end Egglog.Tests.ProofPass
