import EgglogSemantics.Proofs.SourceProof.Soundness

/-! An accepted rule certificate is sound in an explicitly reached source fixed point. -/

namespace Egglog.Tests.SourceProofCorrectness

open SourceProof

def premise : Term := .app "A" []
def conclusion : Term := .app "B" []
def derive : Rule :=
  ⟨[.expr (.app "A" [])], [.expr (.app "B" [])]⟩
def initial : Rule := ⟨[], [.expr premise.toExpr]⟩
def program : Program := ⟨[.run [initial], .run [derive]], [.expr conclusion.toExpr]⟩
def certificate : Proof :=
  .rule ⟨conclusion, conclusion⟩ 1 [] [.rule ⟨premise, premise⟩ 0 [] []]

private def seeded : Database := Database.empty
private def registered : Database := RunRules [initial] seeded
def reached : Database := RunRules [derive] registered

theorem source_reached : ProgramStep Database.empty program.commands reached :=
  .cons rfl (.cons rfl .nil)

theorem source_fragment : program.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide⟩
  simp only [String.isPrefixOf, String.startsWith_string_iff]
  decide

theorem certificate_accepted :
    check program certificate = some ⟨conclusion, conclusion⟩ := by
  have hok : sourceOk program = true := decide_eq_true source_fragment
  simp only [check, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  decide

private theorem initial_deleteFree : ∀ r ∈ [initial], r.DeleteFree := by
  simp [Rule.DeleteFree, Actions.DeleteFree, initial, Action.DeleteFree, Action.monotoneB]

private theorem derive_deleteFree : ∀ r ∈ [derive], r.DeleteFree := by
  simp [Rule.DeleteFree, Actions.DeleteFree, derive, Action.DeleteFree, Action.monotoneB]

private theorem premise_asserted : (premise, premise) ∈ registered.eqs := by
  have hf : seeded.addTerm premise ∈ RuleResults seeded initial :=
    ⟨[], ⟨[], .nil, .nil⟩, rfl⟩
  have hc := SourceMeaning.firing_contained_round initial_deleteFree
    (by simp) hf
  exact hc.eqs (Set.mem_insert _ _)

private theorem initial_match : ValidQuerySubst registered derive.query [] := by
  refine ⟨[[]], .cons ⟨⟨List.Perm.refl [], by simp⟩, ?_⟩ .nil, .single []⟩
  exact .atom rfl (.direct premise_asserted)

private theorem premise_retained : (premise, premise) ∈ reached.eqs := by
  change (premise, premise) ∈ (RunRules [derive] registered).eqs
  rw [RunRules.eq_addEqs derive_deleteFree]
  exact Or.inl premise_asserted

theorem premise_exists : premise ∈ reached.terms :=
  (StoredCong.direct premise_retained).mem_left

private theorem conclusion_asserted : (conclusion, conclusion) ∈ reached.eqs := by
  have hf : registered.addTerm conclusion ∈ RuleResults registered derive :=
    ⟨[], initial_match, rfl⟩
  have hc := SourceMeaning.firing_contained_round derive_deleteFree
    (by simp) hf
  exact hc.eqs (Set.mem_insert _ _)

theorem conclusion_exists : conclusion ∈ reached.terms :=
  (StoredCong.direct conclusion_asserted).mem_left

theorem conclusion_not_initial :
    check program (.rule ⟨conclusion, conclusion⟩ 0 [] []) = none := by
  have hok : sourceOk program = true := decide_eq_true source_fragment
  simp only [check, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  decide

theorem missing_premise_rejected :
    check program (.rule ⟨conclusion, conclusion⟩ 1 [] []) = none := by
  have hok : sourceOk program = true := decide_eq_true source_fragment
  simp only [check, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  decide

private theorem reached_wf : reached.WF := source_reached.wf Database.WF.empty

theorem source_saturated (c : Cmd) (hc : c ∈ program.commands) :
    RunSaturated c.rules reached := by
  have hdf : ∀ r ∈ c.rules, r.DeleteFree := by
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact initial_deleteFree
    · exact derive_deleteFree
  have hfixed : RunRules c.rules reached = reached := by
    apply (runRules_eq_self_iff c.rules reached hdf).mpr
    intro r hr out hout
    have hr' : r = derive ∨ r = initial := by
      simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Or.inr (List.mem_singleton.mp hr)
      · exact Or.inl (List.mem_singleton.mp hr)
    rcases hr' with rfl | rfl
    · obtain ⟨σ, _, hf⟩ := hout
      have he : evalActions σ reached derive.actions =
          some (reached.addTerm conclusion) := rfl
      rw [he] at hf
      obtain rfl := Option.some.inj hf
      constructor
      rintro p (rfl | hp)
      · exact conclusion_asserted
      · exact hp
    · obtain ⟨σ, _, hf⟩ := hout
      have he : evalActions σ reached initial.actions =
          some (reached.addTerm premise) := rfl
      rw [he] at hf
      obtain rfl := Option.some.inj hf
      constructor
      rintro p (rfl | hp)
      · exact premise_retained
      · exact hp
  rw [RunSaturated, hfixed]
  exact Database.SameMeaning.refl _

/-- The checker theorem is instantiated with a real premise and a derived conclusion. -/
theorem accepted_rule_is_supported : Claim.Supported reached ⟨conclusion, conclusion⟩ :=
  check_supported source_reached reached_wf source_saturated certificate_accepted

theorem accepted_rule_infers : reached.Infers conclusion conclusion :=
  check_infers source_reached reached_wf source_saturated certificate_accepted

theorem accepted_rule_is_sound : Cong reached conclusion conclusion :=
  (check_sound source_reached reached_wf source_saturated certificate_accepted
    conclusion_exists conclusion_exists).toCong

end Egglog.Tests.SourceProofCorrectness
