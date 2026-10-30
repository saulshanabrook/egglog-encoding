import EgglogSemantics.Proofs.Congruence.UFCoverage
import EgglogSemantics.Proofs.Congruence.AbstractBuild
import EgglogSemantics.Proofs.Congruence.AbstractRunState
import EgglogSemantics.Proofs.Congruence.AbstractSoundHead
import EgglogSemantics.Proofs.Congruence.LiveRunRead

/-! Compiled rule firings and rounds preserve complete union-find coverage. -/

namespace Egglog.Congruence.Live

open Abstract

/-- A successful compiled rule head supplies its own operand evaluation witnesses. -/
theorem encodedRule_firing_ufTotal {P : Program} (hp : P.Fragment) {r : Rule}
    (hrule : Cmd.rule r ∈ P) {d e : Database} {ρ : Env} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (hu : UFTotal d)
    (hρ : ValidQuerySubst d (encodeRule r).query ρ)
    (hfire : evalLocalActions d (encodeRule r).actions ρ = some e) : UFTotal e := by
  apply encodeLocalActions_ufTotal_of_run (as := r.actions.map leaderAction)
    h.wf hu hρ.mem_terms ?_ ?_ ?_ h.state.uf hfire
  · exact fun b hb => (hρ.mem_values h.storeOk
      (encodeRule_querySafe r (Program.OrderingFree.of_mem hp.noMin hrule).1) b hb).2
  · intro a ha x hx
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    rw [leaderAction_exprs] at hx
    obtain ⟨expr, hexpr, rfl⟩ := List.mem_map.mp hx
    exact (leaderExpr_orderingFree expr).mpr
      (orderingFree_actionExprs (Program.OrderingFree.of_mem hp.noMin hrule).2
        original horiginal expr hexpr)
  · intro a ha x hx fk hfk
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    rw [leaderAction_exprs] at hx
    obtain ⟨expr, hexpr, rfl⟩ := List.mem_map.mp hx
    have hk : fk ∈ P.ctors := mem_program_ctors hrule
      (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨original, horiginal, actionExprs_ctors hexpr (leaderExpr_ctors expr ▸ hfk)⟩))
    exact hsig ▸ (encodeSig_tables hp hk).2

theorem target_firing_ufTotal {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src : Database}
    (hpre : ProgramStep Database.empty pre src) {d e : Database} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d) (hu : UFTotal d)
    {r : Rule} (hr : r ∈ d.rules) {ρ : Env} (hρ : ValidQuerySubst d r.query ρ)
    (hfire : evalLocalActions d r.actions ρ = some e) : UFTotal e := by
  rcases (hrules r).mp hr with ⟨c, hc, hcr⟩ | ⟨s, hs, rfl⟩
  · exact maintenance_ufTotal hp hc hcr hsig h.wf hu hρ hfire
  · have hm : Cmd.rule s ∈ P := by
      apply hsub
      simpa only [Database.empty, Set.mem_empty_iff_false, false_or] using
        (hpre.mem_rules_iff s).mp hs
    exact encodedRule_firing_ufTotal hp hm h hsig hu hρ hfire

theorem target_runReach_ufTotal {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src : Database}
    (hpre : ProgramStep Database.empty pre src) {d e : Database} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d) (hu : UFTotal d)
    {R : RulesetName} (hr : Relation.ReflTransGen (RunStep R) d e) : UFTotal e := by
  apply hu.runReach h (hsig ▸ encodeSig_mergeShape P) ?_ hr
  intro mid hm hs hrules' _ hum r hmem _ ρ post hρ hfire
  apply target_firing_ufTotal hp hsub hpre hm (hs.trans hsig) ?_ hum hmem hρ hfire
  intro r
  rw [hrules']
  exact hrules r

end Egglog.Congruence.Live
