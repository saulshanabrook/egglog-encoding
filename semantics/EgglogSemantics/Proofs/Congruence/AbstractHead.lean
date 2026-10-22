import EgglogSemantics.Proofs.Congruence.LeaderEval
import EgglogSemantics.Proofs.Congruence.UFCoverage

/-! Source firings lift to leader-bound compiled firings. -/

namespace Egglog.Congruence.Abstract

open Live

theorem encodedRule_firing_reads {d : Database} {src querySrc post : Database}
    (h : Rebuilt d) (hdg : d.Diag) (hstore : d.StoreOk) (hdecl : ViewDeclared d)
    (he : EdgesSound d src) (hw : src.WF) (htotal : UFTotal d)
    (hcs : querySrc.sig.AllConstructors) (hreads : Reads d querySrc)
    {r : Rule} {σ : Env}
    (hqp : ∀ p ∈ r.query, p.OrderingFree)
    (hqk : Query.VarsKeyed r.query) (hqg : ∀ p ∈ r.query, p.Grounded)
    (hqn : ∀ v ∈ Query.vars r.query, ¬ "@".isPrefixOf v = true)
    (hp : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hctor : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      querySrc.sig.IsCtor f → d.sig.IsCtor f)
    (huf : d.sig ufName = some (tableDecl 1))
    (hd : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (hm : ValidQuerySubst querySrc r.query σ)
    (hf : evalLocalActions querySrc r.actions σ = some post) :
    ∃ ρ d', ValidQuerySubst d (encodeRule r).query ρ ∧
      evalLocalActions d (encodeRule r).actions ρ = some d' ∧ Reads d' post := by
  obtain ⟨hex, hun⟩ := hreads.normalize h hstore he hw
  have hself : ∀ t ∈ querySrc.terms, ∀ i ∈ d.values,
      ViewRepr d t i → Root d i → d.Out ufName [i] [i] := by
    intro _ _ i hi _ hr
    have hh := h.root_lookup hdg hstore (fun a ha => by
      obtain ⟨b, hb⟩ := htotal a ha
      exact ⟨b, out_of_current hstore hb⟩) hi
    exact (hr _ (h.root_spec i).1) ▸ hh.2
  obtain ⟨ρ, hmatch, _, hρ⟩ := encodedRule_match_of_source h hdg hstore hdecl he hw
    hcs hun hex hself hqp hqk hqg hqn hm 0
  obtain ⟨sp, hsp, rfl⟩ := Option.map_eq_some_iff.mp hf
  have hrename := evalActions_leaderEnv
    (d := { querySrc with env := σ }) hcs hsp
  have hρ' : EnvReads d (leaderEnv σ) ρ := hρ.envReads hdg
    (fun v i hi =>
      (hmatch.mem_values hstore (encodeRule_querySafe r hqp) (v, i) (Env.mem_of_lookup hi)).2)
  have henvread : EnvReads ({ d with env := ρ } : Database)
      (leaderEnv σ) ρ := by
    intro v t ht
    obtain ⟨i, hi, hv, hr⟩ := hρ' v t ht
    exact ⟨i, hi, hv,
      Live.Repr.mono (d := d) (e := { d with env := ρ }) (Set.Subset.refl _) hr⟩
  have hstart : Reads ({ d with env := ρ } : Database)
      { querySrc with env := leaderEnv (σ) } :=
    (hreads.mono (e := ({ d with env := ρ } : Database))
      (Set.Subset.refl _)).restrict ⟨Set.Subset.refl _⟩
  obtain ⟨tp, htp, hpost⟩ := encodeActions_reads
    (src := { querySrc with env := leaderEnv (σ) })
    (d := { d with env := ρ }) hcs
    (by
      intro a ha e he
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
      rw [leaderAction_exprs] at he
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact (leaderExpr_orderingFree e₀).mpr (hp a₀ ha₀ e₀ he₀))
    (by
      intro a ha e he f hf hc
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
      rw [leaderAction_exprs] at he
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact hctor a₀ ha₀ e₀ he₀ f (by simpa using hf) hc)
    (by
      intro a ha e he fk hk
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
      rw [leaderAction_exprs] at he
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact hd a₀ ha₀ e₀ he₀ fk (by simpa using hk)) huf henvread hstart hrename
  refine ⟨ρ, { tp with env := d.env, rules := d.rules }, hmatch, ?_, ?_⟩
  · change (evalActions { d with env := ρ }
      (encodeActions (r.actions.map leaderAction))).map _ = _
    rw [htp]; rfl
  · exact (hpost.mono
      (e := ({ tp with env := d.env, rules := d.rules } : Database))
      (Set.Subset.refl _)).restrict ⟨Set.Subset.refl _⟩

end Egglog.Congruence.Abstract
