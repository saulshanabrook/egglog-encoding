import EgglogSemantics.Proofs.Congruence.AbstractWrites
import EgglogSemantics.Proofs.Congruence.LeaderMatch
import EgglogSemantics.Proofs.Congruence.LeaderSyntax
import EgglogSemantics.Proofs.Congruence.HeadConditions
import EgglogSemantics.Proofs.Congruence.MetadataSyntax
import EgglogSemantics.Proofs.Congruence.AbstractRuntime
import EgglogSemantics.Proofs.SourceModel

/-! Compiled leader heads are justified by actual firings in the completed source. -/

namespace Egglog.Congruence.Abstract

theorem SourceAction.leader {src : Database} {s₁ s₂ : Signature} {ρ₁ ρ₂ : Env}
    {a : Action} (hs : SourceAction src s₁ ρ₁ a)
    (he : ∀ e ∈ actionExprs a, Expr.eval s₂ (leaderExpr e) ρ₂ = Expr.eval s₁ e ρ₁) :
    SourceAction src s₂ ρ₂ (leaderAction a) := by
  cases a with
  | expr e =>
      obtain ⟨t, ht, hm⟩ := hs
      exact ⟨t, (he e (by simp [actionExprs])).trans ht, hm⟩
  | union a b =>
      obtain ⟨ta, tb, ha, hb, hc⟩ := hs
      exact ⟨ta, tb, (he a (by simp [actionExprs])).trans ha,
        (he b (by simp [actionExprs])).trans hb, hc⟩

theorem encodedRule_firing_sound {src d d' : Database} {r : Rule} {σ : Env}
    (hw : src.WF) (hb : src.TermsBuild) (hcs : src.sig.AllConstructors)
    (hrt : Live.Runtime d) (htables : ViewTables d)
    (hs : SoundTerms d src) (hdesc : Descending d)
    (hof : ∀ p ∈ r.query, p.OrderingFree)
    (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hp : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hf : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      d.sig.IsCtor f ↔ src.sig.IsCtor f)
    (hv : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ v ∈ e.vars, v ∈ r.query.vars)
    (hd : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (hmatch : ValidQuerySubst d (encodeRule r).query σ)
    (hfire : evalLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ, ValidQuerySubst src r.query τ ∧ ∀ post,
      evalLocalActions src r.actions τ = some post → SourceSafe post →
        SoundTerms d' post ∧ Descending d' := by
  obtain ⟨τ, hτ, heval⟩ := sourceMatch_leader_evaluations hb hw
    (hs.viewsSound hrt.noUnions.diag) (hs.edgesSound hrt.noUnions.diag)
    hrt.noUnions.diag hrt.storeOk hrt.wf.subtermClosed htables hrt.state.uf hof hg hk hmatch
  refine ⟨τ, hτ, fun post hpost hsafe => ?_⟩
  have hjust : ∀ a ∈ r.actions, SourceAction post src.sig τ a := by
    obtain ⟨sp, hsp, rfl⟩ := Option.map_eq_some_iff.mp hpost
    intro a ha
    exact Egglog.Congruence.SourceAction.mono
      (src := sp) (post := { sp with env := src.env, rules := src.rules })
      ⟨Set.Subset.refl _⟩
      (sourceActions_of_evalActions (src := { src with env := τ }) hcs hsp a ha)
  apply encodeLocalActions_preserves_of_justified (evalLocalActions_wf hw hτ.mem_terms hpost)
    hsafe (hs.mono_src (evalLocalActions_contained hpost).eqs) hdesc
    (as := r.actions.map leaderAction) ?_ ?_ hrt.state.uf ?_ hfire
  · intro a ha e he
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    rw [leaderAction_exprs] at he
    obtain ⟨expr, hexpr, rfl⟩ := List.mem_map.mp he
    exact (leaderExpr_orderingFree expr).mpr (hp original horiginal expr hexpr)
  · intro a ha e he fk hfk
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    rw [leaderAction_exprs] at he
    obtain ⟨expr, hexpr, rfl⟩ := List.mem_map.mp he
    exact hd original horiginal expr hexpr fk (leaderExpr_ctors expr ▸ hfk)
  · intro a ha
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    exact SourceAction.leader (hjust original horiginal)
      (fun e he => heval e (hf original horiginal e he) (hv original horiginal e he))

/-- Domain conditions make the reconstructed source head executable. -/
theorem encodedRule_firing {src d d' : Database} {r : Rule} {σ : Env}
    (hw : src.WF) (_hstore : src.StoreOk) (hb : src.TermsBuild)
    (hcs : src.sig.AllConstructors)
    (hnames : ∀ f dc, src.sig f = some dc → ¬ "@".isPrefixOf f)
    (hrt : Live.Runtime d) (htables : ViewTables d)
    (hs : SoundTerms d src) (hdesc : Descending d)
    (hof : r.OrderingFree) (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hscoped : Actions.Scoped r.actions r.query.vars)
    (hbuild : Actions.Builds r.actions src.sig) (hrun : Actions.UnionRunnable r.actions src)
    (hctor : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (hmatch : ValidQuerySubst d (encodeRule r).query σ)
    (hfire : evalLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src r.query τ ∧ evalLocalActions src r.actions τ = some post ∧
      SoundTerms d' post ∧ Descending d' := by
  have hbexpr := builds_exprs hbuild
  obtain ⟨τ, hτ, hsound⟩ := encodedRule_firing_sound hw hb hcs hrt htables hs hdesc
    hof.1 hg hk (orderingFree_actionExprs hof.2)
    (fun a ha e hem f hfm =>
      ⟨fun _ => hbexpr a ha e hem f hfm, fun hf => hctor f hf⟩)
    (scoped_exprs hscoped) hd hmatch hfire
  have hscope : Actions.Scoped r.actions (Query.bind r.query (Env.dom [])) :=
    Actions.Scoped.mono r.actions
      (fun v hv => List.mem_union_iff.mpr (Or.inr hv)) hscoped
  obtain ⟨post, _, hpost⟩ := evalLocalActions_isSome_of_builds (Scope.Models.dom [])
    hw hscope hbuild hrun hτ
  refine ⟨τ, _, hτ, hpost, hsound _ hpost ?_⟩
  apply sourceSafe_of_names (evalLocalActions_termsBuild hw hb hcs hτ.mem_terms hpost)
  intro f dc hf
  rw [evalLocalActions_sig hpost] at hf
  exact hnames f dc hf

theorem storeOk_of_sourceTerms {src : Database} (hw : src.WF) (hb : src.TermsBuild)
    (hc : src.sig.AllConstructors) : src.StoreOk := by
  have hn : ∀ row, row ∉ src.entries := by
    intro row hr
    obtain ⟨decl, hd, hm, _⟩ := hr.1
    exact hm (by simpa [Signature.mergeOf, hd] using hc row.name)
  refine ⟨fun row hr => (hn row hr).elim, fun row hr => (hn row hr).elim, ?_, ?_⟩
  · intro p hp
    exact Or.inl ⟨termsBuild_isValue hb hw (StoredCong.direct hp).mem_left,
      termsBuild_isValue hb hw (StoredCong.direct hp).mem_right⟩
  · intro b hb'
    exact termsBuild_isValue hb hw (hw.envInTerms b hb')

theorem completion_litFree {src : Database} (hw : src.WF) (hl : src.LitFree) :
    src.completion.LitFree := by
  intro t ht
  cases t with
  | app _ _ => simp [Term.isLit]
  | lit l =>
      obtain ⟨w, _, hi⟩ := (InferredFacts.infers_self_iff_supported hw).mp
        ((Database.mem_completion_iff hw).mp ht)
      have hn : Term.lit l ∉ src.terms := fun hm => hl _ hm (by simp [Term.isLit])
      simp [InferredFacts.interpret, hn] at hi

theorem encodedRule_firing_of_programStep {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src : Database} (hpre : ProgramStep Database.empty pre src)
    {r : Rule} (hmem : Cmd.rule r ∈ P) (hrule : r ∈ src.rules)
    {d d' : Database} {σ : Env} (hrt : Live.Runtime d)
    (hs : SoundTerms d src.completion) (hdesc : Descending d)
    (hsig : d.sig = encodeSig P)
    (hmatch : ValidQuerySubst d (encodeRule r).query σ)
    (hfire : evalLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src.completion r.query τ ∧
      evalLocalActions src.completion r.actions τ = some post ∧
      SoundTerms d' post ∧ Descending d' := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))
  have hsourceStore := storeOk_of_sourceTerms hcs.wf
    (termsBuild_of_programStep (fun c hc => hdom.ctorsOnly c (hsub c hc)) hpre) hcs.sig
  have hcompletion := hsourceStore.completion hcs.wf hcs.sig
  have hb : src.completion.TermsBuild := fun f as ht =>
    (Term.isValue_app_iff.mp (hcompletion.values_of_allConstructors hcs.sig _ ht)).1
  have hbuild := headsBuild_of_programStep hdom hP hpre r hrule
  have hrun : Actions.UnionRunnable r.actions src.completion := by
    rcases hdom.noLitUnion with huf | hlit
    · exact Or.inl ((Cmd.ruleUnionFreeB_iff r).mp (huf _ hmem))
    · exact Or.inr ⟨completion_litFree hcs.wf
        (noLits_of_programStep hdom hlit hsub hpre).terms,
        Cmd.NoLits.of_domain hdom hlit hmem⟩
  apply encodedRule_firing hcs.wf.completion hcompletion hb hcs.sig
    (sourceNames_of_programStep (src := src) hdom hsub hpre) hrt
    (fun f dc hf => encodeSig_view_shape hdom (hsig ▸ hf)) hs hdesc
    (Program.OrderingFree.of_mem hdom.noMin hmem)
    (fun p hp => ((hdom.queryEncodable _ hmem).1 p hp).1)
    (hdom.queryEncodable _ hmem).2 (hdom.headsScoped _ hmem) hbuild hrun
    (sourceConstructors_of_programStep (src := src) hdom hsub hpre hsig) ?_ hmatch hfire
  intro a ha e he fk hk
  have hfk : fk ∈ P.ctors := mem_program_ctors hmem
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, actionExprs_ctors he hk⟩))
  exact hsig ▸ (encodeSig_tables hdom hfk).2

end Egglog.Congruence.Abstract
