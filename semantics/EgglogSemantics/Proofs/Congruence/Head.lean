import EgglogSemantics.Proofs.Congruence.HeadConditions
import EgglogSemantics.Proofs.Congruence.HeadMatch
import EgglogSemantics.Proofs.Congruence.Match
import EgglogSemantics.Proofs.Congruence.BuildDescent
import EgglogSemantics.Proofs.Congruence.Declared
import EgglogSemantics.Proofs.Source.Execution

/-! A compiled rule firing reads a source match and writes only facts justified by
that source rule. Both traversals use the original query. -/

namespace Egglog.Congruence

/-- An actual compiled firing supplies a source match. If that source head runs, every
retained target entry is justified by its post-state. Source-head totality is separate:
the source fragment rules out unbound variables and literal unions. -/
theorem encodedRule_firing_sound {src : Database} {d d' : FDatabase} {r : Rule} {σ : Env}
    (hw : src.WF) (hb : src.TermsBuild) (hcs : src.sig.AllConstructors)
    (hr : d.EqsRefl) (he : d.Closed) (hi : d.IndexOk) (hsc : d.SubtermClosed)
    (hs : SoundTerms d src)
    (hof : ∀ p ∈ r.query, p.OrderingFree)
    (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hp : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hf : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      d.sig.IsCtor f ↔ src.sig.IsCtor f)
    (hv : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ v ∈ e.vars, v ∈ Query.vars r.query)
    (hmatch : σ ∈ matchQuery d (encodeRule r).query)
    (hfire : execLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ, ValidQuerySubst src r.query τ ∧ ∀ post,
      evalLocalActions src r.actions τ = some post → SourceSafe post →
        SoundTerms d' post ∧ (MergeShape d.sig → EntryRowsUF d → EntryRowsUF d') ∧
      (UFTermsDescend d → UFTermsDescend d') := by
  obtain ⟨σ', hσ', hagree⟩ := validQuerySubst_of_mem_matchQuery_diag he hr hi hmatch
  obtain ⟨τ, hτ, heval⟩ := sourceMatch_evaluations hb
    (viewsSound_of_soundTerms hr hs).1 hr.toDatabase
    (fun t ht s hst => by
      rw [Egglog.FDatabase.toDatabase_terms] at ht ⊢
      exact hsc t ht s ((Term.mem_subtermList t).mpr hst)) hof hg hk hσ'
  refine ⟨τ, hτ, fun post hpost hsafe => ?_⟩
  obtain ⟨sp, hsp, rfl⟩ := Option.map_eq_some_iff.mp hpost
  obtain ⟨tp, htp, rfl⟩ := Option.map_eq_some_iff.mp hfire
  have hsafe' : SourceSafe sp := by simpa only [SourceSafe, Database.terms_setEnvRules] using hsafe
  have hsenv : SoundTerms { d with env := σ ++ d.env }
      { src with env := τ ++ src.env } :=
    SoundTerms.mono_src (src := src) (src' := { src with env := τ ++ src.env })
      (Set.Subset.refl _) hs
  have hvalues : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a,
      e.eval d.sig (σ ++ d.env) = e.eval src.sig (τ ++ src.env) := by
    intro a ha e hem
    rw [← Expr.eval_agree (hagree.append_right d.env) e]
    exact heval e (hf a ha e hem) (hv a ha e hem)
  have hsound := encodeActions_soundTerms (hw.appendEnv hτ.mem_terms)
    hsafe' hcs hp hvalues hsenv hsp htp
  refine ⟨SoundTerms.mono_src (src := sp)
    (src' := { sp with env := src.env, rules := src.rules }) (Set.Subset.refl _) hsound, ?_⟩
  constructor
  · intro hshape hhistory
    exact encodeActions_entryRowsUF (d := { d with env := σ ++ d.env }) (d' := tp)
      (hw.appendEnv hτ.mem_terms) hsafe' hcs hp hvalues hshape hhistory hsp htp
  · intro hdes
    exact encodeActions_ufTermsDescend (d := { d with env := σ ++ d.env }) (d' := tp)
      (hw.appendEnv hτ.mem_terms) hsafe' hcs hp hvalues hdes hsp htp

/-- Every compiled firing is justified by an actual source firing. The source-domain
head conditions ensure that the reconstructed match runs successfully, rather than
assuming the existence of a convenient source post-state. -/
theorem encodedRule_firing {src : Database} {d d' : FDatabase} {r : Rule} {σ : Env}
    (hw : src.WF) (hb : src.TermsBuild) (hcs : src.sig.AllConstructors)
    (hnames : ∀ f dc, src.sig f = some dc → ¬ "@".isPrefixOf f)
    (hr : d.EqsRefl) (he : d.Closed) (hi : d.IndexOk) (hsc : d.SubtermClosed)
    (hs : SoundTerms d src) (hof : r.OrderingFree)
    (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hscoped : Actions.Scoped r.actions (Query.vars r.query))
    (hbuild : Actions.Builds r.actions src.sig) (hrun : Actions.UnionRunnable r.actions src)
    (hctor : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    (hmatch : σ ∈ matchQuery d (encodeRule r).query)
    (hfire : execLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src r.query τ ∧ evalLocalActions src r.actions τ = some post ∧
      SoundTerms d' post ∧ (MergeShape d.sig → EntryRowsUF d → EntryRowsUF d') ∧
      (UFTermsDescend d → UFTermsDescend d') := by
  have hbexpr := builds_exprs hbuild
  obtain ⟨τ, hτ, hsound⟩ := encodedRule_firing_sound hw hb hcs hr he hi hsc hs hof.1 hg hk
    (orderingFree_actionExprs hof.2)
    (fun a ha e hem f hfm =>
      ⟨fun _ => hbexpr a ha e hem f hfm,
        fun hf => hctor f hf⟩) (scoped_exprs hscoped) hmatch hfire
  have hscope : Actions.Scoped r.actions (Query.bind r.query (Env.dom src.env)) :=
    Actions.Scoped.mono r.actions
      (fun v hv => List.mem_union_iff.mpr (Or.inr hv)) hscoped
  obtain ⟨post, _, hpost⟩ := evalLocalActions_isSome_of_builds (Scope.Models.dom src.env)
    hw hscope hbuild hrun hτ
  refine ⟨τ, _, hτ, hpost, hsound _ hpost ?_⟩
  apply sourceSafe_of_names (evalLocalActions_termsBuild hw hb hcs hτ.mem_terms hpost)
  intro f dc hf
  rw [evalLocalActions_sig hpost] at hf
  exact hnames f dc hf

/-- At a source prefix, all head-side obligations come from the agreed source domain.
The prelude signature supplies constructor coverage; only target execution invariants remain. -/
theorem encodedRule_firing_of_programStep {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src : Database} (hpre : ProgramStep Database.empty pre src)
    {r : Rule} (hmem : Cmd.rule r ∈ P) (hrule : r ∈ src.rules)
    {d d' : FDatabase} {σ : Env} (hi : d.Inv) (hn : d.NoUnions) (hs : SoundTerms d src)
    (hsig : d.sig = encodeSig P)
    (hmatch : σ ∈ matchQuery d (encodeRule r).query)
    (hfire : execLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src r.query τ ∧ evalLocalActions src r.actions τ = some post ∧
      SoundTerms d' post ∧ (MergeShape d.sig → EntryRowsUF d → EntryRowsUF d') ∧
      (UFTermsDescend d → UFTermsDescend d') := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => by
    rw [hP]; exact List.mem_append_left _ hc
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))
  have hbuild := headsBuild_of_programStep hdom hP hpre r hrule
  have hrun : Actions.UnionRunnable r.actions src := by
    rcases hdom.noLitUnion with huf | hlit
    · exact Or.inl ((Cmd.ruleUnionFreeB_iff r).mp (huf _ hmem))
    · exact Or.inr ⟨(noLits_of_programStep hdom hlit hsub hpre).terms,
        Cmd.NoLits.of_domain hdom hlit hmem⟩
  exact encodedRule_firing hcs.wf
    (termsBuild_of_programStep (fun c hc => hdom.ctorsOnly c (hsub c hc)) hpre) hcs.sig
    (sourceNames_of_programStep hdom hsub hpre) hn.eqsRefl hi.closed hi.index
    (Egglog.FDatabase.SubtermClosed.of_wf hi.wf) hs
    (Program.OrderingFree.of_mem hdom.noMin hmem)
    (fun p hp => ((hdom.queryEncodable _ hmem).1 p hp).1)
    (hdom.queryEncodable _ hmem).2 (hdom.headsScoped _ hmem) hbuild hrun
    (sourceConstructors_of_programStep hdom hsub hpre hsig) hmatch hfire

end Egglog.Congruence
