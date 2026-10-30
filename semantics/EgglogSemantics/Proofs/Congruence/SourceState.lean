import EgglogSemantics.Proofs.Source.Domain

/-! Source terms remain constructor values throughout a constructor-only run. -/

namespace Egglog.Congruence

def ConstructorTerm (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → sig.IsCtor f

theorem ConstructorTerm.lit {sig : Signature} {l : Lit} : ConstructorTerm sig (.lit l) := by
  intro f as h
  rw [Term.subterms_lit, Set.mem_singleton_iff] at h
  exact absurd h (by simp)

theorem constructorTerm_app {sig : Signature} {f : FnName} {args : List Term}
    (hc : sig.IsCtor f) (ha : ∀ a ∈ args, ConstructorTerm sig a) :
    ConstructorTerm sig (.app f args) := by
  intro g as h
  rw [Term.subterms_app, Set.mem_insert_iff] at h
  rcases h with h | h
  · obtain ⟨rfl, -⟩ := Term.app.inj h
    exact hc
  · obtain ⟨a, ha', hs⟩ := by simpa using h
    exact ha a ha' g as hs

mutual

theorem eval_constructorTerm {sig : Signature} {ρ : Env}
    (hρ : ∀ v u, Env.lookup v ρ = some u → ConstructorTerm sig u) :
    ∀ (e : Expr) {t : Term}, e.eval sig ρ = some t → ConstructorTerm sig t
  | .lit _, _, h => by
      obtain rfl : _ = _ := Option.some.inj h
      exact ConstructorTerm.lit
  | .var v, t, h => hρ v t h
  | .app f args, t, h => by
      have hct : sig.IsCtor f := by
        by_contra hc
        rw [Expr.eval_app_not_ctor hc] at h
        exact absurd h (by simp)
      rw [Expr.eval_app_ctor hct] at h
      obtain ⟨is, his, rfl⟩ := Option.map_eq_some_iff.mp h
      exact constructorTerm_app hct (evalList_constructorTerm hρ args his)
  | .min a b, t, h => by
      rw [Expr.eval_min, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, hmap⟩ := h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rcases Term.least_eq_or x y with h | h <;> rw [h]
      · exact eval_constructorTerm hρ a hx
      · exact eval_constructorTerm hρ b hy
  | .ite _ _ yes no, _, h =>
      (Expr.eval_ite_inv h).elim (eval_constructorTerm hρ yes) (eval_constructorTerm hρ no)

theorem evalList_constructorTerm {sig : Signature} {ρ : Env}
    (hρ : ∀ v u, Env.lookup v ρ = some u → ConstructorTerm sig u) :
    ∀ (es : List Expr) {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ t ∈ ts, ConstructorTerm sig t
  | [], _, h => by
      obtain rfl : _ = _ := Option.some.inj h
      simp
  | e :: es, ts, h => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, hrest⟩ := h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact eval_constructorTerm hρ e hu
      · exact evalList_constructorTerm hρ es hus t ht'

end

theorem termsBuild_term {db : Database} (hw : db.WF) (h : db.TermsBuild) {t : Term}
    (ht : t ∈ db.terms) : ConstructorTerm db.sig t :=
  fun f as hs => h f as (hw.subtermClosed t ht hs)

theorem termsBuild_lookup {db : Database} (hw : db.WF) (h : db.TermsBuild) :
    ∀ v t, Env.lookup v db.env = some t → ConstructorTerm db.sig t := fun v t hv =>
  termsBuild_term hw h (hw.envInTerms (v, t) (Env.mem_of_lookup hv))

theorem empty_termsBuild : Database.empty.TermsBuild := by
  intro f as h; exact absurd h (by simp)

theorem termsBuild_of_terms {db : Database}
    (h : ∀ t ∈ db.terms, ConstructorTerm db.sig t) : db.TermsBuild :=
  fun f as hm => h _ hm f as (Term.self_mem_subterms _)

theorem evalAction_termsBuild {db db' : Database}
    (hw : db.WF) (h : db.TermsBuild) (hcs : db.sig.AllConstructors)
    {a : Action} (hv : evalAction db a = some db') : db'.TermsBuild := by
  have hlk := termsBuild_lookup hw h
  have hbase : ∀ t ∈ db.terms, ConstructorTerm db.sig t := fun t ht => termsBuild_term hw h ht
  rcases evalAction_eq_some hv with ⟨e, t, rfl, he, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, he₁, he₂, -, rfl⟩
  · refine termsBuild_of_terms fun s hs => ?_
    rw [Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact hbase s hs'
    · exact fun g gs hg => eval_constructorTerm hlk e
        (by simpa only [Expr.evalAtom_eq_eval hcs] using he) g gs
        (Term.subterms_subset_of_mem hs' hg)
  · refine termsBuild_of_terms fun s hs => ?_
    rw [Database.addEq_terms] at hs
    rcases hs with hs' | hs'
    · rcases hs' with hs'' | hs''
      · exact hbase s hs''
      · exact fun g gs hg =>
          eval_constructorTerm hlk e₁ he₁ g gs (Term.subterms_subset_of_mem hs'' hg)
    · exact fun g gs hg =>
        eval_constructorTerm hlk e₂ he₂ g gs (Term.subterms_subset_of_mem hs' hg)

theorem evalActions_termsBuild {db db' : Database}
    (hw : db.WF) (h : db.TermsBuild) (hcs : db.sig.AllConstructors)
    {as : List Action}
    (hv : evalActions db as = some db') : db'.TermsBuild := by
  induction as generalizing db with
  | nil =>
      rw [evalActions_nil, Option.some_inj] at hv
      exact hv ▸ h
  | cons a as ih =>
      rw [evalActions_cons, Option.bind_eq_some_iff] at hv
      obtain ⟨d, hd, hrest⟩ := hv
      exact ih (evalAction_wf hw hd)
        (evalAction_termsBuild hw h hcs hd)
        (by rw [evalAction_sig hd]; exact hcs)
        hrest

theorem evalLocalActions_termsBuild {db db' : Database}
    (hw : db.WF) (h : db.TermsBuild) (hcs : db.sig.AllConstructors)
    {as : List Action} {σ : Env} (hσ : ∀ b ∈ σ, b.2 ∈ db.terms)
    (hv : evalLocalActions db as σ = some db') : db'.TermsBuild := by
  obtain ⟨d, hd, rfl⟩ := evalLocalActions_eq_some hv
  have hlf : ({ db with env := σ } : Database).TermsBuild := by
    intro f q ht; exact h f q (Database.terms_setEnv ▸ ht)
  intro f q ht
  rw [Database.terms_setEnvRules] at ht
  exact evalActions_termsBuild (hw.appendEnv hσ) hlf hcs hd f q ht

/-- A round can add only values built by its rule heads under source substitutions. -/
theorem termsBuild_runRules {R : RulesetName} {db : Database} (hw : db.WF)
    (h : db.TermsBuild) (hcs : db.sig.AllConstructors) : (RunRules R db).TermsBuild := by
  intro f q ht
  rw [RunRules.sig]
  rw [RunRules.eq_sUnion, Database.sUnion_terms] at ht
  rcases ht with ht | ht
  · exact h f q ht
  · obtain ⟨d, hd, ht⟩ := Set.mem_iUnion₂.mp ht
    obtain ⟨r, _, _, σ, hq, hfire⟩ := hd
    have hm := evalLocalActions_termsBuild hw h hcs hq.mem_terms hfire f q ht
    rwa [evalLocalActions_sig hfire] at hm

/-- Constructor declarations preserve the interpretation of existing values. With
complete atoms, no separate restriction on rule-head write actions is necessary. -/
theorem cmdStep_termsBuild {db db' : Database} (hc : db.CtorState) (h : db.TermsBuild)
    {c : Cmd} (hdecl : c.CtorDecl) (hstep : CmdStep db c db') : db'.TermsBuild := by
  obtain ⟨d, hreach, hcl⟩ := hstep.reach
  cases c with
  | rule r =>
      obtain rfl : d = { db with rules := insert r db.rules } := hreach
      obtain rfl : db' = { db with rules := insert r db.rules } := hcl.eq_of_allConstructors hc.sig
      exact fun f q ht => h f q (Database.terms_setRules ▸ ht)
  | run R =>
      obtain rfl : d = RunRules R db := hreach
      obtain rfl : db' = RunRules R db :=
        hcl.eq_of_allConstructors (by rw [RunRules.sig]; exact hc.sig)
      exact termsBuild_runRules hc.wf h hc.sig
  | saturate R =>
      have hsat : SaturateReach R db db' := cmdStep_saturate_iff.mp hstep
      refine (RunReach.induction (P := fun x => x.CtorState ∧ x.TermsBuild) ?_ hsat.reach
        ⟨hc, h⟩).2
      intro x y hx hxy
      obtain rfl : y = RunRules R x := hxy.eq_of_allConstructors hx.1.sig
      exact ⟨⟨RunRules.wf hx.1.wf, by rw [RunRules.sig]; exact hx.1.sig⟩,
        termsBuild_runRules hx.1.wf hx.2 hx.1.sig⟩
  | decl f dc =>
      obtain rfl : d = { db with sig := Function.update db.sig f (some dc) } := hreach
      obtain rfl : db' = { db with sig := Function.update db.sig f (some dc) } :=
        hcl.eq_of_allConstructors (hc.sig.sigBind hdecl)
      intro g q ht
      exact Signature.IsCtor.update hdecl (h g q (Database.terms_setSig ▸ ht))
  | check q =>
      obtain ⟨_, rfl⟩ := hreach
      rw [hcl.eq_of_allConstructors hc.sig]
      exact h

theorem programStep_termsBuild {db db' : Database} (hc : db.CtorState) (h : db.TermsBuild)
    {p : Program} (hdecl : p.CtorDecls) (hstep : ProgramStep db p db') : db'.TermsBuild := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hstep _ ih =>
      exact ih (hstep.ctorState hc (hdecl c List.mem_cons_self))
        (cmdStep_termsBuild hc h (hdecl c List.mem_cons_self) hstep)
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-- Every state reached by a constructor-source program satisfies the query readback's
source-value invariant, including intermediate command prefixes. -/
theorem termsBuild_of_programStep {P : Program} {src : Database}
    (hctors : P.CtorDecls) (h : ProgramStep Database.empty P src) : src.TermsBuild :=
  programStep_termsBuild Database.CtorState.empty empty_termsBuild hctors h

end Egglog.Congruence
