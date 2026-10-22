import EgglogSemantics.Proofs.SameMeaning
import EgglogSemantics.Proofs.EnvTransform
import EgglogSemantics.Proofs.Query

/-! Ordering-free source evaluation and matching respect inferred constructor facts. -/

namespace Egglog.SourceMeaning

open InferredFacts

/-- Each original binding has a represented counterpart under the same variable. -/
def EnvRelated (d : Database) (σ τ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t →
    ∃ u, Env.lookup v τ = some u ∧ d.Infers t u

mutual

/-- Constructor syntax respects equal interpreted variable values. This statement
also handles expressions whose result has not been represented yet. -/
theorem eval_interpret {d : Database} {σ τ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ interpret d t = interpret d u) :
    ∀ (e : Expr) {t : Term}, e.OrderingFree → e.eval σ = some t →
      ∃ u, e.eval τ = some u ∧ interpret d t = interpret d u
  | .lit l, t, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨.lit l, rfl, rfl⟩
  | .var v, t, _, he => by
      obtain ⟨u, hu, hi⟩ := hσ v t he
      exact ⟨u, hu, hi⟩
  | .app f args, t, hn, he => by
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨us, hus, hi⟩ := evalList_interpret hσ args hn hts
      refine ⟨.app f us, ?_, congrArg (interpretApp d f) hi⟩
      simp only [Expr.eval, hus, Option.map_some]
  | .min _ _, _, hn, _ => by
      simp [Expr.OrderingFree, Expr.hasMin] at hn

theorem evalList_interpret {d : Database} {σ τ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ interpret d t = interpret d u) :
    ∀ (es : List Expr) {ts : List Term}, Expr.OrderingFreeList es →
      Expr.evalList es σ = some ts →
      ∃ us, Expr.evalList es τ = some us ∧ interpretList d ts = interpretList d us
  | [], ts, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨[], rfl, rfl⟩
  | e :: es, ts, hn, he => by
      have hn' : e.OrderingFree ∧ Expr.OrderingFreeList es := by
        simpa [Expr.OrderingFreeList, Expr.hasMinList, Expr.OrderingFree] using hn
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨u, hu, hi⟩ := eval_interpret hσ e hn'.1 ht
      obtain ⟨us, hus, his⟩ := evalList_interpret hσ es hn'.2 hts
      exact ⟨u :: us, by simp [Expr.evalList, hu, hus], congrArg₂ List.cons hi his⟩

end

theorem EnvRelated.mono {d e : Database} {σ τ : Env} (h : EnvRelated d σ τ)
    (hc : d.Contained e) : EnvRelated e σ τ := by
  intro v t ht
  obtain ⟨u, hu, hi⟩ := h v t ht
  exact ⟨u, hu, infers_mono hc hi⟩

theorem EnvRelated.interpret {d : Database} (hw : d.WF) {σ τ : Env}
    (h : EnvRelated d σ τ) : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ interpret d t = interpret d u := by
  intro v t ht
  obtain ⟨u, hu, hi⟩ := h v t ht
  obtain ⟨w, _, hti, hui⟩ := (infers_iff_interpret hw).mp hi
  exact ⟨u, hu, hti.trans hui.symm⟩

/-- The same constructor expression evaluated at related bindings yields
hypothetically congruent terms, even before either output is recorded. -/
theorem eval_congOn {d : Database} (hw : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {e : Expr} {t : Term}
    (hn : e.OrderingFree) (he : e.eval σ = some t) :
    ∃ u, e.eval τ = some u ∧ StoredCongOn d [t, u] t u := by
  obtain ⟨u, hu, _⟩ := eval_interpret (hσ.interpret hw) e hn he
  let D := d.withOperands [t, u]
  have hD : D.WF := hw.addTerms [t, u]
  have hσ' := hσ.mono (Database.Contained.addTerms [t, u] d)
  obtain ⟨u', hu', hi⟩ := eval_interpret (hσ'.interpret hD) e hn he
  obtain rfl := Option.some.inj (hu.symm.trans hu')
  have htD : t ∈ D.terms := Database.mem_addTerms (by simp)
  have huD : u ∈ D.terms := Database.mem_addTerms (by simp)
  refine ⟨u, hu, (infers_iff_cong_of_held hD htD huD).mp ?_⟩
  exact (infers_iff_interpret hD).mpr
    ⟨t, htD, interpret_of_held hD t htD,
      hi.symm.trans (interpret_of_held hD t htD)⟩

/-- Ordering-free patterns transfer to consistently chosen represented bindings. -/
theorem matches_transport {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) {σ τ : Env}
    (hσ : EnvRelated e σ τ) {p : Pattern} (hn : p.OrderingFree)
    (hm : Matches d p σ) : Matches e p τ := by
  cases hm using Matches.storedCases with
  | @expr exp _ w t hw hval hcong =>
      have ht : d.Infers t t :=
        infers_right hd (infers_of_congOn hd (infers_of_held hw) hcong)
      obtain ⟨u, hu, hi⟩ := eval_interpret (hσ.interpret he) exp hn hval
      obtain ⟨w', hw', hti, _⟩ := (infers_iff_interpret he).mp ((h.inferred _ _).mp ht)
      exact .expr hw' hu
        (congOn_of_interpret he u hw' (hi.symm.trans hti)).symm
  | @eq a b _ w ta tb hw hva hvb hwa hab =>
      obtain ⟨ua, hua, hia⟩ := eval_interpret (hσ.interpret he) a hn.1 hva
      obtain ⟨ub, hub, hib⟩ := eval_interpret (hσ.interpret he) b hn.2 hvb
      have hti := (h.inferred ta tb).mp ⟨w, hw, hwa, hab⟩
      obtain ⟨w', hw', hai, hbi⟩ := (infers_iff_interpret he).mp hti
      obtain ⟨v, hv, hva', hvb'⟩ := (infers_iff_interpret he).mpr
        ⟨w', hw', hia.symm.trans hai, hib.symm.trans hbi⟩
      exact .eq hv hua hub hva' hvb'
  | @unequal a b _ ta tb hva hvb hta htb hne =>
      obtain ⟨ua, hua, hia⟩ := eval_interpret (hσ.interpret he) a hn.1 hva
      obtain ⟨ub, hub, hib⟩ := eval_interpret (hσ.interpret he) b hn.2 hvb
      have transport : ∀ t u, interpret e t = interpret e u → Cong d t t → Cong e u u := by
        intro t u hi ht
        obtain ⟨w, hw, hti, _⟩ := (infers_iff_interpret he).mp
          ((h.inferred t t).mp (InferredFacts.congr_iff_infers.mp ht))
        exact InferredFacts.congr_iff_infers.mpr
          ((infers_iff_interpret he).mpr ⟨w, hw, hi.symm.trans hti, hi.symm.trans hti⟩)
      refine .unequal hua hub (transport _ _ hia hta) (transport _ _ hib htb) ?_
      intro hc
      obtain ⟨w, hw, hai, hbi⟩ := (infers_iff_interpret he).mp
        (InferredFacts.congr_iff_infers.mp hc)
      apply hne
      exact InferredFacts.congr_iff_infers.mpr ((h.inferred ta tb).mpr
        ((infers_iff_interpret he).mpr ⟨w, hw, hia.trans hai, hib.trans hbi⟩))


open Classical in
/-- Choose one recorded representative for each inferred class. -/
noncomputable def representative (d : Database) (hw : d.WF) (t : Term) : Term :=
  if h : d.Infers t t then ((infers_iff_interpret hw).mp h).choose else t

theorem representative_spec {d : Database} (hw : d.WF) {t : Term}
    (ht : d.Infers t t) :
    representative d hw t ∈ d.terms ∧ d.Infers t (representative d hw t) := by
  simp only [representative, dif_pos ht]
  have hr := ((infers_iff_interpret hw).mp ht).choose_spec
  exact ⟨hr.1, (infers_iff_interpret hw).mpr
    ⟨_, hr.1, hr.2.1, interpret_of_held hw _ hr.1⟩⟩

theorem envRelated_map {d e : Database} {σ : Env} {w : Term → Term}
    (hs : ∀ b ∈ σ, b.2 ∈ d.terms)
    (hw : ∀ t ∈ d.terms, e.Infers t (w t)) :
    EnvRelated e σ (Env.mapVals w σ) := by
  intro v t ht
  refine ⟨w t, ?_, hw t (hs (v, t) (Env.mem_of_lookup ht))⟩
  simp [lookup_mapVals, ht]

theorem validSubst_map {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) {w : Term → Term}
    (hw : ∀ t ∈ d.terms, w t ∈ e.terms ∧ e.Infers t (w t))
    {p : Pattern} {σ : Env} (hn : p.OrderingFree) (hs : ValidSubst d p σ) :
    ValidSubst e p (Env.mapVals w σ) := by
  refine ⟨⟨?_, ?_⟩, matches_transport hd he h
    (envRelated_map hs.1.2 (fun t ht => (hw t ht).2)) hn hs.2⟩
  · simpa [dom_mapVals] using hs.1.1
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
    exact (hw _ (hs.1.2 a ha)).1

theorem union2_map (w : Term → Term) {σ τ ρ : Env} (h : Env.Union2 σ τ ρ) :
    Env.Union2 (Env.mapVals w σ) (Env.mapVals w τ) (Env.mapVals w ρ) := by
  refine ⟨?_, by rw [h.2, mapVals_append]⟩
  intro b hb t ht
  obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
  rw [lookup_mapVals] at ht
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact congrArg w (h.1 a ha u hu)

theorem unionAll_map (w : Term → Term) {σs : List Env} {σ : Env}
    (h : Env.UnionAll σs σ) :
    Env.UnionAll (σs.map (Env.mapVals w)) (Env.mapVals w σ) := by
  induction h with
  | nil => exact .nil
  | single σ => exact .single _
  | step h _ ih => exact .step (union2_map w h) ih

theorem validQuerySubst_map {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) {w : Term → Term}
    (hw : ∀ t ∈ d.terms, w t ∈ e.terms ∧ e.Infers t (w t))
    {q : Query} {σ : Env} (hn : ∀ p ∈ q, p.OrderingFree)
    (hs : ValidQuerySubst d q σ) : ValidQuerySubst e q (Env.mapVals w σ) := by
  obtain ⟨σs, hps, hu⟩ := hs
  refine ⟨σs.map (Env.mapVals w), ?_, unionAll_map w hu⟩
  clear hu
  induction hps with
  | nil => exact .nil
  | @cons p σ ps σs hp hps ih =>
      exact .cons (validSubst_map hd he h hw (hn p (by simp)) hp)
        (ih (fun p hp => hn p (List.mem_cons_of_mem _ hp)))

/-- A source match can be re-expressed using only recorded representatives of a
state with the same inferred facts. The returned relation supports head transport. -/
theorem validQuerySubst_transport {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e)
    {q : Query} {σ : Env} (hn : ∀ p ∈ q, p.OrderingFree)
    (hs : ValidQuerySubst d q σ) :
    ∃ τ, ValidQuerySubst e q τ ∧ EnvRelated e σ τ := by
  let w := representative e he
  have hw : ∀ t ∈ d.terms, w t ∈ e.terms ∧ e.Infers t (w t) := by
    intro t ht
    exact representative_spec he ((h.inferred t t).mp (infers_of_held ht))
  exact ⟨Env.mapVals w σ, validQuerySubst_map hd he h hw hn hs,
    envRelated_map hs.mem_terms (fun t ht => (hw t ht).2)⟩

/-- Ordering-free constructor queries observe only the inferred state. -/
theorem queryHolds_iff {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e)
    {q : Query} (hn : ∀ p ∈ q, p.OrderingFree) : QueryHolds d q ↔ QueryHolds e q := by
  simp only [queryHolds_iff_validQuerySubst]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ, _⟩ := validQuerySubst_transport hd he h hn hσ
    exact ⟨τ, hτ⟩
  · rintro ⟨τ, hτ⟩
    obtain ⟨σ, hσ, _⟩ := validQuerySubst_transport he hd h.symm hn hτ
    exact ⟨σ, hσ⟩

private theorem evalAction_transport {d e d' : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e)
    {σ τ : Env} (hσ : EnvRelated e σ τ) {a : Action} (hn : a.OrderingFree)
    (hdf : a.DeleteFree)
    (hs : evalAction σ d a = some d') :
    ∃ e', evalAction τ e a = some e' ∧
      d'.SameMeaning e' := by
  cases a with
  | expr exp =>
      simp only [evalAction] at hs
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨u, hu, htu⟩ := eval_congOn he hσ hn ht
      refine ⟨e.addTerm u, ?_, ?_⟩
      · simp [evalAction, hu]
      · exact (h.addTerm hd he t).trans
          (sameMeaning_addTerm_congr he
            htu)
  | union a b =>
      obtain ⟨ta, hta, hs⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨tb, htb, hs⟩ := Option.bind_eq_some_iff.mp hs
      split at hs
      next => cases hs
      next hnl =>
        obtain rfl := Option.some.inj hs
        have hno : ta.isLit = false ∧ tb.isLit = false := by
          simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true] using hnl
        obtain ⟨ua, hua, hca⟩ := eval_congOn he hσ hn.1 hta
        obtain ⟨ub, hub, hcb⟩ := eval_congOn he hσ hn.2 htb
        have hnoa : ua.isLit = false := by
          cases hi : ua.isLit with
          | false => rfl
          | true =>
              have heq := hca.eq_of_isLit (he.addTerms [ta, ua]).litsIsolated (Or.inr hi)
              simp [heq, hi] at hno
        have hnob : ub.isLit = false := by
          cases hi : ub.isLit with
          | false => rfl
          | true =>
              have heq := hcb.eq_of_isLit (he.addTerms [tb, ub]).litsIsolated (Or.inr hi)
              simp [heq, hi] at hno
        have hlit : ta.isLit ∨ tb.isLit → ta = tb := by simp [hno.1, hno.2]
        have hlit' : ua.isLit ∨ ub.isLit → ua = ub := by simp [hnoa, hnob]
        refine ⟨e.addEq ua ub, ?_, ?_⟩
        · simp [evalAction, hua, hub, hnoa, hnob]
        · exact (h.addEq hd he ta tb hlit).trans
            (sameMeaning_addEq_congr he
              hca
              hcb
              hlit hlit')
  | delete _ => simp [Action.DeleteFree, Action.monotoneB] at hdf

private theorem evalActions_transport {d e d' : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e)
    {σ τ : Env} (hσ : EnvRelated e σ τ) {as : List Action} (hn : Actions.OrderingFree as)
    (hdf : Actions.DeleteFree as)
    (hs : evalActions σ d as = some d') :
    ∃ e', evalActions τ e as = some e' ∧
      d'.SameMeaning e' := by
  induction as generalizing d e with
  | nil =>
      obtain rfl := Option.some.inj hs
      exact ⟨e, rfl, h⟩
  | cons a as ih =>
      obtain ⟨mid, hm, hrest⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨mid', hm', hh⟩ := evalAction_transport hd he h hσ hn.1 (hdf _ (by simp)) hm
      have hrel : EnvRelated mid' σ τ :=
        hσ.mono (evalAction_contained (hdf _ (by simp)) hm')
      obtain ⟨e', he', hh'⟩ := ih (evalAction_wf hd hm)
        (evalAction_wf he hm')
        hh hrel hn.2 (fun a ha => hdf a (List.mem_cons_of_mem _ ha)) hrest
      exact ⟨e', by simp [evalActions, hm', he'], hh'⟩

/-- Delete-free, ordering-free heads transport along semantic equivalence. -/
theorem evalLocalActions_transport {d e d' : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) {σ τ : Env} (hσ : EnvRelated e σ τ)
    {as : List Action} (hn : Actions.OrderingFree as) (hdf : Actions.DeleteFree as)
    (hr : evalActions σ d as = some d') :
    ∃ e', evalActions τ e as = some e' ∧ d'.SameMeaning e' :=
  evalActions_transport hd he h hσ hn hdf hr

end Egglog.SourceMeaning
