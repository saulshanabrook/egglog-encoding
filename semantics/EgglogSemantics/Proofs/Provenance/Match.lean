import EgglogSemantics.Proofs.Provenance.Good
import EgglogSemantics.Proofs.Match
import EgglogSemantics.Proofs.MatchEval
import EgglogSemantics.Proofs.Source.Ctors

/-! Query matching is unchanged by the firing log when query names avoid the log prefix
and every variable is an argument of an application pattern. -/

namespace Egglog.Provenance

/-! ### Data names -/

/-- A name outside the log namespace. -/
abbrev DataName (f : FnName) : Prop := firePrefix.isPrefixOf f = false

/-- Every name the expression applies is a data name. -/
def LogFreeExpr (e : Expr) : Prop := ∀ fk ∈ e.ctors, DataName fk.1

def LogFreeExprs (es : List Expr) : Prop := ∀ fk ∈ Expr.ctorsList es, DataName fk.1

/-- Every name the pattern applies is a data name. -/
def LogFreePattern (p : Pattern) : Prop := ∀ fk ∈ p.ctors, DataName fk.1

/-- Every name the query applies is a data name. -/
def LogFreeQuery (q : Query) : Prop := ∀ p ∈ q, LogFreePattern p

theorem LogFreeExpr.app {f : FnName} {args : List Expr} (h : LogFreeExpr (.app f args)) :
    DataName f ∧ LogFreeExprs args :=
  ⟨h (f, args.length) (by rw [Expr.ctors]; exact List.mem_cons_self),
    fun fk hk => h fk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk)⟩

theorem LogFreeExpr.min {a b : Expr} (h : LogFreeExpr (.min a b)) :
    LogFreeExpr a ∧ LogFreeExpr b :=
  ⟨fun fk hk => h fk (by rw [Expr.ctors]; exact List.mem_append_left _ hk),
    fun fk hk => h fk (by rw [Expr.ctors]; exact List.mem_append_right _ hk)⟩

theorem LogFreeExprs.cons {e : Expr} {es : List Expr} (h : LogFreeExprs (e :: es)) :
    LogFreeExpr e ∧ LogFreeExprs es :=
  ⟨fun fk hk => h fk (by rw [Expr.ctorsList]; exact List.mem_append_left _ hk),
    fun fk hk => h fk (by rw [Expr.ctorsList]; exact List.mem_append_right _ hk)⟩

theorem LogFreePattern.expr {e : Expr} (h : LogFreePattern (.expr e)) : LogFreeExpr e := h

theorem LogFreePattern.eq {a b : Expr} (h : LogFreePattern (.eq a b)) :
    LogFreeExpr a ∧ LogFreeExpr b :=
  ⟨fun fk hk => h fk (List.mem_append_left _ hk), fun fk hk => h fk (List.mem_append_right _ hk)⟩

theorem LogFreePattern.ne {a b : Expr} (h : LogFreePattern (.ne a b)) :
    LogFreeExpr a ∧ LogFreeExpr b :=
  ⟨fun fk hk => h fk (List.mem_append_left _ hk), fun fk hk => h fk (List.mem_append_right _ hk)⟩

/-! ### The shadow of an instrumented state -/

/-- What matching sees of an instrumented state `d'` of `d`: the same subsumed rows and,
apart from log rows, the same terms; the original holds no log row. -/
structure Shadow (d d' : Database) : Prop where
  good : Good d
  good' : Good d'
  subsumed : d'.subsumed = d.subsumed
  terms : ∀ t, ¬ IsLog t → (t ∈ d'.terms ↔ t ∈ d.terms)
  noLog : ∀ t ∈ d.terms, ¬ IsLog t

namespace Shadow

variable {d d' : Database} (h : Shadow d d')
include h

theorem terms_sub : d.terms ⊆ d'.terms := fun t ht => (h.terms t (h.noLog t ht)).mpr ht

theorem mem_terms_of_not_log {t : Term} (ht : t ∈ d'.terms) (hl : ¬ IsLog t) : t ∈ d.terms :=
  (h.terms t hl).mp ht

theorem live_iff {t : Term} (hl : ¬ IsLog t) : t ∈ d'.live ↔ t ∈ d.live := by
  rw [h.good'.live_iff, h.good.live_iff, h.terms t hl, h.subsumed]

theorem live_sub : d.live ⊆ d'.live := by
  intro t ht
  have hl : ¬ IsLog t := h.noLog t ((h.good.live_iff).mp ht).1
  exact (h.live_iff hl).mpr ht

end Shadow

/-! ### Keyed variables are bound inside live rows -/

theorem mem_evalList_of_mem {σ : Env} : ∀ {es : List Expr} {ts : List Term},
    Expr.evalList es σ = some ts → ∀ {e : Expr}, e ∈ es → ∃ t, e.eval σ = some t ∧ t ∈ ts
  | [], _, _, _, he => by simp at he
  | e :: es, ts, h, e', he => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨t, ht, List.mem_cons_self⟩
      · obtain ⟨u, hu, hmem⟩ := mem_evalList_of_mem hus he
        exact ⟨u, hu, List.mem_cons_of_mem _ hmem⟩

mutual

/-- A keyed variable of a matching expression is bound to an argument of a live row the
expression names. -/
theorem argVar_matched {db : Database} {σ : Env} {v : Var} :
    ∀ {e : Expr}, Expr.ArgVar v e → Expr.Matches db σ e →
      ∃ f ts t, Term.app f ts ∈ db.live ∧ (f, ts.length) ∈ e.ctors ∧
        Env.lookup v σ = some t ∧ t ∈ ts
  | .lit _, hv, _ => hv.elim
  | .var _, hv, _ => hv.elim
  | .app f args, hv, hm => by
      cases hm with
      | app hargs hts hl =>
        rcases hv with hv | hv
        · obtain ⟨t, ht, hmem⟩ := mem_evalList_of_mem hts hv
          refine ⟨f, _, t, hl, ?_, ht, hmem⟩
          rw [Expr.ctors, Expr.evalList_length hts]
          exact List.mem_cons_self
        · obtain ⟨g, us, t, hl', hg, ht, hmem⟩ := argVarList_matched hv hargs
          exact ⟨g, us, t, hl', by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hg, ht, hmem⟩
  | .min a b, hv, hm => by
      cases hm with
      | min ha hb =>
        rcases hv with hv | hv
        · obtain ⟨g, us, t, hl, hg, ht, hmem⟩ := argVar_matched hv ha
          exact ⟨g, us, t, hl, by rw [Expr.ctors]; exact List.mem_append_left _ hg, ht, hmem⟩
        · obtain ⟨g, us, t, hl, hg, ht, hmem⟩ := argVar_matched hv hb
          exact ⟨g, us, t, hl, by rw [Expr.ctors]; exact List.mem_append_right _ hg, ht, hmem⟩

theorem argVarList_matched {db : Database} {σ : Env} {v : Var} :
    ∀ {es : List Expr}, Expr.ArgVarList v es → Expr.MatchesList db σ es →
      ∃ f ts t, Term.app f ts ∈ db.live ∧ (f, ts.length) ∈ Expr.ctorsList es ∧
        Env.lookup v σ = some t ∧ t ∈ ts
  | [], hv, _ => hv.elim
  | e :: es, hv, hm => by
      cases hm with
      | cons he hes =>
        rcases hv with hv | hv
        · obtain ⟨g, us, t, hl, hg, ht, hmem⟩ := argVar_matched hv he
          exact ⟨g, us, t, hl, by rw [Expr.ctorsList]; exact List.mem_append_left _ hg, ht, hmem⟩
        · obtain ⟨g, us, t, hl, hg, ht, hmem⟩ := argVarList_matched hv hes
          exact ⟨g, us, t, hl, by rw [Expr.ctorsList]; exact List.mem_append_right _ hg, ht,
            hmem⟩

end

theorem pattern_argVar_matched {db : Database} {σ : Env} {v : Var} {p : Pattern}
    (hv : Pattern.ArgVar v p) (hm : Matches db p σ) :
    ∃ f ts t, Term.app f ts ∈ db.live ∧ (f, ts.length) ∈ p.ctors ∧
      Env.lookup v σ = some t ∧ t ∈ ts := by
  cases hm with
  | atom hl => exact argVar_matched hv hl
  | equal hl₁ hl₂ _ _ _ | unequal hl₁ hl₂ _ _ _ =>
    rcases hv with hv | hv
    · obtain ⟨g, us, t, hl, hg, ht, hmem⟩ := argVar_matched hv hl₁
      exact ⟨g, us, t, hl, List.mem_append_left _ hg, ht, hmem⟩
    · obtain ⟨g, us, t, hl, hg, ht, hmem⟩ := argVar_matched hv hl₂
      exact ⟨g, us, t, hl, List.mem_append_right _ hg, ht, hmem⟩

/-! ### Matching through the shadow -/

mutual

/-- An expression of data names that matches in the instrumented state matches in the
original: every row it reads is a data row. -/
theorem matches_of_shadow {d d' : Database} (h : Shadow d d') {σ : Env} :
    ∀ {e : Expr} {t : Term}, LogFreeExpr e →
      (e.eval σ = some t ∧ Expr.Matches d' σ e) → e.eval σ = some t ∧ Expr.Matches d σ e
  | .lit l, _, _, ⟨he, hm⟩ => by
      cases hm with
      | lit hl => exact ⟨he, .lit ((h.live_iff (not_isLog_lit l)).mp hl)⟩
  | .var _, _, _, ⟨he, hm⟩ => by
      cases hm with
      | var hv => exact ⟨he, .var hv⟩
  | .app f args, _, hf, ⟨he, hm⟩ => by
      cases hm with
      | app hargs hts hl =>
        obtain ⟨hf, hargs'⟩ := hf.app
        have hl' := (h.live_iff (not_isLog_app hf)).mp hl
        exact ⟨he, .app (matchesList_of_shadow h hargs' ⟨hts, hargs⟩).2 hts hl'⟩
  | .min a b, _, hf, ⟨he, hm⟩ => by
      cases hm with
      | min ha hb =>
        obtain ⟨x, hx⟩ := ha.eval_exists
        obtain ⟨y, hy⟩ := hb.eval_exists
        exact ⟨he, .min (matches_of_shadow h hf.min.1 ⟨hx, ha⟩).2
          (matches_of_shadow h hf.min.2 ⟨hy, hb⟩).2⟩

theorem matchesList_of_shadow {d d' : Database} (h : Shadow d d') {σ : Env} :
    ∀ {es : List Expr} {ts : List Term}, LogFreeExprs es →
      (Expr.evalList es σ = some ts ∧ Expr.MatchesList d' σ es) →
        Expr.evalList es σ = some ts ∧ Expr.MatchesList d σ es
  | [], _, _, ⟨he, _⟩ => ⟨he, .nil⟩
  | e :: es, _, hf, ⟨he, hm⟩ => by
      cases hm with
      | cons h₁ h₂ =>
        obtain ⟨t, ht⟩ := h₁.eval_exists
        obtain ⟨ts, hts⟩ := h₂.eval_exists
        exact ⟨he, .cons (matches_of_shadow h hf.cons.1 ⟨ht, h₁⟩).2
          (matchesList_of_shadow h hf.cons.2 ⟨hts, h₂⟩).2⟩

end

section

variable {d d' : Database} (h : Shadow d d')
include h

/-- A pattern of data names that matches in the instrumented state under bindings the
original holds matches in the original. -/
theorem pattern_of_shadow {σ : Env} (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ d.terms)
    {p : Pattern} (hp : LogFreePattern p) (hm : Matches d' p σ) : Matches d p σ := by
  have hc : ∀ v t, Env.lookup v σ = some t → Cong d t t :=
    fun v t hv => Database.toCong (hσ v t hv)
  cases hm with
  | atom hl =>
    obtain ⟨t, he⟩ := hl.eval_exists
    exact .atom (matches_of_shadow h hp.expr ⟨he, hl⟩).2
  | equal hl₁ hl₂ he₁ he₂ hcong =>
    have h₁ := matches_of_shadow h hp.eq.1 ⟨he₁, hl₁⟩
    have h₂ := matches_of_shadow h hp.eq.2 ⟨he₂, hl₂⟩
    obtain ⟨rfl, _⟩ := h.good'.cong_iff.mp hcong
    exact .equal h₁.2 h₂.2 he₁ he₂ (Expr.Matches.eval_cong hc h₁)
  | unequal hl₁ hl₂ he₁ he₂ hne =>
    have h₁ := matches_of_shadow h hp.ne.1 ⟨he₁, hl₁⟩
    have h₂ := matches_of_shadow h hp.ne.2 ⟨he₂, hl₂⟩
    refine .unequal h₁.2 h₂.2 he₁ he₂ fun hcong => hne ?_
    obtain ⟨rfl, ht⟩ := h.good.cong_iff.mp hcong
    exact h.good'.cong_iff.mpr ⟨rfl, h.terms_sub ht⟩

/-- A pattern that matches in the original under bindings the original holds matches in
the instrumented state. -/
theorem pattern_of_shadow' {σ : Env} (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ d.terms)
    {p : Pattern} (hm : Matches d p σ) : Matches d' p σ := by
  have hc : ∀ v t, Env.lookup v σ = some t → Cong d t t :=
    fun v t hv => Database.toCong (hσ v t hv)
  cases hm with
  | atom hl =>
    obtain ⟨t, he⟩ := hl.eval_exists
    exact .atom (Expr.Matches.mono_live h.live_sub ⟨he, hl⟩).2
  | equal hl₁ hl₂ he₁ he₂ hcong =>
    obtain ⟨rfl, ht⟩ := h.good.cong_iff.mp hcong
    exact .equal (Expr.Matches.mono_live h.live_sub ⟨he₁, hl₁⟩).2
      (Expr.Matches.mono_live h.live_sub ⟨he₂, hl₂⟩).2 he₁ he₂
      (h.good'.cong_iff.mpr ⟨rfl, h.terms_sub ht⟩)
  | unequal hl₁ hl₂ he₁ he₂ hne =>
    refine .unequal (Expr.Matches.mono_live h.live_sub ⟨he₁, hl₁⟩).2
      (Expr.Matches.mono_live h.live_sub ⟨he₂, hl₂⟩).2 he₁ he₂ fun hcong => hne ?_
    obtain ⟨rfl, _⟩ := h.good'.cong_iff.mp hcong
    exact Expr.Matches.eval_cong hc ⟨he₁, hl₁⟩

/-- A keyed query of data names matches in the instrumented state exactly as in the
original. -/
theorem queryMatches_of_shadow {q : Query} (hk : Query.VarsKeyed q) (hq : LogFreeQuery q)
    {σ : Env} (hm : QueryMatches d' q σ) : QueryMatches d q σ := by
  have hnd : (Env.dom σ).Nodup := hm.1.1.nodup_iff.mpr (Query.vars_nodup q)
  have hσ : ∀ v t, Env.lookup v σ = some t → t ∈ d.terms := by
    intro v t hv
    have hdom : v ∈ Env.dom σ := Env.lookup_isSome_iff_mem_dom.mp (by rw [hv]; rfl)
    obtain ⟨p, hp, hvp⟩ := hk v (hm.1.1.mem_iff.mp hdom)
    obtain ⟨f, ts, t', hl, hf, hv', hmem⟩ := pattern_argVar_matched hvp (hm.2 p hp)
    obtain rfl : t = t' := Option.some.inj (hv.symm.trans hv')
    have hrow : Term.app f ts ∈ d.terms :=
      h.mem_terms_of_not_log (h.good'.live_iff.mp hl).1 (not_isLog_app (hq p hp _ hf))
    exact Database.subtermClosed d _ hrow (Term.IsSubterm.arg hmem (.refl t))
  refine ⟨⟨hm.1.1, fun b hb => ?_⟩, fun p hp => pattern_of_shadow h hσ (hq p hp) (hm.2 p hp)⟩
  rw [h.good.reps_eq]
  exact hσ b.1 b.2 ((Env.lookup_eq_some_iff_mem hnd).mpr hb)

theorem queryMatches_of_shadow' {q : Query} {σ : Env} (hm : QueryMatches d q σ) :
    QueryMatches d' q σ := by
  have hσ : ∀ v t, Env.lookup v σ = some t → t ∈ d.terms :=
    fun v t hv => hm.1.mem_terms (v, t) (Env.mem_of_lookup hv)
  refine ⟨⟨hm.1.1, fun b hb => ?_⟩, fun p hp => pattern_of_shadow' h hσ (hm.2 p hp)⟩
  rw [h.good'.reps_eq]
  exact h.terms_sub (hm.1.mem_terms b hb)

theorem queryMatches_iff {q : Query} (hk : Query.VarsKeyed q) (hq : LogFreeQuery q)
    {σ : Env} : QueryMatches d' q σ ↔ QueryMatches d q σ :=
  ⟨queryMatches_of_shadow h hk hq, queryMatches_of_shadow' h⟩

theorem queryHolds_iff {q : Query} (hk : Query.VarsKeyed q) (hq : LogFreeQuery q) :
    QueryHolds d' q ↔ QueryHolds d q :=
  exists_congr fun _ => queryMatches_iff h hk hq

end

end Egglog.Provenance
