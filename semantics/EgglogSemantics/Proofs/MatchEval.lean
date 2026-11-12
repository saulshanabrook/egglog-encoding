import EgglogSemantics.Proofs.Eval

/-! Expression matching and evaluation. A matching expression has a value, and the pair
`e.eval σ = some t ∧ Expr.Matches db σ e` is stable under environments that agree on the
expression's variables, under a larger live set, and under equal meaning. -/

namespace Egglog

/-- Every matching expression has a defined value, including both operands of `min`. -/
theorem Expr.Matches.eval_exists {db : Database} {σ : Env} {e : Expr}
    (h : Expr.Matches db σ e) : ∃ t, e.eval σ = some t := by
  cases h with
  | lit _ => exact ⟨_, rfl⟩
  | var hv => exact ⟨_, hv⟩
  | @app f _ ts _ he _ => exact ⟨.app f ts, by simp [Expr.eval, he]⟩
  | min ha hb =>
    obtain ⟨a, ha⟩ := ha.eval_exists
    obtain ⟨b, hb⟩ := hb.eval_exists
    exact ⟨Term.least a b, by simp [Expr.eval, ha, hb]⟩

theorem Expr.MatchesList.eval_exists {db : Database} {σ : Env} {es : List Expr}
    (h : Expr.MatchesList db σ es) : ∃ ts, Expr.evalList es σ = some ts := by
  cases h with
  | nil => exact ⟨[], rfl⟩
  | cons he hes =>
    obtain ⟨t, ht⟩ := he.eval_exists
    obtain ⟨ts, hts⟩ := hes.eval_exists
    exact ⟨t :: ts, by simp [Expr.evalList, ht, hts]⟩

/-- Variables get existence from their bindings, not from a liveness premise. -/
theorem Expr.Matches.eval_cong {db : Database} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Cong db t t) {e : Expr} {t : Term}
    (h : e.eval σ = some t ∧ Expr.Matches db σ e) : Cong db t t := by
  obtain ⟨he, hm⟩ := h
  cases hm with
  | lit hl => cases he; exact hl.1
  | var hv => exact hσ _ _ he
  | app _ hs hl =>
    simp only [Expr.eval, hs, Option.map_some, Option.some.injEq] at he
    exact he ▸ hl.1
  | min ha hb =>
    obtain ⟨x, hx, hrest⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hrest
    have hca := Expr.Matches.eval_cong hσ ⟨hx, ha⟩
    have hcb := Expr.Matches.eval_cong hσ ⟨hy, hb⟩
    rcases Term.least_eq_or x y with he | he <;> rw [he]
    exacts [hca, hcb]

mutual

/-- With no subsumption, an instance whose minima are over variables matches as soon as
its result exists. `min` needs both operands, including the unchosen one, which are bound
variables. -/
theorem Expr.Matches.of_eval {db : Database} {σ : Env} (hX : db.subsumed = ∅) :
    ∀ {e : Expr} {t : Term}, e.MinOverVars → e.eval σ = some t → Cong db t t →
      e.eval σ = some t ∧ Expr.Matches db σ e
  | .lit l, _, _, he, ht => by
      cases he
      exact ⟨rfl, .lit (by simpa [Database.live, hX] using ht)⟩
  | .var v, _, _, he, _ => ⟨he, .var he⟩
  | .app f args, _, ho, he, ht => by
      obtain ⟨ts, hs, rfl⟩ := Option.map_eq_some_iff.mp he
      have hargs := Expr.MatchesList.of_eval hX (Expr.minOverVars_app ho) hs (fun t hmem =>
        Cong.subterm ht (.arg hmem (.refl t)))
      exact ⟨by simp [Expr.eval, hs],
        .app hargs.2 hs (by simpa [Database.live, hX] using ht)⟩
  | .min a b, _, ho, he, _ => by
      obtain ⟨ha, hb⟩ := Expr.minOverVars_min ho
      refine ⟨he, ?_⟩
      rw [Expr.eval_min, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, hmap⟩ := he
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp hmap
      exact .min (ha.matches hx) (hb.matches hy)

theorem Expr.MatchesList.of_eval {db : Database} {σ : Env} (hX : db.subsumed = ∅) :
    ∀ {es : List Expr} {ts : List Term}, Expr.MinOverVarsList es →
      Expr.evalList es σ = some ts → (∀ t ∈ ts, Cong db t t) →
      Expr.evalList es σ = some ts ∧ Expr.MatchesList db σ es
  | [], _, _, he, _ => ⟨he, .nil⟩
  | e :: es, _, ho, he, ht => by
      obtain ⟨t, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hs, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ho' := Expr.minOverVarsList_cons ho
      have ha := Expr.Matches.of_eval hX ho'.1 hfirst (ht t (by simp))
      have hargs := Expr.MatchesList.of_eval hX ho'.2 hs (fun u hu => ht u (List.mem_cons_of_mem t hu))
      exact ⟨by simp [Expr.evalList, hfirst, hs], .cons ha.2 hargs.2⟩

end

mutual

/-- Matching depends only on the expression's variables. -/
theorem Expr.matches_agreeOn {db : Database} {σ τ : Env} (e : Expr)
    (ha : ∀ v ∈ e.vars, Env.lookup v σ = Env.lookup v τ) :
    Expr.Matches db σ e ↔ Expr.Matches db τ e := by
  match e with
  | .lit _ => constructor <;> intro h <;> cases h with | lit hl => exact .lit hl
  | .var v =>
    have hv := ha v (by simp)
    constructor
    · intro h; cases h with | var hl => exact .var (by simpa only [← hv] using hl)
    · intro h; cases h with | var hl => exact .var (by simpa only [hv] using hl)
  | .app f args =>
    have he := Expr.evalList_agreeOn args ha
    have hm := Expr.matchesList_agreeOn (db := db) args ha
    constructor
    · intro h
      cases h with
      | app hl hs ht => exact .app (hm.mp hl) (by simpa only [← he] using hs) ht
    · intro h
      cases h with
      | app hl hs ht => exact .app (hm.mpr hl) (by simpa only [he] using hs) ht
  | .min a b =>
    have ha' := Expr.matches_agreeOn (db := db) a (fun v hv => ha v (by simp [hv]))
    have hb' := Expr.matches_agreeOn (db := db) b (fun v hv => ha v (by simp [hv]))
    constructor
    · intro h; cases h with | min h₁ h₂ => exact .min (ha'.mp h₁) (hb'.mp h₂)
    · intro h; cases h with | min h₁ h₂ => exact .min (ha'.mpr h₁) (hb'.mpr h₂)

theorem Expr.matchesList_agreeOn {db : Database} {σ τ : Env} (es : List Expr)
    (ha : ∀ v ∈ Expr.varsList es, Env.lookup v σ = Env.lookup v τ) :
    Expr.MatchesList db σ es ↔ Expr.MatchesList db τ es := by
  match es with
  | [] => exact ⟨fun _ => .nil, fun _ => .nil⟩
  | e :: es =>
    have he := Expr.matches_agreeOn (db := db) e (fun v hv => ha v (by simp [hv]))
    have hes := Expr.matchesList_agreeOn (db := db) es (fun v hv => ha v (by simp [hv]))
    constructor
    · intro h; cases h with | cons h₁ h₂ => exact .cons (he.mp h₁) (hes.mp h₂)
    · intro h; cases h with | cons h₁ h₂ => exact .cons (he.mpr h₁) (hes.mpr h₂)

end

theorem Expr.Matches.of_agreeOn {db : Database} {σ τ : Env} {e : Expr} {t : Term}
    (h : e.eval σ = some t ∧ Expr.Matches db σ e)
    (ha : ∀ v ∈ e.vars, Env.lookup v σ = Env.lookup v τ) :
    e.eval τ = some t ∧ Expr.Matches db τ e := by
  rwa [← e.eval_agreeOn ha, ← e.matches_agreeOn ha]

mutual

theorem Expr.Matches.mono_live {d e : Database} (hl : d.live ⊆ e.live)
    {σ : Env} {a : Expr} {t : Term}
    (h : a.eval σ = some t ∧ Expr.Matches d σ a) :
    a.eval σ = some t ∧ Expr.Matches e σ a := by
  refine ⟨h.1, ?_⟩
  cases h.2 with
  | lit ht => exact .lit (hl ht)
  | var hv => exact .var hv
  | app hm he ht => exact .app (Expr.MatchesList.mono_live hl ⟨he, hm⟩).2 he (hl ht)
  | min ha hb =>
    obtain ⟨a, hea⟩ := ha.eval_exists
    obtain ⟨b, heb⟩ := hb.eval_exists
    exact .min (Expr.Matches.mono_live hl ⟨hea, ha⟩).2 (Expr.Matches.mono_live hl ⟨heb, hb⟩).2

theorem Expr.MatchesList.mono_live {d e : Database} (hl : d.live ⊆ e.live)
    {σ : Env} {as : List Expr} {ts : List Term}
    (h : Expr.evalList as σ = some ts ∧ Expr.MatchesList d σ as) :
    Expr.evalList as σ = some ts ∧ Expr.MatchesList e σ as := by
  refine ⟨h.1, ?_⟩
  cases h.2 with
  | nil => exact .nil
  | cons ha has =>
    obtain ⟨t, ht⟩ := ha.eval_exists
    obtain ⟨ts, hts⟩ := has.eval_exists
    exact .cons (Expr.Matches.mono_live hl ⟨ht, ha⟩).2 (Expr.MatchesList.mono_live hl ⟨hts, has⟩).2

end

/-- Congruent child spellings denote the same live row. -/
theorem Database.live_app_congr {db : Database} {f : FnName} {as bs : List Term}
    (hl : Term.app f as ∈ db.live) (hc : CongList db as bs) :
    Term.app f bs ∈ db.live := by
  have h := Cong.congr hl.1 hc
  refine ⟨h.symm.trans h, ?_⟩
  rintro ⟨u, hu, g, cs, ds, heq, hequ, hcd⟩
  cases heq
  exact hl.2 ⟨u, hu, f, as, ds, rfl, hequ, hc.trans hcd⟩

mutual

/-- Ordering-free matching respects congruent bindings and equal meaning. -/
theorem Expr.Matches.transport {d e : Database} (hm : d.SameMeaning e) {σ τ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ Cong e t u) :
    ∀ {a : Expr} {t : Term}, a.OrderingFree →
      (a.eval σ = some t ∧ Expr.Matches d σ a) →
      ∃ u, (a.eval τ = some u ∧ Expr.Matches e τ a) ∧ Cong e t u
  | .lit l, _, _, ⟨he, hl⟩ => by
      cases he
      cases hl with
      | lit hl =>
        have hl' := (hm.live _).mp hl
        exact ⟨.lit l, ⟨rfl, .lit hl'⟩, hl'.1⟩
  | .var v, _, _, ⟨hv, _⟩ => by
      obtain ⟨u, hu, hc⟩ := hσ v _ hv
      exact ⟨u, ⟨hu, .var hu⟩, hc⟩
  | .app f args, _, ho, ⟨he, hl⟩ => by
      cases hl with
      | app hargs hs hl =>
        simp only [Expr.eval, hs, Option.map_some, Option.some.injEq] at he
        subst he
        obtain ⟨us, hus, hc⟩ := Expr.MatchesList.transport hm hσ ho ⟨hs, hargs⟩
        have hl' := (hm.live _).mp hl
        exact ⟨_, ⟨by simp [Expr.eval, hus.1],
          .app hus.2 hus.1 (Database.live_app_congr hl' hc)⟩, .congr hl'.1 hc⟩
  | .min _ _, _, ho, _ => by simp [Expr.OrderingFree, Expr.hasMin] at ho

theorem Expr.MatchesList.transport {d e : Database} (hm : d.SameMeaning e) {σ τ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t →
      ∃ u, Env.lookup v τ = some u ∧ Cong e t u) :
    ∀ {as : List Expr} {ts : List Term}, Expr.OrderingFreeList as →
      (Expr.evalList as σ = some ts ∧ Expr.MatchesList d σ as) →
      ∃ us, (Expr.evalList as τ = some us ∧ Expr.MatchesList e τ as) ∧ CongList e ts us
  | [], _, _, ⟨he, _⟩ => by
      cases he
      exact ⟨[], ⟨rfl, .nil⟩, .nil⟩
  | a :: as, _, ho, ⟨he, hl⟩ => by
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hs, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ho' : a.OrderingFree ∧ Expr.OrderingFreeList as := by
        simpa [Expr.OrderingFreeList, Expr.OrderingFree, Expr.hasMinList] using ho
      cases hl with
      | cons ha has =>
        obtain ⟨u, hu, hc⟩ := Expr.Matches.transport hm hσ ho'.1 ⟨ht, ha⟩
        obtain ⟨us, hus, hcs⟩ := Expr.MatchesList.transport hm hσ ho'.2 ⟨hs, has⟩
        exact ⟨u :: us, ⟨by simp [Expr.evalList, hu.1, hus.1], .cons hu.2 hus.2⟩, .cons hc hcs⟩

end

end Egglog
