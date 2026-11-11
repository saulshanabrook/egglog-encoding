import EgglogSemantics.Proofs.Congruence.Flatten
import EgglogSemantics.Proofs.Congruence.Invariant
import EgglogSemantics.Proofs.Congruence.Atoms
import EgglogSemantics.Proofs.Congruence.Sound
import EgglogSemantics.Proofs.InterpBase

/-! Completeness of the compiled queries at a canonical state: a source match extends, on
the fresh variables, to a match of the flattened pattern, and every id evaluates to the
representative of the source class. -/

namespace Egglog.Congruence

variable {sub : Bool}

/-! ### Source representatives -/

/-- The representative of a term's source class. -/
noncomputable def srep (src : Database) (t : Term) : Term :=
  open Classical in
  if h : ∃ r ∈ src.reps, Cong src t r then h.choose else t

theorem srep_spec {src : Database} (hr : src.HasReps) {t : Term} (ht : Cong src t t) :
    srep src t ∈ src.reps ∧ Cong src t (srep src t) := by
  have hex : ∃ r ∈ src.reps, Cong src t r := hr t ht
  unfold srep
  rw [dif_pos hex]
  exact hex.choose_spec

theorem srep_eq_of_mem_reps {src : Database} (hr : src.HasReps) {t : Term} (ht : t ∈ src.reps) :
    srep src t = t := by
  have hc : Cong src t t := Database.toCong ht.1
  obtain ⟨h₁, h₂⟩ := srep_spec hr hc
  exact Database.reps_eq_of_cong h₁ ht h₂.symm

theorem srep_eq_of_cong {src : Database} (hr : src.HasReps) {a b : Term} (hab : Cong src a b) :
    srep src a = srep src b := by
  obtain ⟨h₁, h₂⟩ := srep_spec hr (hab.trans hab.symm)
  obtain ⟨h₃, h₄⟩ := srep_spec hr (hab.symm.trans hab)
  exact Database.reps_eq_of_cong h₁ h₃ (h₂.symm.trans (hab.trans h₄))

theorem srep_mem_terms {src : Database} (hr : src.HasReps) {t : Term} (ht : Cong src t t) :
    srep src t ∈ src.terms := (srep_spec hr ht).1.1

theorem Rel.root_eq_srep {src d : Database} (h : Rel sub src d) (hc : Canon d) (hw : src.WF)
    {k : Term} (hk : k ∈ Keys d) : root d k = srep src k := by
  obtain ⟨h₁, h₂⟩ := (h.edge_iff_rep hc hw hk).mp (h.edge_root hk)
  obtain ⟨h₃, h₄⟩ := srep_spec h.src_hasReps (h.cong_self_of_key hk)
  exact Database.reps_eq_of_cong h₁ h₃ (h₂.symm.trans h₄)

/-! ### Fresh bindings -/

/-- Bindings of exactly the fresh variables of an interval. -/
structure Fresh (n m : Nat) (ρ : Env) : Prop where
  fresh : ∀ b ∈ ρ, FreshIn n m b.1
  nodup : (Env.dom ρ).Nodup
  complete : ∀ k, n ≤ k → k < m → freshVar k ∈ Env.dom ρ

theorem Fresh.nil (n : Nat) : Fresh n n [] :=
  ⟨by simp, by simp [Env.dom], fun k h₁ h₂ => by omega⟩

theorem Fresh.not_mem_dom {n m : Nat} {ρ : Env} (h : Fresh n m ρ) {v : Var}
    (hv : ∀ j, n ≤ j → j < m → v ≠ freshVar j) : v ∉ Env.dom ρ := by
  intro hmem
  obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hmem
  obtain ⟨j, hj₁, hj₂, hj⟩ := h.fresh _ ht
  exact hv j hj₁ hj₂ hj

theorem Fresh.lookup_none {n m : Nat} {ρ : Env} (h : Fresh n m ρ) {v : Var}
    (hv : ∀ j, n ≤ j → j < m → v ≠ freshVar j) : Env.lookup v ρ = none :=
  Env.lookup_eq_none_iff.mpr (h.not_mem_dom hv)

theorem Fresh.lookup_none_of_notFresh {n m : Nat} {ρ : Env} (h : Fresh n m ρ) {v : Var}
    (hv : NotFresh v) : Env.lookup v ρ = none :=
  h.lookup_none fun j _ _ => hv j

theorem Fresh.append {n m k : Nat} {ρ₁ ρ₂ : Env} (h₁ : Fresh n m ρ₁) (h₂ : Fresh m k ρ₂)
    (hnm : n ≤ m) (hmk : m ≤ k) : Fresh n k (ρ₁ ++ ρ₂) where
  fresh := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact (h₁.fresh b hb).mono (Nat.le_refl _) hmk
    · exact (h₂.fresh b hb).mono hnm (Nat.le_refl _)
  nodup := by
    rw [Env.dom_append]
    refine List.Nodup.append h₁.nodup h₂.nodup ?_
    intro v hv₁ hv₂
    obtain ⟨t₁, ht₁⟩ := Env.mem_dom_iff.mp hv₁
    obtain ⟨t₂, ht₂⟩ := Env.mem_dom_iff.mp hv₂
    obtain ⟨j₁, -, hj₁, he₁⟩ := h₁.fresh _ ht₁
    obtain ⟨j₂, hj₂, -, he₂⟩ := h₂.fresh _ ht₂
    have := freshVar_inj (he₁.symm.trans he₂)
    omega
  complete := by
    intro j hj₁ hj₂
    rw [Env.dom_append, List.mem_append]
    by_cases hlt : j < m
    · exact Or.inl (h₁.complete j hj₁ hlt)
    · exact Or.inr (h₂.complete j (by omega) hj₂)

/-- The source substitution binds no generated variable. -/
def NoFreshDom (σ : Env) : Prop := ∀ k, freshVar k ∉ Env.dom σ

theorem noFreshDom_of_notFresh {σ : Env} (h : ∀ v ∈ Env.dom σ, NotFresh v) : NoFreshDom σ :=
  fun k hk => h _ hk k rfl

/-- A lookup through the source bindings and a fresh block ignores a later fresh block. -/
theorem lookup_left {σ ρ₁ ρ₂ : Env} {m k : Nat} (h₂ : Fresh m k ρ₂) {v : Var}
    (hv : ∀ j, m ≤ j → j < k → v ≠ freshVar j) :
    Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) = Env.lookup v (σ ++ ρ₁) := by
  by_cases hσ : v ∈ Env.dom σ
  · rw [Env.lookup_append_of_mem hσ, Env.lookup_append_of_mem hσ]
  · rw [Env.lookup_append_of_not_mem hσ, Env.lookup_append_of_not_mem hσ]
    by_cases h₁ : v ∈ Env.dom ρ₁
    · rw [Env.lookup_append_of_mem h₁]
    · rw [Env.lookup_append_of_not_mem h₁, h₂.lookup_none hv, Env.lookup_eq_none_iff.mpr h₁]

/-- A lookup through the source bindings and a later fresh block ignores an earlier one. -/
theorem lookup_right {σ ρ₁ ρ₂ : Env} {n m : Nat} (h₁ : Fresh n m ρ₁) {v : Var}
    (hv : ∀ j, n ≤ j → j < m → v ≠ freshVar j) :
    Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) = Env.lookup v (σ ++ ρ₂) := by
  by_cases hσ : v ∈ Env.dom σ
  · rw [Env.lookup_append_of_mem hσ, Env.lookup_append_of_mem hσ]
  · rw [Env.lookup_append_of_not_mem hσ, Env.lookup_append_of_not_mem hσ,
      Env.lookup_append_of_not_mem (h₁.not_mem_dom hv)]

/-- A source variable reads through the source bindings. -/
theorem lookup_src {σ ρ : Env} {n m : Nat} (h : Fresh n m ρ) {v : Var} (hv : NotFresh v) :
    Env.lookup v (σ ++ ρ) = Env.lookup v σ := by
  by_cases hσ : v ∈ Env.dom σ
  · rw [Env.lookup_append_of_mem hσ]
  · rw [Env.lookup_append_of_not_mem hσ, h.lookup_none_of_notFresh hv,
      Env.lookup_eq_none_iff.mpr hσ]

/-- A variable that is a source variable or fresh in `[n, m)` is not fresh in `[m, k)`. -/
theorem not_freshIn_right {n m k : Nat} {v : Var} (h : NotFresh v ∨ FreshIn n m v) :
    ∀ j, m ≤ j → j < k → v ≠ freshVar j := by
  intro j hj _ hv
  rcases h with h | ⟨i, _, hi, rfl⟩
  · exact h j hv
  · have := freshVar_inj hv
    omega

theorem not_freshIn_left {n m k : Nat} {v : Var} (h : NotFresh v ∨ FreshIn m k v) :
    ∀ j, n ≤ j → j < m → v ≠ freshVar j := by
  intro j _ hj hv
  rcases h with h | ⟨i, hi, _, rfl⟩
  · exact h j hv
  · have := freshVar_inj hv
    omega

/-! ### The fresh block of an application -/

/-- The names of the fresh child variables. -/
def freshNames (next k : Nat) : List Var := (List.range k).map fun i => freshVar (next + i)

theorem freshArgs_eq_map (next k : Nat) : freshArgs next k = (freshNames next k).map Expr.var := by
  simp [freshArgs, freshNames]

theorem freshNames_length (next k : Nat) : (freshNames next k).length = k := by simp [freshNames]

theorem freshNames_getElem {next k i : Nat} (hi : i < k) :
    (freshNames next k)[i]'(by rw [freshNames_length]; exact hi) = freshVar (next + i) := by
  simp [freshNames]

theorem mem_freshNames {next k : Nat} {v : Var} :
    v ∈ freshNames next k ↔ ∃ i, i < k ∧ v = freshVar (next + i) := by
  simp only [freshNames, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem freshNames_nodup (next k : Nat) : (freshNames next k).Nodup := by
  refine (List.nodup_map_iff_inj_on List.nodup_range).mpr fun i _ j _ h => ?_
  have := freshVar_inj h
  omega

/-- The bindings of an application's fresh variables: the children of the held row and the
row's live parent. -/
def appBlock (next : Nat) (bs : List Term) (r : Term) : Env :=
  (freshNames next bs.length).zip bs ++ [(freshVar (next + bs.length), r)]

theorem appBlock_lookup_child {next : Nat} {bs : List Term} {r : Term} {i : Nat}
    (hi : i < bs.length) :
    Env.lookup (freshVar (next + i)) (appBlock next bs r) = some bs[i] := by
  unfold appBlock
  apply Env.lookup_append_of_some
  have := Env.lookup_zip (freshNames next bs.length) bs (by rw [freshNames_length])
    (freshNames_nodup _ _) i (by rw [freshNames_length]; exact hi) hi
  rwa [freshNames_getElem hi] at this

theorem appBlock_lookup_root {next : Nat} {bs : List Term} {r : Term} :
    Env.lookup (freshVar (next + bs.length)) (appBlock next bs r) = some r := by
  unfold appBlock
  rw [Env.lookup_append_of_not_mem]
  · simp
  · intro hmem
    have hsub := Env.dom_zip_subset (freshNames next bs.length) bs hmem
    obtain ⟨i, hi, he⟩ := mem_freshNames.mp hsub
    have := freshVar_inj he
    omega

theorem appBlock_fresh (next : Nat) (bs : List Term) (r : Term) :
    Fresh next (next + bs.length + 1) (appBlock next bs r) where
  fresh := by
    intro b hb
    unfold appBlock at hb
    rcases List.mem_append.mp hb with hb | hb
    · have := Env.mem_dom_of_mem hb
      obtain ⟨i, hi, he⟩ := mem_freshNames.mp (Env.dom_zip_subset _ _ this)
      exact ⟨next + i, by omega, by omega, he⟩
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨next + bs.length, by omega, by omega, rfl⟩
  nodup := by
    unfold appBlock Env.dom
    rw [List.map_append, List.map_fst_zip (by rw [freshNames_length])]
    refine List.Nodup.append (freshNames_nodup _ _) (by simp) ?_
    intro v hv hv'
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv'
    subst hv'
    obtain ⟨i, hi, he⟩ := mem_freshNames.mp hv
    have := freshVar_inj he
    omega
  complete := by
    intro j hj₁ hj₂
    unfold appBlock Env.dom
    rw [List.map_append, List.map_fst_zip (by rw [freshNames_length]), List.mem_append]
    by_cases hlt : j < next + bs.length
    · exact Or.inl (mem_freshNames.mpr ⟨j - next, by omega, by congr 1; omega⟩)
    · right
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      congr 1
      omega

theorem appBlock_values {next : Nat} {bs : List Term} {r : Term} {b : Var × Term}
    (hb : b ∈ appBlock next bs r) : b.2 ∈ bs ∨ b.2 = r := by
  unfold appBlock at hb
  rcases List.mem_append.mp hb with hb | hb
  · exact Or.inl (List.of_mem_zip hb).2
  · simp only [List.mem_singleton] at hb
    subst hb
    exact Or.inr rfl

/-! ### Completeness -/

variable {src d : Database}

theorem matchesList_freshArgs {σ : Env} {next k : Nat}
    (h : ∀ i, i < k → (Env.lookup (freshVar (next + i)) σ).isSome) :
    Expr.MatchesList d σ (freshArgs next k) := by
  rw [freshArgs_eq_map]
  apply matchesList_map_var
  intro v hv
  obtain ⟨i, hi, rfl⟩ := mem_freshNames.mp hv
  exact h i hi

theorem evalList_freshArgs {σ : Env} {next : Nat} {bs : List Term}
    (h : ∀ i (hi : i < bs.length), Env.lookup (freshVar (next + i)) σ = some bs[i]) :
    Expr.evalList (freshArgs next bs.length) σ = some bs := by
  rw [freshArgs_eq_map]
  apply Expr.evalList_map_var _ _ _ (by rw [freshNames_length])
  intro i hi hi'
  rw [freshNames_length] at hi
  rw [freshNames_getElem hi]
  exact h i hi'

/-- The conclusion of expression completeness. -/
def ExprComplete (src d : Database) (e : Expr) (n : Nat) (σ : Env) : Prop :=
  ∃ ρ, Fresh n (encodeQueryExprWith {} e n).2.2 ρ ∧ (∀ b ∈ ρ, b.2 ∈ d.terms) ∧
    (∀ p ∈ (encodeQueryExprWith {} e n).2.1, Matches d p (σ ++ ρ)) ∧
    Expr.Matches d (σ ++ ρ) (encodeQueryExprWith {} e n).1 ∧
    ∃ t, e.eval σ = some t ∧ Cong src t t ∧
      (encodeQueryExprWith {} e n).1.eval (σ ++ ρ) = some (srep src t)

/-- The conclusion of argument-list completeness. -/
def ArgsComplete (src d : Database) (es : List Expr) (n : Nat) (σ : Env) : Prop :=
  ∃ ρ, Fresh n (encodeQueryArgsWith {} es n).2.2 ρ ∧ (∀ b ∈ ρ, b.2 ∈ d.terms) ∧
    (∀ p ∈ (encodeQueryArgsWith {} es n).2.1, Matches d p (σ ++ ρ)) ∧
    ∃ ts, Expr.evalList es σ = some ts ∧ (∀ t ∈ ts, Cong src t t) ∧
      List.Forall₂ (fun x t => Expr.Matches d (σ ++ ρ) x ∧
        x.eval (σ ++ ρ) = some (srep src t)) (encodeQueryArgsWith {} es n).1 ts

mutual

theorem complete_expr (h : Rel sub src d) (hc : Canon d) (hw : src.WF) :
    ∀ (e : Expr) (n : Nat) {σ : Env}, e.MinOverVars → SrcNames e →
    (∀ v ∈ e.vars, NotFresh v) → NoFreshDom σ → (∀ b ∈ σ, b.2 ∈ src.reps) →
    Expr.Matches src σ e → ExprComplete src d e n σ
  | .lit l, n, σ, _, _, _, _, _, hm => by
      cases hm with
      | lit hl =>
        have hmem : Term.lit l ∈ src.terms := by
          obtain ⟨w, hw', hwc⟩ := represented_witness hl.1
          have := InferredFacts.infers_eq_of_isLit hw (InferredFacts.congr_iff_infers.mp hwc)
            (Or.inr rfl)
          rw [this] at hw'
          exact hw'
        refine ⟨[], Fresh.nil n, by simp, by rw [flat_lit]; simp, ?_, .lit l, rfl,
          Database.toCong hmem, ?_⟩
        · rw [flat_lit, List.append_nil]
          exact .lit (h.lit_live_iff.mpr hmem)
        · rw [flat_lit, List.append_nil, Expr.eval_lit,
            srep_eq_of_mem_reps h.src_hasReps (lit_mem_reps hw hmem)]
  | .var v, n, σ, _, _, _, _, hreps, hm => by
      cases hm with
      | @var _ t hv =>
        have ht : t ∈ src.reps := hreps _ (Env.mem_of_lookup hv)
        refine ⟨[], Fresh.nil n, by simp, by rw [flat_var]; simp, ?_, t, hv,
          Database.toCong ht.1, ?_⟩
        · rw [flat_var, List.append_nil]
          exact .var hv
        · rw [flat_var, List.append_nil, Expr.eval_var, hv, srep_eq_of_mem_reps h.src_hasReps ht]
  | .min a b, n, σ, ho, _, _, _, hreps, hm => by
      -- A minimum over variables is passed through: both operands are bound to
      -- representatives, so the smaller is a representative and its own id.
      obtain ⟨ha, hb⟩ := Expr.minOverVars_min ho
      cases hm with
      | min hma hmb =>
        obtain ⟨x, hx⟩ := hma.eval_exists
        obtain ⟨y, hy⟩ := hmb.eval_exists
        obtain ⟨v, _, hv⟩ := ha.eval_binding hx
        obtain ⟨w, _, hw⟩ := hb.eval_binding hy
        have hxr : x ∈ src.reps := hreps _ (Env.mem_of_lookup hv)
        have hyr : y ∈ src.reps := hreps _ (Env.mem_of_lookup hw)
        have hlr : Term.least x y ∈ src.reps := by
          rcases Term.least_eq_or x y with hl | hl <;> rw [hl]
          exacts [hxr, hyr]
        have hev : (Expr.min a b).eval σ = some (Term.least x y) := by
          rw [Expr.eval_min, hx, Option.bind_some, hy, Option.map_some]
        refine ⟨[], Fresh.nil n, by simp, by rw [flat_min]; simp, ?_, Term.least x y, hev,
          Database.toCong hlr.1, ?_⟩
        · rw [flat_min, List.append_nil]
          exact .min (ha.matches hx) (hb.matches hy)
        · rw [flat_min, List.append_nil, hev, srep_eq_of_mem_reps h.src_hasReps hlr]
  | .app f args, n, σ, ho, hnames, hsrc, hσ, hreps, hm => by
      cases hm with
      | @app _ _ ts hargs hev hlive =>
        obtain ⟨hf, hfns⟩ := srcNames_app hnames
        obtain ⟨ρ₁, hfr₁, hval₁, hatoms₁, ts', hev', hcong, hids⟩ :=
          complete_args h hc hw args n (Expr.minOverVars_app ho) hfns (by simpa using hsrc) hσ
            hreps hargs
        obtain rfl : ts = ts' := Option.some.inj (hev.symm.trans hev')
        rcases hflat : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
        rw [hflat] at hfr₁ hatoms₁ hids
        simp only at hfr₁ hatoms₁ hids
        have hle := flatArgs_next_le args n
        rw [hflat] at hle
        simp only at hle
        have hlen := flatArgs_length args n
        rw [hflat] at hlen
        simp only at hlen
        have hts : ts.length = args.length := Expr.evalList_length hev
        -- The held row of the class.
        have hself : Cong src (.app f ts) (.app f ts) := hlive.1
        obtain ⟨bs, hbs, hcl⟩ := represented_app hself
        have hbsLen : bs.length = args.length := by
          rw [← hts]; exact (CongList.forall₂.mp hcl).length_eq.symm
        have hkey : Term.app f bs ∈ Keys d := h.mem_keys_of_src hbs
        set r := root d (.app f bs) with hr
        set ρ₂ := appBlock next bs r with hρ₂
        have hfr₂ : Fresh next (next + bs.length + 1) ρ₂ := appBlock_fresh next bs r
        rw [hbsLen] at hfr₂
        have hval₂ : ∀ b ∈ ρ₂, b.2 ∈ d.terms := by
          intro b hb
          rcases appBlock_values hb with hb | hb
          · exact Keys.subset_terms d
              (h.keys_subterm hkey (Term.arg_subterms hb (Term.self_mem_subterms _)))
          · rw [hb]; exact Keys.subset_terms d (h.root_mem_keys hkey)
        -- Lookups of the fresh child and root variables through the whole substitution.
        have hchild : ∀ i (hi : i < args.length), Env.lookup (freshVar (next + i))
            (σ ++ (ρ₁ ++ ρ₂)) = some (bs[i]'(by omega)) := by
          intro i hi
          rw [Env.lookup_append_of_not_mem (hσ _),
            Env.lookup_append_of_not_mem (hfr₁.not_mem_dom fun j _ hj he => by
              have := freshVar_inj he; omega)]
          exact appBlock_lookup_child (by omega)
        have hrootl : Env.lookup (freshVar (next + args.length)) (σ ++ (ρ₁ ++ ρ₂)) = some r := by
          rw [Env.lookup_append_of_not_mem (hσ _),
            Env.lookup_append_of_not_mem (hfr₁.not_mem_dom fun j _ hj he => by
              have := freshVar_inj he; omega)]
          rw [← hbsLen]
          exact appBlock_lookup_root
        have hevalArgs :
            Expr.evalList (freshArgs next args.length) (σ ++ (ρ₁ ++ ρ₂)) = some bs := by
          rw [← hbsLen]
          exact evalList_freshArgs fun i hi => by rw [hbsLen] at hi; exact hchild i hi
        have hmatchArgs : Expr.MatchesList d (σ ++ (ρ₁ ++ ρ₂)) (freshArgs next args.length) :=
          matchesList_freshArgs fun i hi => by rw [hchild i hi]; rfl
        have hliveB : Term.app f bs ∈ d.live :=
          h.live_of_src_live hbs (Database.live_app_congr hlive hcl)
        -- The earlier atoms and ids read the same through the extended substitution.
        have hagree₁ : ∀ v, NotFresh v ∨ FreshIn n next v →
            Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) = Env.lookup v (σ ++ ρ₁) :=
          fun v hv => lookup_left hfr₂ (not_freshIn_right hv)
        have hvars₁ : ∀ p ∈ ps, ∀ v ∈ p.vars, NotFresh v ∨ FreshIn n next v := by
          intro p hp v hv
          have := flatArgs_vars_sub args n (v := v) (by
            rw [hflat]; exact Query.mem_vars.mpr ⟨p, hp, hv⟩)
          rw [hflat] at this
          rcases this with hv | hv
          · exact Or.inl (hsrc v (by simpa using hv))
          · exact Or.inr hv
        refine ⟨ρ₁ ++ ρ₂, ?_, ?_, ?_, ?_, .app f ts, by rw [Expr.eval_app_ctor, hev]; rfl, hself,
          ?_⟩
        · rw [flat_app hflat]
          simp only
          exact hfr₁.append hfr₂ hle (by omega)
        · intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hval₁ b hb
          · exact hval₂ b hb
        · rw [flat_app hflat]
          simp only
          intro p hp
          rw [List.mem_append, List.mem_append, List.mem_cons, List.mem_singleton] at hp
          rcases hp with (hp | rfl | hp) | rfl
          · exact (hatoms₁ p hp).of_agreeOn fun v hv => (hagree₁ v (hvars₁ p hp v hv)).symm
          · exact matches_app_iff.mpr ⟨bs, hmatchArgs, hevalArgs, hliveB⟩
          · obtain ⟨ax, hax, rfl⟩ := List.mem_map.mp hp
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hax
            have hi' : i < args.length := by
              simpa [freshArgs_length, hlen] using hi
            rw [List.getElem_zip, freshArgs_getElem hi']
            have hxi := (List.forall₂_iff_get.mp hids).2 i (by omega) (by omega)
            simp only [List.get_eq_getElem] at hxi
            obtain ⟨hxm, hxe⟩ := hxi
            have hagx : ∀ v ∈ (xs[i]'(by omega)).vars,
                Env.lookup v (σ ++ ρ₁) = Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) := by
              intro v hv
              have := flatArgs_ids_vars args n (x := xs[i]'(by omega)) (by
                rw [hflat]; exact List.getElem_mem _) hv
              rw [hflat] at this
              refine (hagree₁ v ?_).symm
              rcases this with hv | hv
              · exact Or.inl (hsrc v (by simpa using hv))
              · exact Or.inr hv
            obtain ⟨hxe', hxm'⟩ := Expr.Matches.of_agreeOn ⟨hxe, hxm⟩ hagx
            have hti : Cong src (ts[i]'(by omega)) (ts[i]'(by omega)) :=
              hcong _ (List.getElem_mem _)
            have hedge : Edge d (bs[i]'(by omega)) (srep src (ts[i]'(by omega))) := by
              rw [h.edge_iff_rep hc hw (h.keys_subterm hkey
                (Term.arg_subterms (List.getElem_mem _) (Term.self_mem_subterms _)))]
              refine ⟨(srep_spec h.src_hasReps hti).1, ?_⟩
              have hbt : Cong src (bs[i]'(by omega)) (ts[i]'(by omega)) :=
                ((CongList.forall₂.mp hcl).get (by omega) (by omega)).symm
              exact hbt.trans (srep_spec h.src_hasReps hti).2
            exact matches_uf_iff.mpr ⟨_, _, .var (hchild i hi'), hxm', hchild i hi', hxe', hedge⟩
          · refine matches_uf_iff.mpr ⟨.app f bs, r, .app hmatchArgs hevalArgs hliveB,
              .var hrootl, ?_, hrootl, h.edge_root hkey⟩
            rw [Expr.eval_app_ctor, hevalArgs]; rfl
        · rw [flat_app hflat]
          exact .var hrootl
        · rw [flat_app hflat]
          simp only [Expr.eval_var]
          rw [hrootl, hr, h.root_eq_srep hc hw hkey,
            srep_eq_of_cong h.src_hasReps (Cong.congr hself hcl)]

theorem complete_args (h : Rel sub src d) (hc : Canon d) (hw : src.WF) :
    ∀ (es : List Expr) (n : Nat) {σ : Env}, Expr.MinOverVarsList es →
    (∀ g ∈ Expr.fnsList es, SourceName g) → (∀ v ∈ Expr.varsList es, NotFresh v) → NoFreshDom σ →
    (∀ b ∈ σ, b.2 ∈ src.reps) → Expr.MatchesList src σ es → ArgsComplete src d es n σ
  | [], n, σ, _, _, _, _, _, _ => by
      refine ⟨[], Fresh.nil n, by simp, by rw [flatArgs_nil]; simp, [], rfl, by simp, ?_⟩
      rw [flatArgs_nil]
      exact .nil
  | e :: es, n, σ, ho, hnames, hsrc, hσ, hreps, hm => by
      cases hm with
      | cons hme hmes =>
        obtain ⟨hoe, hoes⟩ := Expr.minOverVarsList_cons ho
        obtain ⟨hne, hnes⟩ := srcNames_cons hnames
        have hsrce : ∀ v ∈ e.vars, NotFresh v := fun v hv => hsrc v (by simp [hv])
        have hsrces : ∀ v ∈ Expr.varsList es, NotFresh v := fun v hv => hsrc v (by simp [hv])
        obtain ⟨ρ₁, hfr₁, hval₁, hatoms₁, hx₁, t, ht, htc, hxe⟩ :=
          complete_expr h hc hw e n hoe hne hsrce hσ hreps hme
        rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
        rw [h₁] at hfr₁ hatoms₁ hx₁ hxe
        simp only at hfr₁ hatoms₁ hx₁ hxe
        obtain ⟨ρ₂, hfr₂, hval₂, hatoms₂, ts, hts, htsc, hids⟩ :=
          complete_args h hc hw es next hoes hnes hsrces hσ hreps hmes
        rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
        rw [h₂] at hfr₂ hatoms₂ hids
        simp only at hfr₂ hatoms₂ hids
        have hn := flat_next_le e n
        have hm' := flatArgs_next_le es next
        rw [h₁] at hn
        rw [h₂] at hm'
        simp only at hn hm'
        have hagree₁ : ∀ v, NotFresh v ∨ FreshIn n next v →
            Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) = Env.lookup v (σ ++ ρ₁) :=
          fun v hv => lookup_left hfr₂ (not_freshIn_right hv)
        have hagree₂ : ∀ v, NotFresh v ∨ FreshIn next last v →
            Env.lookup v (σ ++ (ρ₁ ++ ρ₂)) = Env.lookup v (σ ++ ρ₂) :=
          fun v hv => lookup_right hfr₁ (not_freshIn_left hv)
        have hvars₁ : ∀ p ∈ ps, ∀ v ∈ p.vars, NotFresh v ∨ FreshIn n next v := by
          intro p hp v hv
          have := flat_vars_sub e n (v := v) (by rw [h₁]; exact Query.mem_vars.mpr ⟨p, hp, hv⟩)
          rw [h₁] at this
          rcases this with hv | hv
          · exact Or.inl (hsrce v hv)
          · exact Or.inr hv
        have hvars₂ : ∀ p ∈ qs, ∀ v ∈ p.vars, NotFresh v ∨ FreshIn next last v := by
          intro p hp v hv
          have := flatArgs_vars_sub es next (v := v) (by
            rw [h₂]; exact Query.mem_vars.mpr ⟨p, hp, hv⟩)
          rw [h₂] at this
          rcases this with hv | hv
          · exact Or.inl (hsrces v hv)
          · exact Or.inr hv
        have hxvars : ∀ v ∈ x.vars, NotFresh v ∨ FreshIn n next v := by
          intro v hv
          rcases flat_id_cases e n with ⟨hx, -, -⟩ | ⟨k, hx, hk₁, hk₂, -⟩
          · rw [h₁] at hx; simp only at hx
            rw [hx] at hv
            exact Or.inl (hsrce v hv)
          · rw [h₁] at hx hk₂; simp only at hx hk₂
            rw [hx, Expr.vars_var, List.mem_singleton] at hv
            exact Or.inr ⟨k, hk₁, hk₂, hv⟩
        refine ⟨ρ₁ ++ ρ₂, ?_, ?_, ?_, t :: ts, ?_, ?_, ?_⟩
        · rw [flatArgs_cons h₁ h₂]
          exact hfr₁.append hfr₂ hn hm'
        · intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hval₁ b hb
          · exact hval₂ b hb
        · rw [flatArgs_cons h₁ h₂]
          simp only
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact (hatoms₁ p hp).of_agreeOn fun v hv => (hagree₁ v (hvars₁ p hp v hv)).symm
          · exact (hatoms₂ p hp).of_agreeOn fun v hv => (hagree₂ v (hvars₂ p hp v hv)).symm
        · rw [Expr.evalList_cons, ht, Option.bind_some, hts, Option.map_some]
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact htc
          · exact htsc u hu
        · rw [flatArgs_cons h₁ h₂]
          simp only
          refine .cons ?_ ?_
          · obtain ⟨hxe', hxm'⟩ := Expr.Matches.of_agreeOn ⟨hxe, hx₁⟩
              fun v hv => (hagree₁ v (hxvars v hv)).symm
            exact ⟨hxm', hxe'⟩
          · rw [List.forall₂_iff_get] at hids ⊢
            refine ⟨hids.1, fun i h₁' h₂' => ?_⟩
            obtain ⟨hxm, hxe⟩ := hids.2 i h₁' h₂'
            have hx'vars : ∀ v ∈ (xs.get ⟨i, h₁'⟩).vars, NotFresh v ∨ FreshIn next last v := by
              intro v hv
              have := flatArgs_ids_vars es next (x := xs.get ⟨i, h₁'⟩) (by
                rw [h₂]; exact List.get_mem _ _) hv
              rw [h₂] at this
              rcases this with hv | hv
              · exact Or.inl (hsrces v hv)
              · exact Or.inr hv
            obtain ⟨hxe', hxm'⟩ := Expr.Matches.of_agreeOn ⟨hxe, hxm⟩
              fun v hv => (hagree₂ v (hx'vars v hv)).symm
            exact ⟨hxm', hxe'⟩

end

end Egglog.Congruence
