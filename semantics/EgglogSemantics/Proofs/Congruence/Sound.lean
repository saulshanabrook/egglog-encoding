import EgglogSemantics.Proofs.Congruence.Flatten
import EgglogSemantics.Proofs.Congruence.Invariant
import EgglogSemantics.Proofs.Congruence.Atoms
import EgglogSemantics.Proofs.InterpBase

/-! Soundness of the compiled queries: whenever the atoms of a flattened source pattern
match in a reading of the compiled state, the source pattern matches, with its ids
congruent to the source values. The reading is a database whose live edges and live
applications are sound for the source (`Reads`), which a canonical compiled state is
(`Rel.reads`): a live application of the compiled state is one the source holds live,
since every spelling the source considers subsumed is subsumed at a rebuild fixpoint. A
disequality needs the reading to be canonical as well, so that two ids differ only when
their source values are not congruent. -/

namespace Egglog.Congruence

variable {sub : Bool}

/-- A database whose live rows and live applications are sound for the source. -/
structure Reads (src D : Database) : Prop where
  diag : D.Diag
  edge : ∀ k p, Edge D k p → Cong src k p ∧ k ∈ src.terms ∧ p ∈ src.terms
  app : ∀ f ts, SourceName f → Term.app f ts ∈ D.live → Term.app f ts ∈ src.live
  lit : ∀ l, Term.lit l ∈ D.live → Term.lit l ∈ src.live

/-- A held literal is live: no row is a spelling of it. -/
theorem lit_live_of_mem_terms {src : Database} {l : Lit} (ht : Term.lit l ∈ src.terms) :
    Term.lit l ∈ src.live := by
  refine ⟨Database.toCong ht, ?_⟩
  rintro ⟨u, _, f, as, bs, heq, _, _⟩
  cases heq

/-- A live literal is held. -/
theorem lit_mem_terms_of_live {src : Database} (hw : src.WF) {l : Lit}
    (hl : Term.lit l ∈ src.live) : Term.lit l ∈ src.terms := by
  obtain ⟨w, hw', hwc⟩ := represented_witness hl.1
  have := InferredFacts.infers_eq_of_isLit hw (InferredFacts.congr_iff_infers.mp hwc) (Or.inr rfl)
  rw [this] at hw'
  exact hw'

theorem Rel.reads {src d : Database} (h : Rel sub src d) (hc : Canon d) (hw : src.WF) :
    Reads src d where
  diag := h.diag
  edge := fun _ _ he => ⟨h.edge_cong he, h.key_mem_src (h.key_of_edge he),
    h.key_mem_src (h.parent_of_edge he)⟩
  app := fun _ _ hf hl =>
    (h.app_live_iff_src hc hw (h.app_mem_src_of_mem_terms hf
      ((Congruence.app_live_iff h.diag).mp hl).1)).mp hl
  lit := fun _ hl => lit_live_of_mem_terms (h.lit_live_iff.mp hl)

theorem evalList_of_forall₂ {σ : Env} : ∀ {es : List Expr} {ts : List Term},
    List.Forall₂ (fun e t => e.eval σ = some t) es ts → Expr.evalList es σ = some ts
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      rw [Expr.evalList_cons, h, Option.bind_some, evalList_of_forall₂ hs, Option.map_some]

/-- A source expression's names are source names. -/
def SrcNames (e : Expr) : Prop := ∀ g ∈ e.fns, SourceName g

/-- The expressions a pattern evaluates: its sides. -/
def _root_.Egglog.Pattern.exprs : Pattern → List Expr
  | .expr e => [e]
  | .eq a b => [a, b]
  | .ne a b => [a, b]

theorem srcNames_app {f : FnName} {args : List Expr} (h : SrcNames (.app f args)) :
    SourceName f ∧ ∀ g ∈ Expr.fnsList args, SourceName g :=
  ⟨h f (by simp [Expr.fns]), fun g hg => h g (by simp [Expr.fns, hg])⟩

theorem srcNames_cons {e : Expr} {es : List Expr}
    (h : ∀ g ∈ Expr.fnsList (e :: es), SourceName g) :
    SrcNames e ∧ ∀ g ∈ Expr.fnsList es, SourceName g :=
  ⟨fun g hg => h g (by simp [Expr.fnsList, hg]), fun g hg => h g (by simp [Expr.fnsList, hg])⟩

/-- A literal the source holds is its own representative. -/
theorem lit_mem_reps {src : Database} (hw : src.WF) {l : Lit} (ht : Term.lit l ∈ src.terms) :
    Term.lit l ∈ src.reps := by
  refine ⟨ht, fun s _ hs hlt => ?_⟩
  rw [InferredFacts.infers_eq_of_isLit hw (InferredFacts.congr_iff_infers.mp hs) (Or.inr rfl)]
    at hlt
  simp at hlt

/-- A list every position of which matches, matches. -/
theorem matchesList_of_forall_getElem {db : Database} {σ : Env} : ∀ {es : List Expr},
    (∀ j (hj : j < es.length), Expr.Matches db σ es[j]) → Expr.MatchesList db σ es
  | [], _ => .nil
  | e :: es, h =>
      .cons (h 0 (by simp)) (matchesList_of_forall_getElem fun j hj => h (j + 1) (by simpa using hj))

variable {src D : Database}

mutual

/-- If the atoms of a flattened expression match, the expression matches in the source and
its id is congruent to the value. A minimum over variables is passed through: it
evaluates to a binding on both sides. -/
theorem sound_expr (hr : Reads src D) : ∀ (e : Expr) (n : Nat) {σ' σ : Env},
    e.MinOverVars → SrcNames e →
    (∀ v ∈ e.vars, Env.lookup v σ' = Env.lookup v σ) →
    (∀ v t, Env.lookup v σ = some t → t ∈ src.terms) →
    (∀ p ∈ (encodeQueryExprWith {} e n).2.1, Matches D p σ') →
    Expr.Matches D σ' (encodeQueryExprWith {} e n).1 →
    ∀ {i : Term}, (encodeQueryExprWith {} e n).1.eval σ' = some i →
    ∃ t, e.eval σ = some t ∧ Cong src t i ∧ Expr.Matches src σ e
  | .lit l, n, σ', σ, _, _, _, _, _, hx, i, hi => by
      rw [flat_lit] at hx hi
      simp only [Expr.eval_lit, Option.some.injEq] at hi
      subst hi
      have hl : Term.lit l ∈ src.live := by
        cases hx with
        | lit hl => exact hr.lit l hl
      exact ⟨.lit l, rfl, hl.1, .lit hl⟩
  | .var v, n, σ', σ, _, _, hag, hσ, _, _, i, hi => by
      rw [flat_var] at hi
      simp only [Expr.eval_var] at hi
      rw [hag v (by simp)] at hi
      exact ⟨i, hi, Database.toCong (hσ v i hi), .var hi⟩
  | .min a b, n, σ', σ, ho, _, hag, hσ, _, _, i, hi => by
      obtain ⟨ha, hb⟩ := Expr.minOverVars_min ho
      rw [flat_min] at hi
      simp only at hi
      rw [Expr.eval_agreeOn (.min a b) hag] at hi
      refine ⟨i, hi, Database.toCong ?_, ?_⟩
      · rw [Expr.eval_min, Option.bind_eq_some_iff] at hi
        obtain ⟨x, hx, hmap⟩ := hi
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
        obtain ⟨v, _, hv⟩ := ha.eval_binding hx
        obtain ⟨w, _, hw⟩ := hb.eval_binding hy
        rcases Term.least_eq_or x y with hl | hl <;> rw [hl]
        · exact hσ v x hv
        · exact hσ w y hw
      · rw [Expr.eval_min, Option.bind_eq_some_iff] at hi
        obtain ⟨x, hx, hmap⟩ := hi
        obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp hmap
        exact .min (ha.matches hx) (hb.matches hy)
  | .app f args, n, σ', σ, ho, hnames, hag, hσ, hm, _, i, hi => by
      rcases hflat : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hlen := flatArgs_length args n
      rw [hflat] at hlen
      simp only at hlen
      rw [flat_app hflat] at hm hi
      simp only at hm hi
      obtain ⟨hf, hfns⟩ := srcNames_app hnames
      -- The application atom.
      have hA := hm (.expr (.app f (freshArgs next args.length))) (by simp)
      obtain ⟨as, _, has, hliveA⟩ := matches_app_iff.mp hA
      have haslive : Term.app f as ∈ src.live := hr.app f as hf hliveA
      have hasrc : Cong src (.app f as) (.app f as) := haslive.1
      -- The root atom.
      have hY := hm (.expr (ufRow (.app f (freshArgs next args.length))
        (.var (freshVar (next + args.length))))) (by simp)
      obtain ⟨ta, i', _, _, hta, hi', hey⟩ := matches_uf_iff.mp hY
      obtain rfl : ta = Term.app f as := by
        rw [Expr.eval_app_ctor, has] at hta
        exact (Option.some.inj hta).symm
      simp only [Expr.eval_var] at hi hi'
      obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
      -- The children.
      have hargs := sound_args hr args n (Expr.minOverVars_app ho) hfns (by simpa using hag) hσ
        (by
          intro p hp
          rw [hflat] at hp
          exact hm p (List.mem_append_left _ (List.mem_append_left _ hp)))
      rw [hflat] at hargs
      simp only at hargs
      have hasLen : as.length = args.length := by
        rw [Expr.evalList_length has, freshArgs_length]
      have hpoint : ∀ (j : Nat) (hj : j < args.length),
          ∃ t, args[j].eval σ = some t ∧ Cong src t (as[j]'(by omega)) ∧
            Expr.Matches src σ args[j] := by
        intro j hj
        have hZ := hm (.expr (ufRow ((freshArgs next args.length)[j]'(by
          rw [freshArgs_length]; exact hj)) (xs[j]'(by omega)))) (by
          apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_cons_of_mem
          refine List.mem_map.mpr ⟨((freshArgs next args.length)[j]'(by
            rw [freshArgs_length]; exact hj), xs[j]'(by omega)), ?_, rfl⟩
          rw [List.mem_iff_getElem]
          refine ⟨j, by rw [List.length_zip, freshArgs_length, hlen, Nat.min_self]; exact hj, ?_⟩
          rw [List.getElem_zip])
        obtain ⟨a, ij, _, hxm, ha, hij, hedge⟩ := matches_uf_iff.mp hZ
        obtain ⟨a', ha', hev⟩ := Expr.getElem?_of_evalList has j
          (by rw [List.getElem?_eq_getElem (by rw [freshArgs_length]; exact hj)])
        rw [List.getElem?_eq_getElem (by omega)] at ha'
        obtain rfl : a' = as[j]'(by omega) := (Option.some.inj ha').symm
        obtain rfl : a = as[j]'(by omega) := Option.some.inj (ha.symm.trans hev)
        obtain ⟨t, ht, hti, htm⟩ := (List.forall₂_iff_get.mp hargs).2 j hj (by omega) hxm hij
        exact ⟨t, ht, hti.trans (hr.edge _ _ hedge).1.symm, htm⟩
      choose ts hts using fun j : Fin args.length => hpoint j j.2
      let tl : List Term := List.ofFn ts
      have htl : List.Forall₂ (fun e t => e.eval σ = some t) args tl := by
        rw [List.forall₂_iff_get]
        refine ⟨by simp [tl], fun j hj₁ hj₂ => ?_⟩
        simp only [List.get_eq_getElem, tl, List.getElem_ofFn]
        exact (hts ⟨j, hj₁⟩).1
      have hcl : CongList src tl as := by
        rw [CongList.forall₂, List.forall₂_iff_get]
        refine ⟨by simp [tl, hasLen], fun j hj₁ hj₂ => ?_⟩
        simp only [List.get_eq_getElem, tl, List.getElem_ofFn]
        exact (hts ⟨j, by simpa [tl] using hj₁⟩).2.1
      have hmatches : Expr.MatchesList src σ args :=
        matchesList_of_forall_getElem fun j hj => (hts ⟨j, hj⟩).2.2
      have hevt : Expr.evalList args σ = some tl := evalList_of_forall₂ htl
      refine ⟨.app f tl, ?_, ?_, ?_⟩
      · rw [Expr.eval_app_ctor, hevt]; rfl
      · exact ((Cong.congr hasrc hcl.symm).symm.trans (hr.edge _ _ hey).1)
      · exact .app hmatches hevt (Database.live_app_congr haslive hcl.symm)

theorem sound_args (hr : Reads src D) : ∀ (es : List Expr) (n : Nat) {σ' σ : Env},
    Expr.MinOverVarsList es → (∀ g ∈ Expr.fnsList es, SourceName g) →
    (∀ v ∈ Expr.varsList es, Env.lookup v σ' = Env.lookup v σ) →
    (∀ v t, Env.lookup v σ = some t → t ∈ src.terms) →
    (∀ p ∈ (encodeQueryArgsWith {} es n).2.1, Matches D p σ') →
    List.Forall₂ (fun e x => Expr.Matches D σ' x → ∀ {i : Term}, x.eval σ' = some i →
      ∃ t, e.eval σ = some t ∧ Cong src t i ∧ Expr.Matches src σ e) es
      (encodeQueryArgsWith {} es n).1
  | [], _, _, _, _, _, _, _, _ => by rw [flatArgs_nil]; exact .nil
  | e :: es, n, σ', σ, ho, hnames, hag, hσ, hm => by
      obtain ⟨hoe, hoes⟩ := Expr.minOverVarsList_cons ho
      obtain ⟨hne, hnes⟩ := srcNames_cons hnames
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂] at hm ⊢
      simp only at hm ⊢
      refine .cons ?_ ?_
      · intro hx i hi
        have := sound_expr hr e n hoe hne (fun v hv => hag v (by simp [hv])) hσ
          (fun p hp => hm p (List.mem_append_left _ (by rw [h₁] at hp; exact hp)))
        rw [h₁] at this
        exact this hx hi
      · have := sound_args hr es next hoes hnes (fun v hv => hag v (by simp [hv])) hσ
          (fun p hp => hm p (List.mem_append_right _ (by rw [h₂] at hp; exact hp)))
        rw [h₂] at this
        exact this

end

/-- An expression whose flattening matched also matches in the source, as its atom. -/
theorem sound_expr_matches (hr : Reads src D) {e : Expr} {n : Nat}
    {σ' σ : Env} (ho : e.MinOverVars) (hnames : SrcNames e)
    (hag : ∀ v ∈ e.vars, Env.lookup v σ' = Env.lookup v σ)
    (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ src.terms)
    (hm : ∀ p ∈ (encodeQueryExprWith {} e n).2.1, Matches D p σ')
    (hx : Expr.Matches D σ' (encodeQueryExprWith {} e n).1) :
    ∃ t i, e.eval σ = some t ∧ (encodeQueryExprWith {} e n).1.eval σ' = some i ∧
      Cong src t i ∧ Expr.Matches src σ e := by
  obtain ⟨i, hi⟩ := hx.eval_exists
  obtain ⟨t, ht, hti, hmatch⟩ := sound_expr hr e n ho hnames hag hσ hm hx hi
  exact ⟨t, i, ht, hi, hti, hmatch⟩

/-- At a reading where every live edge leads to a source representative, the id of a
flattened expression is a source representative: a held literal, a bound representative,
the smaller of two such, or the root of an application. -/
theorem id_mem_reps (hr : Reads src D) (hw : src.WF)
    (hroot : ∀ k p, Edge D k p → p ∈ src.reps) (e : Expr) (n : Nat) {σ' σ : Env}
    (ho : e.MinOverVars) (hag : ∀ v ∈ e.vars, Env.lookup v σ' = Env.lookup v σ)
    (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ src.reps)
    (hm : ∀ p ∈ (encodeQueryExprWith {} e n).2.1, Matches D p σ')
    (hx : Expr.Matches D σ' (encodeQueryExprWith {} e n).1) {i : Term}
    (hi : (encodeQueryExprWith {} e n).1.eval σ' = some i) : i ∈ src.reps := by
  cases e with
  | lit l =>
    rw [flat_lit] at hx hi
    simp only [Expr.eval_lit, Option.some.injEq] at hi
    subst hi
    cases hx with
    | lit hl => exact lit_mem_reps hw (lit_mem_terms_of_live hw (hr.lit l hl))
  | var v =>
    rw [flat_var] at hi
    simp only [Expr.eval_var] at hi
    rw [hag v (by simp)] at hi
    exact hσ v i hi
  | min a b =>
    obtain ⟨ha, hb⟩ := Expr.minOverVars_min ho
    rw [flat_min] at hi
    simp only at hi
    rw [Expr.eval_agreeOn (.min a b) hag, Expr.eval_min, Option.bind_eq_some_iff] at hi
    obtain ⟨x, hx', hmap⟩ := hi
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
    obtain ⟨v, _, hv⟩ := ha.eval_binding hx'
    obtain ⟨w, _, hw⟩ := hb.eval_binding hy
    rcases Term.least_eq_or x y with hl | hl <;> rw [hl]
    · exact hσ v x hv
    · exact hσ w y hw
  | app f args =>
    rcases hflat : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
    rw [flat_app hflat] at hm hi
    simp only at hm hi
    have hY := hm (.expr (ufRow (.app f (freshArgs next args.length))
      (.var (freshVar (next + args.length))))) (by simp)
    obtain ⟨_, i', _, _, _, hi', hey⟩ := matches_uf_iff.mp hY
    simp only [Expr.eval_var] at hi hi'
    obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
    exact hroot _ _ hey

/-- What the soundness of a disequality needs of the reading: it is canonical, so every
live edge leads to a source representative, the source bindings are representatives, and
the compiled bindings are held. Two ids then differ exactly when their source values are
not congruent. -/
structure NeSound (src D : Database) (σ σ' : Env) : Prop where
  wf : src.WF
  root : ∀ k p, Edge D k p → p ∈ src.reps
  reps : ∀ v t, Env.lookup v σ = some t → t ∈ src.reps
  held : ∀ v t, Env.lookup v σ' = some t → t ∈ D.terms

/-- If a compiled pattern's atoms match, the source pattern matches. A disequality needs
the canonical reading. -/
theorem sound_pattern (hr : Reads src D) {p : Pattern} (n : Nat)
    (ho : p.MinOverVars) (hsc : p.Scoped) (hnames : ∀ e ∈ p.exprs, SrcNames e)
    {σ' σ : Env} (hne : p.monotoneB = true ∨ NeSound src D σ σ')
    (hag : ∀ v ∈ p.vars, Env.lookup v σ' = Env.lookup v σ)
    (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ src.terms)
    (hm : ∀ q ∈ (encodePatternWith {} p n).1, Matches D q σ') : Matches src p σ := by
  cases p with
  | expr e =>
    rw [pattern_expr] at hm
    simp only at hm
    cases e with
    | app f args =>
      rcases hflat : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hY := hm (.expr (ufRow (.app f (freshArgs next args.length))
        (.var (freshVar (next + args.length))))) (by rw [flat_app hflat]; simp)
      obtain ⟨_, i, _, hxm, _, _, _⟩ := matches_uf_iff.mp hY
      have hx : Expr.Matches D σ' (encodeQueryExprWith {} (.app f args) n).1 := by
        rw [flat_app hflat]; exact hxm
      obtain ⟨t, i, ht, _, _, hmatch⟩ := sound_expr_matches hr ho
        (hnames _ (by simp [Pattern.exprs])) hag hσ hm hx
      exact .atom hmatch
    | lit _ => exact hsc.elim
    | var _ => exact hsc.elim
    | min _ _ => exact hsc.elim
  | eq l r =>
    obtain ⟨hol, hor⟩ := Pattern.minOverVars_eq ho
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    rw [pattern_eq h₁ h₂] at hm
    have hE := hm (.eq x₁ x₂) (by simp)
    obtain ⟨i₁, i₂, hm₁, hm₂, hi₁, hi₂, hc⟩ := matches_eq_iff.mp hE
    have hag₁ : ∀ v ∈ l.vars, Env.lookup v σ' = Env.lookup v σ := fun v hv =>
      hag v (by simp [Pattern.vars, hv])
    have hag₂ : ∀ v ∈ r.vars, Env.lookup v σ' = Env.lookup v σ := fun v hv =>
      hag v (by simp [Pattern.vars, hv])
    obtain ⟨t₁, i₁', ht₁, hi₁', hc₁, hl⟩ := sound_expr_matches hr hol
      (hnames l (by simp [Pattern.exprs])) hag₁ hσ
      (fun q hq => hm q (by rw [h₁] at hq; simp [hq])) (by rw [h₁]; exact hm₁)
    obtain ⟨t₂, i₂', ht₂, hi₂', hc₂, hrm⟩ := sound_expr_matches hr hor
      (hnames r (by simp [Pattern.exprs])) hag₂ hσ
      (fun q hq => hm q (by rw [h₂] at hq; simp [hq])) (by rw [h₂]; exact hm₂)
    rw [h₁] at hi₁'
    rw [h₂] at hi₂'
    simp only at hi₁' hi₂'
    obtain rfl : i₁ = i₁' := Option.some.inj (hi₁.symm.trans hi₁')
    obtain rfl : i₂ = i₂' := Option.some.inj (hi₂.symm.trans hi₂')
    have heq : i₁ = i₂ := hc.eq_of_diag hr.diag
    subst heq
    exact .equal hl hrm ht₁ ht₂ (hc₁.trans hc₂.symm)
  | ne l r =>
    rcases hne with hmono | hne
    · simp [Pattern.monotoneB] at hmono
    obtain ⟨hol, hor⟩ := Pattern.minOverVars_ne ho
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    rw [pattern_ne h₁ h₂] at hm
    have hE := hm (.ne x₁ x₂) (by simp)
    obtain ⟨i₁, i₂, hm₁, hm₂, hi₁, hi₂, hc⟩ := matches_ne_iff.mp hE
    have hag₁ : ∀ v ∈ l.vars, Env.lookup v σ' = Env.lookup v σ := fun v hv =>
      hag v (by simp [Pattern.vars, hv])
    have hag₂ : ∀ v ∈ r.vars, Env.lookup v σ' = Env.lookup v σ := fun v hv =>
      hag v (by simp [Pattern.vars, hv])
    have hml : ∀ q ∈ (encodeQueryExprWith {} l n).2.1, Matches D q σ' := fun q hq =>
      hm q (by rw [h₁] at hq; simp [hq])
    have hmr : ∀ q ∈ (encodeQueryExprWith {} r next).2.1, Matches D q σ' := fun q hq =>
      hm q (by rw [h₂] at hq; simp [hq])
    have hxl : Expr.Matches D σ' (encodeQueryExprWith {} l n).1 := by rw [h₁]; exact hm₁
    have hxr : Expr.Matches D σ' (encodeQueryExprWith {} r next).1 := by rw [h₂]; exact hm₂
    have hil : (encodeQueryExprWith {} l n).1.eval σ' = some i₁ := by rw [h₁]; exact hi₁
    have hir : (encodeQueryExprWith {} r next).1.eval σ' = some i₂ := by rw [h₂]; exact hi₂
    -- Both ids are source representatives, so congruent values would make them one.
    have hr₁ : i₁ ∈ src.reps :=
      id_mem_reps hr hne.wf hne.root l n hol hag₁ hne.reps hml hxl hil
    have hr₂ : i₂ ∈ src.reps :=
      id_mem_reps hr hne.wf hne.root r next hor hag₂ hne.reps hmr hxr hir
    obtain ⟨t₁, i₁', ht₁, hi₁', hc₁, hl⟩ := sound_expr_matches hr hol
      (hnames l (by simp [Pattern.exprs])) hag₁ hσ hml hxl
    obtain ⟨t₂, i₂', ht₂, hi₂', hc₂, hrm⟩ := sound_expr_matches hr hor
      (hnames r (by simp [Pattern.exprs])) hag₂ hσ hmr hxr
    obtain rfl : i₁ = i₁' := Option.some.inj (hil.symm.trans hi₁')
    obtain rfl : i₂ = i₂' := Option.some.inj (hir.symm.trans hi₂')
    refine .unequal hl hrm ht₁ ht₂ fun hcong => hc ?_
    have heq : i₁ = i₂ := Database.reps_eq_of_cong hr₁ hr₂ (hc₁.symm.trans (hcong.trans hc₂))
    subst heq
    exact Expr.Matches.eval_cong (fun v t h => Database.toCong (hne.held v t h)) ⟨hi₁, hm₁⟩

/-- If a compiled query's atoms match, every source pattern matches. -/
theorem sound_query (hr : Reads src D) {q : Query} (n : Nat)
    (ho : ∀ p ∈ q, p.MinOverVars) (hsc : ∀ p ∈ q, p.Scoped)
    (hnames : ∀ p ∈ q, ∀ e ∈ p.exprs, SrcNames e)
    {σ' σ : Env} (hne : (∀ p ∈ q, p.monotoneB = true) ∨ NeSound src D σ σ')
    (hag : ∀ v ∈ Query.vars q, Env.lookup v σ' = Env.lookup v σ)
    (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ src.terms)
    (hm : ∀ p ∈ (encodeQueryWith {} q n).1, Matches D p σ') : ∀ p ∈ q, Matches src p σ := by
  induction q generalizing n with
  | nil => simp
  | cons p ps ih =>
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    rw [query_cons h₁ h₂] at hm
    simp only at hm
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact sound_pattern hr n (ho _ (by simp)) (hsc _ (by simp)) (hnames _ (by simp))
        (hne.imp_left fun h => h p' (by simp)) (fun v hv => hag v (by simp [hv])) hσ
        (fun q hq => hm q (by rw [h₁] at hq; exact List.mem_append_left _ hq))
    · exact ih next (fun p hp => ho p (by simp [hp])) (fun p hp => hsc p (by simp [hp]))
        (fun p hp => hnames p (by simp [hp])) (hne.imp_left fun h p hp => h p (by simp [hp]))
        (fun v hv => hag v (by simp [hv]))
        (fun q hq => hm q (by rw [h₂] at hq; exact List.mem_append_right _ hq)) p' hp'

end Egglog.Congruence
