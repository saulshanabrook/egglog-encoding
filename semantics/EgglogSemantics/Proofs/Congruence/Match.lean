import EgglogSemantics.Proofs.Congruence.QuerySafety
import EgglogSemantics.Proofs.Congruence.QuerySubst
import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.Source.Domain
import EgglogSemantics.Proofs.Congruence.Correspond
import EgglogSemantics.Congruence.Encode

/-!
# Source matches from flattened table queries

The recursion follows the original query and the compiler's left-to-right postorder.
Sound view rows supply both equality and existence of source premises. No annotation,
proof column, or saved flattening tree is used.
-/

namespace Egglog.Congruence

mutual

inductive QueryRead (d : Database) (ρ : Env) : Expr → Term → Prop where
  | lit {l : Lit} : QueryRead d ρ (.lit l) (.lit l)
  | var {v : Var} {i : Term} : Env.lookup v ρ = some i → QueryRead d ρ (.var v) i
  | app {f : FnName} {args : List Expr} {es : List Term} {i : Term} :
      QueryReadList d ρ args es → d.Out (viewName f) es [i] →
      QueryRead d ρ (.app f args) i

inductive QueryReadList (d : Database) (ρ : Env) : List Expr → List Term → Prop where
  | nil : QueryReadList d ρ [] []
  | cons {a : Expr} {i : Term} {as : List Expr} {is : List Term} :
      QueryRead d ρ a i → QueryReadList d ρ as is → QueryReadList d ρ (a :: as) (i :: is)

end

inductive PatternRead (d : Database) (ρ : Env) : Pattern → Prop where
  | expr {e : Expr} {i : Term} : QueryRead d ρ e i → PatternRead d ρ (.expr e)
  | eq {e₁ e₂ : Expr} {i : Term} :
      QueryRead d ρ e₁ i → QueryRead d ρ e₂ i → PatternRead d ρ (.eq e₁ e₂)

def Env.ReadsAs (src : Database) (ρs ρt : Env) (vs : List Var) : Prop :=
  ∀ v ∈ vs, ∀ i, Env.lookup v ρt = some i →
    ∃ t, Env.lookup v ρs = some t ∧ StoredCong src t i ∧ t.IsValue src.sig

theorem Env.ReadsAs.mono {src : Database} {ρs ρt : Env} {vs ws : List Var}
    (h : Env.ReadsAs src ρs ρt vs) (hsub : ws ⊆ vs) : Env.ReadsAs src ρs ρt ws :=
  fun v hv => h v (hsub hv)

def CongUp (src : Database) (t i : Term) : Prop :=
  ∀ D : Database, src.Contained D → (∀ s ∈ t.subterms, s ∈ D.terms) → StoredCong D t i

theorem CongUp.lit {src : Database} {l : Lit} : CongUp src (.lit l) (.lit l) :=
  fun _ _ hsub => Database.toStored (hsub _ (Term.self_mem_subterms _))

theorem CongUp.of_cong {src : Database} {t i : Term} (h : StoredCong src t i) : CongUp src t i :=
  fun _ hc _ => StoredCong.mono hc h

theorem CongUp.congList {src D : Database} (hcon : src.Contained D) {ts es : List Term}
    (h : List.Forall₂ (CongUp src) ts es)
    (hsub : ∀ t ∈ ts, ∀ s ∈ t.subterms, s ∈ D.terms) : StoredCongList D ts es := by
  rw [StoredCongList.forall₂]
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab hl ih =>
    exact .cons (hab D hcon (hsub a (by simp))) (ih fun t ht => hsub t (by simp [ht]))

theorem CongUp.congOn {src : Database} {t i : Term} (h : CongUp src t i) :
    StoredCongOn src [t] t i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨t, by simp, hs⟩

theorem CongUp.congOn_pair_left {src : Database} {t u i : Term} (h : CongUp src t i) :
    StoredCongOn src [t, u] t i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨t, by simp, hs⟩

theorem CongUp.congOn_pair_right {src : Database} {t u i : Term} (h : CongUp src u i) :
    StoredCongOn src [t, u] u i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨u, by simp, hs⟩

mutual

theorem congUp_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {ρs ρt : Env} {e : Expr} {i : Term} (h : QueryRead d ρt e i)
    (hlink : Env.ReadsAs src ρs ρt e.vars) :
    ∃ t, e.eval src.sig ρs = some t ∧ CongUp src t i := by
  revert hlink
  induction h using QueryRead.rec
    (motive_2 := fun es is _ => Env.ReadsAs src ρs ρt (Expr.varsList es) →
      ∃ ts, Expr.evalList src.sig es ρs = some ts ∧ List.Forall₂ (CongUp src) ts is) with
  | lit => exact fun _ => ⟨_, rfl, CongUp.lit⟩
  | @var v i hlk =>
    intro hlink
    obtain ⟨t, ht, hc, hv⟩ := hlink v (by simp [Expr.vars]) i hlk
    exact ⟨t, ht, .of_cong hc⟩
  | @app f args es i _ ho ih =>
    intro hlink
    obtain ⟨as, ham, hal, hae⟩ := hs f _ _ ho
    have hctor := hb f as ham
    obtain ⟨ts, hts, hup⟩ := ih (by simpa [Expr.vars] using hlink)
    refine ⟨.app f ts, by simp [Expr.eval, hctor, hts], fun D hcon hsub => ?_⟩
    have hlD : StoredCongList D ts es :=
      CongUp.congList hcon hup fun t ht s hs' => hsub s (Term.arg_subterms ht hs')
    exact (StoredCong.congr (Database.toStored (hsub _ (Term.self_mem_subterms _)))
      (Database.toStored (hcon.terms ham)) (hlD.trans (StoredCongList.mono hcon hal).symm)).trans (StoredCong.mono hcon hae)
  | nil _ => exact ⟨[], rfl, .nil⟩
  | @cons a i as is _ _ ih ihl hlink =>
    obtain ⟨t, ht, hc⟩ := ih (hlink.mono (by
      intro v hv; rw [Expr.varsList_cons, List.mem_union_iff]; exact Or.inl hv))
    obtain ⟨ts, hts, hcs⟩ := ihl (hlink.mono (by
      intro v hv; rw [Expr.varsList_cons, List.mem_union_iff]; exact Or.inr hv))
    exact ⟨t :: ts, by simp [Expr.evalList, ht, hts], .cons hc hcs⟩

end

theorem mem_terms_of_queryRead {src d : Database} (hs : ViewsSound d src) {ρs ρt : Env}
    {e : Expr} {i : Term} (h : QueryRead d ρt e i) (hlink : Env.ReadsAs src ρs ρt e.vars)
    (hnl : ∀ l, e = .lit l → Term.lit l ∈ src.terms) : i ∈ src.terms := by
  cases h with
  | lit => exact hnl _ rfl
  | var hlk =>
    obtain ⟨_, _, hc, _⟩ := hlink _ (by simp [Expr.vars]) _ hlk
    exact hc.mem_right
  | app _ ho =>
    obtain ⟨_, _, _, hae⟩ := hs _ _ _ ho
    exact hae.mem_right

theorem matches_expr_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {τ ρt : Env} {e : Expr} {i : Term} (h : QueryRead d ρt e i)
    (hlink : Env.ReadsAs src τ ρt e.vars)
    (hnl : ∀ l, e = .lit l → Term.lit l ∈ src.terms) :
    Matches src (.expr e) τ := by
  obtain ⟨t, ht, hup⟩ := congUp_of_queryRead hb hs h hlink
  exact .expr (mem_terms_of_queryRead hs h hlink hnl) (Expr.evalAtom_of_eval ht) hup.congOn.symm

theorem matches_eq_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {τ ρt : Env} {e₁ e₂ : Expr} {i : Term}
    (h₁ : QueryRead d ρt e₁ i) (h₂ : QueryRead d ρt e₂ i)
    (hlink : Env.ReadsAs src τ ρt (e₁.vars ∪ e₂.vars))
    (hnl : (∀ l, e₁ = .lit l → Term.lit l ∈ src.terms) ∨
      (∀ l, e₂ = .lit l → Term.lit l ∈ src.terms)) : Matches src (.eq e₁ e₂) τ := by
  have hl₁ : Env.ReadsAs src τ ρt e₁.vars :=
    hlink.mono fun v hv => List.mem_union_iff.mpr (Or.inl hv)
  have hl₂ : Env.ReadsAs src τ ρt e₂.vars :=
    hlink.mono fun v hv => List.mem_union_iff.mpr (Or.inr hv)
  obtain ⟨t₁, ht₁, hu₁⟩ := congUp_of_queryRead hb hs h₁ hl₁
  obtain ⟨t₂, ht₂, hu₂⟩ := congUp_of_queryRead hb hs h₂ hl₂
  have hi : i ∈ src.terms :=
    hnl.elim (fun hn => mem_terms_of_queryRead hs h₁ hl₁ hn)
      (fun hn => mem_terms_of_queryRead hs h₂ hl₂ hn)
  exact .eq hi ht₁ ht₂ hu₁.congOn_pair_left.symm
    (hu₁.congOn_pair_left.trans hu₂.congOn_pair_right.symm)

theorem matches_of_patternRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {τ ρt : Env} {p : Pattern} (hg : p.GroundedAt src)
    (h : PatternRead d ρt p) (hlink : Env.ReadsAs src τ ρt p.vars) :
    Matches src p τ := by
  cases h with
  | expr hr => exact matches_expr_of_queryRead hb hs hr hlink hg
  | eq h₁ h₂ => exact matches_eq_of_queryRead hb hs h₁ h₂ hlink hg

theorem validQuerySubst_of_patternReads {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {q : Query} {g : Var → Term} {ρt : Env}
    (hgt : ∀ v ∈ Query.vars q, g v ∈ src.values)
    (hlink : ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i → StoredCong src (g v) i)
    (hgr : ∀ p ∈ q, p.GroundedAt src) (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ τ, ValidQuerySubst src q τ ∧ (∀ b ∈ τ, b.1 ∈ Query.vars q) ∧
      ∀ v ∈ Query.vars q, Env.lookup v τ = some (g v) := by
  apply validQuerySubst_of_assignment hgt
  intro p hp
  refine matches_of_patternRead hb hs (hgr p hp) (hread p hp) fun v hv i hi => ?_
  exact ⟨g v, lookup_nil_sourceSubst hv, hlink v (Query.mem_vars.mpr ⟨p, hp, hv⟩) i hi,
    (hgt v (Query.mem_vars.mpr ⟨p, hp, hv⟩)).2⟩


mutual

theorem exists_source_of_argVar {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} {e : Expr} {i : Term} (h : QueryRead d ρt e i) (hv : Expr.ArgVar v e) :
    ∃ j t, Env.lookup v ρt = some j ∧ StoredCong src t j := by
  cases h with
  | lit => exact absurd hv (by simp [Expr.ArgVar])
  | var => exact absurd hv (by simp [Expr.ArgVar])
  | @app f args es i hl ho =>
    obtain ⟨as, -, hal, -⟩ := hs f _ _ ho
    rcases hv with hv | hv
    · exact exists_source_of_memVar hl hal hv
    · exact exists_source_of_argVarList hs hl hv

theorem exists_source_of_memVar {src d : Database} {ρt : Env} {v : Var} :
    ∀ {args : List Expr} {es as : List Term}, QueryReadList d ρt args es →
      StoredCongList src as es → Expr.var v ∈ args →
      ∃ j t, Env.lookup v ρt = some j ∧ StoredCong src t j
  | _, _, _, .nil, _, hv => absurd hv (by simp)
  | _, _, _, .cons hr hl, hc, hv => by
    cases hc with
    | cons hc hcl =>
      rcases List.mem_cons.mp hv with rfl | hv
      · cases hr with
        | var hlk => exact ⟨_, _, hlk, hc⟩
      · exact exists_source_of_memVar hl hcl hv

theorem exists_source_of_argVarList {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} : ∀ {args : List Expr} {es : List Term}, QueryReadList d ρt args es →
      Expr.ArgVarList v args → ∃ j t, Env.lookup v ρt = some j ∧ StoredCong src t j
  | _, _, .nil, hv => absurd hv (by simp [Expr.ArgVarList])
  | _, _, .cons hr hl, hv => by
    rcases hv with hv | hv
    · exact exists_source_of_argVar hs hr hv
    · exact exists_source_of_argVarList hs hl hv

end

theorem exists_source_of_patternArgVar {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} {p : Pattern} (h : PatternRead d ρt p) (hv : Pattern.ArgVar v p) :
    ∃ j t, Env.lookup v ρt = some j ∧ StoredCong src t j := by
  cases h with
  | expr hr => exact exists_source_of_argVar hs hr hv
  | eq h₁ h₂ => exact hv.elim (exists_source_of_argVar hs h₁) (exists_source_of_argVar hs h₂)

/-- Every declared view has the compiler's singleton-output table declaration. -/
def ViewTables (d : Database) : Prop :=
  ∀ f decl, d.sig (viewName f) = some decl → ∃ k, decl = tableDecl k

theorem out_of_matches_entry {d : Database} (hd : d.Diag)
    (hstore : d.StoreOk) (hdecl : ViewTables d)
    {as : List Expr} {f : FnName} {v : Var} {σ : Env}
    (h : Matches d (.expr (.app (viewName f) (as ++ [.var v]))) σ) :
    ∃ ts us, Expr.evalList d.sig as σ = some ts ∧
      Expr.evalList d.sig [.var v] σ = some us ∧
      Term.app (viewName f) (ts ++ us) ∈ d.terms ∧ d.Out (viewName f) ts us := by
  cases h using Matches.storedCases with
  | expr hw hev hc =>
    obtain ⟨decl, hf, heval⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨k, rfl⟩ := hdecl f decl hf
    have hwidth : (as ++ [Expr.var v]).length = k + 1 := by
      by_contra hn
      have hn' : as.length ≠ k := by simpa using hn
      simp [tableDecl, FnDecl.entryWidth, hn'] at heval
    obtain ⟨cols, hcols, rfl⟩ := Expr.evalAtom_app_inv hev
    obtain ⟨ts, us, hts, hus, rfl⟩ := Expr.evalList_append hcols
    have heq := congOn_eq_of_diag hd hc
    subst heq
    have hvalid : (Entry.mk (viewName f) ts us).Valid d.sig := by
      refine ⟨tableDecl k, hf, by simp [tableDecl], ?_, ?_, (hstore.term hw).childrenValues⟩
      · have := Expr.evalList_length hts
        simp only [List.length_append, List.length_singleton] at hwidth
        simp only [tableDecl]
        omega
      · simpa [tableDecl] using Expr.evalList_length hus
    refine ⟨ts, us, hts, hus, hw, ts, CongList.refl fun a ha => ?_,
      hstore.entry_of_held_atom hvalid hw⟩
    exact d.subtermClosed _ hw
      (Term.arg_subterms (List.mem_append_left _ ha) (Term.self_mem_subterms a))

theorem encodeQueryExpr_var {v : Var} {n : Nat} :
    encodeQueryExpr (.var v) n = (.var v, [], n) := rfl

theorem encodeQueryExpr_app_expr {f : FnName} {args : List Expr} {n : Nat} :
    (encodeQueryExpr (.app f args) n).1 = .var (freshVar (encodeQueryArgs args n).2.2) := rfl

theorem encodeQueryExpr_app_atoms {f : FnName} {args : List Expr} {n : Nat} :
    (encodeQueryExpr (.app f args) n).2.1 =
      (encodeQueryArgs args n).2.1 ++
        [.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))] := rfl

theorem encodeQueryArgs_cons_exprs {e : Expr} {es : List Expr} {n : Nat} :
    (encodeQueryArgs (e :: es) n).1 =
      (encodeQueryExpr e n).1 :: (encodeQueryArgs es (encodeQueryExpr e n).2.2).1 := rfl

theorem encodeQueryArgs_cons_atoms {e : Expr} {es : List Expr} {n : Nat} :
    (encodeQueryArgs (e :: es) n).2.1 =
      (encodeQueryExpr e n).2.1 ++ (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.1 := rfl

theorem encodePattern_expr_atoms {e : Expr} {n : Nat} :
    (encodePattern (.expr e) n).1 = (encodeQueryExpr e n).2.1 := rfl

theorem encodePattern_eq_atoms {e₁ e₂ : Expr} {n : Nat} :
    (encodePattern (.eq e₁ e₂) n).1 =
      (encodeQueryExpr e₁ n).2.1 ++
        (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).2.1 ++
        [.eq (encodeQueryExpr e₁ n).1 (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1] := rfl

theorem encodeQuery_cons_atoms {p : Pattern} {ps : Query} {n : Nat} :
    (encodeQuery (p :: ps) n).1 =
      (encodePattern p n).1 ++ (encodeQuery ps (encodePattern p n).2).1 := rfl

theorem encodePattern_subset_encodeQuery {p : Pattern} : ∀ {q : Query}, p ∈ q → ∀ n : Nat,
    ∃ m, (encodePattern p m).1 ⊆ (encodeQuery q n).1
  | [], hp, _ => absurd hp (by simp)
  | p' :: ps, hp, n => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨n, by
        rw [encodeQuery_cons_atoms]; exact fun a ha => List.mem_append.mpr (Or.inl ha)⟩
    · obtain ⟨m, hm⟩ := encodePattern_subset_encodeQuery hp' (encodePattern p' n).2
      exact ⟨m, by
        rw [encodeQuery_cons_atoms]; exact fun a ha => List.mem_append.mpr (Or.inr (hm ha))⟩

theorem mem_encodeQueryArgs_of_mem {v : Var} : ∀ {args : List Expr} {n : Nat},
    Expr.var v ∈ args → Expr.var v ∈ (encodeQueryArgs args n).1
  | [], _, h => absurd h (by simp)
  | a :: as, n, h => by
    rw [encodeQueryArgs_cons_exprs]
    rcases List.mem_cons.mp h with rfl | h'
    · rw [encodeQueryExpr_var]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_encodeQueryArgs_of_mem h')

/-! The flattening emits no atom for a `min`, so the reading lemmas below ask the source
expression to be ordering-free; the source domain guarantees it. -/

mutual

theorem lookup_isSome_of_argVar {d : Database} {σ : Env} {v : Var} :
    ∀ (e : Expr) (n : Nat), e.OrderingFree →
      (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      Expr.ArgVar v e → (Env.lookup v (σ)).isSome
  | .lit _, _, _, _, hv => absurd hv (by simp [Expr.ArgVar])
  | .var _, _, _, _, hv => absurd hv (by simp [Expr.ArgVar])
  | .min _ _, _, hof, _, _ => (Expr.not_orderingFree_min hof).elim
  | .ite _ _ _ _, _, hof, _, _ => (Expr.not_orderingFree_ite hof).elim
  | .app f args, n, hof, hm, hv => by
    rw [encodeQueryExpr_app_atoms] at hm
    rcases hv with hv | hv
    · cases hm (.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))) (by simp) using Matches.storedCases with
      | expr _ hev _ =>
        obtain ⟨cols, hcols, -⟩ := Expr.evalAtom_app_inv hev
        obtain ⟨ts, us, hts, -, -⟩ := Expr.evalList_append hcols
        exact Expr.lookup_isSome_of_mem_evalList hts (mem_encodeQueryArgs_of_mem hv)
    · exact lookup_isSome_of_argVarList args n (Expr.orderingFree_app hof)
        (fun a ha => hm a (List.mem_append.mpr (Or.inl ha))) hv

theorem lookup_isSome_of_argVarList {d : Database} {σ : Env} {v : Var} :
    ∀ (es : List Expr) (n : Nat), Expr.OrderingFreeList es →
      (∀ a ∈ (encodeQueryArgs es n).2.1, Matches d a σ) →
      Expr.ArgVarList v es → (Env.lookup v (σ)).isSome
  | [], _, _, _, hv => absurd hv (by simp [Expr.ArgVarList])
  | e :: es, n, hof, hm, hv => by
    rw [encodeQueryArgs_cons_atoms] at hm
    rcases hv with hv | hv
    · exact lookup_isSome_of_argVar e n (Expr.orderingFreeList_cons hof).1
        (fun a ha => hm a (List.mem_append.mpr (Or.inl ha))) hv
    · exact lookup_isSome_of_argVarList es (encodeQueryExpr e n).2.2
        (Expr.orderingFreeList_cons hof).2
        (fun a ha => hm a (List.mem_append.mpr (Or.inr ha))) hv

end

theorem lookup_isSome_of_patternArgVar {d : Database} {σ : Env} {v : Var} :
    ∀ (p : Pattern) (n : Nat), p.OrderingFree →
      (∀ a ∈ (encodePattern p n).1, Matches d a σ) → Pattern.ArgVar v p →
      (Env.lookup v (σ)).isSome
  | .expr e, n, hof, hm, hv => lookup_isSome_of_argVar e n hof hm hv
  | .eq e₁ e₂, n, hof, hm, hv => by
    rw [encodePattern_eq_atoms] at hm
    rcases hv with hv | hv
    · exact lookup_isSome_of_argVar e₁ n hof.1
        (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha))))) hv
    · exact lookup_isSome_of_argVar e₂ (encodeQueryExpr e₁ n).2.2 hof.2
        (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha))))) hv

theorem exists_eval_encodeQueryExpr {d : Database} {σ : Env} :
    ∀ (e : Expr) (n : Nat), e.OrderingFree →
      (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      (∀ v ∈ e.vars, ∃ t, Env.lookup v σ = some t ∧ t.IsValue d.sig) →
      ∃ i, Expr.eval d.sig (encodeQueryExpr e n).1 (σ) = some i
  | .lit l, _, _, _, _ => ⟨.lit l, rfl⟩
  | .var v, _, _, _, hb => by
    obtain ⟨t, ht, hv⟩ := hb v (by simp)
    exact ⟨t, ht⟩
  | .min _ _, _, hof, _, _ => (Expr.not_orderingFree_min hof).elim
  | .ite _ _ _ _, _, hof, _, _ => (Expr.not_orderingFree_ite hof).elim
  | .app f args, n, _, hm, _ => by
    rw [encodeQueryExpr_app_atoms] at hm
    rw [encodeQueryExpr_app_expr, Expr.eval_var]
    cases hm (.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))) (by simp) using Matches.storedCases with
    | expr _ hev _ =>
      obtain ⟨cols, hcols, -⟩ := Expr.evalAtom_app_inv hev
      obtain ⟨ts, us, -, hus, -⟩ := Expr.evalList_append hcols
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at hus
      obtain ⟨a, ha, _⟩ := hus
      exact ⟨a, ha⟩
private theorem evalList_one_var {sig : Signature} {x : Var} {ρ : Env} {us : List Term}
    (h : Expr.evalList sig [.var x] ρ = some us) :
    ∃ a, Env.lookup x ρ = some a ∧ us = [a] := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain rfl : rest = [] := (Option.some.inj hrest).symm
  exact ⟨a, ha, rfl⟩

mutual

theorem queryRead_of_matches {d : Database} (hd : d.Diag)
    (hstore : d.StoreOk) (hdecl : ViewTables d) {σ : Env} :
    ∀ (e : Expr) (n : Nat) {i : Term}, e.OrderingFree →
      (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      Expr.eval d.sig (encodeQueryExpr e n).1 (σ) = some i →
      QueryRead d (σ) e i
  | .lit l, _, _, _, _, hi => by
    obtain rfl : Term.lit l = _ := Option.some.inj hi
    exact .lit
  | .var _, _, _, _, _, hi => .var hi
  | .min _ _, _, _, hof, _, _ => (Expr.not_orderingFree_min hof).elim
  | .ite _ _ _ _, _, _, hof, _, _ => (Expr.not_orderingFree_ite hof).elim
  | .app f args, n, i, hof, hm, hi => by
    rw [encodeQueryExpr_app_atoms] at hm
    rw [encodeQueryExpr_app_expr, Expr.eval_var] at hi
    obtain ⟨ts, us, hts, hus, -, ho⟩ :=
      out_of_matches_entry hd hstore hdecl
        (as := (encodeQueryArgs args n).1)
        (hm (.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))) (by simp))
    obtain ⟨a, ha, rfl⟩ := evalList_one_var hus
    obtain rfl : a = i := Option.some.inj (ha.symm.trans hi)
    exact .app (queryReadList_of_matches hd hstore hdecl args n (Expr.orderingFree_app hof)
      (fun x hx => hm x (List.mem_append.mpr (Or.inl hx))) hts) ho

theorem queryReadList_of_matches {d : Database} (hd : d.Diag)
    (hstore : d.StoreOk) (hdecl : ViewTables d) {σ : Env} :
    ∀ (es : List Expr) (n : Nat) {ts : List Term}, Expr.OrderingFreeList es →
      (∀ a ∈ (encodeQueryArgs es n).2.1, Matches d a σ) →
      Expr.evalList d.sig (encodeQueryArgs es n).1 (σ) = some ts →
      QueryReadList d (σ) es ts
  | [], _, _, _, _, h => by
    obtain rfl : ([] : List Term) = _ := Option.some.inj h
    exact .nil
  | e :: es, n, ts, hof, hm, h => by
    rw [encodeQueryArgs_cons_atoms] at hm
    rw [encodeQueryArgs_cons_exprs, Expr.evalList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h'⟩ := h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact .cons (queryRead_of_matches hd hstore hdecl e n (Expr.orderingFreeList_cons hof).1
        (fun x hx => hm x (List.mem_append.mpr (Or.inl hx))) ht)
      (queryReadList_of_matches hd hstore hdecl es (encodeQueryExpr e n).2.2
        (Expr.orderingFreeList_cons hof).2
        (fun x hx => hm x (List.mem_append.mpr (Or.inr hx))) hus)

end

theorem patternRead_of_matches {d : Database} (hd : d.Diag)
    (hstore : d.StoreOk) (hdecl : ViewTables d) {σ : Env} :
    ∀ (p : Pattern) (n : Nat), p.OrderingFree →
      (∀ v ∈ p.vars, ∃ t, Env.lookup v σ = some t ∧ t.IsValue d.sig) →
      (∀ a ∈ (encodePattern p n).1, Matches d a σ) → PatternRead d (σ) p
  | .expr e, n, hof, hb, hm => by
    rw [encodePattern_expr_atoms] at hm
    obtain ⟨i, hi⟩ := exists_eval_encodeQueryExpr e n hof hm hb
    exact .expr (queryRead_of_matches hd hstore hdecl e n hof hm hi)
  | .eq e₁ e₂, n, hof, _, hm => by
    rw [encodePattern_eq_atoms] at hm
    cases hm (.eq (encodeQueryExpr e₁ n).1 (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1)
        (by simp) using Matches.storedCases with
    | @eq _ _ _ w t₁ t₂ hw he₁ he₂ hc₁ hc₂ =>
      obtain rfl : t₁ = t₂ := congOn_eq_of_diag hd hc₂
      exact .eq
        (queryRead_of_matches hd hstore hdecl e₁ n hof.1
          (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha)))))
          he₁)
        (queryRead_of_matches hd hstore hdecl e₂ (encodeQueryExpr e₁ n).2.2 hof.2
          (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha)))))
          he₂)

theorem patternReads_of_encodeQuery_matches {tgt : Database} (hd : tgt.Diag)
    (hstore : tgt.StoreOk) (hdecl : ViewTables tgt) {q : Query} {n : Nat} {σ : Env}
    (hof : ∀ p ∈ q, p.OrderingFree) (hk : Query.VarsKeyed q)
    (hval : ∀ b ∈ σ, b.2 ∈ tgt.values)
    (h : ∀ p ∈ (encodeQuery q n).1, Matches tgt p σ) :
    ∀ p ∈ q, PatternRead tgt σ p := by
  have hblock : ∀ p ∈ q, ∃ m, ∀ a ∈ (encodePattern p m).1, Matches tgt a σ := by
    intro p hp
    obtain ⟨m, hsub⟩ := encodePattern_subset_encodeQuery hp n
    exact ⟨m, fun a ha => h a (hsub ha)⟩
  have hbound : ∀ v ∈ Query.vars q, (Env.lookup v σ).isSome := by
    intro v hv
    obtain ⟨p, hp, ha⟩ := hk v hv
    obtain ⟨m, hm⟩ := hblock p hp
    exact lookup_isSome_of_patternArgVar p m (hof p hp) hm ha
  intro p hp
  obtain ⟨m, hm⟩ := hblock p hp
  exact patternRead_of_matches hd hstore hdecl p m (hof p hp)
    (fun v hv => by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hbound v (Query.mem_vars.mpr ⟨p, hp, hv⟩))
      exact ⟨t, ht, (hval (v, t) (Env.mem_of_lookup ht)).2⟩) hm


theorem patternReads_of_encodeQuery {tgt : Database} (hd : tgt.Diag)
    (hstore : tgt.StoreOk) (hdecl : ViewTables tgt)
    {q : Query} {n : Nat} {σ : Env}
    (hof : ∀ p ∈ q, p.OrderingFree) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∀ p ∈ q, PatternRead tgt σ p :=
  patternReads_of_encodeQuery_matches hd hstore hdecl hof hk
    (h.mem_values hstore (encodeQuery_safe q n hof hk))
    (fun _ hp => h.matches_of_mem hp)

theorem mem_terms_of_patternArgVar {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} {p : Pattern} (h : PatternRead d ρt p) (hv : Pattern.ArgVar v p) :
    ∃ i, Env.lookup v ρt = some i ∧ i ∈ src.terms := by
  obtain ⟨j, t, hj, hc⟩ := exists_source_of_patternArgVar hs h hv
  exact ⟨j, hj, hc.mem_right⟩

def idReading (ρt : Env) : Var → Term := fun v => (Env.lookup v ρt).getD (.lit (.int 0))

theorem idReading_eq {ρt : Env} {v : Var} {i : Term} (h : Env.lookup v ρt = some i) :
    idReading ρt v = i := by simp [idReading, h]

theorem termsBuild_isValue {src : Database} (hb : src.TermsBuild) (hw : src.WF)
    {t : Term} (ht : t ∈ src.terms) : t.IsValue src.sig := by
  induction t using Term.recTerm with
  | lit l => exact .lit _ _
  | app f as ih =>
    exact .app (hb f as ht) fun a ha => ih a ha
      (hw.subtermClosed _ ht (Term.arg_subterms ha (Term.self_mem_subterms _)))

theorem exists_validQuerySubst_at_ids {src d : Database} (hb : src.TermsBuild) (hw : src.WF)
    (hs : ViewsSound d src) {q : Query} {ρt : Env}
    (hgr : ∀ p ∈ q, p.GroundedAt src) (hk : Query.VarsKeyed q)
    (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ τ, ValidQuerySubst src q τ ∧ (∀ b ∈ τ, b.1 ∈ Query.vars q) ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i →
        Env.lookup v τ = some i := by
  have hbound : ∀ v ∈ Query.vars q, ∃ i, Env.lookup v ρt = some i ∧ i ∈ src.terms := by
    intro v hv
    obtain ⟨p, hp, ha⟩ := hk v hv
    exact mem_terms_of_patternArgVar hs (hread p hp) ha
  have hgt : ∀ v ∈ Query.vars q, idReading ρt v ∈ src.values := by
    intro v hv
    obtain ⟨i, hi, hm⟩ := hbound v hv
    rw [idReading_eq hi]; exact ⟨hm, termsBuild_isValue hb hw hm⟩
  obtain ⟨τ, hv, hdom, hτ⟩ := validQuerySubst_of_patternReads hb hs
    (g := idReading ρt) hgt
    (fun v hv i hi => idReading_eq hi ▸ Database.toStored (hgt v hv).1) hgr hread
  exact ⟨τ, hv, hdom, fun v hvq i hi => by
    rw [hτ v hvq, idReading_eq hi]⟩

/-- A match of the flattened query supplies an existing source match at the same values.
This is the query obligation used when transporting a compiled rule head to the source. -/
theorem sourceMatch_of_encodedQuery {src tgt : Database} (hb : src.TermsBuild) (hw : src.WF)
    (hs : ViewsSound tgt src) (hd : tgt.Diag)
    (hstore : tgt.StoreOk) (hdecl : ViewTables tgt) {q : Query} {n : Nat} {σ : Env}
    (hof : ∀ p ∈ q, p.OrderingFree) (hg : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∃ τ, ValidQuerySubst src q τ ∧ (∀ b ∈ τ, b.1 ∈ Query.vars q) ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v σ = some i →
        Env.lookup v (τ) = some i :=
  exists_validQuerySubst_at_ids hb hw hs (fun p hp => (hg p hp).groundedAt) hk
    (patternReads_of_encodeQuery hd hstore hdecl hof hk h)

end Egglog.Congruence
