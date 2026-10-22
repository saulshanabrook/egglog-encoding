import EgglogSemantics.Proofs.Congruence.LiveFixedpoint
import EgglogSemantics.Proofs.Congruence.QuerySubst
import EgglogSemantics.Proofs.Congruence.RebuildSubst

/-! Current-row closure follows from actual completed maintenance rounds. -/

namespace Egglog.Congruence.Abstract

theorem Matches.bound {d : Database} {p : Pattern} {ρ : Env} (hm : Matches d p ρ) (ho : p.OrderingFree)
    {v : Var} (hv : v ∈ p.vars) : (Env.lookup v ρ).isSome := by
  cases hm with
  | @atom e _ _ he _ =>
      cases e with
      | app f es =>
          obtain ⟨ts, he, _⟩ := Expr.evalAtom_app_inv he
          exact Expr.lookup_isSome_of_mem_varsList ho he hv
      | lit _ | var _ | min _ _ => exact Expr.lookup_isSome_of_mem_vars ho he hv
      | ite => exact (Expr.not_orderingFree_ite ho).elim
  | equal ha hb _ =>
      rcases List.mem_union_iff.mp hv with hv | hv
      · exact Expr.lookup_isSome_of_mem_vars ho.1 ha hv
      · exact Expr.lookup_isSome_of_mem_vars ho.2 hb hv

theorem evalAtom_of_row {sig : Signature} {row : Entry} (hv : row.Shape sig)
    {es : List Expr} {ρ : Env} (he : Expr.evalList sig es ρ = some row.columns) :
    (Expr.app row.name es).evalAtom sig ρ = some row.atom := by
  obtain ⟨decl, hd, hm, hk, hv⟩ := hv
  have hw : es.length = decl.entryWidth := by
    rw [← Expr.evalList_length he]
    simp [Entry.columns, hk, hv, FnDecl.entryWidth, hm]
  rw [Expr.evalAtom_app_decl hd (Or.inr hw), he]
  rfl

theorem match_current {d : Database} {row : Entry} (hr : row ∈ d.entries)
    {es : List Expr} {ρ : Env} (he : Expr.evalList d.sig es ρ = some row.columns) :
    Matches d (.expr (.app row.name es)) ρ := by
  have held := (StoredCong.direct hr.2).mem_left
  exact .atom (evalAtom_of_row hr.1 he) (Database.toCong held)

theorem out_values {d : Database} (hd : d.Diag) (hs : d.StoreOk)
    {f : FnName} {cs vs : List Term} (ho : d.Out f cs vs) :
    ∀ t ∈ cs ++ vs, t ∈ d.values := fun t ht =>
  ⟨ho.columns hd t ht, (hs.entry_valid (ho.entry hd)).column_values t ht⟩

/-- Construct the actual rule firing, retaining value guards in its query substitution. -/
theorem atom_rule_result {d : Database} {r : Rule} {ρ : Env}
    (hval : ∀ b ∈ ρ, b.2 ∈ d.values) (hnames : ∀ b ∈ ρ, b.1 ∈ Query.vars r.query)
    (hq : ∀ p ∈ r.query, Matches d p ρ) (ho : ∀ p ∈ r.query, p.OrderingFree)
    {row : Entry} (hv : row.Valid d.sig)
    {es : List Expr} (hhead : r.actions = [.expr (.app row.name es)])
    (he : Expr.evalList d.sig es ρ = some row.columns) :
    d.putEntry row ∈ RuleResults d r := by
  have hbound : ∀ v ∈ Query.vars r.query,
      ∃ t, Env.lookup v ρ = some t ∧ t ∈ d.values := by
    intro v hv
    obtain ⟨p, hp, hv⟩ := Query.mem_vars.mp hv
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (Matches.bound (hq p hp) (ho p hp) hv)
    exact ⟨t, ht, hval (v, t) (Env.mem_of_lookup ht)⟩
  obtain ⟨σ, hσ, hag⟩ := validQuerySubst_of_matches hbound hq
  have heσ : Expr.evalList d.sig es σ = some row.columns := by
    rw [Expr.evalList_agreeOn es (fun v hv => ?_)]
    · exact he
    by_cases hvq : v ∈ r.query.vars
    · exact hag v hvq
    · have hnoneσ : Env.lookup v σ = none := Env.lookup_eq_none_iff.mpr fun hvσ => by
        obtain ⟨p, hp, hfv⟩ := hσ.mem_dom_iff.mp hvσ
        exact hvq (Query.mem_vars.mpr ⟨p, hp, (p.mem_freeVars.mp hfv).1⟩)
      have hnoneρ : Env.lookup v ρ = none := Env.lookup_eq_none_iff.mpr fun hvρ => by
        obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hvρ
        exact hvq (hnames (v, t) ht)
      rw [hnoneσ, hnoneρ]
  refine ⟨σ, hσ, ?_⟩
  rw [hhead]
  have hev := evalAtom_of_row hv.shape heσ
  simp only [evalLocalActions, evalActions, evalAction, hev, Option.map_some,
    Option.bind_some]
  rfl

theorem atom_rule_bound {d : Database} {R : RulesetName} (h : Live.State d)
    (hg : Live.GeneratedTables d.sig) (hn : d.NoUnions) (hs : d.StoreOk)
    (hrules : d.RulesSafe)
    (hsat : RunSaturated R d) {r : Rule} (hr : r ∈ d.rules)
    (hR : r.ruleset = R) {ρ : Env}
    (hval : ∀ b ∈ ρ, b.2 ∈ d.values) (hnames : ∀ b ∈ ρ, b.1 ∈ Query.vars r.query)
    (hq : ∀ p ∈ r.query, Matches d p ρ) {f : FnName} {cs : List Term} {a : Term}
    (hv : (Entry.mk f cs [a]).Valid d.sig) {es : List Expr}
    (hhead : r.actions = [.expr (.app f es)])
    (he : Expr.evalList d.sig es ρ = some (cs ++ [a])) :
    ∃ b, d.Out f cs [b] ∧ Live.Joined d a b ∧ IdLe b a := by
  have hf := atom_rule_result hval hnames hq (hrules r hr).2 hv hhead he
  have hrow : Entry.mk f cs [a] ∈ (d.putEntry ⟨f, cs, [a]⟩).entries := by
    rw [Database.putEntry_entries hv]; exact Set.mem_insert _ _
  obtain ⟨b, hb, hj, hle⟩ := Live.firing_row_bound h hg hn hs hrules hsat hr hR hf hrow
  exact ⟨b, out_of_current hs hb, hj, hle⟩

theorem compress_closed {d : Database} {R : RulesetName} (h : Live.State d)
    (hg : Live.GeneratedTables d.sig) (hn : d.NoUnions) (hs : d.StoreOk)
    (hrules : d.RulesSafe)
    (hsat : RunSaturated R d) (hr : { pathCompressRule with ruleset := R } ∈ d.rules)
    (hdesc : ∀ a b, d.Out ufName [a] [b] → IdLe b a)
    {a b c : Term} (hab : d.Out ufName [a] [b]) (hbc : d.Out ufName [b] [c]) :
    d.Out ufName [a] [c] := by
  let ρ : Env := [("@a", a), ("@b", b), ("@c", c)]
  have ha := out_values hn.diag hs hab a (by simp)
  have hb := out_values hn.diag hs hab b (by simp)
  have hc := out_values hn.diag hs hbc c (by simp)
  have hval : ∀ v ∈ ρ, v.2 ∈ d.values := by
    intro v hv
    simp only [ρ, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have hq : ∀ p ∈ pathCompressRule.query, Matches d p ρ := by
    intro p hp
    simp only [pathCompressRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact match_current (hab.entry hn.diag) (by
        simp [ρ, Expr.evalList, Expr.eval, Env.lookup, hb.2,
          Entry.columns])
    · exact match_current (hbc.entry hn.diag) (by
        simp [ρ, Expr.evalList, Expr.eval, Env.lookup, hc.2,
          Entry.columns])
  obtain ⟨x, hx, _, hle⟩ := atom_rule_bound h hg hn hs hrules hsat hr rfl hval
    (by simp [ρ, pathCompressRule, Query.vars, Pattern.vars, Expr.vars, Expr.varsList])
    hq (Live.ufEntry_valid h.uf ha.2 hc.2) rfl (by
      simp [ρ, Expr.evalList, Expr.eval, Env.lookup])
  have he : x = b := List.singleton_inj.mp (hsat.1.out_unique hx hab)
  have hbc' : b = c := (he ▸ hle).antisymm (hdesc b c hbc)
  exact hbc' ▸ hab


private theorem varsList_map_var (vs : List Var) (v : Var) :
    v ∈ Expr.varsList (vs.map Expr.var) ↔ v ∈ vs := by
  induction vs with
  | nil => simp
  | cons w ws ih => simp [Expr.vars, ih]

theorem rebuildSubst_names {q : Query} {f : FnName} {arg : Expr}
    (cs : List Term) (e x : Term)
    (hv : Pattern.expr (.app (viewName f) (rebuildVars cs.length ++ [.var "@e"])) ∈ q)
    (hu : Pattern.expr (.app ufName [arg, .var "@x"]) ∈ q) :
    ∀ b ∈ rebuildSubst cs e x, b.1 ∈ Query.vars q := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Query.mem_vars.mpr ⟨_, hv, by simp [Pattern.vars, Expr.vars, Expr.varsList]⟩
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Query.mem_vars.mpr ⟨_, hu, by simp [Pattern.vars, Expr.vars, Expr.varsList]⟩
  apply Query.mem_vars.mpr
  refine ⟨_, hv, ?_⟩
  change b.1 ∈ Expr.varsList (rebuildVars cs.length ++ [.var "@e"])
  apply (Expr.mem_varsList_append _ _).mpr
  apply Or.inl
  rw [rebuildVars_eq_map, varsList_map_var]
  exact (List.of_mem_zip hb).1

theorem rebuildSubst_values {d : Database} {cs : List Term} {e x : Term}
    (hc : ∀ t ∈ cs, t ∈ d.values) (he : e ∈ d.values) (hx : x ∈ d.values) :
    ∀ b ∈ rebuildSubst cs e x, b.2 ∈ d.values := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact he
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hx
  exact hc b.2 (List.of_mem_zip hb).2


theorem output_closed {d : Database} {R : RulesetName} (h : Live.State d)
    (hg : Live.GeneratedTables d.sig) (hn : d.NoUnions) (hs : d.StoreOk)
    (hrules : d.RulesSafe)
    (hsat : RunSaturated R d)
    (hdesc : ∀ a b, d.Out ufName [a] [b] → IdLe b a)
    {f : FnName} {cs : List Term} {e x : Term}
    (hr : { eclassRule f cs.length with ruleset := R } ∈ d.rules)
    (hv : d.Out (viewName f) cs [e]) (he : d.Out ufName [e] [x]) :
    d.Out (viewName f) cs [x] := by
  have hcs : ∀ t ∈ cs, t ∈ d.values := fun t ht =>
    out_values hn.diag hs hv t (List.mem_append_left _ ht)
  have heval := out_values hn.diag hs hv e (by simp)
  have hxval := out_values hn.diag hs he x (by simp)
  have hval := rebuildSubst_values hcs heval hxval
  have hkeys := eval_rebuildVars cs e x (fun t ht => (hcs t ht).2)
  have hq : ∀ p ∈ (eclassRule f cs.length).query,
      Matches d p (rebuildSubst cs e x) := by
    intro p hp
    simp only [eclassRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · apply match_current (hv.entry hn.diag)
      simp [Expr.evalList_append_map, hkeys, Expr.evalList, Expr.eval,
        Entry.columns]
    · apply match_current (he.entry hn.diag)
      simp [Expr.evalList, Expr.eval, Entry.columns]
  have hvalid : (Entry.mk (viewName f) cs [x]).Valid d.sig :=
    (hs.entry_valid (hv.entry hn.diag)).with_value rfl (by simpa using hxval.2)
  obtain ⟨b, hb, _, hle⟩ := atom_rule_bound h hg hn hs hrules hsat hr rfl hval
    (rebuildSubst_names cs e x (f := f) (arg := .var "@e") (by simp [eclassRule])
      (by simp [eclassRule])) hq hvalid rfl (by
        simp [Expr.evalList_append_map, hkeys, Expr.evalList, Expr.eval,
          hxval.2])
  have hbe : b = e := List.singleton_inj.mp (hsat.1.out_unique hb hv)
  have hex : e = x := (hbe ▸ hle).antisymm (hdesc e x he)
  exact hex ▸ hv

theorem view_root_of_output {d : Database} (hn : MergeNormal d)
    (hout : ∀ f cs e x, d.Out (viewName f) cs [e] → d.Out ufName [e] [x] →
      d.Out (viewName f) cs [x]) {f : FnName} {cs : List Term} {e : Term}
    (hv : d.Out (viewName f) cs [e]) : Root d e := by
  intro x hx
  rcases hx with hx | hx
  · exact hx.symm
  exact List.singleton_inj.mp (hn.out_unique (hout f cs e x hv hx) hv)

theorem child_closed {d : Database} {R : RulesetName} (h : Live.State d)
    (hg : Live.GeneratedTables d.sig) (hn : d.NoUnions) (hs : d.StoreOk)
    (hrules : d.RulesSafe)
    (hsat : RunSaturated R d)
    (hcompress : ∀ a b c, d.Out ufName [a] [b] → d.Out ufName [b] [c] →
      d.Out ufName [a] [c])
    (hroots : ∀ f cs e, d.Out (viewName f) cs [e] → Root d e)
    {f : FnName} {cs : List Term} {e x : Term} {i : Nat} (hi : i < cs.length)
    (hr : { childRule f cs.length i with ruleset := R } ∈ d.rules)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hv : d.Out (viewName f) cs [e]) (he : d.Out ufName [cs[i]] [x]) :
    d.Out (viewName f) (cs.set i x) [e] := by
  have hcs : ∀ t ∈ cs, t ∈ d.values := fun t ht =>
    out_values hn.diag hs hv t (List.mem_append_left _ ht)
  have heval := out_values hn.diag hs hv e (by simp)
  have hxval := out_values hn.diag hs he x (by simp)
  have hval := rebuildSubst_values hcs heval hxval
  have hkeys := eval_rebuildVars cs e x (fun t ht => (hcs t ht).2)
  have hq : ∀ p ∈ (childRule f cs.length i).query,
      Matches d p (rebuildSubst cs e x) := by
    intro p hp
    simp only [childRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · apply match_current (hv.entry hn.diag)
      simp [Expr.evalList_append_map, hkeys, Expr.evalList, Expr.eval,
        Entry.columns]
    · apply match_current (he.entry hn.diag)
      simp only [Expr.evalList, Expr.eval, rebuildSubst_key (e := e) (x := x) i hi,
        rebuildSubst_x]
      simp [Entry.columns]
  have hx : Expr.eval d.sig (.var "@x") (rebuildSubst cs e x) = some x := by
    simp [Expr.eval]
  have hhead : Expr.evalList d.sig
      ((rebuildVars cs.length).set i (.var "@x") ++ [.var "@e"])
      (rebuildSubst cs e x) = some (cs.set i x ++ [e]) := by
    rw [Expr.evalList_append_map, Expr.evalList_set hkeys i hx]
    simp [Expr.evalList, Expr.eval]
  have hvalid : (Entry.mk (viewName f) (cs.set i x) [e]).Valid d.sig := by
    exact ⟨tableDecl cs.length, hf, by simp [tableDecl], by simp [tableDecl], rfl,
      Expr.evalList_isValue (fun b hb => (hval b hb).2) hhead⟩
  obtain ⟨b, hb, hj, _⟩ := atom_rule_bound h hg hn hs hrules hsat hr rfl hval
    (rebuildSubst_names cs e x (f := f) (arg := .var ("@c" ++ toString i))
      (by simp [childRule]) (by simp [childRule])) hq hvalid rfl hhead
  have heb : e = b := joined_roots_eq hs hsat.1 hcompress hj
    (hroots f cs e hv) (hroots f (cs.set i x) b hb)
  exact heb ▸ hb

/-- Re-keying individual columns composes to an arbitrary tuple of parent steps. -/
theorem keys_closed {d : Database} {f : FnName}
    (hchild : ∀ cs e i (hi : i < cs.length) x,
      d.Out (viewName f) cs [e] → d.Out ufName [cs[i]] [x] →
        d.Out (viewName f) (cs.set i x) [e]) {cs ds : List Term}
    (hcs : List.Forall₂ (Parent d) cs ds) :
    ∀ pre e, d.Out (viewName f) (pre ++ cs) [e] → d.Out (viewName f) (pre ++ ds) [e] := by
  induction hcs with
  | nil => exact fun _ _ h => h
  | @cons a b cs ds hab _ ih =>
      intro pre e ho
      have hn : d.Out (viewName f) (pre ++ b :: cs) [e] := by
        rcases hab with rfl | hab
        · exact ho
        · have hi : pre.length < (pre ++ a :: cs).length := by simp
          have huf : d.Out ufName [(pre ++ a :: cs)[pre.length]] [b] := by simpa using hab
          have hnew := hchild _ e pre.length hi b ho huf
          simpa using hnew
      simpa only [List.append_assoc, List.singleton_append] using
        ih (pre ++ [b]) e (by simpa only [List.append_assoc, List.singleton_append] using hn)


/-- Each current view has the generated maintenance rules for its key width. -/
def TablesPresent (d : Database) (R : RulesetName := rebuildRuleset) : Prop :=
  ∀ f cs e, d.Out (viewName f) cs [e] →
    d.sig (viewName f) = some (tableDecl cs.length) ∧
    { eclassRule f cs.length with ruleset := R } ∈ d.rules ∧
      ∀ i < cs.length, { childRule f cs.length i with ruleset := R } ∈ d.rules

/-- Actual completed rounds establish closure despite consuming conflicting head rows. -/
theorem closed_of_saturated {d : Database} {R : RulesetName} (h : Live.State d)
    (hg : Live.GeneratedTables d.sig) (hn : d.NoUnions) (hs : d.StoreOk)
    (hrules : d.RulesSafe)
    (hsat : RunSaturated R d) (ht : TablesPresent d R)
    (hr : { pathCompressRule with ruleset := R } ∈ d.rules)
    (hdesc : ∀ a b, d.Out ufName [a] [b] → IdLe b a) : Closed d := by
  have hc : ∀ a b c, d.Out ufName [a] [b] → d.Out ufName [b] [c] →
      d.Out ufName [a] [c] := fun _ _ _ => compress_closed h hg hn hs hrules hsat hr hdesc
  have ho : ∀ f cs e x, d.Out (viewName f) cs [e] → d.Out ufName [e] [x] →
      d.Out (viewName f) cs [x] := fun f cs e _ hv =>
    output_closed h hg hn hs hrules hsat hdesc (ht f cs e hv).2.1 hv
  have hroot : ∀ f cs e, d.Out (viewName f) cs [e] → Root d e :=
    fun _ _ _ => view_root_of_output hsat.1 ho
  refine ⟨hc, ?_, ?_, ho, ?_⟩
  · intro a b c hab hac
    exact Parent.join_of_normal hsat.1 (Or.inr hab) (Or.inr hac)
  · intro f cs a b ha hb
    have he := List.singleton_inj.mp (hsat.1.out_unique ha hb)
    exact ⟨a, .refl d a, Or.inl he.symm⟩
  · intro f cs ds e hv hl
    apply keys_closed (d := d) (f := f) (fun cs e i hi x hv he =>
      child_closed h hg hn hs hrules hsat hc hroot hi ((ht f cs e hv).2.2 i hi)
        (ht f cs e hv).1 hv he) hl [] e hv

theorem rebuilt_of_saturated {d : Database} {R : RulesetName} (h : Live.State d)
    (hg : Live.GeneratedTables d.sig) (hn : d.NoUnions) (hs : d.StoreOk)
    (hrules : d.RulesSafe)
    (hw : d.WF) (hfin : d.terms.Finite) (hsat : RunSaturated R d)
    (ht : TablesPresent d R) (hr : { pathCompressRule with ruleset := R } ∈ d.rules)
    (hdesc : ∀ a b, d.Out ufName [a] [b] → IdLe b a) : Rebuilt d :=
  ⟨hw, hfin, closed_of_saturated h hg hn hs hrules hsat ht hr hdesc, hdesc⟩

/-- A total current UF domain supplies both positive lookups in the leader guard. -/
theorem Rebuilt.root_lookup {d : Database} (h : Rebuilt d) (hd : d.Diag)
    (hs : d.StoreOk) (htotal : ∀ a ∈ d.values, ∃ b, d.Out ufName [a] [b])
    {a : Term} (ha : a ∈ d.values) :
    d.Out ufName [a] [h.root a] ∧ d.Out ufName [h.root a] [h.root a] := by
  have hav : h.root a ∈ d.values := by
    rcases (h.root_spec a).1 with he | he
    · exact he ▸ ha
    · exact out_values hd hs he _ (by simp)
  obtain ⟨b, hb⟩ := htotal (h.root a) hav
  have he : b = h.root a := (h.root_spec a).2 b (Or.inr hb)
  have hself : d.Out ufName [h.root a] [h.root a] := he ▸ hb
  refine ⟨?_, hself⟩
  rcases (h.root_spec a).1 with he | he
  · exact he ▸ hself
  · exact he

end Egglog.Congruence.Abstract
