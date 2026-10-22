import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.Order
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.FiniteSaturation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Termination of generated destructive merging

An output of rank `n` has weight `5 ^ n`. A collision consumes two distinct rows
before evaluating its merge body. A changed merge inserts the result and at most
two UF rows, all at the minimum output; their combined weight is strictly smaller.
-/

namespace Egglog.Congruence.Live

/-- Rank in an arbitrary finite set of value terms. -/
noncomputable def valueRank (values : Set Term) (t : Term) : Nat :=
  {s : Term | s ∈ values ∧ Term.blt s t = true}.ncard

theorem valueRank_lt {values : Set Term} (hv : values.Finite) {a b : Term}
    (ha : a ∈ values) (hab : Term.blt a b = true) :
    valueRank values a < valueRank values b := by
  apply Set.ncard_lt_ncard ?_ (hv.subset fun _ h => h.1)
  refine ⟨?_, ?_⟩
  · intro t ht
    exact ⟨ht.1, Term.blt_trans t a b ht.2 hab⟩
  · intro h
    have := (h ⟨ha, hab⟩).2
    simp at this

/-- The fallback is irrelevant for legal generated rows, whose output is a singleton. -/
def rowValue (e : Entry) : Term := e.value.headD (.lit (.int 0))

def rowWeight (rank : Term → Nat) (e : Entry) : Nat := 5 ^ rank (rowValue e)

theorem rowWeight_pos (rank : Term → Nat) (e : Entry) : 0 < rowWeight rank e :=
  Nat.pow_pos (by decide)

/-- A finite sum extended to arbitrary sets by zero; proofs use it only on finite sets. -/
noncomputable def weightSum (rank : Term → Nat) (rows : Set Entry) : Nat := by
  classical
  exact if h : rows.Finite then ∑ e ∈ h.toFinset, rowWeight rank e else 0

theorem weightSum_eq {rank : Term → Nat} {rows : Set Entry} (h : rows.Finite) :
    weightSum rank rows = ∑ e ∈ h.toFinset, rowWeight rank e := by
  classical
  simp [weightSum, h]

theorem weightSum_insert_le (rank : Term → Nat) {rows : Set Entry}
    (h : rows.Finite) (e : Entry) :
    weightSum rank (insert e rows) ≤ weightSum rank rows + rowWeight rank e := by
  classical
  rw [weightSum_eq (h.insert e), weightSum_eq h]
  have hset : (h.insert e).toFinset = insert e h.toFinset := by ext; simp
  rw [hset]
  by_cases he : e ∈ h.toFinset
  · rw [Finset.insert_eq_of_mem he]
    omega
  · rw [Finset.sum_insert he]
    omega

theorem weightSum_erase_add (rank : Term → Nat) {rows : Set Entry}
    (h : rows.Finite) {e : Entry} (he : e ∈ rows) :
    weightSum rank (rows \ {e}) + rowWeight rank e = weightSum rank rows := by
  classical
  rw [weightSum_eq (h.subset Set.sdiff_subset), weightSum_eq h]
  have hset : (h.subset (Set.sdiff_subset : rows \ {e} ⊆ rows)).toFinset =
      h.toFinset.erase e := by ext; simp [and_comm]
  rw [hset]
  exact Finset.sum_erase_add _ _ (by simpa using he)

theorem weightSum_mono (rank : Term → Nat) {rows rows' : Set Entry}
    (h : rows'.Finite) (hsub : rows ⊆ rows') : weightSum rank rows ≤ weightSum rank rows' := by
  classical
  rw [weightSum_eq (h.subset hsub), weightSum_eq h]
  exact Finset.sum_le_sum_of_subset (by intro e he; simpa using hsub (by simpa using he))

/-- The total weight of current rows. -/
noncomputable def potential (rank : Term → Nat) (d : Database) : Nat :=
  weightSum rank d.entries

theorem pow_weight_gap {rank : Term → Nat} {a b : Term} (h : rank a < rank b) :
    5 * 5 ^ rank a ≤ 5 ^ rank b := by
  calc
    5 * 5 ^ rank a = 5 ^ (rank a + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ 5 ^ rank b := Nat.pow_le_pow_right (by decide) (by omega)

/-- The exact generated declaration and singleton output shape of a live row. -/
structure LegalRow (sig : Signature) (e : Entry) : Prop where
  declared : sig e.name = some (tableDecl e.key.length)
  output : ∃ a, e.value = [a]

/-- Generated table shape for the finite current store. -/
structure State (d : Database) : Prop where
  finite : d.FiniteStore
  uf : d.sig ufName = some (tableDecl 1)
  rows : ∀ e ∈ d.entries, LegalRow d.sig e
  typed : ∀ e ∈ d.entries, e.Valid d.sig

def OutputsIn (values : Set Term) (d : Database) : Prop :=
  ∀ e ∈ d.entries, ∀ a ∈ e.value, a ∈ values

def ufEntry (a b : Term) : Entry := ⟨ufName, [a], [b]⟩

theorem ufEntry_valid {sig : Signature} (huf : sig ufName = some (tableDecl 1))
    {a b : Term} (ha : a.IsValue sig) (hb : b.IsValue sig) :
    (ufEntry a b).Valid sig := by
  refine ⟨tableDecl 1, huf, by simp [tableDecl], rfl, rfl, ?_⟩
  simpa [ufEntry, Entry.columns] using And.intro ha hb

private theorem result_valid {sig : Signature} {row : Entry} {a b : Term} {vs : List Term}
    (hr : row.Valid sig) (ha : row.value = [a]) (hb : b.IsValue sig)
    (hvs : vs = [a] ∨ vs = [Term.least a b]) :
    (Entry.mk row.name row.key vs).Valid sig := by
  have hva := hr.output_values a (by simp [ha])
  apply hr.with_value
  · rcases hvs with rfl | rfl <;> simp [ha]
  · rcases hvs with rfl | rfl
    · simpa using hva
    · simpa using hva.least hb

/-- The generated merge body inserts two UF rows, both at the chosen minimum. -/
theorem eval_mergeBody {d : Database} (huf : d.sig ufName = some (tableDecl 1))
    (a b : Term) :
    evalActions { d with env := mergeEnv ["old"] ["new"] [a] [b] } mergeBody =
      some (Database.putEntry (ufEntry b (Term.least a b))
        (Database.putEntry (ufEntry a (Term.least a b))
          { d with env := mergeEnv ["old"] ["new"] [a] [b] })) := by
  simp [mergeBody, evalActions, evalAction, Expr.evalAtom, huf, tableDecl, FnDecl.entryWidth,
    Expr.evalList, Expr.eval, mergeEnv, Env.lookup, ufEntry, Entry.atom, Entry.columns,
    Database.putEntry]

/-- The generated merge writes both minimum links and returns the smaller id. -/
theorem eval_merge {d : Database} (huf : d.sig ufName = some (tableDecl 1))
    (a b : Term) :
    evalMerge { d with env := mergeEnv ["old"] ["new"] [a] [b] } mergeBody mergeResult =
      some (Database.putEntry (ufEntry b (Term.least a b))
        (Database.putEntry (ufEntry a (Term.least a b))
          { d with env := mergeEnv ["old"] ["new"] [a] [b] }), [Term.least a b]) := by
  apply evalMerge_eq_some.mpr
  refine ⟨eval_mergeBody huf a b, ?_⟩
  simp [mergeResult, Expr.evalList, Expr.eval, mergeEnv, Env.lookup,
    Database.putEntry, Database.addTerm]

theorem mergeValues_exists {d : Database} (huf : d.sig ufName = some (tableDecl 1))
    (k : Nat) (a b : Term) (_ha : a.IsValue d.sig) (_hb : b.IsValue d.sig) :
    ∃ e vs, MergeValues d (tableDecl k) [a] [b] e vs :=
  ⟨_, _, .eval rfl (eval_merge huf a b)⟩

theorem mergeValues_effects {d e : Database} (huf : d.sig ufName = some (tableDecl 1))
    {k : Nat} {a b : Term} {vs : List Term}
    (ha : a.IsValue d.sig) (hb : b.IsValue d.sig)
    (h : MergeValues d (tableDecl k) [a] [b] e vs) :
    e.sig = d.sig ∧ vs = [Term.least a b] ∧
      e.entries = insert (ufEntry b (Term.least a b))
        (insert (ufEntry a (Term.least a b)) d.entries) := by
  cases h with
  | eval hm he =>
    simp only [tableDecl, Option.some.injEq, MergeSpec.merge.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩
    rw [eval_merge huf a b] at he
    cases he
    refine ⟨rfl, rfl, ?_⟩
    let start : Database := { d with env := mergeEnv ["old"] ["new"] [a] [b] }
    change ((Database.putEntry (ufEntry b (Term.least a b))
      (Database.putEntry (ufEntry a (Term.least a b)) start))).entries = _
    rw [Database.putEntry_entries
        (d := start.putEntry (ufEntry a (Term.least a b)))
        (ufEntry_valid huf hb (ha.least hb)),
      Database.putEntry_entries (d := start) (ufEntry_valid huf ha (ha.least hb))]
    rfl

def mergeCost (rank : Term → Nat) (a b : Term) : Nat := 5 * 5 ^ rank (Term.least a b)

theorem mergeCost_lt (rank : Term → Nat) {a b : Term} (hne : a ≠ b)
    (hab : Term.blt a b = true → rank a < rank b)
    (hba : Term.blt b a = true → rank b < rank a) :
    mergeCost rank a b < 5 ^ rank a + 5 ^ rank b := by
  have hpa : 0 < 5 ^ rank a := Nat.pow_pos (by decide)
  have hpb : 0 < 5 ^ rank b := Nat.pow_pos (by decide)
  unfold mergeCost Term.least
  by_cases hlt : Term.blt b a = true
  · rw [if_pos hlt]
    have := pow_weight_gap (hba hlt)
    omega
  · rw [if_neg hlt]
    have := pow_weight_gap (hab ((Term.blt_total a b hne).resolve_right hlt))
    omega

theorem potential_erase_add (rank : Term → Nat) {d : Database} (hf : d.FiniteStore)
    {e : Entry} (he : e ∈ d.entries) (ht : e.Valid d.sig) :
    potential rank (d.eraseEntry e) + rowWeight rank e = potential rank d := by
  have := weightSum_erase_add rank hf.entries he
  simpa only [potential, Database.eraseEntry_entries ht] using this

/-- The result and two possible UF rows cost at most five minimum weights.
The loose bound is convenient for comparing against either strictly larger output. -/
theorem potential_merge_le (rank : Term → Nat) {d e : Database} (hf : d.FiniteStore)
    (huf : d.sig ufName = some (tableDecl 1)) {k : Nat} {a b : Term} {vs : List Term}
    (ha : a.IsValue d.sig) (hb : b.IsValue d.sig)
    (h : MergeValues d (tableDecl k) [a] [b] e vs) (f : FnName) (key : List Term)
    (hr : (Entry.mk f key vs).Valid e.sig) :
    potential rank (e.putEntry ⟨f, key, vs⟩) ≤ potential rank d + mergeCost rank a b := by
  obtain ⟨_, rfl, he⟩ := mergeValues_effects huf ha hb h
  have hu := weightSum_insert_le rank hf.entries (ufEntry a (Term.least a b))
  have hv := weightSum_insert_le rank
    (hf.entries.insert (ufEntry a (Term.least a b))) (ufEntry b (Term.least a b))
  have hi := weightSum_insert_le rank
    ((hf.entries.insert (ufEntry a (Term.least a b))).insert (ufEntry b (Term.least a b)))
    ⟨f, key, [Term.least a b]⟩
  simp only [potential, Database.putEntry_entries hr, he]
  simp only [rowWeight, rowValue, ufEntry, List.headD_cons] at hi hu hv
  simp only [mergeCost, ufEntry]
  omega

/-- Every actual generated merge strictly decreases the weighted live-store potential. -/
theorem potential_step_lt {values : Set Term} (hv : values.Finite)
    {d e : Database} (h : State d) (hdg : d.Diag) (hin : OutputsIn values d) (hs : MergeStep d e) :
    potential (valueRank values) e < potential (valueRank values) d := by
  obtain ⟨old, new, decl, mid, vs, ho, hn, hne, hname, hd, hkeys, hm, rfl⟩ := mergeStep_iff.mp hs
  have hold := h.rows old ho
  have hnew := h.rows new hn
  have hdecl : decl = tableDecl old.key.length := Option.some.inj (hd.symm.trans hold.declared)
  subst decl
  obtain ⟨a, ha⟩ := hold.output
  obtain ⟨b, hb⟩ := hnew.output
  have hab : a ≠ b := by
    intro hab
    have hk := CongList.eq_of_diag hdg hkeys
    apply hne
    cases old; cases new
    simp_all
  have hav := hin old ho a (by simp [ha])
  have hbv := hin new hn b (by simp [hb])
  have hva := (h.typed old ho).output_values a (by simp [ha])
  have hvb := (h.typed new hn).output_values b (by simp [hb])
  rw [ha, hb] at hm
  have hvs := (mergeValues_effects (d := (d.eraseEntry old).eraseEntry new)
    h.uf hva hvb hm).2
  have hresult := result_valid (h.typed old ho) ha hvb
    (Or.inr hvs.1)
  have hcost := potential_merge_le (valueRank values)
    ((h.finite.eraseEntry old).eraseEntry new) h.uf hva hvb hm old.name old.key
    (by simpa only [hm.sig, Database.eraseEntry_sig] using hresult)
  have he1 := potential_erase_add (valueRank values) h.finite ho (h.typed old ho)
  have he2 := potential_erase_add (valueRank values) (h.finite.eraseEntry old)
    (e := new) (by rw [Database.eraseEntry_entries (h.typed old ho)]
                   exact ⟨hn, by simpa using Ne.symm hne⟩)
    (h.typed new hn)
  have hlt := mergeCost_lt (valueRank values) hab
    (fun ht => valueRank_lt hv hav ht) (fun ht => valueRank_lt hv hbv ht)
  simp only [rowWeight, rowValue, ha, hb, List.headD_cons] at he1 he2
  omega

def AllRows (P : Entry → Prop) (d : Database) : Prop :=
  ∀ e ∈ d.entries, P e

theorem AllRows.eraseEntry {P : Entry → Prop} {d : Database} (h : AllRows P d)
    (e : Entry) (he : e.Valid d.sig) : AllRows P (d.eraseEntry e) := by
  intro row hr
  exact h row (Database.eraseEntry_entries_subset he hr)

theorem AllRows.putEntry {P : Entry → Prop} {d : Database} (h : AllRows P d)
    {e : Entry} (he : P e) (hv : e.Valid d.sig) : AllRows P (d.putEntry e) := by
  intro row hr
  simp only [Database.putEntry_entries hv, Set.mem_insert_iff] at hr
  rcases hr with rfl | hr
  · exact he
  · exact h row hr

theorem mergeValues_allRows {P : Entry → Prop} {d e : Database}
    (huf : d.sig ufName = some (tableDecl 1)) {k : Nat} {a b : Term} {vs : List Term}
    (hva : a.IsValue d.sig) (hvb : b.IsValue d.sig)
    (h : MergeValues d (tableDecl k) [a] [b] e vs) (hd : AllRows P d)
    (ha : P (ufEntry a (Term.least a b))) (hb : P (ufEntry b (Term.least a b))) :
    AllRows P e := by
  obtain ⟨_, _, hp⟩ := mergeValues_effects huf hva hvb h
  intro row hr
  change row ∈ e.entries at hr
  rw [hp] at hr
  rcases hr with rfl | rfl | hr
  · exact hb
  · exact ha
  · exact hd row hr

private theorem least_eq_or (a b : Term) : Term.least a b = a ∨ Term.least a b = b := by
  unfold Term.least
  split <;> simp

private theorem good_uf {sig : Signature} {values : Set Term}
    (huf : sig ufName = some (tableDecl 1)) (a : Term) {b : Term} (hb : b ∈ values) :
    LegalRow sig (ufEntry a b) ∧ ∀ v ∈ (ufEntry a b).value, v ∈ values := by
  refine ⟨⟨huf, ⟨b, rfl⟩⟩, ?_⟩
  intro v hv
  obtain rfl := List.mem_singleton.mp hv
  exact hb

private theorem good_result {sig : Signature} {values : Set Term} {old : Entry}
    (hold : LegalRow sig old) {a b : Term} {vs : List Term}
    (ha : a ∈ values) (hb : b ∈ values)
    (hvs : vs = [a] ∨ vs = [Term.least a b]) :
    LegalRow sig ⟨old.name, old.key, vs⟩ ∧ ∀ v ∈ vs, v ∈ values := by
  have hlo : Term.least a b ∈ values :=
    (least_eq_or a b).elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
  rcases hvs with rfl | rfl
  · exact ⟨⟨hold.declared, ⟨a, rfl⟩⟩, fun _ hv => (List.mem_singleton.mp hv) ▸ ha⟩
  · exact ⟨⟨hold.declared, ⟨_, rfl⟩⟩, fun _ hv => (List.mem_singleton.mp hv) ▸ hlo⟩

/-- Generated merging preserves legal rows and never invents a new output value. -/
theorem state_step {values : Set Term} {d e : Database} (h : State d)
    (hin : OutputsIn values d) (hs : MergeStep d e) : State e ∧ OutputsIn values e := by
  have hsig := hs.sig
  have hf := hs.finiteStore h.finite
  have hd : AllRows (fun row => row.Valid d.sig ∧ LegalRow d.sig row ∧
      ∀ v ∈ row.value, v ∈ values) d :=
    fun row hr => ⟨h.typed row hr, h.rows row hr, hin row hr⟩
  suffices hg : AllRows (fun row => row.Valid d.sig ∧ LegalRow d.sig row ∧
      ∀ v ∈ row.value, v ∈ values) e from
    ⟨⟨hf, hsig ▸ h.uf, fun row hr => hsig ▸ (hg row hr).2.1,
      fun row hr => hsig ▸ (hg row hr).1⟩, fun row hr => (hg row hr).2.2⟩
  obtain ⟨old, new, decl, mid, vs, ho, hn, _, _, hdcl, _, hm, rfl⟩ := mergeStep_iff.mp hs
  have hold := hd old ho
  have hnew := hd new hn
  have hdecl : decl = tableDecl old.key.length :=
    Option.some.inj (hdcl.symm.trans hold.2.1.declared)
  subst decl
  obtain ⟨a, ha⟩ := hold.2.1.output
  obtain ⟨b, hb⟩ := hnew.2.1.output
  have hav := hold.2.2 a (by simp [ha])
  have hbv := hnew.2.2 b (by simp [hb])
  have hva := hold.1.output_values a (by simp [ha])
  have hvb := hnew.1.output_values b (by simp [hb])
  have hlo : Term.least a b ∈ values :=
    (least_eq_or a b).elim (fun h => h.symm ▸ hav) (fun h => h.symm ▸ hbv)
  rw [ha, hb] at hm
  have hmrows := mergeValues_allRows (d := (d.eraseEntry old).eraseEntry new)
    h.uf hva hvb hm ((hd.eraseEntry old hold.1).eraseEntry new hnew.1)
    ⟨ufEntry_valid h.uf hva (hva.least hvb), good_uf h.uf a hlo⟩
    ⟨ufEntry_valid h.uf hvb (hva.least hvb), good_uf h.uf b hlo⟩
  have hvs := (mergeValues_effects (d := (d.eraseEntry old).eraseEntry new)
    h.uf hva hvb hm).2
  have hvres := result_valid hold.1 ha hvb
    (Or.inr hvs.1)
  apply hmrows.putEntry
  · exact ⟨hvres, good_result hold.2.1 hav hbv
      (Or.inr hvs.1)⟩
  · simpa only [hm.sig, Database.eraseEntry_sig] using hvres

/-- Every unfinished legal generated state has an actual merge successor. -/
theorem step_exists {d : Database} (h : State d) (hn : ¬ MergeNormal d) :
    ∃ e, MergeStep d e := by
  classical
  have hu : ¬ ∀ old ∈ d.entries, ∀ new ∈ d.entries,
      old.name = new.name → CongList d old.key new.key → old = new := hn
  push Not at hu
  obtain ⟨old, ho, new, hnew, hname, hkeys, hne⟩ := hu
  have hold := h.rows old ho
  have hnrow := h.rows new hnew
  obtain ⟨a, ha⟩ := hold.output
  obtain ⟨b, hb⟩ := hnrow.output
  obtain ⟨mid, vs, hm⟩ := mergeValues_exists
    (d := (d.eraseEntry old).eraseEntry new) h.uf old.key.length a b
    ((h.typed old ho).output_values a (by simp [ha]))
    ((h.typed new hnew).output_values b (by simp [hb]))
  rw [← ha, ← hb] at hm
  exact ⟨_, .collide' ho hnew hne hname hold.declared hkeys hm⟩

theorem state_closure {values : Set Term} {d e : Database} (h : State d)
    (hin : OutputsIn values d) (hs : MergeClosure d e) : State e ∧ OutputsIn values e := by
  induction hs with
  | refl => exact ⟨h, hin⟩
  | tail _ hstep ih => exact state_step ih.1 ih.2 hstep

/-- The initial output universe is finite even when constructor values are unbounded globally. -/
def outputValues (d : Database) : Set Term :=
  ⋃ row ∈ d.entries, {v | v ∈ row.value}

theorem outputValues_finite {d : Database} (h : d.FiniteStore) : (outputValues d).Finite :=
  h.entries.biUnion fun row _ => List.finite_toSet row.value

theorem outputsIn_self (d : Database) : OutputsIn (outputValues d) d :=
  fun row hr _ hv => Set.mem_iUnion₂.mpr ⟨row, hr, hv⟩

theorem mergeStep_diag {d e : Database} (h : State d) (hd : d.Diag)
    (hs : MergeStep d e) : e.Diag := by
  obtain ⟨_, _, _, _, _, ho, _, _, _, hdecl, _, hm, rfl⟩ := mergeStep_iff.mp hs
  have he := Option.some.inj (hdecl.symm.trans (h.rows _ ho).declared)
  subst he
  apply (hm.diag ?_ ((hd.eraseEntry _).eraseEntry _)).putEntry
  simp [FnDecl.UnionFree, tableDecl, mergeBody, Action.UnionFree]

theorem mergeClosure_diag {d e : Database} (h : State d) (hd : d.Diag)
    (hs : MergeClosure d e) : e.Diag := by
  induction hs with
  | refl => exact hd
  | tail hp hs ih =>
    exact mergeStep_diag (state_closure h (outputsIn_self d) hp).1 ih hs

/-- All actual merge schedules from a finite legal generated state decrease a natural
potential. This excludes infinite destructive-merge schedules, not only cycles in equations. -/
theorem merge_wellFounded {d : Database} (h : State d) (hd : d.Diag) :
    WellFounded (fun e' e => MergeClosure d e ∧ MergeStep e e') := by
  apply (measure (potential (valueRank (outputValues d)))).wf.mono
  intro e' e hs
  have he := state_closure h (outputsIn_self d) hs.1
  exact potential_step_lt (outputValues_finite h.finite) he.1
    (mergeClosure_diag h hd hs.1) he.2 hs.2

/-- Generated minimum merges always normalize. Row legality and finiteness are concrete
state invariants; there is no assumed progress or termination premise in this theorem. -/
theorem normalize_exists {d : Database} (h : State d) (hd : d.Diag) : ∃ e, MergeNormalize d e := by
  apply mergeNormalize_exists_of_measure d (potential (valueRank (outputValues d)))
  intro e he hn
  have hs := state_closure h (outputsIn_self d) he
  obtain ⟨e', hstep⟩ := step_exists hs.1 hn
  exact ⟨e', hstep, potential_step_lt (outputValues_finite h.finite) hs.1
    (mergeClosure_diag h hd he) hs.2 hstep⟩

end Egglog.Congruence.Live
