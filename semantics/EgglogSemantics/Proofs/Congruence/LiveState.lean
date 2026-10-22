import EgglogSemantics.Proofs.Congruence.LiveNormalization
import EgglogSemantics.Proofs.StatePreservation

/-! The checked row view derives generated-row shape directly from declarations. -/

namespace Egglog.Congruence.Live

/-- Every function declaration uses the generated minimum merge; constructors are unrestricted. -/
def GeneratedTables (sig : Signature) : Prop :=
  ∀ f decl, sig f = some decl → decl.merge ≠ none → ∃ k, decl = tableDecl k

theorem State.of_generated {d : Database} (hf : d.FiniteStore)
    (huf : d.sig ufName = some (tableDecl 1)) (hg : GeneratedTables d.sig)
    (ht : ∀ row ∈ d.entries, row.Valid d.sig) : State d := by
  refine ⟨hf, huf, ?_, ht⟩
  intro row hr
  obtain ⟨decl, hd, hm, hk, hv⟩ := hr.1
  obtain ⟨k, rfl⟩ := hg row.name decl hd hm
  have hkey : row.key.length = k := hk
  refine ⟨by simpa [hkey] using hd, ?_⟩
  have hlen : row.value.length = 1 := hv
  cases he : row.value with
  | nil => simp [he] at hlen
  | cons v rest =>
    have hrest : rest = [] := by simpa [he] using hlen
    exact ⟨v, by simp [hrest]⟩

theorem State.setEnv {d : Database} (h : State d) (env : Env) :
    State { d with env } := ⟨h.finite.setEnv env, h.uf, h.rows, h.typed⟩

theorem State.addTerm {d : Database} (h : State d) {t : Term}
    (hv : t.IsValue d.sig) : State (d.addTerm t) := by
  refine ⟨h.finite.addTerm t, h.uf, ?_, ?_⟩
  · simpa only [Database.addTerm_entries hv, Database.addTerm_sig] using h.rows
  · simpa only [Database.addTerm_entries hv, Database.addTerm_sig] using h.typed

theorem State.addEq {d : Database} (h : State d) {a b : Term}
    (ha : a.IsValue d.sig) (hb : b.IsValue d.sig) : State (d.addEq a b) := by
  refine ⟨h.finite.addEq a b, by simpa using h.uf, ?_, ?_⟩
  · simpa only [Database.addEq_entries ha hb, Database.addEq_sig] using h.rows
  · simpa only [Database.addEq_entries ha hb, Database.addEq_sig] using h.typed

theorem State.putEntry {d : Database} (h : State d) {row : Entry}
    (hr : LegalRow d.sig row) (hv : row.Valid d.sig) : State (d.putEntry row) := by
  refine ⟨h.finite.putEntry row, by simpa using h.uf, ?_, ?_⟩
  · intro e he
    simp only [Database.putEntry_entries hv, Set.mem_insert_iff] at he
    exact he.elim (fun he => he ▸ hr) (h.rows e)
  · intro e he
    simp only [Database.putEntry_entries hv, Set.mem_insert_iff] at he
    exact he.elim (fun he => he ▸ hv) (h.typed e)

/-- Successful actions preserve finite generated states and flat rows. -/
theorem State.evalAction {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hs : d.StoreOk) {a : Action} (he : evalAction d a = some e) : State e := by
  apply State.of_generated (evalAction_finiteStore h.finite he)
  · simpa only [evalAction_sig he] using h.uf
  · simpa only [evalAction_sig he] using hg
  · exact fun _ hr => (evalAction_storeOk hs he).entry_valid hr

theorem State.evalActions {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hs : d.StoreOk) {as : List Action} (he : evalActions d as = some e) : State e := by
  apply State.of_generated (evalActions_finiteStore h.finite he)
  · simpa only [evalActions_sig he] using h.uf
  · simpa only [evalActions_sig he] using hg
  · exact fun _ hr => (evalActions_storeOk hs he).entry_valid hr

theorem State.evalLocalActions {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hs : d.StoreOk) {as : List Action} {env : Env}
    (hv : ∀ b ∈ env, b.2.IsValue d.sig) (he : evalLocalActions d as env = some e) : State e := by
  apply State.of_generated (evalLocalActions_finiteStore h.finite he)
  · simpa only [evalLocalActions_sig he] using h.uf
  · simpa only [evalLocalActions_sig he] using hg
  · exact fun _ hr => (evalLocalActions_storeOk hs hv he).entry_valid hr

theorem State.runRules {d : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hs : d.StoreOk) (hq : d.RulesSafe) (R : RulesetName) : State (RunRules R d) :=
  State.of_generated (RunRules.finiteStore h.finite R) h.uf hg
    (fun _ hr => (RunRules.storeOk hs hq).entry_valid hr)

/-- A completed round always exists for a finite generated state. -/
theorem State.runStep_exists {d : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hs : d.StoreOk) (hq : d.RulesSafe) (hn : d.NoUnions) (R : RulesetName) :
    ∃ e, RunStep R d e :=
  normalize_exists (h.runRules hg hs hq R) (RunRules.diag hn)

theorem State.runStep {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hs : d.StoreOk) (hq : d.RulesSafe) {R : RulesetName} (hr : RunStep R d e) : State e :=
  (state_closure (h.runRules hg hs hq R) (outputsIn_self _) hr.1).1

end Egglog.Congruence.Live
