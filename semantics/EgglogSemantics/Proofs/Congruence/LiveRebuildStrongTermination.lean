import EgglogSemantics.Proofs.Congruence.LiveRebuildTermination
import Mathlib.Order.WellFounded

/-! Every completed rebuilding schedule reaches its first unchanged round. -/

namespace Egglog.Congruence.Live

/-- Changing completed rounds are well founded throughout a finite reachable store universe. -/
theorem rounds_wellFounded_of_finite_bound {d : Database} (h : Runtime d)
    (hn : MergeNormal d) (R : RulesetName) {bound : Set (Term × Term)}
    (hb : bound.Finite)
    (hbound : ∀ e, Relation.ReflTransGen (RunStep R) d e → e.eqs ⊆ bound) :
    WellFounded (fun e' e => Relation.ReflTransGen (RunStep R) d e ∧
      RunStep R e e' ∧ ¬ e.SameMeaning e') := by
  classical
  let states : Set Database := {e | Relation.ReflTransGen (RunStep R) d e}
  have hfinite : states.Finite := by
    apply (hb.finite_subsets.image (fun E => { d with eqs := E })).subset
    intro e he
    refine ⟨e.eqs, hbound e he, ?_⟩
    exact Database.ext (RunReach.sig he).symm rfl (RunReach.env he).symm
      (runReach_rules he).symm
  let below (e : Database) : Set Database := {s | s ∈ states ∧ Advances s e}
  have hbelow (e : Database) : (below e).Finite := hfinite.subset (fun _ hs => hs.1)
  have hnormal : ∀ e ∈ states, MergeNormal e := by
    intro e he
    induction he with
    | refl => exact hn
    | tail _ hs _ => exact hs.normal
  apply (measure (fun e => states.ncard - (below e).ncard)).wf.mono
  rintro e' e ⟨he, hs, hchange⟩
  have he' : e' ∈ states := he.tail hs
  have hadv := Advances.runStep (h.runReach he) hs
  have hss : below e ⊂ below e' := by
    refine ⟨fun s hse => ⟨hse.1, hse.2.trans hadv⟩, ?_⟩
    intro hback
    have hreverse := (hback ⟨he', Advances.refl e'⟩).2
    have heq := hadv.antisymm hreverse (h.runReach he) (h.runReach he')
      (hnormal e he) (hnormal e' he')
    exact hchange (heq ▸ Database.SameMeaning.refl e)
  have hlt := Set.ncard_lt_ncard hss (hbelow e')
  have hle := Set.ncard_le_ncard (show below e' ⊆ states from fun _ hs => hs.1) hfinite
  change states.ncard - (below e').ncard < states.ncard - (below e).ncard
  omega

/-- Every completed-round trace meets the operational saturation stopping condition. -/
theorem round_trace_stops_of_finite_bound {d : Database} (h : Runtime d)
    (hn : MergeNormal d) (R : RulesetName) {bound : Set (Term × Term)}
    (hb : bound.Finite)
    (hbound : ∀ e, Relation.ReflTransGen (RunStep R) d e → e.eqs ⊆ bound)
    (trace : Nat → Database) (hstart : trace 0 = d)
    (hstep : ∀ n, RunStep R (trace n) (trace (n + 1))) :
    ∃ n, (trace n).SameMeaning (trace (n + 1)) := by
  classical
  by_contra hstop
  have hreach : ∀ n, Relation.ReflTransGen (RunStep R) d (trace n) := by
    intro n
    induction n with
    | zero => rw [hstart]
    | succ n ih => exact ih.tail (hstep n)
  have hchain := wellFounded_iff_isEmpty_descending_chain.mp
    (rounds_wellFounded_of_finite_bound h hn R hb hbound)
  exact hchain.false ⟨trace, fun n => ⟨hreach n, hstep n,
    fun he => hstop ⟨n, he⟩⟩⟩

/-- A trace that has an unchanged round contains an actual finite saturation execution. -/
theorem round_trace_saturates {R : RulesetName} (trace : Nat → Database)
    (hstep : ∀ n, RunStep R (trace n) (trace (n + 1)))
    (hstop : ∃ n, (trace n).SameMeaning (trace (n + 1))) :
    ∃ n, SaturateReach R (trace 0) (trace (n + 1)) := by
  classical
  have hfirst : ∀ (n : Nat) (trace : Nat → Database),
      (∀ k, RunStep R (trace k) (trace (k + 1))) →
      (∀ k < n, ¬ (trace k).SameMeaning (trace (k + 1))) →
      (trace n).SameMeaning (trace (n + 1)) →
      SaturateReach R (trace 0) (trace (n + 1)) := by
    intro n
    induction n with
    | zero => intro trace hs _ he; exact .done (hs 0) he
    | succ n ih =>
        intro trace hs hn he
        exact .step (hs 0) (hn 0 (by omega))
          (ih (fun k => trace (k + 1)) (fun k => hs (k + 1))
            (fun k hk => hn (k + 1) (by omega)) he)
  exact ⟨Nat.find hstop, hfirst _ trace hstep
    (fun _ hk => Nat.find_min hstop hk) (Nat.find_spec hstop)⟩

/-- All generated rebuilding schedules make well-founded progress between changed rounds. -/
theorem rebuild_rounds_wellFounded {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    WellFounded (fun e' e => Relation.ReflTransGen (RunStep rebuildRuleset) d e ∧
      RunStep rebuildRuleset e e' ∧ ¬ e.SameMeaning e') := by
  have hv : d.values.Finite :=
    (Database.finite_terms h.state.finite.eqs).subset (fun _ ht => ht.1)
  have hb := hv.union (atomsOver_finite P hv)
  apply rounds_wellFounded_of_finite_bound h hn rebuildRuleset (hb.prod hb)
  intro e he
  exact eqs_bound_of_values hp (h.runReach he) ((RunReach.sig he).trans hsig)
    (maintenance_runReach_values_subset hp h hsig honly he)

/-- Any choice of completed rebuilding rounds reaches an unchanged round. -/
theorem rebuild_trace_stops {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (trace : Nat → Database) (hstart : trace 0 = d)
    (hstep : ∀ n, RunStep rebuildRuleset (trace n) (trace (n + 1))) :
    ∃ n, (trace n).SameMeaning (trace (n + 1)) := by
  have hv : d.values.Finite :=
    (Database.finite_terms h.state.finite.eqs).subset (fun _ ht => ht.1)
  have hb := hv.union (atomsOver_finite P hv)
  apply round_trace_stops_of_finite_bound h hn rebuildRuleset (hb.prod hb) ?_
    trace hstart hstep
  intro e he
  exact eqs_bound_of_values hp (h.runReach he) ((RunReach.sig he).trans hsig)
    (maintenance_runReach_values_subset hp h hsig honly he)

/-- Saturation follows a finite prefix of every supplied completed-round schedule. -/
theorem rebuild_trace_saturates {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (trace : Nat → Database) (hstart : trace 0 = d)
    (hstep : ∀ n, RunStep rebuildRuleset (trace n) (trace (n + 1))) :
    ∃ n, SaturateReach rebuildRuleset d (trace (n + 1)) := by
  obtain ⟨n, hn⟩ := round_trace_saturates trace hstep
    (rebuild_trace_stops hp h hn hsig honly trace hstart hstep)
  exact ⟨n, hstart ▸ hn⟩

/-- Both stages terminate for every choice of merges. `RunRules` is an atomic operation
in these relations; this does not specify an interleaved rule-firing machine. -/
theorem rebuild_phases_wellFounded {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    WellFounded (fun e' e => Relation.ReflTransGen (RunStep rebuildRuleset) d e ∧
      RunStep rebuildRuleset e e' ∧ ¬ e.SameMeaning e') ∧
    ∀ mid, Relation.ReflTransGen (RunStep rebuildRuleset) d mid →
      WellFounded (fun e' e => MergeClosure (RunRules rebuildRuleset mid) e ∧
        MergeStep e e') := by
  exact ⟨rebuild_rounds_wellFounded hp h hn hsig honly,
    fun _ hr => merge_wellFounded ((h.runReach hr).runRules rebuildRuleset).state
      ((h.runReach hr).runRules rebuildRuleset).noUnions.diag⟩

end Egglog.Congruence.Live
