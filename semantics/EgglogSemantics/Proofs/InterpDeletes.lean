import EgglogSemantics.Proofs.NoUnions
import EgglogSemantics.Proofs.Deletes
import EgglogSemantics.Proofs.Congruence.Properties

/-! Interpreter refinement for union-free programs, including deletes, disequality and `min`. -/

namespace Egglog

/-- Deleting rows preserves the index invariants: terms and index rows use the same
filter, including the same protection for nested rows. -/
theorem FDatabase.IndexOk.deleteAtoms {d : FDatabase} (hi : d.IndexOk)
    (cl : Finset (Term × Term)) (X : List Term) : (d.deleteAtoms cl X).IndexOk := by
  unfold FDatabase.deleteAtoms
  split
  · exact hi
  · constructor
    intro r hr
    obtain ⟨hr, hk⟩ := List.mem_filter.mp hr
    exact List.mem_filter.mpr ⟨hi.ctor r hr, hk⟩

theorem FDatabase.IndexCurrent.deleteAtoms {d : FDatabase} (hi : d.IndexCurrent)
    (cl : Finset (Term × Term)) (X : List Term) : (d.deleteAtoms cl X).IndexCurrent := by
  unfold FDatabase.deleteAtoms
  split
  · exact hi
  · intro f as ht
    obtain ⟨ht, hk⟩ := List.mem_filter.mp ht
    exact List.mem_filter.mpr ⟨hi f as ht, hk⟩

/-- The executable protects proper subterms of all pre-state terms. -/
theorem FDatabase.SubtermClosed.deleteAtoms {d : FDatabase} (hc : d.SubtermClosed)
    (cl : Finset (Term × Term)) (X : List Term) : (d.deleteAtoms cl X).SubtermClosed := by
  unfold FDatabase.deleteAtoms
  split
  · exact hc
  · intro t ht s hs
    obtain ⟨ht, hk⟩ := List.mem_filter.mp ht
    by_cases heq : s = t
    · subst s
      exact List.mem_filter.mpr ⟨ht, hk⟩
    · apply List.mem_filter.mpr
      refine ⟨hc t ht s hs, ?_⟩
      have hp : (d.terms.any fun u => u != s && decide (s ∈ u.subtermList)) = true := by
        simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
        exact ⟨t, ht, Ne.symm heq, hs⟩
      simp only [hp, Bool.not_true, Bool.and_false, Bool.false_and, Bool.not_false]

/-- Empty raw equations are stable through deletion and avoid dangling reflexive pairs. -/
theorem FDatabase.closed_deleteAtoms_of_eqs_empty {d : FDatabase} (hc : d.SubtermClosed)
    (he : d.eqs = []) (cl : Finset (Term × Term)) (X : List Term) :
    (d.deleteAtoms cl X).Closed := by
  refine ⟨?_, hc.deleteAtoms cl X⟩
  unfold FDatabase.deleteAtoms
  split <;> simp [he]

private theorem congrTuple_eq_of_diag {d : FDatabase} (hc : d.SubtermClosed)
    (hd : d.EqsRefl) {as bs : List Term}
    (h : FDatabase.congrTuple d.closureF as bs = true) : as = bs := by
  apply CongList.eq_of_diag hd.toDatabase
  apply CongList.forall₂.mpr
  simp only [FDatabase.congrTuple, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, decide_eq_true_eq] at h
  exact List.forall₂_iff_zip.mpr ⟨h.1, fun hp => FDatabase.mem_closureF_imp hc (h.2 _ hp)⟩

/-- In diagonal finite stores, row matching is structural identity, with no literal rows. -/
theorem FDatabase.sameRow_iff_of_diag {d : FDatabase} (hc : d.SubtermClosed)
    (hd : d.EqsRefl) {s t : Term} (hs : s ∈ d.terms) :
    sameRow d.closureF s t = true ↔ s = t ∧ s.isLit = false := by
  cases s with
  | lit l => simp [sameRow, Term.isLit]
  | app f as =>
    cases t with
    | lit l => simp [sameRow]
    | app g bs =>
      simp only [sameRow, Bool.and_eq_true, beq_iff_eq, Term.app.injEq, Term.isLit,
        and_true]
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, congrTuple_eq_of_diag hc hd h⟩
      · rintro ⟨rfl, rfl⟩
        have ha : ∀ a ∈ as, a ∈ d.terms := fun a ha =>
          hc _ hs a (Term.mem_subtermList_of_isSubterm (.arg ha (.refl _)))
        exact ⟨rfl, (congrTuple_iff hc ha ha).mpr (CongList.refl
          (fun a ha' => (mem_toDatabase_terms hc).mpr (ha a ha')))⟩

/-- The executable deletion has the same term census as diagonal specification deletion. -/
theorem FDatabase.mem_deleteAtoms_terms_of_diag {d : FDatabase} (hc : d.SubtermClosed)
    (hd : d.EqsRefl) (X : List Term) (s : Term) :
    s ∈ (d.deleteAtoms d.closureF X).terms ↔ s ∈ d.terms ∧
      (¬ (s ∈ X ∧ s.isLit = false) ∨ ∃ t ∈ d.terms, s ≠ t ∧ s ∈ t.subterms) := by
  classical
  unfold FDatabase.deleteAtoms
  split
  · rename_i hx
    have hx : X = [] := List.isEmpty_iff.mp hx
    simp [hx]
  · have he : (d.eqs.any fun p => p.1 != p.2 && (p.1 == s || p.2 == s)) = false := by
      apply Bool.eq_false_iff.mpr
      change ¬ (d.eqs.any fun p => p.1 != p.2 && (p.1 == s || p.2 == s)) = true
      simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne]
      rintro ⟨p, hp, hn, _⟩
      exact hn (hd p hp)
    simp only [List.mem_filter]
    apply and_congr_right
    intro hs
    have hr : X.any (sameRow d.closureF s) = true ↔ s ∈ X ∧ s.isLit = false := by
      simp only [List.any_eq_true, sameRow_iff_of_diag hc hd hs]
      constructor
      · rintro ⟨t, ht, rfl, hn⟩
        exact ⟨ht, hn⟩
      · rintro ⟨ht, hn⟩
        exact ⟨s, ht, rfl, hn⟩
    simp only [he, Bool.not_false, Bool.and_true, Bool.not_eq_true']
    rw [Bool.and_eq_false_iff]
    have hrf : X.any (sameRow d.closureF s) = false ↔ ¬ (s ∈ X ∧ s.isLit = false) := by
      rw [Bool.eq_false_iff]
      change (¬ X.any (sameRow d.closureF s) = true) ↔ _
      rw [hr]
    rw [hrf, Bool.not_eq_false']
    simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
      Term.mem_subtermList, Term.mem_subterms, ne_comm]


/-- Deletion agrees with the refined specification on every diagonal, subterm-closed
finite state, even if its raw equation list contains redundant reflexive pairs. -/
theorem FDatabase.toDatabase_deleteAtoms {d : FDatabase} (hc : d.SubtermClosed)
    (hd : d.EqsRefl) (X : List Term) :
    (d.deleteAtoms d.closureF X).toDatabase.SameMeaning
      (d.toDatabase.deleteRows {t | t ∈ X}) := by
  have hd' : (d.deleteAtoms d.closureF X).EqsRefl := by
    unfold FDatabase.deleteAtoms
    split <;> exact hd
  refine ⟨fun a b => ?_⟩
  rw [Cong.iff_eq_and_mem_of_diag hd'.toDatabase,
    Cong.iff_eq_and_mem_of_diag (hd.toDatabase.deleteRows _),
    mem_toDatabase_terms (hc.deleteAtoms _ _),
    Database.mem_deleteRows_terms_of_diag hd.toDatabase, toDatabase_terms hc,
    mem_deleteAtoms_terms_of_diag hc hd]
  rfl


/-- The same environment satisfies the same patterns in states of equal meaning,
including disequality and expressions using `min`. -/
theorem Database.SameMeaning.matches_iff {d e : Database} (h : d.SameMeaning e)
    (p : Pattern) (σ : Env) : Matches d p σ ↔ Matches e p σ := by
  have forward {d e : Database} (h : d.SameMeaning e) {p : Pattern} {σ : Env}
      (hm : Matches d p σ) : Matches e p σ := by
    cases hm with
    | atom ht hc => exact .atom ht ((h.congr _ _).mp hc)
    | equal ht hu hc => exact .equal ht hu ((h.congr _ _).mp hc)
    | unequal ht hu hc hd hn =>
      exact .unequal ht hu ((h.congr _ _).mp hc) ((h.congr _ _).mp hd)
        (fun he => hn ((h.congr _ _).mpr he))
  exact ⟨forward h, forward h.symm⟩

/-- On diagonal states the binding domains agree too, so no environment transport or
ordering-freedom premise is needed. -/
theorem Database.SameMeaning.queryMatches_iff_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag) (q : Query) (σ : Env) :
    QueryMatches d q σ ↔ QueryMatches e q σ := by
  simp only [QueryMatches, ValidEnv, h.terms_eq_of_diag hd he, h.matches_iff]

theorem Database.SameMeaning.queryHolds_iff_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag) (q : Query) :
    QueryHolds d q ↔ QueryHolds e q := by
  simp only [QueryHolds, h.queryMatches_iff_of_diag hd he]

/-- Round transport for diagonal pre-states allows every pattern and action, including
unions in the resulting state. -/
theorem Database.SameMeaning.runRules_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag) (R : List Rule) :
    (RunRules R d).SameMeaning (RunRules R e) := by
  have hw : RunWrites R d = RunWrites R e := by
    simp only [RunWrites, h.queryMatches_iff_of_diag hd he]
  have hx : RunErases R d = RunErases R e := by
    simp only [RunErases, h.queryMatches_iff_of_diag hd he]
  unfold RunRules
  rw [hw, hx]
  exact FDatabase.meaning_addEqs (h.deleteRows_of_diag hd he _) _

/-- Without raw equations, one round refines the specification for arbitrary rule heads.
Unions are permitted in this round; later rounds need fresh invariant proofs. -/
theorem execRunRules_RunRules_of_eqs_empty {R : List Rule} {d : FDatabase}
    (hc : d.SubtermClosed) (he : d.eqs = []) (hi : d.IndexOk) (hj : d.IndexCurrent) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R d.toDatabase) := by
  have hclosed : d.Closed := ⟨by simp [he], hc⟩
  have hd : d.EqsRefl := by simp [FDatabase.EqsRefl, he]
  have hb := FDatabase.closed_deleteAtoms_of_eqs_empty hc he d.closureF (roundDeletes R d)
  have hdel := FDatabase.toDatabase_deleteAtoms hc hd (roundDeletes R d)
  rw [roundDeletes_eq_RunErases hclosed hi hj] at hdel
  exact (execRunRules_deletes_writes hclosed hi hj hb).trans
    (FDatabase.meaning_addEqs hdel _)

/-- Union-free rounds refine deletion and writes without restricting `min` or disequality. -/
theorem execRunRules_RunRules_noUnions {R : List Rule} {d : FDatabase}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R d.toDatabase) :=
  execRunRules_RunRules_of_eqs_empty hc hn.eqs hi hj

/-- Deletion and writes preserve both directions of the row-index invariant. -/
theorem execRunRules_index_with_deletes {R : List Rule} {d : FDatabase}
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    (execRunRules R d).IndexOk ∧ (execRunRules R d).IndexCurrent :=
  execRunRules_index_of_deleteAtoms (hi.deleteAtoms _ _) (hj.deleteAtoms _ _)

theorem closed_execRunRules_noUnions {R : List Rule} {d : FDatabase}
    (hc : d.SubtermClosed) (hn : d.NoUnions) : (execRunRules R d).Closed :=
  closed_execRunRules_of_deleteAtoms
    (FDatabase.closed_deleteAtoms_of_eqs_empty hc hn.eqs _ _)


private structure UnionFreeInterpReady (d : FDatabase) : Prop where
  closed : d.Closed
  indexOk : d.IndexOk
  indexCurrent : d.IndexCurrent
  noUnions : d.NoUnions

private theorem UnionFreeInterpReady.of_invariants {d : FDatabase}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions) :
    UnionFreeInterpReady d := ⟨⟨by simp [hn.eqs], hc⟩, hi, hj, hn⟩

private theorem UnionFreeInterpReady.round {d : FDatabase} (h : UnionFreeInterpReady d)
    (R : List Rule) (hu : ∀ r ∈ R, r.UnionFree) : UnionFreeInterpReady (execRunRules R d) :=
  let hi := execRunRules_index_with_deletes (R := R) h.indexOk h.indexCurrent
  ⟨closed_execRunRules_noUnions h.closed.subterms h.noUnions, hi.1, hi.2,
    execRunRules_noUnions h.noUnions hu⟩

private theorem UnionFreeInterpReady.empty : UnionFreeInterpReady FDatabase.empty := by
  exact ⟨FDatabase.empty_closed, ⟨by simp [FDatabase.empty]⟩,
    by simp [FDatabase.IndexCurrent, FDatabase.empty], .empty⟩

private theorem UnionFreeInterpReady.iterate {d : FDatabase} (h : UnionFreeInterpReady d)
    (R : List Rule) (hu : ∀ r ∈ R, r.UnionFree) (k : Nat) :
    UnionFreeInterpReady ((execRunRules R)^[k] d) := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Function.iterate_succ_apply'] using ih.round R hu

private theorem UnionFreeInterpReady.saturate {R : List Rule} {n : Nat} {d e : FDatabase}
    (h : UnionFreeInterpReady d) (hu : ∀ r ∈ R, r.UnionFree) (hs : d.runSaturateF R n = some e) :
    UnionFreeInterpReady e := by
  obtain ⟨k, rfl⟩ := runSaturateF_iterate n hs
  exact h.iterate R hu k


private theorem UnionFreeInterpReady.cmd {d e : FDatabase} (h : UnionFreeInterpReady d)
    {c : Cmd} (hu : c.UnionFree) (he : execCmd d c = some e) : UnionFreeInterpReady e := by
  cases c with
  | run R => cases Option.some.inj he; exact h.round R hu
  | saturate R => exact h.saturate hu he

private theorem congr_eq_of_meaning {d e : Database} (h : d.SameMeaning e) :
    Cong d = Cong e := by
  funext a b
  exact propext (h.congr a b)

private theorem fixed_saturate_meaning {R : List Rule} {d e : Database}
    (hfix : d.SameMeaning (RunRules R d)) (h : SaturateReach R d e) : d.SameMeaning e := by
  cases h with
  | fixpoint => exact hfix
  | again hn _ => exact (hn (congr_eq_of_meaning hfix)).elim

private theorem round_transport_noUnions {d : FDatabase} {db : Database}
    (h : UnionFreeInterpReady d) (hn : db.NoUnions) (hh : d.toDatabase.SameMeaning db)
    (R : List Rule) : (execRunRules R d).toDatabase.SameMeaning (RunRules R db) :=
  (execRunRules_RunRules_noUnions h.closed.subterms h.indexOk h.indexCurrent h.noUnions).trans
    (hh.runRules_of_diag h.noUnions.toDatabase.diag hn.diag R)

private theorem settled_transport_noUnions {R : List Rule} {d : FDatabase} {db : Database}
    (h : UnionFreeInterpReady d) (hn : db.NoUnions) (hh : d.toDatabase.SameMeaning db)
    (hs : d.sameData (execRunRules R d) = true) :
    db.SameMeaning (RunRules R db) ∧ d.toDatabase.SameMeaning (RunRules R db) := by
  have hr := round_transport_noUnions h hn hh R
  simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at hs
  rw [toDatabase_eq_of_fields hs.1.1 hs.2] at hr
  exact ⟨hh.symm.trans hr, hr⟩

private theorem runSaturateF_transport_noUnions {R : List Rule}
    (hu : ∀ r ∈ R, r.UnionFree) : ∀ (n : Nat)
    {d e : FDatabase} {db : Database}, UnionFreeInterpReady d → db.NoUnions →
    d.toDatabase.SameMeaning db → d.runSaturateF R n = some e →
    ∃ out, SaturateReach R db out ∧ e.toDatabase.SameMeaning out := by
  intro n
  induction n with
  | zero =>
    intro d e db hd hn hh hs
    unfold FDatabase.runSaturateF at hs
    split at hs
    · rename_i hfixed
      cases Option.some.inj hs
      obtain ⟨hfix, hmean⟩ := settled_transport_noUnions hd hn hh hfixed
      exact ⟨_, .fixpoint (congr_eq_of_meaning hfix), hmean⟩
    · cases hs
  | succ n ih =>
    intro d e db hd hn hh hs
    unfold FDatabase.runSaturateF at hs
    split at hs
    · rename_i hfixed
      cases Option.some.inj hs
      obtain ⟨hfix, hmean⟩ := settled_transport_noUnions hd hn hh hfixed
      exact ⟨_, .fixpoint (congr_eq_of_meaning hfix), hmean⟩
    · obtain ⟨out, hout, hmean⟩ := ih (hd.round R hu) (RunRules.noUnions hn hu)
        (round_transport_noUnions hd hn hh R) hs
      by_cases hfix : Cong db = Cong (RunRules R db)
      · have hdb : db.SameMeaning (RunRules R db) := ⟨fun a b => by rw [hfix]⟩
        have hnext := hdb.runRules_of_diag hn.diag (RunRules.diag hn hu) R
        exact ⟨_, .fixpoint hfix, hmean.trans (fixed_saturate_meaning hnext hout).symm⟩
      · exact ⟨out, .again hfix hout, hmean⟩

/-- Successful finite saturation refines semantic saturation for union-free rules,
including deletes, disequality and `min`. Structural stopping may take redundant rounds. -/
theorem runSaturateF_saturateReach_noUnions {R : List Rule} {n : Nat} {d e : FDatabase}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions)
    (hu : ∀ r ∈ R, r.UnionFree) (hs : d.runSaturateF R n = some e) :
    ∃ out, SaturateReach R d.toDatabase out ∧ e.toDatabase.SameMeaning out :=
  runSaturateF_transport_noUnions hu n (.of_invariants hc hi hj hn) hn.toDatabase (.refl _) hs

private theorem iterate_transport_noUnions {R : List Rule}
    (hu : ∀ r ∈ R, r.UnionFree) : ∀ (k : Nat)
    {d : FDatabase} {db : Database}, UnionFreeInterpReady d → db.NoUnions →
    d.toDatabase.SameMeaning db →
    ((execRunRules R)^[k] d).toDatabase.SameMeaning ((RunRules R)^[k] db) := by
  intro k
  induction k with
  | zero => intro d db _ _ hh; exact hh
  | succ k ih =>
    intro d db h hn hh
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (h.round R hu) (RunRules.noUnions hn hu) (round_transport_noUnions h hn hh R)

/-- Any fixed number of union-free rounds agrees with the same specification iteration. -/
theorem execRunRules_iterate_noUnions {R : List Rule} (k : Nat) {d : FDatabase}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent)
    (hn : d.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) :
    ((execRunRules R)^[k] d).toDatabase.SameMeaning ((RunRules R)^[k] d.toDatabase) :=
  iterate_transport_noUnions hu k (.of_invariants hc hi hj hn) hn.toDatabase (.refl _)

private theorem execCmd_transport_noUnions {d e : FDatabase} {db : Database}
    (h : UnionFreeInterpReady d) (hn : db.NoUnions) (hh : d.toDatabase.SameMeaning db)
    {c : Cmd} (hu : c.UnionFree) (he : execCmd d c = some e) :
    ∃ out, CmdStep db c out ∧ e.toDatabase.SameMeaning out := by
  cases c with
  | run R => cases Option.some.inj he; exact ⟨_, rfl, round_transport_noUnions h hn hh R⟩
  | saturate R => exact runSaturateF_transport_noUnions hu _ h hn hh he

/-- A successful union-free command preserves its specification meaning. -/
theorem execCmd_cmdStep_noUnions {d e : FDatabase} (hc : d.SubtermClosed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions) {c : Cmd} (hu : c.UnionFree)
    (hs : execCmd d c = some e) :
    ∃ out, CmdStep d.toDatabase c out ∧ e.toDatabase.SameMeaning out :=
  execCmd_transport_noUnions (.of_invariants hc hi hj hn) hn.toDatabase (.refl _) hu hs

private theorem execProgram_transport_noUnions {p : List Cmd} :
    ∀ {d e : FDatabase} {db : Database}, UnionFreeInterpReady d → db.NoUnions →
    d.toDatabase.SameMeaning db → (∀ c ∈ p, c.UnionFree) → execProgram d p = some e →
    ∃ out, ProgramStep db p out ∧ e.toDatabase.SameMeaning out := by
  induction p with
  | nil =>
    intro d e db _ _ hh _ hs
    cases Option.some.inj hs
    exact ⟨db, .nil, hh⟩
  | cons c cs ih =>
    intro d e db hd hn hh hu hs
    obtain ⟨mid, hmid, hrest⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨out, hout, hmean⟩ := execCmd_transport_noUnions hd hn hh (hu c (by simp)) hmid
    obtain ⟨last, hlast, hmean'⟩ := ih (hd.cmd (hu c (by simp)) hmid)
      (hout.noUnions hn (hu c (by simp))) hmean (fun c hc => hu c (by simp [hc])) hrest
    exact ⟨last, .cons hout hlast, hmean'⟩

/-- Union-free executable programs refine the specification, without any monotonicity,
ordering, scoping or arity premises. Fuel exhaustion is excluded by successful execution. -/
theorem execProgram_programStep_noUnions {p : List Cmd} {d e : FDatabase}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions)
    (hu : (∀ c ∈ p, c.UnionFree)) (hs : execProgram d p = some e) :
    ∃ out, ProgramStep d.toDatabase p out ∧ e.toDatabase.SameMeaning out :=
  execProgram_transport_noUnions (.of_invariants hc hi hj hn) hn.toDatabase (.refl _) hu hs

/-- Every successful union-free execution from empty has a specification result with
exactly the same meaning, including programs using deletes, disequality and `min`. -/
theorem exec_programStep_noUnions {p : Program} {e : FDatabase}
    (hu : p.UnionFree) (hs : exec p = some e) :
    ∃ out, ProgramStep Database.empty p.commands out ∧ e.toDatabase.SameMeaning out := by
  have h := UnionFreeInterpReady.empty
  simpa only [FDatabase.toDatabase_empty] using
    execProgram_programStep_noUnions h.closed.subterms h.indexOk h.indexCurrent h.noUnions hu hs


/-- Closed finite stores remain closed throughout union-free iterations with deletion. -/
theorem closed_iterate_noUnions {R : List Rule} (hu : ∀ r ∈ R, r.UnionFree) :
    ∀ (k : Nat) {d : FDatabase},
    d.SubtermClosed → d.NoUnions → ((execRunRules R)^[k] d).Closed := by
  intro k
  induction k with
  | zero => intro d hc hn; exact ⟨by simp [hn.eqs], hc⟩
  | succ k ih =>
    intro d hc hn
    rw [Function.iterate_succ_apply]
    exact ih (closed_execRunRules_noUnions hc hn).subterms (execRunRules_noUnions hn hu)

theorem execCmd_closed_noUnions {d e : FDatabase} (hc : d.SubtermClosed) (hn : d.NoUnions)
    {c : Cmd} (hu : c.UnionFree) (hs : execCmd d c = some e) : e.Closed := by
  have he : d.Closed := ⟨by simp [hn.eqs], hc⟩
  cases c with
  | run R => cases Option.some.inj hs; exact closed_execRunRules_noUnions hc hn
  | saturate R =>
    obtain ⟨k, rfl⟩ := runSaturateF_iterate _ hs
    exact closed_iterate_noUnions hu k hc hn

/-- Closure is preserved by every successful union-free program, including deletes. -/
theorem execProgram_closed_noUnions {p : List Cmd} {d e : FDatabase}
    (hc : d.SubtermClosed) (hn : d.NoUnions) (hu : (∀ c ∈ p, c.UnionFree))
    (hs : execProgram d p = some e) : e.Closed := by
  induction p generalizing d with
  | nil => cases Option.some.inj hs; exact ⟨by simp [hn.eqs], hc⟩
  | cons c cs ih =>
    obtain ⟨mid, hm, ht⟩ := Option.bind_eq_some_iff.mp hs
    exact ih (execCmd_closed_noUnions hc hn (hu c (by simp)) hm).subterms
      (execCmd_noUnions (hu c (by simp)) hn hm) (fun c hc => hu c (by simp [hc])) ht

theorem exec_closed_noUnions {p : Program} {e : FDatabase}
    (hu : p.UnionFree) (hs : exec p = some e) : e.Closed :=
  execProgram_closed_noUnions FDatabase.empty_closed.subterms .empty hu hs

/-- Every nonsaturating command succeeds in both execution models. -/
theorem execCmd_success_iff_of_noSaturate {d : FDatabase} {c : Cmd} (hns : c.NoSaturate) :
    (execCmd d c).isSome = true ↔ ∃ out, CmdStep d.toDatabase c out :=
  execCmd_toDatabase hns

private theorem execCmd_exists_noUnions {d : FDatabase} {c : Cmd} (hns : c.NoSaturate) :
    ∃ e, execCmd d c = some e := by
  cases c with
  | run R => exact ⟨_, rfl⟩
  | saturate R => cases hns

private theorem execProgram_complete_transport_noUnions {p : List Cmd} :
    ∀ {d : FDatabase} {db out : Database}, UnionFreeInterpReady d → db.NoUnions →
    d.toDatabase.SameMeaning db → (∀ c ∈ p, c.UnionFree) →
    (∀ c ∈ p, c.NoSaturate) → ProgramStep db p out →
    ∃ e, execProgram d p = some e ∧ e.toDatabase.SameMeaning out := by
  induction p with
  | nil =>
    intro d db out _ _ hh _ _ hs
    cases hs
    exact ⟨d, rfl, hh⟩
  | cons c cs ih =>
    intro d db out h hn hh hu hns hs
    cases hs with
    | @cons _ mid _ _ _ hc hrest =>
      obtain ⟨e, he⟩ := execCmd_exists_noUnions (d := d) (hns c (by simp))
      obtain ⟨mid', hmid', hmean⟩ := execCmd_transport_noUnions h hn hh (hu c (by simp)) he
      have heq : mid' = mid := CmdStep.det hmid' hc
      subst mid'
      obtain ⟨last, hlast, hmean'⟩ := ih (h.cmd (hu c (by simp)) he)
        (hc.noUnions hn (hu c (by simp)))
        hmean (fun c hc => hu c (by simp [hc])) (fun c hc => hns c (by simp [hc])) hrest
      exact ⟨last, by simp [execProgram, he, hlast], hmean'⟩

/-- Every successful nonsaturating union-free specification program has an executable
result of the same meaning. Deletes, disequality and `min` require no extra premises. -/
theorem execProgram_complete_noUnions {p : List Cmd} {d : FDatabase} {out : Database}
    (hc : d.SubtermClosed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hn : d.NoUnions)
    (hu : ∀ c ∈ p, c.UnionFree) (hns : ∀ c ∈ p, c.NoSaturate)
    (hs : ProgramStep d.toDatabase p out) :
    ∃ e, execProgram d p = some e ∧ e.toDatabase.SameMeaning out :=
  execProgram_complete_transport_noUnions (.of_invariants hc hi hj hn) hn.toDatabase
    (.refl _) hu hns hs

theorem exec_complete_noUnions {p : Program} {out : Database}
    (hu : p.UnionFree) (hns : p.NoSaturate) (hs : ProgramStep Database.empty p.commands out) :
    ∃ e, exec p = some e ∧ e.toDatabase.SameMeaning out := by
  have h := UnionFreeInterpReady.empty
  exact execProgram_complete_noUnions h.closed.subterms h.indexOk h.indexCurrent h.noUnions
    hu hns (by simpa only [FDatabase.toDatabase_empty] using hs)

/-- The constructor-and-delete compiler always produces a union-free program, so every
successful reference-interpreter execution refines that compiled program's specification.
This does not assert equivalence with the source program. -/
theorem Congruence.exec_encode_programStep {p : Program} {e : FDatabase}
    (hs : exec (Congruence.encode p) = some e) :
    ∃ out, ProgramStep Database.empty (Congruence.encode p).commands out ∧
      e.toDatabase.SameMeaning out :=
  exec_programStep_noUnions (Congruence.encode_unionFree p) hs

private theorem UnionFreeInterpReady.program {cs : List Cmd} {d e : FDatabase}
    (hd : UnionFreeInterpReady d) (hu : ∀ c ∈ cs, c.UnionFree)
    (hs : execProgram d cs = some e) : UnionFreeInterpReady e := by
  induction cs generalizing d with
  | nil => cases Option.some.inj hs; exact hd
  | cons c cs ih =>
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp hs
    exact ih (hd.cmd (hu c (by simp)) hc) (fun c hc => hu c (by simp [hc])) ht

/-- Union-free command execution also agrees on its final check, including disequality. -/
theorem exec_programStep_check_noUnions {p : Program} {e : FDatabase}
    (hu : p.UnionFree) (hs : exec p = some e) :
    ∃ out, ProgramStep Database.empty p.commands out ∧ e.toDatabase.SameMeaning out ∧
      (e.holds p.check = true ↔ QueryHolds out p.check) := by
  obtain ⟨out, hout, hm⟩ := exec_programStep_noUnions hu hs
  have he := UnionFreeInterpReady.empty.program hu hs
  exact ⟨out, hout, hm, (FDatabase.holds_iff_queryHolds he.closed he.indexOk
    he.indexCurrent p.check).trans (hm.queryHolds_iff_of_diag he.noUnions.toDatabase.diag
      (hout.noUnions Database.NoUnions.empty hu).diag p.check)⟩

/-- The observer refines both finite outcomes for arbitrary union-free programs. -/
theorem observe_eval_noUnions {p : Program} {r : ExecutionResult}
    (hu : p.UnionFree) (hs : observe p = some r) :
    ∃ result, Eval Database.empty p result ∧ result.succeeded = r.succeeded := by
  apply observe_eval_of_exec ?_ hs
  intro e he
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check_noUnions hu he
  exact ⟨out, hout, hq⟩

end Egglog
