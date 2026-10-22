import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Proofs.Step
import Mathlib.Order.WellFounded

namespace Egglog

theorem InfiniteTrace.reachable {rel : Database → Database → Prop} {d : Database}
    {trace : Nat → Database} (hstart : trace 0 = d)
    (hstep : ∀ n, rel (trace n) (trace (n + 1))) :
    ∀ n, Relation.ReflTransGen rel d (trace n) := by
  intro n
  induction n with
  | zero => rw [hstart]
  | succ n ih => exact ih.tail (hstep n)

theorem not_infiniteTrace_of_wellFounded {rel : Database → Database → Prop} {d : Database}
    (hw : WellFounded (fun e' e => Relation.ReflTransGen rel d e ∧ rel e e')) :
    ¬ InfiniteTrace rel d := by
  rintro ⟨trace, hstart, hstep⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp hw).false
    ⟨trace, fun n => ⟨InfiniteTrace.reachable hstart hstep n, hstep n⟩⟩

theorem changingRunStep_iff {R : List Rule} {db db' : Database} :
    ChangingRun R db db' ↔ db' = RunRules R db ∧ ¬ db.SameMeaning db' := by
  constructor
  · rintro ⟨rfl, hn⟩
    exact ⟨rfl, fun h => hn (funext fun a => funext fun b => propext (h.congr a b))⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨rfl, fun he => hn ⟨fun a b => by rw [he]⟩⟩

theorem changingRunReach_runReach {R : List Rule} {d e : Database}
    (h : Relation.ReflTransGen (ChangingRun R) d e) :
    Relation.ReflTransGen (fun a b => b = RunRules R a) d e :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.1) _ _ h

theorem not_saturateDiverges_of_wellFounded {R : List Rule} {d : Database}
    (hrounds : WellFounded (fun e' e =>
      Relation.ReflTransGen (fun a b => b = RunRules R a) d e ∧
      e' = RunRules R e ∧ ¬ e.SameMeaning e')) : ¬ SaturateDiverges R d := by
  apply not_infiniteTrace_of_wellFounded
  exact hrounds.mono (fun _ _ h => ⟨changingRunReach_runReach h.1, changingRunStep_iff.mp h.2⟩)

theorem ProgramDiverges.append_iff {p q : List Cmd} {d : Database} :
    ProgramDiverges d (p ++ q) ↔
      ProgramDiverges d p ∨ ∃ mid, ProgramStep d p mid ∧ ProgramDiverges mid q := by
  induction p generalizing d with
  | nil =>
      constructor
      · exact fun h => Or.inr ⟨d, .nil, h⟩
      · rintro (h | ⟨mid, hm, h⟩)
        · cases h
        · obtain rfl := hm.nil_inv; exact h
  | cons c cs ih =>
      constructor
      · intro h
        cases h with
        | head hc => exact Or.inl (.head hc)
        | tail hc hs =>
            rcases ih.mp hs with hs | ⟨mid, hm, htail⟩
            · exact Or.inl (.tail hc hs)
            · exact Or.inr ⟨mid, .cons hc hm, htail⟩
      · rintro (h | ⟨mid, hm, h⟩)
        · cases h with
          | head hc => exact .head hc
          | tail hc hs => exact .tail hc (ih.mpr (Or.inl hs))
        · obtain ⟨next, hc, ht⟩ := hm.cons_inv
          exact .tail hc (ih.mpr (Or.inr ⟨mid, ht, h⟩))

theorem not_cmdDiverges_of_allConstructors {d : Database} {c : Cmd}
    (hn : c.NoSaturate) : ¬ CmdDiverges d c := by
  intro h
  cases h with | saturate _ => exact hn.elim

/-- Bounded programs cannot diverge. -/
theorem not_programDiverges_of_allConstructors {d : Database} {P : Program}
    (hn : P.NoSaturate) : ¬ ProgramDiverges d P.commands := by
  have aux : ∀ {cs : List Cmd}, (∀ c ∈ cs, c.NoSaturate) →
      ¬ ProgramDiverges d cs := by
    intro cs hn h
    induction h with
    | head h => exact not_cmdDiverges_of_allConstructors (hn _ List.mem_cons_self) h
    | tail _ _ ih => exact ih (fun c hc => hn c (List.mem_cons_of_mem _ hc))
  exact aux hn

end Egglog
