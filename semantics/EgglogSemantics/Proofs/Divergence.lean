import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Proofs.Step
import Mathlib.Order.WellFounded

namespace Egglog

/-- Every point of a trace is reached by finitely many passes. -/
theorem InfinitePasses.reachable {rel : Database → Database → Prop} {d : Database}
    {trace : Nat → Database} (hstart : trace 0 = d)
    (hstep : ∀ n, rel (trace n) (trace (n + 1))) :
    ∀ n, Relation.ReflTransGen rel d (trace n) := by
  intro n
  induction n with
  | zero => rw [hstart]
  | succ n ih => exact ih.tail (hstep n)

theorem not_infinitePasses_of_wellFounded {S : Schedule} {d : Database}
    (hw : WellFounded (fun e' e =>
      Relation.ReflTransGen (fun a b => Reach a S b) d e ∧
      Reach e S e' ∧ ¬ e.SameMeaning e')) : ¬ InfinitePasses S d := by
  rintro ⟨trace, hstart, hstep⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp hw).false
    ⟨trace, fun n => ⟨InfinitePasses.reachable hstart (fun n => (hstep n).1) n, hstep n⟩⟩

theorem changingRunStep_iff {R : List Rule} {db db' : Database} :
    (Reach db (.run R) db' ∧ ¬ db.SameMeaning db') ↔
      db' = RunRules R db ∧ ¬ db.SameMeaning db' := by
  constructor
  · rintro ⟨h, hn⟩
    cases h
    exact ⟨rfl, hn⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨.run, hn⟩

theorem changingRunReach_runReach {R : List Rule} {d e : Database}
    (h : Relation.ReflTransGen
      (fun a b => Reach a (.run R) b ∧ ¬ a.SameMeaning b) d e) :
    Relation.ReflTransGen (fun a b => b = RunRules R a) d e :=
  Relation.ReflTransGen.mono (fun _ _ hs => (changingRunStep_iff.mp hs).1) _ _ h

/-- Divergence splits at a sequence boundary. -/
theorem Diverges.append_iff {p q : Schedule} {d : Database} :
    Diverges d (.seq p q) ↔
      Diverges d p ∨ ∃ mid, Reach d p mid ∧ Diverges mid q := by
  constructor
  · intro h
    cases h with
    | seqLeft h => exact Or.inl h
    | seqRight hs h => exact Or.inr ⟨_, hs, h⟩
  · rintro (h | ⟨mid, hs, h⟩)
    · exact .seqLeft h
    · exact .seqRight hs h

/-- A saturation-free schedule cannot diverge. -/
theorem not_cmdDiverges_of_allConstructors {d : Database} {S : Schedule}
    (hn : S.NoSaturate) : ¬ Diverges d S := by
  intro h
  induction h with
  | seqLeft _ ih => exact ih hn.1
  | seqRight _ _ ih => exact ih hn.2
  | body | later | forever => exact hn.elim

/-- Bounded programs cannot diverge. -/
theorem not_programDiverges_of_allConstructors {d : Database} {P : Program}
    (hn : P.NoSaturate) : ¬ Diverges d P.schedule :=
  not_cmdDiverges_of_allConstructors hn

/-- A saturation of runs cannot diverge when all changing rounds decrease. -/
theorem not_saturateDiverges_of_wellFounded {R : List Rule} {d : Database}
    (hrounds : WellFounded (fun e' e =>
      Relation.ReflTransGen (fun a b => b = RunRules R a) d e ∧
      e' = RunRules R e ∧ ¬ e.SameMeaning e')) :
    ¬ Diverges d (.saturate (.run R)) := by
  have aux : ∀ e, Relation.ReflTransGen (fun a b => b = RunRules R a) d e →
      ¬ Diverges e (.saturate (.run R)) := by
    intro e
    induction e using hrounds.induction with
    | h e ih =>
      intro he hd
      cases hd with
      | body hb => exact not_cmdDiverges_of_allConstructors (S := .run R) trivial hb
      | later hs hn ht =>
        obtain ⟨rfl, hm⟩ := changingRunStep_iff.mp ⟨hs, hn⟩
        exact ih _ ⟨he, rfl, hm⟩ (he.tail rfl) ht
      | forever hi =>
        apply not_infinitePasses_of_wellFounded (S := .run R) ?_ hi
        exact hrounds.mono (fun a b h => by
          refine ⟨he.trans (Relation.ReflTransGen.mono ?_ _ _ h.1),
            (changingRunStep_iff.mp h.2).1, (changingRunStep_iff.mp h.2).2⟩
          intro x y hs
          cases hs
          rfl)
  exact aux d .refl

end Egglog
