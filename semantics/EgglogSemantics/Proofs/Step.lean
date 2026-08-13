import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Match

namespace Egglog
/-! ### `set` legality

`Action.SetLegal` is egglog's own restriction on `set`: on an all-constructors signature it
admits nothing at all, so that fragment is exactly the fragment with no `set`. -/
/-- **No `set` is legal on an all-constructors signature.** `SetLegal` asks for a
non-constructor and there is none, so every `set` case below is impossible rather
than merely well behaved. -/
theorem Action.SetLegal.elim {sig : Signature} (hsig : sig.AllConstructors) {f : FnName}
    {args out : List Expr} (h : (Action.set f args out).SetLegal sig) : False :=
  h (hsig f)

/-- `SetLegal` does not care *which* all-constructors signature it is read against,
because under one there is no legal `set` to disagree about. This is what lets a `decl`
change the signature without invalidating the rules the database already holds. -/
theorem Actions.SetLegal.of_allConstructors {as : List Action} {sig sig' : Signature}
    (hsig : sig.AllConstructors) (h : Actions.SetLegal as sig) :
    Actions.SetLegal as sig' := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    refine ⟨?_, ih h.2⟩
    cases a with
    | set f args out => exact (Action.SetLegal.elim (args := args) (out := out) hsig h.1).elim
    | expr _ => trivial
    | letBind _ _ => trivial
    | union _ _ => trivial

theorem Rule.SetLegal.of_allConstructors {r : Rule} {sig sig' : Signature}
    (hsig : sig.AllConstructors) (h : r.SetLegal sig) : r.SetLegal sig' :=
  Actions.SetLegal.of_allConstructors hsig h

/-! ### The constructor fragment's state

`MergeStep` fires only on a `.merge` function, so a signature that declares none makes the
merge phase empty; that is what turns the relational `CmdStep` back into a partial
function. -/
/-- `AllConstructors` survives a command, provided the command declares a constructor. -/
theorem Signature.AllConstructors.sigBind {sig : Signature} (h : sig.AllConstructors)
    {c : Cmd} (hc : c.CtorDecl) : (c.sigBind sig).AllConstructors := by
  cases c with
  | decl f d =>
    intro g
    change ((Function.update sig f (some d)) g).bind FnDecl.merge = none
    rw [Function.update_apply]
    split
    · exact hc
    · exact h g
  | _ => exact h

/-- The state half of the constructor fragment: the database is well formed and the
signature declares no merge function.

`WF` is what `Proofs/Interp.lean`'s `execRunRules_RunRules` reads, and `AllConstructors` is
what makes `MergeStep` vacuous, so that a command has exactly one result. Bundled because
they move together across a command and because a `decl` moves the signature, which is why
`CmdStep.ctorState` takes `Cmd.CtorDecl` and nothing else. -/
structure Database.CtorState (db : Database) : Prop where
  wf : db.WF
  sig : db.sig.AllConstructors

theorem Database.CtorState.empty : Database.empty.CtorState where
  wf := Database.WF.empty
  sig := by intro f; simp [Signature.mergeOf, Database.empty]

/-- A declaration whose entry has no merge keeps every constructor a constructor, and makes
the declared name one. This is the direction `Cmd.CtorDecl` buys: a *merge* declaration
would take `IsCtor` away at the declared name, which is `Falsity.claim1`. -/
theorem Signature.IsCtor.update {sig : Signature} {f g : FnName} {d : FnDecl}
    (hd : d.merge = none) (h : sig.IsCtor g) :
    Signature.IsCtor (Function.update sig f (some d)) g := by
  obtain ⟨e, he, hm⟩ := h
  by_cases hg : g = f
  · subst hg; exact ⟨d, Function.update_self .., hd⟩
  · exact ⟨e, by rw [Function.update_of_ne hg]; exact he, hm⟩

/-- **Declaring a name the signature does not mention keeps every constructor.** Unlike
`Signature.IsCtor.update` this puts no condition on the declaration: whatever `f` is
declared to be, it was not a constructor before, so nothing that *was* one is disturbed.

This is what declaration-required buys. A *re*declaration is the case it does not
cover, and `Falsity.claim1` is where that bites. -/
theorem Signature.IsCtor.update_of_fresh {sig : Signature} {f g : FnName} {dc : FnDecl}
    (hf : sig f = none) (h : sig.IsCtor g) :
    Signature.IsCtor (Function.update sig f (some dc)) g := by
  obtain ⟨e, he, hm⟩ := h
  have hg : g ≠ f := by rintro rfl; rw [hf] at he; exact absurd he (by simp)
  exact ⟨e, by rw [Function.update_of_ne hg]; exact he, hm⟩

/-! ### The merge phase -/
theorem MergeStep.sig {d₁ d₂ : Database} (h : MergeStep d₁ d₂) : d₂.sig = d₁.sig := by
  cases h with
  | collide _ _ _ _ _ _ _ hbody _ => simpa using evalActions_sig hbody

theorem MergeClosure.sig {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.sig = d₁.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

/-- A merge writes its combined row and then restores the caller's environment and rule
list, so neither field ever moves. -/
theorem MergeStep.envRules {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  cases h with
  | collide => exact ⟨rfl, rfl⟩

theorem MergeClosure.envRules {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.envRules.1.trans ih.1, hstep.envRules.2.trans ih.2⟩

/-- **No merge fires on an all-constructors signature.** `MergeStep.collide` needs a
`.merge` function and there is none, so every command's merge phase is empty. -/
theorem MergeStep.not_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeStep db db') : False := by
  cases h with
  | @collide _ f _ _ _ _ _ _ _ _ hd hm _ _ _ _ _ _ _ =>
    have hno := hsig f
    rw [Signature.mergeOf, hd, Option.bind_some, hm] at hno
    simp at hno

theorem MergeClosure.eq_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (MergeStep.not_of_allConstructors hsig (ih ▸ hstep)).elim

/-- **A merge phase out of a merge-saturated state is the identity.** The other reason a
merge closure collapses, and the one that makes `CmdStep`'s trailing phase neutral after a
`Cmd.saturate` — which is how the uniform phase survives the new command. -/
theorem MergeClosure.eq_of_mergeSaturated {db db' : Database} (hs : MergeSaturated db)
    (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => subst ih; exact hs _ hstep

/-! ### Rule firing -/
theorem RuleResults.sig {db d : Database} {r : Rule} (h : d ∈ RuleResults db r) :
    d.sig = db.sig := by
  obtain ⟨σ, _, hstep⟩ := h; exact evalLocalActions_sig hstep

theorem RuleResults.wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ RuleResults db r) : d.WF := by
  obtain ⟨σ, hq, hstep⟩ := h; exact evalLocalActions_wf hw hq.mem_terms hstep

theorem RunRules.wf {R : RulesetName} {db : Database} (hw : db.WF) : (RunRules R db).WF :=
  hw.sUnion fun _ hd => RuleResults.wf hw hd.choose_spec.2.2

@[simp] theorem RunRules.sig {R : RulesetName} {db : Database} :
    (RunRules R db).sig = db.sig := by
  simp only [RunRules, Database.sUnion_sig]

/-- **A ruleset is at a fixpoint exactly when none of its rules adds an equation.**

The right-hand side is the shape a "the rules have run out" hypothesis is naturally
written in — `Encoding/Encode.lean`'s `Rebuilt` is one — and the left is the fixpoint
`Cmd.saturate` reaches. Identifying them is what turns such a hypothesis into a
postcondition. -/
theorem runRules_eq_self_iff (R : RulesetName) (db : Database) :
    RunRules R db = db ↔
      ∀ r ∈ db.rules, r.ruleset = R → ∀ d ∈ RuleResults db r, Database.Contained d db := by
  constructor
  · intro h r hr hR d hd
    refine ⟨fun p hp => ?_⟩
    have hsub : d.eqs ⊆ (RunRules R db).eqs := fun q hq =>
      Or.inr (Set.mem_biUnion (Set.mem_setOf.mpr ⟨r, hr, hR, hd⟩) hq)
    rw [h] at hsub
    exact hsub hp
  · intro h
    refine Database.ext rfl ?_ rfl rfl
    refine Set.Subset.antisymm ?_ Set.subset_union_left
    rintro p (hp | hp)
    · exact hp
    · obtain ⟨d, ⟨r, hr, hR, hd⟩, hp⟩ := Set.mem_iUnion₂.mp hp
      exact (h r hr hR d hd).eqs hp

/-! ### A saturating run

`Cmd.saturate` is a fixpoint condition rather than a `cmdEffect`, so the three facts every
command needs — the signature it leaves, the constructor fragment it keeps, and determinism
there — are proved for its *rounds* instead. Each is an induction along
`Relation.ReflTransGen (RunStep R)`. -/
theorem RunStep.sig {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.sig = db.sig := by
  rw [MergeClosure.sig h, RunRules.sig]

/-- Rounds preserve the signature, so `Cmd.saturate` leaves it alone. -/
theorem RunReach.sig {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.sig = db.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

/-- On a constructor signature a round has no merge phase, so it is the *function*
`RunRules R`. -/
theorem RunStep.eq_of_allConstructors {R : RulesetName} {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : RunStep R db db') : db' = RunRules R db :=
  MergeClosure.eq_of_allConstructors (by rw [RunRules.sig]; exact hsig) h

/-- So a state rounds reach is an iterate of it. -/
theorem RunReach.iterate {R : RulesetName} {db d : Database} (hsig : db.sig.AllConstructors)
    (h : Relation.ReflTransGen (RunStep R) db d) : ∃ k, (RunRules R)^[k] db = d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail e f hde hstep ih =>
      obtain ⟨k, hk⟩ := ih
      have hse : e.sig.AllConstructors := by rw [RunReach.sig hde]; exact hsig
      exact ⟨k + 1, by
        rw [Function.iterate_succ_apply', hk, ← hstep.eq_of_allConstructors hse]⟩

/-- **An invariant a round preserves is preserved by a saturating run.** The rounds are the
one unbounded iteration in the semantics, so every "this holds at every reachable state"
argument passes through here. -/
theorem RunReach.induction {R : RulesetName} {P : Database → Prop}
    (hstep : ∀ db db', P db → RunStep R db db' → P db') {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) (hp : P db) : P d := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact hstep _ _ ih hs

/-- Rounds keep the constructor fragment. -/
theorem RunReach.ctorState {R : RulesetName} {db d : Database} (h : db.CtorState)
    (hr : Relation.ReflTransGen (RunStep R) db d) : d.CtorState := by
  induction hr with
  | refl => exact h
  | tail _ hstep ih =>
      rw [hstep.eq_of_allConstructors ih.sig]
      exact ⟨RunRules.wf ih.wf, by rw [RunRules.sig]; exact ih.sig⟩

/-- **A saturating run is deterministic on the constructor fragment**: two fixpoints of one
deterministic iteration coincide. This is what `CmdStep.det` needs, and it is why the
fixpoint condition costs nothing there. -/
theorem saturateReach_det {R : RulesetName} {db d₁ d₂ : Database}
    (hsig : db.sig.AllConstructors) (h₁ : SaturateReach R db d₁)
    (h₂ : SaturateReach R db d₂) : d₁ = d₂ := by
  obtain ⟨k₁, hk₁⟩ := RunReach.iterate hsig h₁.1
  obtain ⟨k₂, hk₂⟩ := RunReach.iterate hsig h₂.1
  rcases Nat.le_total k₁ k₂ with hle | hle
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Nat.add_comm, Function.iterate_add_apply, hk₁, Function.iterate_fixed h₁.2.1] at hk₂
    exact hk₂
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Nat.add_comm, Function.iterate_add_apply, hk₂, Function.iterate_fixed h₂.2.1] at hk₁
    exact hk₁.symm

/-! ### A command's effect

`CmdStep` is `cmdEffect` followed by a merge phase, so every fact about a command splits
into a fact about the deterministic effect and `MergeClosure`'s own. -/
theorem cmdEffect_sig {db d : Database} {c : Cmd} (h : cmdEffect db c = some d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | action a => simp only [cmdEffect] at h; exact evalAction_sig h
  | rule r => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl
  | run R => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl
  | saturate R => exact absurd h (by simp [cmdEffect])
  | decl f dc => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl

theorem cmdEffect_wf {db d : Database} (hw : db.WF) {c : Cmd}
    (h : cmdEffect db c = some d) : d.WF := by
  cases c with
  | action a => simp only [cmdEffect] at h; exact evalAction_wf hw h
  | rule r => simp only [cmdEffect, Option.some.injEq] at h; subst h; exact hw.congr rfl rfl
  | run R => simp only [cmdEffect, Option.some.injEq] at h; subst h; exact RunRules.wf hw
  | saturate R => exact absurd h (by simp [cmdEffect])
  | decl f dc =>
    simp only [cmdEffect, Option.some.injEq] at h; subst h; exact hw.congr rfl rfl

/-- The signature a command leaves is all-constructors provided the command declares a
constructor. This is what makes the merge phase that *follows* the effect empty — including
after a `.decl`, which is the case the uniform merge phase added. -/
theorem cmdEffect_allConstructors {db d : Database} (hsig : db.sig.AllConstructors)
    {c : Cmd} (hdecl : c.CtorDecl) (h : cmdEffect db c = some d) :
    d.sig.AllConstructors := by
  rw [cmdEffect_sig h]; exact hsig.sigBind hdecl

/-! ### What a command reaches

`cmdReach` is `cmdEffect` on four commands out of five and a fixpoint condition on
`Cmd.saturate`. Absorbing the split here is what keeps it out of `CmdStep`'s proofs
below. -/
theorem cmdReach_of_cmdEffect {db d : Database} {c : Cmd} (hns : c.NoSaturate)
    (h : cmdEffect db c = some d) : cmdReach db c d := by
  cases c with
  | saturate R => exact (hns : False).elim
  | _ => exact h

theorem cmdEffect_of_cmdReach {db d : Database} {c : Cmd} (hns : c.NoSaturate)
    (h : cmdReach db c d) : cmdEffect db c = some d := by
  cases c with
  | saturate R => exact (hns : False).elim
  | _ => exact h

theorem cmdReach_sig {db d : Database} {c : Cmd} (h : cmdReach db c d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | saturate R => exact RunReach.sig (show SaturateReach R db d from h).1
  | _ => exact cmdEffect_sig h

theorem cmdReach_allConstructors {db d : Database} (hsig : db.sig.AllConstructors)
    {c : Cmd} (hdecl : c.CtorDecl) (h : cmdReach db c d) : d.sig.AllConstructors := by
  rw [cmdReach_sig h]; exact hsig.sigBind hdecl

theorem cmdReach_ctorState {db d : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hr : cmdReach db c d) : d.CtorState := by
  refine ⟨?_, cmdReach_allConstructors h.sig hdecl hr⟩
  cases c with
  | saturate R => exact (RunReach.ctorState h (show SaturateReach R db d from hr).1).wf
  | _ => exact cmdEffect_wf h.wf hr

/-- What a command reaches is unique on the constructor fragment: `cmdEffect` is a
function, and a saturating run's fixpoint is unique by `saturateReach_det`. -/
theorem cmdReach_det {db e₁ e₂ : Database} (hsig : db.sig.AllConstructors) {c : Cmd}
    (h₁ : cmdReach db c e₁) (h₂ : cmdReach db c e₂) : e₁ = e₂ := by
  cases c with
  | saturate R => exact saturateReach_det hsig h₁ h₂
  | _ => exact Option.some.inj ((show cmdEffect db _ = some e₁ from h₁).symm.trans h₂)

/-! ### The step relations

The step relations are the semantics, so what is proved about them here is what a program
run leaves. -/
theorem CmdStep.sig {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db'.sig = c.sigBind db.sig := by
  obtain ⟨d, hreach, hcl⟩ := h
  rw [hcl.sig]; exact cmdReach_sig hreach

/-- **A command keeps the constructor fragment's state, with no condition on its actions.**
The one thing that has to be excluded is the *declaration* of a `:merge` function, which is
`Cmd.CtorDecl`; a `set` cannot disturb either field. -/
theorem CmdStep.ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hstep : CmdStep db c db') : db'.CtorState := by
  obtain ⟨d, hreach, hcl⟩ := hstep
  have hd := cmdReach_ctorState h hdecl hreach
  rw [hcl.eq_of_allConstructors hd.sig]
  exact hd

/-- **`CmdStep`'s trailing merge phase is neutral on `Cmd.saturate`.** `SaturateReach`
already ends merge-saturated, so the phase that `.rule` and `.decl` pay for uniformly is
free here too, and `CmdStep` stays one `def` over all five commands. -/
theorem cmdStep_saturate_iff {R : RulesetName} {db db' : Database} :
    CmdStep db (.saturate R) db' ↔ SaturateReach R db db' := by
  refine ⟨fun ⟨d, hreach, hcl⟩ => ?_, fun h => ⟨db', h, Relation.ReflTransGen.refl⟩⟩
  have hreach' : SaturateReach R db d := hreach
  rw [MergeClosure.eq_of_mergeSaturated hreach'.2.2 hcl]
  exact hreach'

/-! #### Inversion

`ProgramStep` is a relation, so reading a run *backwards* — what must have happened at
each command — is a `cases` rather than a projection. These two package it, which is what
lets a proof peel a concrete program one command at a time without nesting. -/
theorem ProgramStep.cons_inv {db d' : Database} {c : Cmd} {cs : Program}
    (h : ProgramStep db (c :: cs) d') : ∃ d, CmdStep db c d ∧ ProgramStep d cs d' := by
  cases h with | cons hc hrest => exact ⟨_, hc, hrest⟩

theorem ProgramStep.nil_inv {db d' : Database} (h : ProgramStep db [] d') : db = d' := by
  cases h with | nil => rfl

/-- Running `p` then `q` is running `p ++ q`. What lets a concrete program be built a
prefix at a time. -/
theorem ProgramStep.append {db d d' : Database} {p q : Program} (h₁ : ProgramStep db p d) :
    ProgramStep d q d' → ProgramStep db (p ++ q) d' := by
  induction h₁ with
  | nil => exact id
  | cons hc _ ih => exact fun h₂ => .cons hc (ih h₂)

/-- The invariant argument: an invariant preserved by one command holds at every reachable
state. It is spelled out rather than instantiated because the invariant here is not a bare
`Database → Prop` — each step also takes the command's own side condition. -/
theorem ProgramStep.ctorState {db db' : Database} (h : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hstep : ProgramStep db p db') : db'.CtorState := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hc _ ih =>
    exact ih (hc.ctorState h (hdecl c (by simp)))
      (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-! #### Determinism on the constructor fragment

`CmdStep` and `ProgramStep` are relations because the merge phase is one — a command may
stop anywhere in `MergeClosure`. On a constructor signature there is no merge phase, so
the freedom is gone and the relation is a partial function. This is what lets a concrete
run be read backwards one command at a time, and it is what makes the interpreter's
refinement an *equality* rather than a reachability statement. -/
/-- One command has at most one result where no merge fires.

`cmdEffect` is a function, so the two runs agree up to the merge phase and
`MergeClosure.eq_of_allConstructors` collapses that. `Cmd.CtorDecl` is needed because the
merge phase now follows a `.decl` as well: declaring a `:merge` function is exactly how a
run on an otherwise constructor-only state regains a choice. -/
theorem CmdStep.det {db d₁ d₂ : Database} (hsig : db.sig.AllConstructors) {c : Cmd}
    (hdecl : c.CtorDecl) (h₁ : CmdStep db c d₁) (h₂ : CmdStep db c d₂) : d₁ = d₂ := by
  obtain ⟨e₁, hr₁, hcl₁⟩ := h₁
  obtain ⟨e₂, hr₂, hcl₂⟩ := h₂
  obtain rfl := cmdReach_det hsig hr₁ hr₂
  have hs := cmdReach_allConstructors hsig hdecl hr₁
  rw [hcl₁.eq_of_allConstructors hs, hcl₂.eq_of_allConstructors hs]

/-- A whole program has at most one result on the constructor fragment. The side
conditions are `CmdStep.ctorState`'s: they are what keeps `AllConstructors` true at every
intermediate state, which is what `CmdStep.det` needs there. -/
theorem ProgramStep.det {db d₁ d₂ : Database} (hc : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (h₁ : ProgramStep db p d₁) (h₂ : ProgramStep db p d₂) :
    d₁ = d₂ := by
  induction p generalizing db d₁ d₂ with
  | nil => rw [← h₁.nil_inv, ← h₂.nil_inv]
  | cons c cs ih =>
    obtain ⟨e₁, he₁, hr₁⟩ := h₁.cons_inv
    obtain ⟨e₂, he₂, hr₂⟩ := h₂.cons_inv
    obtain rfl := he₁.det hc.sig (hdecl c (by simp)) he₂
    exact ih (he₁.ctorState hc (hdecl c (by simp)))
      (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc')) hr₁ hr₂

end Egglog
