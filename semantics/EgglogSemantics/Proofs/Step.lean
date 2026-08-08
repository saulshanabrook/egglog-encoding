import EgglogSemantics.Spec.Merge
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Spec.Step
import EgglogSemantics.Proofs.Match

namespace Egglog
@[simp] theorem runProgram_nil {db : Database} : runProgram db [] = some db := rfl

@[simp] theorem runProgram_cons {db : Database} {c : Cmd} {cs : Program} :
    runProgram db (c :: cs) = (stepCmd db c).bind fun db' => runProgram db' cs := rfl

theorem runProgram_append {db : Database} {p q : Program} :
    runProgram db (p ++ q) = (runProgram db p).bind fun db' => runProgram db' q := by
  induction p generalizing db with
  | nil => rfl
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv]
    | some db₁ => simp [hv, ih]

/-! ### Rule results agree with the caller on env and rules

This is what makes `Database.sUnion`'s left bias faithful to the Redex `U_d`: the
operands `(run)` unions all carry the pre-state's environment and rules, so taking
them from the left operand loses nothing. -/
theorem ruleResults_env {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    d.env = db.env :=
  evalLocalActions_env h.choose_spec.2

theorem ruleResults_rules {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    d.rules = db.rules :=
  evalLocalActions_rules h.choose_spec.2

theorem ruleResults_contained {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    db.Contained d :=
  evalLocalActions_contained h.choose_spec.2

theorem ruleResults_wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ ruleResults db r) : d.WF :=
  evalLocalActions_wf hw h.choose_spec.1.mem_terms h.choose_spec.2

/-! ### Steps only add, and preserve well-formedness -/
@[simp] theorem runRules_env {db : Database} : (runRules db).env = db.env := rfl

@[simp] theorem runRules_rules {db : Database} : (runRules db).rules = db.rules := rfl

theorem runRules_contained (db : Database) : db.Contained (runRules db) :=
  Database.Contained.sUnion db _

theorem runRules_wf {db : Database} (hw : db.WF) : (runRules db).WF :=
  hw.sUnion fun _ hd => ruleResults_wf hw hd.choose_spec.2

theorem stepCmd_contained {db db' : Database} {c : Cmd} (h : stepCmd db c = some db') :
    db.Contained db' := by
  cases c with
  | action a => exact evalAction_contained h
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact ⟨subset_rfl, subset_rfl, subset_rfl⟩
  | run =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact runRules_contained db
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem stepCmd_wf {db db' : Database} (hw : db.WF) {c : Cmd}
    (h : stepCmd db c = some db') : db'.WF := by
  cases c with
  | action a => exact evalAction_wf hw h
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ ⟨hw.subtermClosed, hw.eqsInTerms, hw.envInTerms⟩
  | run =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ runRules_wf hw
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ ⟨hw.subtermClosed, hw.eqsInTerms, hw.envInTerms⟩

theorem runProgram_contained {db db' : Database} {p : Program}
    (h : runProgram db p = some db') : db.Contained db' := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ .refl db
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [runProgram_cons, hv, Option.bind_some] at h
      exact (stepCmd_contained hv).trans (ih h)

theorem runProgram_wf {db db' : Database} (hw : db.WF) {p : Program}
    (h : runProgram db p = some db') : db'.WF := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hw
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [runProgram_cons, hv, Option.bind_some] at h
      exact ih (stepCmd_wf hw hv) h

theorem run_wf {p : Program} {db : Database} (h : run p = some db) : db.WF :=
  runProgram_wf Database.WF.empty h

@[simp] theorem runRounds_zero {db : Database} : runRounds 0 db = db := rfl

theorem runRounds_succ {n : Nat} {db : Database} :
    runRounds (n + 1) db = runRounds n (runRules db) := rfl

/-- The other way round: a round can be taken last as well as first. -/
theorem runRounds_succ' {n : Nat} {db : Database} :
    runRounds (n + 1) db = runRules (runRounds n db) := by
  induction n generalizing db with
  | zero => rfl
  | succ m ih => rw [runRounds_succ, ih, runRounds_succ]

theorem runRounds_contained (n : Nat) (db : Database) : db.Contained (runRounds n db) := by
  induction n generalizing db with
  | zero => exact .refl db
  | succ n ih => exact (runRules_contained db).trans (ih (runRules db))

theorem runRounds_wf {db : Database} (hw : db.WF) (n : Nat) : (runRounds n db).WF := by
  induction n generalizing db with
  | zero => exact hw
  | succ n ih => exact ih (runRules_wf hw)

@[simp] theorem runRounds_env {n : Nat} {db : Database} : (runRounds n db).env = db.env := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, ih, runRules_env]

@[simp] theorem runRounds_rules {n : Nat} {db : Database} :
    (runRounds n db).rules = db.rules := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, ih, runRules_rules]

/-- Once saturated, every further round changes nothing. -/
theorem Saturated.runRounds_eq {db : Database} (h : Saturated db) (n : Nat) :
    runRounds n db = db := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, h, ih h]

/-- A round that adds nothing means the next round's result is the same database.
This is the stopping condition a saturating schedule tests for. -/
theorem Saturated.runRounds_succ_eq {db : Database} {n : Nat}
    (h : Saturated (runRounds n db)) : runRounds (n + 1) db = runRounds n db := by
  rw [runRounds_succ', h]

/-! ### `runRules` sees a substitution only up to agreement

An executable enumerator emits one substitution per agreement class, where the spec
admits the whole class (`ValidEnv` fixes the domain only up to permutation). This is
what makes those contribute the same databases. -/
theorem ruleResults_of_agree {db : Database} {r : Rule} {σ σ' : Env} (hag : Env.Agree σ σ')
    (hσ' : ValidQuerySubst db r.query σ') {d : Database}
    (hd : evalLocalActions db r.actions σ = some d) : d ∈ ruleResults db r :=
  ⟨σ', hσ', (evalLocalActions_agree r.actions hag).symm.trans hd⟩

/-! ### Equalities survive -/
/-- Nothing a program derives is ever retracted: the semantics only adds terms and
equalities, so `Cong` is monotone along a run. -/
theorem cong_runProgram {db db' : Database} {p : Program} (h : runProgram db p = some db')
    {a b : Term} (hc : Cong db a b) : Cong db' a b :=
  hc.mono (runProgram_contained h)

/-! ### Constructor rows survive a run

`Database.CtorRows` — the rows are exactly the ones the terms induce — is what
`Proofs/Merge.lean`'s `mcong_iff_cong` wants of a database besides an all-constructors
signature, and until now nothing connected it to a database a program can produce.
`Proofs/Database.lean` shows every database operation preserves it. What is left is to
carry it along the semantics, which takes three side conditions, each of them necessary:

* `Signature.AllConstructors`, because a `:merge` function's row is not a constructor
  row;
* `Action.SetLegal`, egglog's own restriction on `set`, because `set` is the one action
  that writes a row of its own choosing — `Database.not_ctorRows_addRow` is the failure;
* `Cmd.CtorDecl`, because declaring a `:merge` function turns rows *already present*
  into a `MergeStep` collision, whose combined row need not be a constructor row. No
  `set` occurs there, so `SetLegal` does not cover it.

Under the first two together there is in fact no legal `set` at all
(`Action.SetLegal.elim`): the constructor fragment is exactly the fragment with no
`set`, which is also why nothing before M9 needed any of this. -/
/-- On an all-constructors signature every function's merge is `.union`.

The same statement as `Proofs/Merge.lean`'s `Signature.mergeOf_eq_union`, under another
name rather than imported: that file sits above this one in the import graph and will
want `Proofs/Interp.lean` once `execM_reachable` is proved, so importing it here would
risk a cycle. The two should become one lemma when these results move next to
`mcong_iff_cong`. -/
theorem Signature.AllConstructors.mergeOf_eq {sig : Signature} (h : sig.AllConstructors)
    (f : FnName) : sig.mergeOf f = MergeSpec.union := by
  unfold Signature.mergeOf
  cases hf : sig f with
  | none => rfl
  | some d => exact h f d hf

/-- **No `set` is legal on an all-constructors signature.** `SetLegal` asks for a merge
that is not `.union` and there is none, so every `set` case below is impossible rather
than merely well behaved. -/
theorem Action.SetLegal.elim {sig : Signature} (hsig : sig.AllConstructors) {f : FnName}
    {args out : List Expr} (h : (Action.set f args out).SetLegal sig) : False :=
  h (hsig.mergeOf_eq f)

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
    | set f args out => exact (Action.SetLegal.elim hsig h.1).elim
    | expr _ => trivial
    | letBind _ _ => trivial
    | union _ _ => trivial

theorem Rule.SetLegal.of_allConstructors {r : Rule} {sig sig' : Signature}
    (hsig : sig.AllConstructors) (h : r.SetLegal sig) : r.SetLegal sig' :=
  Actions.SetLegal.of_allConstructors hsig h

/-- `AllConstructors` survives a command, provided the command declares a constructor. -/
theorem Signature.AllConstructors.sigBind {sig : Signature} (h : sig.AllConstructors)
    {c : Cmd} (hc : c.CtorDecl) : (c.sigBind sig).AllConstructors := by
  cases c with
  | decl f d =>
    intro g d' hg
    by_cases hgf : g = f
    · subst hgf
      rw [Cmd.sigBind, Function.update_self] at hg
      exact Option.some.inj hg ▸ hc
    · rw [Cmd.sigBind, Function.update_of_ne hgf] at hg
      exact h g d' hg
  | _ => exact h

/-- The state half of the constructor fragment: the signature declares only
constructors, no rule the database holds can `set`, and the rows are the terms'.

Bundled because all three have to move together — a `decl` changes the signature, so it
changes what `SetLegal` means for the rules already stored, and `runRules` needs those
rules legal to keep the rows constructor rows. -/
structure Database.CtorState (db : Database) : Prop where
  sig : db.sig.AllConstructors
  rules : ∀ r ∈ db.rules, r.SetLegal db.sig
  rows : db.CtorRows

theorem Database.CtorState.empty : Database.empty.CtorState where
  sig := by intro f d h; simp [Database.empty] at h
  rules := by simp [Database.empty]
  rows := Database.CtorRows.empty

/-! #### The functional semantics -/
/-- No action touches the signature. Belongs in `Proofs/Eval.lean` beside
`evalAction_rules`; it is here because that file is not this one's to edit. -/
theorem evalAction_sig {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.sig = db.sig := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ | ⟨_, _, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, rfl⟩
  · rfl
  · rfl
  · rfl
  · simp

theorem evalAction_ctorRows {db db' : Database} (hsig : db.sig.AllConstructors)
    {a : Action} (hlegal : a.SetLegal db.sig) (hrows : db.CtorRows)
    (h : evalAction db a = some db') : db'.CtorRows := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, rfl⟩ | ⟨f, args, out, as, v, rfl, -, -, rfl⟩
  · exact hrows.addTerm t
  · exact hrows.addTerm t
  · exact hrows.addEq t₁ t₂
  · exact (Action.SetLegal.elim hsig hlegal).elim

theorem evalActions_ctorRows {db db' : Database} (hsig : db.sig.AllConstructors)
    {as : List Action} (hlegal : Actions.SetLegal as db.sig) (hrows : db.CtorRows)
    (h : evalActions db as = some db') : db'.CtorRows := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hrows
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact ih (by rw [evalAction_sig hv]; exact hsig)
        (by rw [evalAction_sig hv]; exact hlegal.2)
        (evalAction_ctorRows hsig hlegal.1 hrows hv) h

theorem evalLocalActions_ctorRows {db db' : Database} (hsig : db.sig.AllConstructors)
    {as : List Action} {σ : Env} (hlegal : Actions.SetLegal as db.sig)
    (hrows : db.CtorRows) (h : evalLocalActions db as σ = some db') : db'.CtorRows := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  exact evalActions_ctorRows (db := { db with env := db.env ++ σ }) (db' := d)
    hsig hlegal hrows hv

theorem ruleResults_ctorRows {db d : Database} (hsig : db.sig.AllConstructors) {r : Rule}
    (hlegal : r.SetLegal db.sig) (hrows : db.CtorRows) (h : d ∈ ruleResults db r) :
    d.CtorRows :=
  evalLocalActions_ctorRows hsig hlegal hrows h.choose_spec.2

theorem runRules_ctorRows {db : Database} (h : db.CtorState) : (runRules db).CtorRows :=
  h.rows.sUnion fun _ hd =>
    ruleResults_ctorRows h.sig (h.rules _ hd.choose_spec.1) h.rows hd.choose_spec.2

theorem runRules_ctorState {db : Database} (h : db.CtorState) : (runRules db).CtorState :=
  ⟨h.sig, h.rules, runRules_ctorRows h⟩

/-- The signature a command leaves is `Cmd.sigBind`'s, which is what lets
`Program.SetLegal` thread through a `decl`. -/
theorem stepCmd_sig {db db' : Database} {c : Cmd} (h : stepCmd db c = some db') :
    db'.sig = c.sigBind db.sig := by
  cases c with
  | action a => exact evalAction_sig h
  | rule r => simp only [stepCmd, Option.some.injEq] at h; exact h ▸ rfl
  | run => simp only [stepCmd, Option.some.injEq] at h; exact h ▸ rfl
  | decl f d => simp only [stepCmd, Option.some.injEq] at h; exact h ▸ rfl

theorem stepCmd_ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hlegal : c.SetLegal db.sig) (hv : stepCmd db c = some db') :
    db'.CtorState := by
  cases c with
  | action a =>
    exact ⟨by rw [evalAction_sig hv]; exact h.sig,
      by rw [evalAction_sig hv, evalAction_rules hv]; exact h.rules,
      evalAction_ctorRows h.sig hlegal h.rows hv⟩
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at hv
    subst hv
    refine ⟨h.sig, ?_, h.rows⟩
    rintro r' (rfl | hr')
    · exact hlegal
    · exact h.rules r' hr'
  | run =>
    simp only [stepCmd, Option.some.injEq] at hv
    subst hv
    exact runRules_ctorState h
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at hv
    subst hv
    exact ⟨h.sig.sigBind hdecl,
      fun r hr => Rule.SetLegal.of_allConstructors h.sig (h.rules r hr), h.rows⟩

theorem runProgram_ctorState {db db' : Database} (h : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hlegal : p.SetLegal db.sig)
    (hv : runProgram db p = some db') : db'.CtorState := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ hv : db = db') ▸ h
  | cons c cs ih =>
    cases hc : stepCmd db c with
    | none => simp [hc] at hv
    | some db₁ =>
      simp only [runProgram_cons, hc, Option.bind_some] at hv
      exact ih (stepCmd_ctorState h (hdecl c (by simp)) hlegal.1 hc)
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
        (by rw [stepCmd_sig hc]; exact hlegal.2) hv

/-- A whole run stays in the constructor fragment. -/
theorem run_ctorRows {p : Program} {db : Database} (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal Database.empty.sig) (h : run p = some db) : db.CtorRows :=
  (runProgram_ctorState Database.CtorState.empty hdecl hlegal h).rows

/-! #### The step relations

M9's relational semantics, where the headline lives. `MergeStep` is the case `SetLegal`
cannot reach: it fires only on a `.merge` function, so `AllConstructors` makes it
vacuous and a round is `RunRules` and nothing else. -/
theorem Database.ActionStep.sig {db d : Database} {a : Action}
    (h : Database.ActionStep db a d) : d.sig = db.sig := by
  cases h <;> simp

theorem Database.ActionStep.rules {db d : Database} {a : Action}
    (h : Database.ActionStep db a d) : d.rules = db.rules := by
  cases h <;> simp

theorem Database.ActionStep.ctorRows {db d : Database} {a : Action}
    (h : Database.ActionStep db a d) (hsig : db.sig.AllConstructors)
    (hlegal : a.SetLegal db.sig) (hrows : db.CtorRows) : d.CtorRows := by
  cases h with
  | expr _ => exact hrows.addTerm _
  | letBind _ => exact hrows.addTerm _
  | union _ _ => exact hrows.addEq _ _
  | set _ _ => exact (Action.SetLegal.elim hsig hlegal).elim

theorem Database.ActionsStep.sig {db d : Database} {as : List Action}
    (h : Database.ActionsStep db as d) : d.sig = db.sig := by
  induction h with
  | nil => rfl
  | cons hstep _ ih => rw [ih, hstep.sig]

theorem Database.ActionsStep.ctorRows {db d : Database} {as : List Action}
    (h : Database.ActionsStep db as d) (hsig : db.sig.AllConstructors)
    (hlegal : Actions.SetLegal as db.sig) (hrows : db.CtorRows) : d.CtorRows := by
  induction h with
  | nil => exact hrows
  | cons hstep _ ih =>
    exact ih (by rw [hstep.sig]; exact hsig) (by rw [hstep.sig]; exact hlegal.2)
      (hstep.ctorRows hsig hlegal.1 hrows)

theorem MergeStep.sig {d₁ d₂ : Database} (h : MergeStep d₁ d₂) : d₂.sig = d₁.sig := by
  cases h with
  | collide _ _ _ _ hbody _ => simpa using hbody.sig

theorem MergeClosure.sig {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.sig = d₁.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

theorem RunStep.sig {db db' : Database} (h : RunStep db db') : db'.sig = db.sig :=
  MergeClosure.sig (d₁ := RunRules db) h

/-- **No merge fires on an all-constructors signature.** `MergeStep.collide` needs a
`.merge` function and there is none, so the merge phase of a round is empty. -/
theorem MergeStep.not_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeStep db db') : False := by
  cases h with
  | collide _ _ _ hm _ _ =>
    rw [hsig.mergeOf_eq] at hm
    exact absurd hm (by simp)

theorem MergeClosure.eq_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (MergeStep.not_of_allConstructors hsig (ih ▸ hstep)).elim

/-- A round on constructors is exactly `RunRules`: the merge phase does nothing. -/
theorem RunStep.eq_runRules {db db' : Database} (hsig : db.sig.AllConstructors)
    (h : RunStep db db') : db' = RunRules db :=
  MergeClosure.eq_of_allConstructors hsig h

/-- **Why `Cmd.CtorDecl` is a hypothesis, and why `SetLegal` alone would not do.**

Declare `f` a `:merge` function and the constructor row `f ↦ (f)` *already present*
collides with itself, so the merge body runs and writes whatever it likes at that key —
here the literal `0`. No `set` occurs anywhere, so no restriction on actions can rule
this out; what has to be ruled out is the declaration.

This is the one place the preservation chain needed a side condition beyond the `set`
one, and it is why `ProgramStep.ctorRows` takes `Program.CtorDecls`. -/
theorem exists_mergeStep_not_ctorRows :
    ∃ db db' : Database, db.CtorRows ∧ MergeStep db db' ∧ ¬db'.CtorRows :=
  ⟨{ sig := fun g => if g = "f" then some ⟨0, 1, .merge [] [.lit (.int 0)]⟩ else none
     terms := (Term.app "f" []).subterms
     rows := Database.ctorRowsOf (Term.app "f" []).subterms
     eqs := ∅
     env := []
     rules := ∅ },
    _, rfl,
    MergeStep.collide (f := "f") (as := []) (bs := []) (a := [Term.app "f" []])
      (b := [Term.app "f" []]) (vs := [Term.lit (.int 0)]) (body := [])
      (res := [.lit (.int 0)]) ⟨rfl, Term.IsSubterm.refl _⟩ ⟨rfl, Term.IsSubterm.refl _⟩
      .nil (by simp [Signature.mergeOf]) .nil (.cons .lit .nil),
    Database.not_ctorRows_of_mem (Set.mem_insert _ _) (by simp)⟩

theorem RuleResults.ctorRows {db d : Database} (hsig : db.sig.AllConstructors) {r : Rule}
    (hlegal : r.SetLegal db.sig) (hrows : db.CtorRows) (h : d ∈ RuleResults db r) :
    d.CtorRows := by
  obtain ⟨σ, d', -, hstep, rfl⟩ := h
  exact hstep.ctorRows hsig hlegal hrows

theorem RunRules.ctorRows {db : Database} (h : db.CtorState) : (RunRules db).CtorRows :=
  h.rows.sUnion fun _ hd =>
    RuleResults.ctorRows h.sig (h.rules _ hd.choose_spec.1) h.rows hd.choose_spec.2

theorem CmdStep.sig {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db'.sig = c.sigBind db.sig := by
  cases h with
  | action ha => exact ha.sig
  | rule => rfl
  | run hrun => exact hrun.sig
  | decl => rfl

theorem CmdStep.ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hlegal : c.SetLegal db.sig) (hstep : CmdStep db c db') :
    db'.CtorState := by
  cases hstep with
  | action ha =>
    exact ⟨by rw [ha.sig]; exact h.sig, by rw [ha.sig, ha.rules]; exact h.rules,
      ha.ctorRows h.sig hlegal h.rows⟩
  | rule =>
    refine ⟨h.sig, ?_, h.rows⟩
    rintro r' (rfl | hr')
    · exact hlegal
    · exact h.rules r' hr'
  | run hrun =>
    rw [RunStep.eq_runRules h.sig hrun]
    exact ⟨h.sig, h.rules, RunRules.ctorRows h⟩
  | decl =>
    exact ⟨h.sig.sigBind hdecl,
      fun r hr => Rule.SetLegal.of_allConstructors h.sig (h.rules r hr), h.rows⟩

/-- The invariant argument, in the shape `Proofs/Merge.lean`'s `invariant_of_step` gives
it: an invariant preserved by one command holds at every reachable state. It is spelled
out rather than instantiated because the invariant here is not a bare `Database → Prop`
— each step also takes the command's own two side conditions. -/
theorem ProgramStep.ctorState {db db' : Database} (h : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hlegal : p.SetLegal db.sig) (hstep : ProgramStep db p db') :
    db'.CtorState := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hc _ ih =>
    exact ih (hc.ctorState h (hdecl c (by simp)) hlegal.1)
      (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
      (by rw [hc.sig]; exact hlegal.2)

/-- **The headline.** A program that declares only constructors and never `set`s a
constructor leaves the row set determined by the term set.

The three side conditions are not interchangeable: `SetLegal` rules out the action that
writes a bad row, `CtorDecls` rules out the *declaration* that would let `MergeStep`
write one with no action involved, and `AllConstructors` of the starting signature is
what makes both bite. -/
theorem ProgramStep.ctorRows {db db' : Database} {p : Program}
    (hstep : ProgramStep db p db') (hrows : db.CtorRows)
    (hsig : db.sig.AllConstructors) (hdecl : p.CtorDecls) (hlegal : p.SetLegal db.sig)
    (hrules : ∀ r ∈ db.rules, r.SetLegal db.sig) : db'.CtorRows :=
  (ProgramStep.ctorState ⟨hsig, hrules, hrows⟩ hdecl hlegal hstep).rows

/-- **`mcong_iff_cong` applies to whatever a constructor program runs to.**

Its two hypotheses are `db.sig.AllConstructors` and `db.CtorRows`, and this produces
both, so `MCong db a b ↔ Cong db a b` at the end state follows by
`mcong_iff_cong hc.1 hc.2`.

Stated as the pair rather than as the `Iff` because `mcong_iff_cong` lives in
`Proofs/Merge.lean`, which is above this file in the import graph. It should be restated
there as the `Iff` once these results move next to it. -/
theorem ProgramStep.mcong_iff_cong_premises {p : Program} {db : Database}
    (hstep : ProgramStep Database.empty p db) (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal Database.empty.sig) :
    db.sig.AllConstructors ∧ db.CtorRows :=
  let hc := ProgramStep.ctorState Database.CtorState.empty hdecl hlegal hstep
  ⟨hc.sig, hc.rows⟩

end Egglog
