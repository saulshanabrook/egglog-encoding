import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Scope

/-!
# Is a merge phase after *every* command semantics-preserving?

Scratch, not part of the library. `CmdStep` now runs `cmdEffect` and then a merge phase,
where `.rule` and `.decl` previously took none.

* `.rule` — neutral: `ruleStep_iff` shows the new step is a merge phase of the *pre-state*
  followed by the old effect, so it adds no state a merge phase before the command does not
  already reach.
* `.decl` — neutral **once `Spec/Scope.lean`'s `MergeDeclared` is asked**: `declStep_iff`.
  Without that check it is not, and the counterexample now lives in the library —
  `Proofs/Counterexamples.lean`'s `decl_enables_merge` and `gdecl_not_mergeDeclared`.

Only the neutrality half is left here. It is not a falsity witness, so it does not belong in
`Proofs/Counterexamples.lean`; it belongs beside `Proofs/Step.lean`'s `CmdStep` lemmas, and
is unbuilt until it is moved there.
-/

namespace Egglog
namespace Scratch

/-! ### `Cong` reads `eqs` and nothing else -/

theorem Cong.of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {a b : Term}
    (hc : Cong d₁ a b) : Cong d₂ a b := by
  induction hc using Cong.rec (motive_2 := fun as bs _ => CongList d₂ as bs) with
  | assert hab => exact Cong.assert (h ▸ hab)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ ih₁ ih₂ ih => exact Cong.congr ih₁ ih₂ ih
  | nil => exact CongList.nil
  | cons _ _ ih₁ ih₂ => exact CongList.cons ih₁ ih₂

theorem CongList.of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {as bs : List Term}
    (hc : CongList d₁ as bs) : CongList d₂ as bs := by
  induction hc using CongList.rec (motive_1 := fun a b _ => Cong d₂ a b) with
  | assert hab => exact Cong.assert (h ▸ hab)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ ih₁ ih₂ ih => exact Cong.congr ih₁ ih₂ ih
  | nil => exact CongList.nil
  | cons _ _ ih₁ ih₂ => exact CongList.cons ih₁ ih₂

theorem mem_terms_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {t : Term}
    (ht : t ∈ d₁.terms) : t ∈ d₂.terms := Cong.of_eqs_eq h ht

/-! ### Adding a rule commutes with a merge step -/

theorem evalAction_rules (db : Database) (R : Set Rule) (a : Action) :
    evalAction { db with rules := R } a
      = (evalAction db a).map fun d => { d with rules := R } := by
  cases a with
  | expr e => cases h : e.eval db.sig db.env <;> simp [evalAction, h, Database.addTerm]
  | letBind v e => cases h : e.eval db.sig db.env <;> simp [evalAction, h, Database.addTerm]
  | union e₁ e₂ =>
      cases h₁ : e₁.eval db.sig db.env with
      | none => simp [evalAction, h₁]
      | some t₁ =>
          cases h₂ : e₂.eval db.sig db.env with
          | none => simp [evalAction, h₁, h₂]
          | some t₂ =>
              simp only [evalAction, h₁, h₂, Option.bind_some]
              split <;> simp [Database.addEq, Database.addTerm]
  | set f args out =>
      cases h₁ : Expr.evalList db.sig args db.env <;>
        cases h₂ : Expr.evalList db.sig out db.env <;>
          simp [evalAction, h₁, h₂, Database.addTerm]

theorem evalActions_rules (R : Set Rule) : ∀ (db : Database) (as : List Action),
    evalActions { db with rules := R } as
      = (evalActions db as).map fun d => { d with rules := R }
  | _, [] => by simp [evalActions]
  | db, a :: as => by
      cases h : evalAction db a with
      | none => simp [evalActions, evalAction_rules, h]
      | some d =>
          have hstep : evalActions { db with rules := R } (a :: as)
              = evalActions { d with rules := R } as := by
            simp [evalActions, evalAction_rules, h]
          rw [hstep, evalActions_rules R d as]
          simp [evalActions, h]

theorem MergeStep.rules_eq {db db' : Database} (h : MergeStep db db') :
    db'.rules = db.rules := by cases h; rfl

theorem MergeStep.setRules {db db' : Database} (h : MergeStep db db') (R : Set Rule) :
    MergeStep { db with rules := R } { db' with rules := R } := by
  cases h with
  | @collide d f decl as bs a b vs body res hsig hmerge ha hb hma hmb hcl heval hres =>
      refine MergeStep.collide (d := { d with rules := R }) hsig hmerge ha hb
        (mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hma)
        (mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hmb)
        (CongList.of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hcl) ?_ hres
      rw [show ({ db with rules := R, env := mergeEnv a b } : Database)
            = { { db with env := mergeEnv a b } with rules := R } from rfl,
        evalActions_rules, heval]
      rfl

/-- The merge phase a `rules` update gained runs just as well *before* the update. -/
theorem mergeClosure_setRules {db db' : Database} {R : Set Rule} :
    MergeClosure { db with rules := R } db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with rules := R } := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨db, Relation.ReflTransGen.refl, rfl⟩
    | @tail x y _ hstep ih =>
        obtain ⟨d, hcl, rfl⟩ := ih
        have hstep' : MergeStep d { y with rules := d.rules } :=
          MergeStep.setRules hstep d.rules
        have hrules : y.rules = R := MergeStep.rules_eq hstep
        exact ⟨{ y with rules := d.rules }, hcl.tail hstep', by rw [← hrules]⟩
  · rintro ⟨d, hcl, rfl⟩
    induction hcl with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (MergeStep.setRules hstep R)

/-- **`.rule` is neutral.** The new step is a merge phase of the pre-state followed by the
old effect: every state it adds is one the *preceding* merge phase already reaches. -/
theorem ruleStep_iff {db db' : Database} {r : Rule} :
    CmdStep db (.rule r) db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with rules := insert r db.rules } := by
  simpa [CmdStep, cmdReach, cmdEffect] using
    mergeClosure_setRules (db := db) (db' := db') (R := insert r db.rules)

/-! ### `.decl` is neutral once `MergeDeclared` is asked

`declStep_iff`, under `SigMergeDeclared` — the state-level reading of
`Program.MergeDeclared`, which `programStep_sigMergeDeclared` derives from it. A **fresh**
`f` is then named by no existing `:merge`, so no merge body evaluates differently, and a
`DeclaredTerms` state holds no `f`-headed entry to collide.

The `set` head clause of `Action.Declared` is load-bearing: a head is not in `Expr.fns` and
`evalAction` never checks it, so without the clause a merge body could plant entries of the
name being declared, and the declaration would turn them into a collision. -/

/-- Every declared merge function's body and result name only functions the signature has. -/
def SigMergeDeclared (sig : Signature) : Prop :=
  ∀ g d ms, sig g = some d → d.merge = some ms → ms.Declared sig

theorem exprDeclared_mono {e : Expr} {sig sig' : Signature}
    (hm : ∀ g, sig g ≠ none → sig' g ≠ none) (h : e.Declared sig) : e.Declared sig' :=
  fun g hg => (h g hg).imp id (hm g)

theorem actionDeclared_mono {a : Action} {sig sig' : Signature}
    (hm : ∀ g, sig g ≠ none → sig' g ≠ none) (h : a.Declared sig) : a.Declared sig' := by
  cases a with
  | expr e => exact exprDeclared_mono hm h
  | letBind _ e => exact exprDeclared_mono hm h
  | union e₁ e₂ => exact ⟨exprDeclared_mono hm h.1, exprDeclared_mono hm h.2⟩
  | set g args out =>
      exact ⟨hm g h.1, fun e he => exprDeclared_mono hm (h.2.1 e he),
        fun e he => exprDeclared_mono hm (h.2.2 e he)⟩

theorem actionsDeclared_mono {sig sig' : Signature} (hm : ∀ g, sig g ≠ none → sig' g ≠ none) :
    ∀ {as : List Action}, Actions.Declared as sig → Actions.Declared as sig'
  | [], _ => trivial
  | _ :: _, h => ⟨actionDeclared_mono hm h.1, actionsDeclared_mono hm h.2⟩

theorem mergeDeclared_mono {ms : MergeSpec} {sig sig' : Signature}
    (hm : ∀ g, sig g ≠ none → sig' g ≠ none) (h : ms.Declared sig) : ms.Declared sig' := by
  cases ms with
  | merge body res =>
      exact ⟨actionsDeclared_mono hm h.1, fun e he => exprDeclared_mono hm (h.2 e he)⟩
  | noMerge => trivial

/-- `Cmd.MergeDeclared` establishes the invariant: the new function's `:merge` is checked
against the signature it is already in, and every older one still resolves. -/
theorem sigMergeDeclared_decl {sig : Signature} {f : FnName} {d : FnDecl}
    (h : SigMergeDeclared sig) (hc : Cmd.MergeDeclared (.decl f d) sig) :
    SigMergeDeclared (Function.update sig f (some d)) := by
  have hm : ∀ g, sig g ≠ none → Function.update sig f (some d) g ≠ none := by
    intro g hg
    by_cases hgf : g = f
    · simp [hgf]
    · simpa [Function.update_of_ne hgf] using hg
  intro g d' ms hg hms
  by_cases hgf : g = f
  · subst hgf
    rw [Function.update_self] at hg
    obtain rfl := Option.some.inj hg
    exact hc ms hms
  · rw [Function.update_of_ne hgf] at hg
    exact mergeDeclared_mono hm (h g d' ms hg hms)

/-! #### Structural induction, and the names an expression applies -/

@[elab_as_elim]
theorem recExpr {motive : Expr → Prop} (lit : ∀ l, motive (.lit l)) (var : ∀ v, motive (.var v))
    (app : ∀ f args, (∀ a ∈ args, motive a) → motive (.app f args)) (e : Expr) : motive e :=
  Expr.rec (motive_1 := motive) (motive_2 := fun args => ∀ a ∈ args, motive a) lit var
    (fun f args ih => app f args ih) (fun a ha => by simp at ha)
    (fun _ _ iht ihts a ha => (List.mem_cons.mp ha).elim (fun h => h ▸ iht) (ihts a)) e

@[elab_as_elim]
theorem recTerm {motive : Term → Prop} (lit : ∀ l, motive (.lit l))
    (app : ∀ f args, (∀ a ∈ args, motive a) → motive (.app f args)) (t : Term) : motive t :=
  Term.rec (motive_1 := motive) (motive_2 := fun args => ∀ a ∈ args, motive a) lit
    (fun f args ih => app f args ih) (fun a ha => by simp at ha)
    (fun _ _ iht ihts a ha => (List.mem_cons.mp ha).elim (fun h => h ▸ iht) (ihts a)) t

theorem fns_subset {a : Expr} : ∀ {args : List Expr}, a ∈ args → a.fns ⊆ Expr.fnsList args
  | e :: es, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact fun x hx => by simp only [Expr.fnsList, List.mem_union_iff]; exact Or.inl hx
      · exact fun x hx => by
          simp only [Expr.fnsList, List.mem_union_iff]; exact Or.inr (fns_subset h hx)

/-! #### Evaluation does not read the signature outside `Expr.fns` -/

theorem evalAction_sig {db d : Database} {a : Action} (h : evalAction db a = some d) :
    d.sig = db.sig := by
  cases a with
  | expr e => rw [evalAction] at h; rcases Option.map_eq_some_iff.mp h with ⟨t, -, rfl⟩; rfl
  | letBind v e => rw [evalAction] at h; rcases Option.map_eq_some_iff.mp h with ⟨t, -, rfl⟩; rfl
  | union e₁ e₂ =>
      rw [evalAction] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨t₁, -, h⟩
      rcases Option.bind_eq_some_iff.mp h with ⟨t₂, -, h⟩
      split at h
      · exact absurd h (by simp)
      · rw [← Option.some.inj h]; rfl
  | set g args out =>
      rw [evalAction] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨as, -, h⟩
      rcases Option.map_eq_some_iff.mp h with ⟨vs, -, rfl⟩; rfl

theorem evalActions_sig : ∀ {as : List Action} {db d : Database},
    evalActions db as = some d → d.sig = db.sig
  | [], _, _, h => by rw [evalActions] at h; rw [← Option.some.inj h]
  | _ :: _, _, _, h => by
      rw [evalActions] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨db', h', h''⟩
      rw [evalActions_sig h'', evalAction_sig h']

theorem evalList_update {sig sig' : Signature} {σ : Env} :
    ∀ (args : List Expr), (∀ a ∈ args, a.eval sig σ = a.eval sig' σ) →
      Expr.evalList sig args σ = Expr.evalList sig' args σ
  | [], _ => rfl
  | e :: es, h => by
      rw [Expr.evalList, Expr.evalList, h e (List.mem_cons_self ..),
        evalList_update es fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- Declaring a name a `Declared` expression cannot mention leaves its value alone. -/
theorem eval_update {sig sig' : Signature} {f : FnName} (hf : sig f = none)
    (hag : ∀ g, g ≠ f → sig g = sig' g) :
    ∀ (e : Expr), e.Declared sig → ∀ (σ : Env), e.eval sig σ = e.eval sig' σ := by
  intro e
  induction e using recExpr with
  | lit l => intro _ σ; rfl
  | var v => intro _ σ; rfl
  | app g args ih =>
      intro hdec σ
      have hargs : ∀ a ∈ args, a.Declared sig := fun a ha x hx =>
        hdec x (by rw [Expr.fns]; exact List.mem_cons_of_mem _ (fns_subset ha hx))
      have hlist : Expr.evalList sig args σ = Expr.evalList sig' args σ :=
        evalList_update args fun a ha => ih a ha (hargs a ha) σ
      rw [Expr.eval, Expr.eval, hlist]
      cases hp : Prim.ofName g with
      | some p => rfl
      | none =>
          have hgf : g ≠ f := by
            rintro rfl
            rcases hdec g (by rw [Expr.fns]; exact List.mem_cons_self ..) with h | h
            · exact h hp
            · exact h hf
          have hiff : sig.IsCtor g ↔ sig'.IsCtor g := by
            simp only [Signature.IsCtor, hag g hgf]
          by_cases hc : sig.IsCtor g
          · rw [if_pos hc, if_pos (hiff.mp hc)]
          · rw [if_neg hc, if_neg fun h => hc (hiff.mpr h)]

theorem evalAction_update {f : FnName} {sig' : Signature} {db : Database} {a : Action}
    (hf : db.sig f = none) (hag : ∀ g, g ≠ f → db.sig g = sig' g) (hd : a.Declared db.sig) :
    evalAction { db with sig := sig' } a
      = (evalAction db a).map fun d => { d with sig := sig' } := by
  cases a with
  | expr e =>
      have he := eval_update hf hag e hd db.env
      cases h : e.eval db.sig db.env <;> simp [evalAction, ← he, h, Database.addTerm]
  | letBind v e =>
      have he := eval_update hf hag e hd db.env
      cases h : e.eval db.sig db.env <;> simp [evalAction, ← he, h, Database.addTerm]
  | union e₁ e₂ =>
      have h₁ := eval_update hf hag e₁ hd.1 db.env
      have h₂ := eval_update hf hag e₂ hd.2 db.env
      cases hc₁ : e₁.eval db.sig db.env with
      | none => simp [evalAction, ← h₁, hc₁]
      | some t₁ =>
          cases hc₂ : e₂.eval db.sig db.env with
          | none => simp [evalAction, ← h₁, ← h₂, hc₁, hc₂]
          | some t₂ =>
              simp only [evalAction, ← h₁, ← h₂, hc₁, hc₂, Option.bind_some]
              split <;> simp [Database.addEq, Database.addTerm]
  | set g args out =>
      have h₁ := evalList_update (sig := db.sig) (sig' := sig') (σ := db.env) args
        fun a ha => eval_update hf hag a (hd.2.1 a ha) db.env
      have h₂ := evalList_update (sig := db.sig) (sig' := sig') (σ := db.env) out
        fun a ha => eval_update hf hag a (hd.2.2 a ha) db.env
      cases hc₁ : Expr.evalList db.sig args db.env <;>
        cases hc₂ : Expr.evalList db.sig out db.env <;>
          simp [evalAction, ← h₁, ← h₂, hc₁, hc₂, Database.addTerm]

theorem evalActions_update {f : FnName} {sig' : Signature} :
    ∀ (as : List Action) (db : Database), db.sig f = none →
      (∀ g, g ≠ f → db.sig g = sig' g) → Actions.Declared as db.sig →
      evalActions { db with sig := sig' } as
        = (evalActions db as).map fun d => { d with sig := sig' } := by
  intro as
  induction as with
  | nil => intro db _ _ _; simp [evalActions]
  | cons a as ih =>
      intro db hf hag hd
      cases h : evalAction db a with
      | none => simp [evalActions, evalAction_update hf hag hd.1, h]
      | some d =>
          have hsig : d.sig = db.sig := evalAction_sig h
          have hstep : evalActions { db with sig := sig' } (a :: as)
              = evalActions { d with sig := sig' } as := by
            simp [evalActions, evalAction_update hf hag hd.1, h]
          rw [hstep, ih d (by rw [hsig]; exact hf) (by rw [hsig]; exact hag)
            (by rw [hsig]; exact hd.2)]
          simp [evalActions, h]

/-! #### The name being declared occurs in no term -/

/-- `f` heads `t` or one of its subterms. -/
inductive Mentions (f : FnName) : Term → Prop where
  | head (args : List Term) : Mentions f (.app f args)
  | arg {g : FnName} {args : List Term} {a : Term} :
      a ∈ args → Mentions f a → Mentions f (.app g args)

/-- The invariant a declaration of `f` carries through its merge phase. -/
structure Avoids (f : FnName) (db : Database) : Prop where
  terms : ∀ t ∈ db.terms, ¬ Mentions f t
  env : ∀ b ∈ db.env, ¬ Mentions f b.2

theorem not_mentions_lit {f : FnName} {l : Lit} : ¬ Mentions f (.lit l) := fun h => by cases h

theorem not_mentions_args {f g : FnName} {args : List Term}
    (h : ¬ Mentions f (.app g args)) : ∀ t ∈ args, ¬ Mentions f t :=
  fun _ ht hm => h (Mentions.arg ht hm)

theorem mentions_of_subterm {f : FnName} {s t : Term} (h : Term.IsSubterm s t) :
    Mentions f s → Mentions f t := by
  induction h with
  | refl => exact id
  | arg hmem _ ih => exact fun hs => Mentions.arg hmem (ih hs)

theorem avoids_of_eqs_eq {f : FnName} {d₁ d₂ : Database} (heq : d₂.eqs = d₁.eqs)
    (henv : ∀ b ∈ d₂.env, ¬ Mentions f b.2) (h : Avoids f d₁) : Avoids f d₂ :=
  ⟨fun t ht => h.terms t (mem_terms_of_eqs_eq heq ht), henv⟩

/-- Avoidance is a property of the *asserted* equations: no equation `d` adds mentions `f`. -/
theorem avoids_terms_of_eqs {f : FnName} {db d : Database}
    (hav : ∀ t ∈ db.terms, ¬ Mentions f t)
    (hsub : ∀ p ∈ d.eqs, p ∈ db.eqs ∨ ¬ Mentions f p.1 ∧ ¬ Mentions f p.2) :
    ∀ t ∈ d.terms, ¬ Mentions f t := by
  have key : ∀ {a b : Term}, Cong d a b → ¬ Mentions f a ∧ ¬ Mentions f b := by
    intro a b hab
    induction hab using Cong.rec (motive_2 := fun _ _ _ => True) with
    | assert hp =>
        rcases hsub _ hp with hq | hq
        · exact ⟨hav _ (eqsInTerms_free (Cong.assert hq)).1,
            hav _ (eqsInTerms_free (Cong.assert hq)).2⟩
        · exact hq
    | symm _ ih => exact ⟨ih.2, ih.1⟩
    | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
    | congr _ _ _ ih₁ ih₂ _ => exact ⟨ih₁.1, ih₂.1⟩
    | nil => trivial
    | cons => trivial
  exact fun t ht => (key ht).1

theorem avoids_addTerm {f : FnName} {db : Database} {t : Term}
    (hav : ∀ s ∈ db.terms, ¬ Mentions f s) (ht : ¬ Mentions f t) :
    ∀ s ∈ (db.addTerm t).terms, ¬ Mentions f s := by
  refine avoids_terms_of_eqs hav ?_
  intro p hp
  simp only [Database.addTerm, Set.mem_union, Set.mem_setOf_eq] at hp
  rcases hp with hp | ⟨s, hs, rfl⟩
  · exact Or.inl hp
  · exact Or.inr ⟨fun h => ht (mentions_of_subterm hs h), fun h => ht (mentions_of_subterm hs h)⟩

theorem avoids_addEq {f : FnName} {db : Database} {a b : Term}
    (hav : ∀ s ∈ db.terms, ¬ Mentions f s) (ha : ¬ Mentions f a) (hb : ¬ Mentions f b) :
    ∀ s ∈ (db.addEq a b).terms, ¬ Mentions f s := by
  refine avoids_terms_of_eqs hav ?_
  intro p hp
  simp only [Database.addEq, Database.addTerm, Set.mem_insert_iff, Set.mem_union,
    Set.mem_setOf_eq] at hp
  rcases hp with rfl | (hp | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact Or.inl hp
  · exact Or.inr ⟨fun h => ha (mentions_of_subterm hs h), fun h => ha (mentions_of_subterm hs h)⟩
  · exact Or.inr ⟨fun h => hb (mentions_of_subterm hs h), fun h => hb (mentions_of_subterm hs h)⟩

/-- A `DeclaredTerms` state holds no term mentioning an undeclared name. -/
theorem avoids_of_declaredTerms {f : FnName} {db : Database} (hf : db.sig f = none)
    (hwf : db.WF) (hdt : db.DeclaredTerms) : Avoids f db := by
  have key : ∀ (t : Term), t ∈ db.terms → ¬ Mentions f t := by
    intro t
    induction t using recTerm with
    | lit l => intro _; exact not_mentions_lit
    | app g args ih =>
        intro hmem hmen
        cases hmen with
        | head =>
            obtain ⟨d, hd, -⟩ := hdt f args hmem
            rw [hf] at hd
            exact absurd hd (by simp)
        | arg ha hm =>
            exact ih _ ha (hwf.subtermClosed _ hmem (Term.IsSubterm.arg ha (.refl _))) hm
  exact ⟨key, fun b hb => key b.2 (hwf.envInTerms b hb)⟩

/-! #### Evaluation builds no term mentioning an undeclared name -/

theorem lookup_mem {v : Var} : ∀ {σ : Env} {t : Term},
    Env.lookup v σ = some t → ∃ b ∈ σ, b.2 = t
  | (w, s) :: σ, t, h => by
      rw [Env.lookup] at h
      split at h
      · exact ⟨(w, s), List.mem_cons_self .., Option.some.inj h⟩
      · obtain ⟨c, hc, rfl⟩ := lookup_mem h
        exact ⟨c, List.mem_cons_of_mem _ hc, rfl⟩

/-- A primitive returns an operand or a literal. -/
theorem prim_result {p : Prim} {ts : List Term} {t : Term} (h : p.apply ts = some t) :
    t ∈ ts ∨ ∃ l, t = Term.lit l := by
  unfold Prim.apply at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact Or.inl (by unfold Term.orderingMin; split <;> simp)
  · exact Or.inl (by unfold Term.orderingMax; split <;> simp)
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

theorem prim_avoids {f : FnName} {p : Prim} {ts : List Term} {t : Term}
    (hts : ∀ s ∈ ts, ¬ Mentions f s) (h : p.apply ts = some t) : ¬ Mentions f t := by
  rcases prim_result h with hm | ⟨l, rfl⟩
  · exact hts t hm
  · exact not_mentions_lit

theorem evalList_avoids {sig : Signature} {f : FnName} {σ : Env} :
    ∀ (args : List Expr) (ts : List Term),
      (∀ a ∈ args, ∀ t, a.eval sig σ = some t → ¬ Mentions f t) →
      Expr.evalList sig args σ = some ts → ∀ s ∈ ts, ¬ Mentions f s := by
  intro args
  induction args with
  | nil =>
      intro ts _ h s hs
      rw [Expr.evalList] at h
      rw [← Option.some.inj h] at hs
      simp at hs
  | cons e es ih =>
      intro ts ihe h s hs
      rw [Expr.evalList] at h
      obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ihe e (List.mem_cons_self ..) _ ht
      · exact ih ts' (fun a ha => ihe a (List.mem_cons_of_mem _ ha)) hts' s hs'

/-- `Expr.eval` builds only heads the signature declares, so an undeclared `f` stays out. -/
theorem eval_avoids {sig : Signature} {f : FnName} {σ : Env} (hf : sig f = none)
    (hσ : ∀ b ∈ σ, ¬ Mentions f b.2) :
    ∀ (e : Expr) (t : Term), e.eval sig σ = some t → ¬ Mentions f t := by
  intro e
  induction e using recExpr with
  | lit l => intro t h; rw [Expr.eval] at h; rw [← Option.some.inj h]; exact not_mentions_lit
  | var v =>
      intro t h
      rw [Expr.eval] at h
      obtain ⟨b, hb, rfl⟩ := lookup_mem h
      exact hσ b hb
  | app g args ih =>
      intro t h
      rw [Expr.eval] at h
      cases hp : Prim.ofName g with
      | some p =>
          rw [hp] at h
          obtain ⟨ts, hts, happ⟩ := Option.bind_eq_some_iff.mp h
          exact prim_avoids (evalList_avoids args ts ih hts) happ
      | none =>
          rw [hp] at h
          by_cases hc : sig.IsCtor g
          · rw [if_pos hc] at h
            obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
            intro hmen
            cases hmen with
            | head =>
                obtain ⟨d, hd, -⟩ := hc
                rw [hf] at hd
                exact absurd hd (by simp)
            | arg hmem hm => exact evalList_avoids args ts ih hts _ hmem hm
          · rw [if_neg hc] at h; exact absurd h (by simp)

theorem evalAction_avoids {f : FnName} {db d : Database} {a : Action}
    (hf : db.sig f = none) (hd : a.Declared db.sig) (hav : Avoids f db)
    (h : evalAction db a = some d) : Avoids f d := by
  cases a with
  | expr e =>
      rw [evalAction] at h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨avoids_addTerm hav.terms (eval_avoids hf hav.env e t ht), hav.env⟩
  | letBind v e =>
      rw [evalAction] at h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      have hat := eval_avoids hf hav.env e t ht
      refine avoids_of_eqs_eq (d₁ := db.addTerm t) rfl (fun b hb => ?_)
        ⟨avoids_addTerm hav.terms hat, hav.env⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hat
      · exact hav.env b hb
  | union e₁ e₂ =>
      rw [evalAction] at h
      obtain ⟨t₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨t₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · exact absurd h (by simp)
      · obtain rfl := Option.some.inj h
        exact ⟨avoids_addEq hav.terms (eval_avoids hf hav.env e₁ t₁ h₁)
          (eval_avoids hf hav.env e₂ t₂ h₂), hav.env⟩
  | set g args out =>
      rw [evalAction] at h
      obtain ⟨as, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨avoids_addTerm hav.terms fun hmen => ?_, hav.env⟩
      cases hmen with
      | head => exact hd.1 hf
      | arg hmem hm =>
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact evalList_avoids args as
              (fun a _ t ht => eval_avoids hf hav.env a t ht) h₁ _ hmem hm
          · exact evalList_avoids out vs
              (fun a _ t ht => eval_avoids hf hav.env a t ht) h₂ _ hmem hm

theorem evalActions_avoids {f : FnName} :
    ∀ (as : List Action) (db d : Database), db.sig f = none → Actions.Declared as db.sig →
      Avoids f db → evalActions db as = some d → Avoids f d := by
  intro as
  induction as with
  | nil => intro db d _ _ hav h; rw [evalActions] at h; rw [← Option.some.inj h]; exact hav
  | cons a as ih =>
      intro db d hf hd hav h
      rw [evalActions] at h
      obtain ⟨db', h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      have hsig : db'.sig = db.sig := evalAction_sig h₁
      exact ih db' d (by rw [hsig]; exact hf) (by rw [hsig]; exact hd.2)
        (evalAction_avoids hf hd.1 hav h₁) h₂

/-! #### A merge step preserves the invariant -/

theorem mergeEnvIdx_mem : ∀ {i : Nat} {os ns : List Term} {p : Var × Term},
    p ∈ mergeEnvIdx i os ns → p.2 ∈ os ∨ p.2 ∈ ns
  | _, [], _, _, h => by simp [mergeEnvIdx] at h
  | _, _ :: _, [], _, h => by simp [mergeEnvIdx] at h
  | _, o :: os, n :: ns, p, h => by
      rw [mergeEnvIdx] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · exact (mergeEnvIdx_mem h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

theorem mergeEnv_mem {os ns : List Term} {p : Var × Term} (h : p ∈ mergeEnv os ns) :
    p.2 ∈ os ∨ p.2 ∈ ns := by
  unfold mergeEnv at h
  split at h
  · rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (by simp)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (by simp)
      · simp at h
  · exact mergeEnvIdx_mem h

theorem mergeStep_sig {db x : Database} (h : MergeStep db x) : x.sig = db.sig := by
  cases h with
  | @collide d _ _ _ _ a b _ _ _ _ _ _ _ _ _ _ heval _ =>
      exact evalActions_sig (db := { db with env := mergeEnv a b }) (d := d) heval

theorem mergeClosure_sig {db d : Database} (h : MergeClosure db d) : d.sig = db.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [mergeStep_sig hstep, ih]

theorem mergeStep_avoids {f : FnName} {db x : Database} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hav : Avoids f db) (h : MergeStep db x) : Avoids f x := by
  cases h with
  | @collide d g decl as bs a b vs body res hsig hmerge _ _ hta htb _ heval hres =>
      have hgf : g ≠ f := by rintro rfl; rw [hf] at hsig; exact absurd hsig (by simp)
      have hdec := hsmd g decl (.merge body res) hsig hmerge
      have hta' := hav.terms _ hta
      have htb' := hav.terms _ htb
      have hmenv : ∀ p ∈ mergeEnv a b, ¬ Mentions f p.2 := by
        intro p hp
        rcases mergeEnv_mem hp with hm | hm
        · exact not_mentions_args hta' _ (List.mem_append_right _ hm)
        · exact not_mentions_args htb' _ (List.mem_append_right _ hm)
      have hdav : Avoids f d :=
        evalActions_avoids body { db with env := mergeEnv a b } d hf hdec.1
          (avoids_of_eqs_eq (d₁ := db) rfl hmenv hav) heval
      have hdsig : d.sig = db.sig := evalActions_sig (db := { db with env := mergeEnv a b }) heval
      have hvs : ∀ v ∈ vs, ¬ Mentions f v :=
        evalList_avoids res vs
          (fun e _ t ht => eval_avoids (by rw [hdsig]; exact hf) hdav.env e t ht) hres
      refine avoids_of_eqs_eq (d₁ := d.addTerm (.app g (as ++ vs))) rfl hav.env
        ⟨avoids_addTerm hdav.terms fun hmen => ?_, hdav.env⟩
      cases hmen with
      | head => exact hgf rfl
      | arg hmem hm =>
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact not_mentions_args hta' _ (List.mem_append_left _ hmem) hm
          · exact hvs _ hmem hm

theorem mergeClosure_avoids {f : FnName} {db d : Database} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hav : Avoids f db) (h : MergeClosure db d) :
    Avoids f d := by
  induction h with
  | refl => exact hav
  | @tail p q hcl hstep ih =>
      have hpsig : p.sig = db.sig := mergeClosure_sig hcl
      exact mergeStep_avoids (by rw [hpsig]; exact hf) (by rw [hpsig]; exact hsmd) ih hstep

/-! #### The declaration commutes with its merge phase -/

theorem mergeStep_update_iff {f : FnName} {fd : FnDecl} {db x : Database}
    (hf : db.sig f = none) (hsmd : SigMergeDeclared db.sig) (hav : Avoids f db) :
    MergeStep { db with sig := Function.update db.sig f (some fd) } x ↔
      ∃ y, MergeStep db y ∧ x = { y with sig := Function.update db.sig f (some fd) } := by
  have hag : ∀ g, g ≠ f → db.sig g = Function.update db.sig f (some fd) g :=
    fun g hg => (Function.update_of_ne hg _ _).symm
  set sig' := Function.update db.sig f (some fd) with hsig'
  constructor
  · intro h
    cases h with
    | @collide d g decl as bs a b vs body res hsig hmerge harity hbrity hta htb hcl heval hres =>
        have hsigg : sig' g = some decl := hsig
        have hta' : Term.app g (as ++ a) ∈ db.terms :=
          mem_terms_of_eqs_eq (d₁ := { db with sig := sig' }) (d₂ := db) rfl hta
        have htb' : Term.app g (bs ++ b) ∈ db.terms :=
          mem_terms_of_eqs_eq (d₁ := { db with sig := sig' }) (d₂ := db) rfl htb
        have hcl' : CongList db as bs :=
          CongList.of_eqs_eq (d₁ := { db with sig := sig' }) (d₂ := db) rfl hcl
        have hgf : g ≠ f := by rintro rfl; exact hav.terms _ hta' (Mentions.head _)
        rw [hsig', Function.update_of_ne hgf] at hsigg
        have hdec := hsmd g decl (.merge body res) hsigg hmerge
        have heval' : evalActions { { db with env := mergeEnv a b } with sig := sig' } body
            = some d := heval
        rw [evalActions_update body { db with env := mergeEnv a b } hf hag hdec.1] at heval'
        obtain ⟨d₀, hd₀, rfl⟩ := Option.map_eq_some_iff.mp heval'
        have hd₀sig : d₀.sig = db.sig :=
          evalActions_sig (db := { db with env := mergeEnv a b }) hd₀
        have hres' : Expr.evalList sig' res d₀.env = some vs := hres
        refine ⟨_, MergeStep.collide hsigg hmerge harity hbrity hta' htb' hcl' hd₀ ?_, rfl⟩
        refine Eq.trans ?_ hres'
        exact evalList_update res fun e he =>
          eval_update (by rw [hd₀sig]; exact hf) (by rw [hd₀sig]; exact hag) e
            (by rw [hd₀sig]; exact hdec.2 e he) d₀.env
  · rintro ⟨y, h, rfl⟩
    cases h with
    | @collide d g decl as bs a b vs body res hsig hmerge harity hbrity hta htb hcl heval hres =>
        have hgf : g ≠ f := by rintro rfl; rw [hf] at hsig; exact absurd hsig (by simp)
        have hdec := hsmd g decl (.merge body res) hsig hmerge
        have hdsig : d.sig = db.sig :=
          evalActions_sig (db := { db with env := mergeEnv a b }) heval
        refine MergeStep.collide (d := { d with sig := sig' })
          (show sig' g = some decl by rw [hsig', Function.update_of_ne hgf]; exact hsig)
          hmerge harity hbrity
          (mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with sig := sig' }) rfl hta)
          (mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with sig := sig' }) rfl htb)
          (CongList.of_eqs_eq (d₁ := db) (d₂ := { db with sig := sig' }) rfl hcl) ?_ ?_
        · show evalActions { { db with env := mergeEnv a b } with sig := sig' } body
            = some { d with sig := sig' }
          rw [evalActions_update body { db with env := mergeEnv a b } hf hag hdec.1, heval]
          rfl
        · show Expr.evalList sig' res d.env = some vs
          refine Eq.trans ?_ hres
          exact (evalList_update res fun e he =>
            eval_update (by rw [hdsig]; exact hf) (by rw [hdsig]; exact hag) e
              (by rw [hdsig]; exact hdec.2 e he) d.env).symm

theorem mergeClosure_setSig {f : FnName} {fd : FnDecl} {db db' : Database}
    (hf : db.sig f = none) (hsmd : SigMergeDeclared db.sig) (hav : Avoids f db) :
    MergeClosure { db with sig := Function.update db.sig f (some fd) } db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with sig := Function.update db.sig f (some fd) } := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨db, Relation.ReflTransGen.refl, rfl⟩
    | @tail _ q _ hstep ih =>
        obtain ⟨d, hcl, rfl⟩ := ih
        have hdsig : d.sig = db.sig := mergeClosure_sig hcl
        have hiff := mergeStep_update_iff (f := f) (fd := fd) (db := d) (x := q)
          (by rw [hdsig]; exact hf) (by rw [hdsig]; exact hsmd)
          (mergeClosure_avoids hf hsmd hav hcl)
        rw [hdsig] at hiff
        obtain ⟨y, hy, rfl⟩ := hiff.mp hstep
        exact ⟨y, hcl.tail hy, rfl⟩
  · rintro ⟨d, hcl, rfl⟩
    induction hcl with
    | refl => exact Relation.ReflTransGen.refl
    | @tail p q hcl hstep ih =>
        have hpsig : p.sig = db.sig := mergeClosure_sig hcl
        have hiff := mergeStep_update_iff (f := f) (fd := fd) (db := p)
          (x := { q with sig := Function.update db.sig f (some fd) })
          (by rw [hpsig]; exact hf) (by rw [hpsig]; exact hsmd)
          (mergeClosure_avoids hf hsmd hav hcl)
        rw [hpsig] at hiff
        exact ih.tail (hiff.mpr ⟨q, hstep, rfl⟩)

/-- **`.decl` is neutral.** Under the checks — the declared name fresh, every `:merge` in
the signature declared, the state well-formed — the merge phase the declaration gained is
one the *preceding* merge phase already reaches. -/
theorem declStep_iff {db db' : Database} {f : FnName} {fd : FnDecl} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hwf : db.WF) (hdt : db.DeclaredTerms) :
    CmdStep db (.decl f fd) db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with sig := Function.update db.sig f (some fd) } := by
  simpa [CmdStep, cmdReach, cmdEffect] using
    mergeClosure_setSig (fd := fd) hf hsmd (avoids_of_declaredTerms hf hwf hdt)

/-! #### `Program.MergeDeclared` supplies `declStep_iff`'s hypothesis -/

theorem runReach_sig {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.sig = db.sig := by
  induction h with
  | refl => rfl
  | @tail x y _ hstep ih =>
      have hx : (RunRules R x).sig = x.sig := rfl
      rw [mergeClosure_sig hstep, hx, ih]

theorem cmdEffect_sig {db d : Database} {c : Cmd} (h : cmdEffect db c = some d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | action a => rw [cmdEffect] at h; rw [evalAction_sig h]; rfl
  | rule r => rw [cmdEffect] at h; rw [← Option.some.inj h]; rfl
  | run R => rw [cmdEffect] at h; rw [← Option.some.inj h]; rfl
  | saturate R => exact absurd h (by simp [cmdEffect])
  | decl g d' => rw [cmdEffect] at h; rw [← Option.some.inj h]; rfl

theorem cmdReach_sig {db d : Database} {c : Cmd} (h : cmdReach db c d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | saturate R => exact runReach_sig (show SaturateReach R db d from h).1
  | _ => exact cmdEffect_sig h

theorem cmdStep_sig {db d : Database} {c : Cmd} (h : CmdStep db c d) :
    d.sig = c.sigBind db.sig := by
  obtain ⟨x, hx, hcl⟩ := h
  rw [mergeClosure_sig hcl, cmdReach_sig hx]

theorem cmdStep_sigMergeDeclared {db d : Database} {c : Cmd} (hsmd : SigMergeDeclared db.sig)
    (hc : c.MergeDeclared db.sig) (h : CmdStep db c d) : SigMergeDeclared d.sig := by
  rw [cmdStep_sig h]
  cases c with
  | action a => exact hsmd
  | rule r => exact hsmd
  | run R => exact hsmd
  | saturate R => exact hsmd
  | decl g d' => exact sigMergeDeclared_decl hsmd hc

/-- Every state a checked program reaches satisfies the invariant, so `declStep_iff` covers
every `.decl` such a program runs. -/
theorem programStep_sigMergeDeclared : ∀ {db d : Database} {p : Program}, ProgramStep db p d →
    SigMergeDeclared db.sig → Program.MergeDeclared p db.sig → SigMergeDeclared d.sig := by
  intro db d p h
  induction h with
  | nil => exact fun hsmd _ => hsmd
  | @cons db x _ c _ hstep _ ih =>
      intro hsmd hp
      exact ih (cmdStep_sigMergeDeclared hsmd hp.1 hstep)
        (by rw [cmdStep_sig hstep]; exact hp.2)

/-! ### What `MergeDeclared` rules out

Without it, `.decl` is *not* neutral, and the witness has moved into the library:
`Proofs/Counterexamples.lean`'s `decl_enables_merge`, `gdecl_not_mergeDeclared` and
`db₀_not_sigMergeDeclared`. `g` is a merge function whose `:merge` result names `f`, and `f`
is declared afterwards; `Program.DeclsFresh` permits that, and so does every other check,
since only `MergeDeclared` walks into a `:merge` body. -/

end Scratch
end Egglog
