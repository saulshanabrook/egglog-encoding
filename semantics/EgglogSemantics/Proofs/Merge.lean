import EgglogSemantics.Spec.Step
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Proofs.Congruence
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Proofs.Interp

/-!
# What M9 has to prove

`MERGE.md` says which theorem buys what.

## The two transports, and the conditions that buy them

Everything in this file is proved, and there are no `sorry`s. Two lemmas transport a
*specification* fact along `Database.Recorded` — `MergeStep.transport_recorded` and
`RuleResults.mono_recorded` — and **both are false at an arbitrary recorder**. What makes
them true is a legality condition, and there are **two**, either of which closes both:
`Program.UnionFree` and `Program.OrderingFree`. Their disjunction is what reaches
`execM_contained`'s statement; the sections "Union-freedom, and where it puts `Recorded`"
and "Ordering-freedom, and where it puts `Recorded`" below are where they are developed.

`Recorded` says every equation of `d₁` is matched by an equation of `d₂` whose endpoints
are congruent **in `d₂` extended by the two terms in question** — `Database.CongOn`, which
posits the terms reflexively and lets `Cong.congr` close over them. So `d₂` need not hold a
term `d₁` holds; it holds a congruent one. It follows that `Recorded` moves an entry's
**key** columns, which is what the interpreter's rebuild does and the whole reason the
contract is `Recorded`, but also its **value** columns, which the interpreter never does.

What removes the extension is `Conservativity`: adding reflexive equations for terms the
database does not hold cannot relate two terms it does. That is what proves
`Cong.mono_recorded` at the pinned ambient and, with it, `Database.Recorded.trans` — both
under `WF`, which is where the two new `WF` premises on `trans` come from.

Conservativity rescues neither transport, and the obstruction is the same both times: a
run under a *congruent* environment does not record the run under the original.
`min`/`max` matching on literals is fixed — `evalAction` refuses a `union` on a literal, so
`Database.WF.litsIsolated` holds, `Cong.eq_of_isLit` makes a literal's class a singleton
and `Prim.apply_cong` is the resulting stability. What is left is
`ordering-min`/`ordering-max`, which choose by `Term.blt`, a *structural* order, where
egglog chooses by e-class id. `union (f 1) (g 1)` sends `ordering-min (f 1) (f 2)` to
`f 1` and `ordering-min (g 1) (f 2)` to `f 2`, which are not congruent, with no literal
anywhere and every state well formed. No condition on the *database* repairs it. Two
conditions on the *program* do, and each closes **both** transports:

* **`Program.UnionFree`.** `Action.union` is the only action that asserts an equation
  between distinct terms, so a program with none reaches only states whose `eqs` are
  diagonal, and there congruence is equality: `Database.Recorded` and `Database.Contained`
  coincide, and the transports along `Contained` are `MergeStep.transport` and
  `MergeClosure.transport`, already proved.
* **`Program.OrderingFree`.** Then `Expr.eval` *is* congruence-stable (`eval_owes`), so a
  run under the congruent environment a `Recorded` witness supplies gives a congruent
  result — which is what recording asks for. This restricts no `union` at all. That a
  `:merge` body runs under a `mergeEnv` built from value columns `Recorded` moves *before*
  any body expression is evaluated is **not** an obstruction: a moved environment is
  congruent, and nothing reads it except through `Expr.eval`. The one thing this arm needs
  that `Recorded` does not say outright is that the specification holds an entry with the
  *same head* — `recorded_entry`, from an induction over the derivation plus a sharpened
  conservativity (`cong_pin`).

`MergeStep.transport_recorded` without either condition is not merely unproved but
**false**, refuted at `Encoding/Encode.lean`'s own `:merge` body, and its statement carries
the counterexample. Neither arm is vacuous, and between them they cover the encoding and
the equational fragment: `encodeAction` turns a source `union` into `.set @UF [ordering-max
x₁ x₂] [ordering-min x₁ x₂]`, so `encode` uses `ordering-max` — which the second arm
forbids — and emits no `Action.union` at all, which is the first arm; while a source
program with `(union (add a b) (add b a))` and `min`/`max` merges is the second arm and not
the first.

Also **false**, and so restated or deleted rather than left open:

* `Database.Out.mono_recorded`. `Out` reads the key up to congruence and the value columns
  syntactically, and `Recorded` moves both; there is no restatement that both holds and
  serves `mergeOneOriented_mergeStep`, which needs the value columns verbatim. It is
  **deleted**, and the two `Database.Out` facts it used to supply are now premises, carried
  by `mergeRound_contained`'s fold invariant. See the section above `Database.Recorded`.
* the same-`σ`, same-`d₂` family: `Cong.mono_recorded` in its old shape
  (`Cong d₁ a b → Cong d₂ a b`) and with it
  `ValidEnv`/`ValidSubst`/`ValidQuerySubst.mono_recorded`. The counterexample is recorded at
  `Cong.mono_recorded`.

## Known-broken statements, removed

`MergeStep.diamond_of_join` (`hjoin` vacuous under `le := fun _ _ => False`),
`execM_current_of_lattice` (refuted three ways in `Proofs/Lattice.lean`),
`mergeRound_closure` (stated with no hypotheses, both of which are forced) and
`FDatabase.mergeRound_rowCount` (false; `keyRowCount` is what the difftest runs) are
deleted rather than carried as `sorry`s. `RunStep.unique_of_confluent` went with
`RunStep`; `unique_of_diamond` survives under `MergeClosure`.
-/

namespace Egglog
/-! ### The constructor fragment collapses

Congruence is M2's already; this says the same of the *step* relations. -/
/-- With no `.merge` function there is no collision to resolve, so a round is `RunRules`
and nothing else: M9 restricted to constructors is M0–M8 unchanged. -/
theorem MergeStep.saturated_of_allConstructors {db : Database}
    (hsig : db.sig.AllConstructors) : MergeSaturated db := by
  intro db' h
  exact (MergeStep.not_of_allConstructors hsig h).elim

/-! ### The one signature change worth naming

`Cong` reads neither `sig` nor `rows`, so a declaration cannot take a derivation away.
Named rather than inlined because `CmdStep.mono_recorded`'s `.decl` case is the only
place it is spent, and the name says what that case is doing. -/

/-- Declaring a name preserves every derivation. -/
theorem Cong.mono_update {db : Database} {f : FnName} {dc : FnDecl} {a b : Term}
    (h : Cong db a b) :
    Cong ({ db with sig := Function.update db.sig f (some dc) } : Database) a b :=
  Cong.mono (show db.Contained { db with sig := Function.update db.sig f (some dc) } from
    ⟨subset_rfl⟩) h

@[inherit_doc Cong.mono_update]
theorem CongList.mono_update {db : Database} {f : FnName} {dc : FnDecl} {as bs : List Term}
    (h : CongList db as bs) :
    CongList ({ db with sig := Function.update db.sig f (some dc) } : Database) as bs :=
  CongList.mono (show db.Contained { db with sig := Function.update db.sig f (some dc) } from
    ⟨subset_rfl⟩) h

/-- `Out` is monotone, because both of its conjuncts are. A rule body reading a table
never *loses* a match — the property an overwriting merge would destroy, and the one
seminaive evaluation rests on. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, CongList.mono h hl, h.terms hrow⟩

/-- Pointwise congruence respects concatenation, which is how an entry's key and value
halves are read off one application. -/
theorem CongList.append {db : Database} : ∀ {as bs cs ds : List Term},
    CongList db as bs → CongList db cs ds → CongList db (as ++ cs) (bs ++ ds)
  | [], [], _, _, .nil, h₂ => h₂
  | _ :: _, _ :: _, _, _, .cons hab hl, h₂ => .cons hab (CongList.append hl h₂)

/-! ### `CongOn`, moved around

`Database.withOperands` posits a list of terms reflexively, so a `CongOn` fact survives
anything that only adds equations — a larger database, or a different `sig`, `env` or
`rules`, none of which `Cong` reads. Widening the operand *list* is
`Conservativity.withOperands_mono_list`, below, where it is needed. -/

@[inherit_doc CongOn] def CongListOn
    (db : Database) (ts : List Term) (as bs : List Term) : Prop :=
  CongList (db.withOperands ts) as bs

/-- A posited term is self-congruent. -/
theorem mem_congOn_self {db : Database} {ts : List Term} {a : Term} (h : a ∈ ts) :
    CongOn db ts a a := Database.mem_addTerms h

theorem congOn_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {ts : List Term} {a b : Term}
    (hc : CongOn d₁ ts a b) : CongOn d₂ ts a b := Cong.mono (h.addTerms_mono ts) hc

/-- `addTerms` writes `eqs` from `eqs`, so databases agreeing there agree after it. -/
theorem Database.addTerms_eqs_of_eqs {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs)
    (ts : List Term) : (d₁.addTerms ts).eqs = (d₂.addTerms ts).eqs := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (by simp [Database.addTerm, h])

/-- `sig` is invisible to `CongOn`, as it is to `Cong`. -/
theorem congOn_setSig {db : Database} {sig : Signature} {ts : List Term} {a b : Term}
    (h : CongOn db ts a b) : CongOn ({ db with sig := sig } : Database) ts a b :=
  Cong.mono (show (db.withOperands ts).Contained
    ((({ db with sig := sig } : Database)).withOperands ts) from
    ⟨(Database.addTerms_eqs_of_eqs (d₁ := db)
      (d₂ := ({ db with sig := sig } : Database)) rfl ts).subset⟩) h

/-- `env` and `rules` are invisible to `CongOn`, as they are to `Cong`. -/
theorem congOn_setEnvRules {db : Database} {σ : Env} {rs : Set Rule} {ts : List Term}
    {a b : Term} (h : CongOn db ts a b) :
    CongOn ({ db with env := σ, rules := rs } : Database) ts a b :=
  Cong.mono (show (db.withOperands ts).Contained
    ((({ db with env := σ, rules := rs } : Database)).withOperands ts) from
    ⟨(Database.addTerms_eqs_of_eqs (d₁ := db)
      (d₂ := ({ db with env := σ, rules := rs } : Database)) rfl ts).subset⟩) h

/-! ### Recording: containment for an implementation that re-keys

`Database.Recorded` is why the refinement chain cannot run on `Contained` alone: a rebuild
moves an entry onto the canonical key of its class, which congruence still sees and `⊆`
does not.

It has **one** clause now, and it is weaker than the three it replaces in a way that
changes shapes rather than vocabulary. Each `p ∈ d₁.eqs` is matched by *some* `q ∈ d₂.eqs`
whose endpoints are congruent to `p`'s **in `d₂.withOperands [p.1, p.2]`** — so a term of
`d₁` is not a term of `d₂`, it is congruent to one, and the extension that witnesses it is
chosen per equation. That is exactly the slack the re-keying needs, and exactly what makes
the relation hard to compose. -/

/-! ### Conservativity of `withOperands`

A `Recorded` witness lives in `d₂` extended by two phantom operands, and composing two
witnesses lands in `d₂` extended by more of them. What takes an extension back off is that
it is **conservative**: reflexive equations for terms the database does not hold cannot
relate two terms it does.

The proof is a model. Interpret every term in `Quot (Cong db)`, the classes of `db` (a term
`db` does not hold is its own class). An application is sent to the class of a *database
entry* with the same head whose arguments have the same values, if there is one, and to a
junk class otherwise. Both branches read the head and the argument **values** only, so the
interpretation validates `Cong.congr` — including the case the extension exercises, where
one side is an entry and the other a phantom.

This is what makes `Cong.mono_recorded` land in the pinned two-operand ambient `Recorded`
itself uses, and with it `Database.Recorded.trans`. -/

namespace Conservativity

/-- `Cong.mono` with its hypothesis weakened from presence to derivability: a derivation
replays wherever each *asserted* equation of `D` is derivable. -/
theorem cong_replay {D E : Database} (h : ∀ p ∈ D.eqs, Cong E p.1 p.2) {a b : Term}
    (hc : Cong D a b) : Cong E a b := by
  induction hc using Cong.rec (motive_2 := fun as bs _ => CongList E as bs) with
  | assert hab => exact h _ hab
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congr _ _ _ ih₁ ih₂ ihl => exact .congr ih₁ ih₂ ihl
  | nil => exact .nil
  | cons _ _ ih ihl => exact .cons ih ihl

/-- `Database.Contained.addTerms`, read as the subset it wraps. -/
theorem eqs_subset_addTerms (ts : List Term) (db : Database) :
    db.eqs ⊆ (db.addTerms ts).eqs := (Database.Contained.addTerms ts db).eqs

/-- `addTerms` adds reflexive pairs and nothing else. This is the whole content of
conservativity's hypothesis. -/
theorem mem_addTerms_eqs : ∀ (ts : List Term) (db : Database) (p : Term × Term),
    p ∈ (db.addTerms ts).eqs → p ∈ db.eqs ∨ p.1 = p.2
  | [], _, _, h => Or.inl h
  | t :: ts, db, p, h => by
      rcases mem_addTerms_eqs ts (db.addTerm t) p h with h' | h'
      · rcases h' with h' | ⟨s, _, hs⟩
        · exact Or.inl h'
        · exact Or.inr (by rw [← hs])
      · exact Or.inr h'

/-- The sharper reading: a new pair is reflexive *on a subterm of an operand*. -/
theorem mem_addTerms_eqs' : ∀ (ts : List Term) (db : Database) (p : Term × Term),
    p ∈ (db.addTerms ts).eqs → p ∈ db.eqs ∨ ∃ t ∈ ts, ∃ s ∈ t.subterms, p = (s, s)
  | [], _, _, h => Or.inl h
  | t :: ts, db, p, h => by
      rcases mem_addTerms_eqs' ts (db.addTerm t) p h with h' | ⟨u, hu, s, hs, rfl⟩
      · rcases h' with h' | ⟨s, hs, hp⟩
        · exact Or.inl h'
        · exact Or.inr ⟨t, List.mem_cons_self .., s, hs, hp.symm⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem t hu, s, hs, rfl⟩

theorem refl_mem_addTerms {s t : Term} (hs : s ∈ t.subterms) :
    ∀ (ts : List Term) (db : Database), t ∈ ts → (s, s) ∈ (db.addTerms ts).eqs
  | [], _, hmem => by simp at hmem
  | u :: ts, db, hmem => by
      rcases List.mem_cons.mp hmem with heq | hmem
      · exact eqs_subset_addTerms ts (db.addTerm u) (Or.inr ⟨s, heq ▸ hs, rfl⟩)
      · exact refl_mem_addTerms hs ts (db.addTerm u) hmem

theorem addTerms_eqs_mono {d₁ d₂ : Database} (h : d₁.eqs ⊆ d₂.eqs) (ts : List Term) :
    (d₁.addTerms ts).eqs ⊆ (d₂.addTerms ts).eqs :=
  (Database.Contained.addTerms_mono ⟨h⟩ ts).eqs

/-- Widening the operand list. -/
theorem withOperands_mono_list {db : Database} {ts us : List Term} (h : ∀ t ∈ ts, t ∈ us) :
    (db.withOperands ts).eqs ⊆ (db.withOperands us).eqs := by
  intro p hp
  rcases mem_addTerms_eqs' ts db p hp with hq | ⟨t, ht, s, hs, rfl⟩
  · exact eqs_subset_addTerms us db hq
  · exact refl_mem_addTerms hs us db (h t ht)

/-- Every term a database holds is subterm-closed as soon as the *asserted* pairs are. -/
theorem terms_subtermClosed {E : Database}
    (h : ∀ p ∈ E.eqs, p.1.subterms ⊆ E.terms ∧ p.2.subterms ⊆ E.terms) :
    ∀ t ∈ E.terms, t.subterms ⊆ E.terms := by
  have key : ∀ {a b : Term}, Cong E a b → a.subterms ⊆ E.terms ∧ b.subterms ⊆ E.terms := by
    intro a b hc
    induction hc using Cong.rec (motive_2 := fun _ _ _ => True) with
    | assert hab => exact h _ hab
    | symm _ ih => exact ⟨ih.2, ih.1⟩
    | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
    | congr _ _ _ ih₁ ih₂ _ => exact ⟨ih₁.1, ih₂.1⟩
    | nil => trivial
    | cons => trivial
  exact fun t ht => (key ht).1

/-- `db.withOperands ts` is subterm-closed whenever `db` is. -/
theorem withOperands_subtermClosed {db : Database}
    (hwf : ∀ t ∈ db.terms, t.subterms ⊆ db.terms) (ts : List Term) :
    ∀ t ∈ (db.withOperands ts).terms, t.subterms ⊆ (db.withOperands ts).terms := by
  refine terms_subtermClosed ?_
  have grow : db.terms ⊆ (db.withOperands ts).terms := fun _ hx =>
    Cong.mono (Database.Contained.addTerms ts db) hx
  intro p hp
  rcases mem_addTerms_eqs' ts db p hp with hq | ⟨t, ht, s, hs, rfl⟩
  · have hm := eqsInTerms_free (Cong.assert hq)
    exact ⟨fun x hx => grow (hwf _ hm.1 hx), fun x hx => grow (hwf _ hm.2 hx)⟩
  · have hsub : ∀ x ∈ (s : Term).subterms, x ∈ (db.withOperands ts).terms := fun x hx =>
      Cong.assert (refl_mem_addTerms (Term.subterms_subset_of_mem hs hx) ts db ht)
    exact ⟨hsub, hsub⟩

/-! #### The model -/

/-- The classes of `db`. -/
abbrev Cls (db : Database) := Quot (Cong db)

/-- `Cong db` is symmetric and transitive already, so its equivalence closure adds only
reflexivity. -/
theorem eq_or_cong_of_eqvGen {db : Database} {a b : Term}
    (h : Relation.EqvGen (Cong db) a b) : a = b ∨ Cong db a b := by
  induction h with
  | rel _ _ hr => exact Or.inr hr
  | refl _ => exact Or.inl rfl
  | symm _ _ _ ih => rcases ih with rfl | hc; exacts [Or.inl rfl, Or.inr hc.symm]
  | trans _ _ _ _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | h₁
    · exact ih₂
    · rcases ih₂ with rfl | h₂
      exacts [Or.inr h₁, Or.inr (h₁.trans h₂)]

theorem eq_or_cong_of_cls_eq {db : Database} {a b : Term}
    (h : Quot.mk (Cong db) a = Quot.mk (Cong db) b) : a = b ∨ Cong db a b :=
  eq_or_cong_of_eqvGen (Quot.eqvGen_exact h)

open Classical in
/-- The value an application gets: a function of the head and the argument **values**. -/
noncomputable def Iapp (db : Database) (f : FnName) (vs : List (Cls db)) : Cls db :=
  if h : ∃ bs : List Term, Term.app f bs ∈ db.terms ∧ vs = bs.map (Quot.mk (Cong db)) then
    Quot.mk (Cong db) (Term.app f h.choose)
  else Quot.mk (Cong db) (Term.app f (vs.map Quot.out))

mutual

/-- The interpretation. -/
noncomputable def I (db : Database) : Term → Cls db
  | .lit l => Quot.mk (Cong db) (.lit l)
  | .app f as => Iapp db f (IList db as)

/-- `I` over an argument list. -/
noncomputable def IList (db : Database) : List Term → List (Cls db)
  | [] => []
  | t :: ts => I db t :: IList db ts

end

theorem congList_of_map_eq {db : Database} :
    ∀ {as cs : List Term}, (∀ a ∈ as, a ∈ db.terms) →
      as.map (Quot.mk (Cong db)) = cs.map (Quot.mk (Cong db)) → CongList db as cs
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, c :: cs, hmem, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    have ha : a ∈ db.terms := hmem a (List.mem_cons_self ..)
    refine .cons ?_ (congList_of_map_eq (fun x hx => hmem x (List.mem_cons_of_mem a hx)) h.2)
    rcases eq_or_cong_of_cls_eq h.1 with rfl | hc
    exacts [ha, hc]

/-- **The interpretation is the identity on the classes of `db`.** -/
theorem I_eq_of_mem {db : Database} (hsub : ∀ t ∈ db.terms, t.subterms ⊆ db.terms) :
    ∀ t : Term, t ∈ db.terms → I db t = Quot.mk (Cong db) t := by
  intro t
  induction t using Term.rec (motive_2 := fun ts => (∀ x ∈ ts, x ∈ db.terms) →
      IList db ts = ts.map (Quot.mk (Cong db))) with
  | lit l => intro _; rfl
  | app f as ih =>
    intro hmem
    have hargs : ∀ x ∈ as, x ∈ db.terms := fun x hx =>
      hsub _ hmem (Term.IsSubterm.arg hx (Term.IsSubterm.refl x))
    have hlist : IList db as = as.map (Quot.mk (Cong db)) := ih hargs
    have hex : ∃ bs : List Term, Term.app f bs ∈ db.terms ∧
        IList db as = bs.map (Quot.mk (Cong db)) := ⟨as, hmem, hlist⟩
    change Iapp db f (IList db as) = _
    rw [Iapp, dif_pos hex]
    apply Quot.sound
    have hspec := hex.choose_spec
    have hcs : ∀ x ∈ hex.choose, x ∈ db.terms := fun x hx =>
      hsub _ hspec.1 (Term.IsSubterm.arg hx (Term.IsSubterm.refl x))
    exact Cong.congr hspec.1 hmem
      (congList_of_map_eq hcs (hspec.2.symm.trans hlist))
  | nil => rfl
  | cons t ts iht ihts =>
    have hmem : ∀ x ∈ t :: ts, x ∈ db.terms := by assumption
    change I db t :: IList db ts = _
    rw [iht (hmem t (List.mem_cons_self ..)),
      ihts fun x hx => hmem x (List.mem_cons_of_mem t hx), List.map_cons]

/-- **The interpretation validates every derivation of the extension.** -/
theorem I_congr {db E : Database} (hsub : ∀ t ∈ db.terms, t.subterms ⊆ db.terms)
    (hE : ∀ p ∈ E.eqs, p ∈ db.eqs ∨ p.1 = p.2) {a b : Term} (hc : Cong E a b) :
    I db a = I db b := by
  induction hc using Cong.rec (motive_2 := fun as bs _ => IList db as = IList db bs) with
  | @assert x y hxy =>
    rcases hE _ hxy with hp | hp
    · have hcong : Cong db x y := Cong.assert hp
      have hm := eqsInTerms_free hcong
      rw [I_eq_of_mem hsub x hm.1, I_eq_of_mem hsub y hm.2]
      exact Quot.sound hcong
    · exact congrArg (I db) (hp : x = y)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @congr f as bs _ _ _ _ _ ihl =>
    change Iapp db f (IList db as) = Iapp db f (IList db bs)
    rw [ihl]
  | nil => rfl
  | cons _ _ ih ihl => change _ :: _ = _ :: _; rw [ih, ihl]

/-- **Conservativity.** Reflexive equations for terms `db` does not hold cannot relate two
terms it does; `withOperands ts` is exactly such an extension. -/
theorem conservative {db E : Database} (hsub : ∀ t ∈ db.terms, t.subterms ⊆ db.terms)
    (hE : ∀ p ∈ E.eqs, p ∈ db.eqs ∨ p.1 = p.2) {u v : Term} (hu : u ∈ db.terms)
    (hv : v ∈ db.terms) (h : Cong E u v) : Cong db u v := by
  have hI := I_congr hsub hE h
  rw [I_eq_of_mem hsub u hu, I_eq_of_mem hsub v hv] at hI
  rcases eq_or_cong_of_cls_eq hI with rfl | hc
  exacts [hu, hc]

/-- Conservativity, packaged for the operand ambient: the phantom operands drop out. -/
theorem congOn_elim {db : Database} (hwf : ∀ t ∈ db.terms, t.subterms ⊆ db.terms)
    {ts : List Term} {u v : Term} (hu : u ∈ db.terms) (hv : v ∈ db.terms)
    (h : CongOn db ts u v) : Cong db u v :=
  conservative hwf (fun p hp => mem_addTerms_eqs ts db p hp) hu hv h

/-! #### The wide ambient

`withOperands` takes a *list*; transporting a whole derivation needs a whole term **set** in
scope. `amb` is that, and `conservative` is what takes it back off again. -/

/-- `D` with every term of `S` recorded reflexively. -/
def amb (D : Database) (S : Set Term) : Database :=
  { D with eqs := D.eqs ∪ {p | ∃ t ∈ S, p = (t, t)} }

theorem subset_amb {D : Database} {S : Set Term} : D.eqs ⊆ (amb D S).eqs :=
  fun _ h => Or.inl h

theorem amb_refl {D : Database} {S : Set Term} {t : Term} (h : t ∈ S) :
    (t, t) ∈ (amb D S).eqs := Or.inr ⟨t, h, rfl⟩

theorem mem_amb_eqs {D : Database} {S : Set Term} {p : Term × Term}
    (h : p ∈ (amb D S).eqs) : p ∈ D.eqs ∨ p.1 = p.2 := by
  rcases h with h | ⟨t, -, rfl⟩
  exacts [Or.inl h, Or.inr rfl]

/-- An operand list whose subterms `S` covers adds nothing the wide ambient lacks. -/
theorem withOperands_subset_amb {D : Database} {S : Set Term} {ts : List Term}
    (h : ∀ t ∈ ts, ∀ s ∈ t.subterms, s ∈ S) : (D.withOperands ts).eqs ⊆ (amb D S).eqs := by
  intro p hp
  rcases mem_addTerms_eqs' ts D p hp with hq | ⟨t, ht, s, hs, rfl⟩
  · exact Or.inl hq
  · exact amb_refl (h t ht s hs)

/-- An operand *pair* whose subterms `S` covers. This is the shape `Recorded`'s clause
hands over. -/
theorem pair_operands_subset {D E : Database} {S : Set Term} {x y : Term}
    (hx : ∀ s ∈ (x : Term).subterms, s ∈ S) (hy : ∀ s ∈ (y : Term).subterms, s ∈ S)
    (hE : E.eqs ⊆ D.eqs) : (E.withOperands [x, y]).eqs ⊆ (amb D S).eqs := by
  refine (addTerms_eqs_mono hE [x, y]).trans (withOperands_subset_amb ?_)
  rintro t ht s hs
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hx s hs
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact hy s hs
    · simp at ht

/-- Conservativity over the wide ambient. -/
theorem amb_elim {db : Database} (hwf : ∀ t ∈ db.terms, t.subterms ⊆ db.terms)
    {S : Set Term} {u v : Term} (hu : u ∈ db.terms) (hv : v ∈ db.terms)
    (h : Cong (amb db S) u v) : Cong db u v :=
  conservative hwf (fun _ hp => mem_amb_eqs hp) hu hv h

/-! #### Transport along `Recorded` -/

/-- Every equation of `d₁` is derivable in the wide ambient. This is the step that cannot
be sharpened: the derivation of one equation may pass through any term `d₁` holds, which is
why `S` has to cover them all before conservativity can take the widening back off. -/
theorem cong_of_mem_eqs {d₁ d₂ : Database} (h : d₁.Recorded d₂) (hwf : d₁.WF)
    {S : Set Term} (hS : d₁.terms ⊆ S) {D : Database} (hD : d₂.eqs ⊆ D.eqs)
    {p : Term × Term} (hp : p ∈ d₁.eqs) : Cong (amb D S) p.1 p.2 := by
  obtain ⟨q, hq, h₁, h₂⟩ := h.eqs p hp
  have hmem := eqsInTerms_free (Cong.assert hp)
  have hsub : (d₂.withOperands [p.1, p.2]).eqs ⊆ (amb D S).eqs :=
    pair_operands_subset (fun s hs => hS (hwf.subtermClosed _ hmem.1 hs))
      (fun s hs => hS (hwf.subtermClosed _ hmem.2 hs)) hD
  exact (Cong.mono ⟨hsub⟩ h₁).trans
    ((Cong.assert (subset_amb (hD hq))).trans (Cong.mono ⟨hsub⟩ h₂).symm)

/-- A whole derivation of `d₁`, moved into the wide ambient. -/
theorem cong_transport {d₁ d₂ : Database} (h : d₁.Recorded d₂) (hwf : d₁.WF)
    {S : Set Term} (hS : d₁.terms ⊆ S) {D : Database} (hD : d₂.eqs ⊆ D.eqs)
    {a b : Term} (hc : Cong d₁ a b) : Cong (amb D S) a b :=
  cong_replay (fun _ hp => cong_of_mem_eqs h hwf hS hD hp) hc

/-- One endpoint of the composition behind `Database.Recorded.trans`. `x` is one endpoint
of `d₁`'s equation, `y` the matching one of `d₂`'s witness, `z` the matching one of `d₃`'s;
the two witnesses are reached in *different* ambients, and the wide one absorbs the
difference. -/
theorem trans_side {d₂ d₃ : Database} (h₂₃ : d₂.Recorded d₃) (hwf₂ : d₂.WF) (hwf₃ : d₃.WF)
    {ts : List Term} {q : Term × Term} (hq : q ∈ d₂.eqs) {x y z : Term} (hxt : x ∈ ts)
    (hz : z ∈ d₃.terms) (hxy : Cong (d₂.withOperands ts) x y)
    (hyz : Cong (d₃.withOperands [q.1, q.2]) y z) : Cong (d₃.withOperands ts) x z := by
  have hD3 : d₃.eqs ⊆ (d₃.withOperands ts).eqs := eqs_subset_addTerms _ d₃
  -- (a) `d₂`'s derivation replays in `d₃` widened by all of `d₂`'s terms
  have hall : ∀ w ∈ (d₂.withOperands ts).eqs,
      Cong (amb (d₃.withOperands ts) d₂.terms) w.1 w.2 := by
    intro w hw
    rcases mem_addTerms_eqs' ts d₂ w hw with hw2 | ⟨t, ht, s, hs, rfl⟩
    · obtain ⟨r', hr', h₁', h₂'⟩ := h₂₃.eqs w hw2
      have hwm := eqsInTerms_free (Cong.assert hw2)
      have hsub := pair_operands_subset (D := d₃.withOperands ts) (S := d₂.terms)
        (fun s hs => hwf₂.subtermClosed _ hwm.1 hs)
        (fun s hs => hwf₂.subtermClosed _ hwm.2 hs) hD3
      exact (Cong.mono ⟨hsub⟩ h₁').trans
        ((Cong.assert (subset_amb (hD3 hr'))).trans (Cong.mono ⟨hsub⟩ h₂').symm)
    · exact Cong.assert (subset_amb (refl_mem_addTerms hs ts d₃ ht))
  -- (b) `d₃`'s own witness for `q` lives there too
  have hqmem := eqsInTerms_free (Cong.assert hq)
  have hsubq := pair_operands_subset (D := d₃.withOperands ts) (S := d₂.terms)
    (fun s hs => hwf₂.subtermClosed _ hqmem.1 hs)
    (fun s hs => hwf₂.subtermClosed _ hqmem.2 hs) hD3
  -- (c) both endpoints are `d₃`-side, so conservativity takes the widening back off
  exact amb_elim (withOperands_subtermClosed hwf₃.subtermClosed ts)
    (Database.mem_addTerms hxt) (Cong.mono ⟨hD3⟩ hz)
    ((cong_replay hall hxy).trans (Cong.mono ⟨hsubq⟩ hyz))

end Conservativity

open Conservativity in
/-- **`Cong.mono` along `Recorded`.**

The conclusion cannot be `Cong d₂ a b`. Counterexample: `d₁.eqs = {(F c, F c)}` and
`d₂.eqs = {(F e, F e), (c, e)}`. Then `d₁.Recorded d₂` — take `q := (F e, F e)`, since
`withOperands [F c, F c]` posits `F c`, `F e` is already present and `c = e` is asserted,
so `Cong.congr` gives `F c = F e` — while `F c ∉ d₂.terms`, so `Cong d₂ (F c) (F c)` is
false.

What does hold is the same **pinned** ambient `Recorded`'s own clause uses: the two
endpoints, and nothing else. The derivation may pass through any term of `d₁`, so it is run
in `d₂` widened by all of them and conservativity takes the widening back off — which is
what the two `WF` hypotheses pay for. -/
theorem Cong.mono_recorded {d₁ d₂ : Database} (h : d₁.Recorded d₂) (hwf₁ : d₁.WF)
    (hwf₂ : d₂.WF) {a b : Term} (hc : Cong d₁ a b) : CongOn d₂ [a, b] a b :=
  amb_elim (withOperands_subtermClosed hwf₂.subtermClosed [a, b])
    (Database.mem_addTerms (by simp)) (Database.mem_addTerms (by simp))
    (cong_transport h hwf₁ (fun _ hx => hx) (eqs_subset_addTerms [a, b] d₂) hc)

open Conservativity in
/-- The list form, which is what an entry atom needs. The ambient is a single list covering
both sides, since `Cong.congr` wants all the operands of an application in scope at once. -/
theorem CongList.mono_recorded {d₁ d₂ : Database} (h : d₁.Recorded d₂) (hwf₁ : d₁.WF)
    (hwf₂ : d₂.WF) : ∀ {as bs : List Term}, CongList d₁ as bs →
      ∀ ts : List Term, (∀ a ∈ as, a ∈ ts) → (∀ b ∈ bs, b ∈ ts) → CongListOn d₂ ts as bs
  | _, _, .nil, _, _, _ => .nil
  | a :: as, b :: bs, .cons hab hl, ts, hta, htb => by
    refine .cons (Cong.mono ⟨withOperands_mono_list ?_⟩ (Cong.mono_recorded h hwf₁ hwf₂ hab))
      (CongList.mono_recorded h hwf₁ hwf₂ hl ts
        (fun x hx => hta x (List.mem_cons_of_mem a hx))
        (fun x hx => htb x (List.mem_cons_of_mem b hx)))
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hta t (List.mem_cons_self ..)
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact htb t (List.mem_cons_self ..)
      · simp at ht

/-! **There is no `Out.mono` along `Recorded`, in any form its consumer could use.**

`Out d₂ f as vs` reads the key `as` up to congruence and the value columns `vs`
*syntactically*, and `Recorded` moves both. It moves the key because `Cong.mono_recorded`
lands in `d₂.withOperands [a, b]` rather than in `d₂`, and `Conservativity.congOn_elim`
takes that ambient off only against endpoints `d₂` already holds. It moves the values
because an equation of `d₂` may relate a value column to another term: with
`d₁.eqs = {(f k v, f k v), (k, k), (v, v)}` and
`d₂.eqs = {(f k w, f k w), (k, k), (w, w), (v, v), (v, w)}` both states are well formed and
`d₁.Recorded d₂` — the witness for the entry is `f k w`, reached by `Cong.congr` under
`v = w` — while `d₂` holds no `f`-entry whose value column is `v`, so `d₂.Out f as' [v]`
fails for every `as'`.

That second half is not an artefact: it is the interpreter's own situation, since the
implementation canonicalises a row's outputs and the specification keeps the originals.
`mergeOneOriented_mergeStep` needs the value columns *verbatim* — the merge body has to run
under the same `mergeEnv` on both sides — so it takes the two `Database.Out` facts as
hypotheses instead. `mergeRound_contained` carries them: they are about the fixed pre-pass
row list, `FDatabase.IndexOk.entry` establishes them at the rebuild, and `Out.mono` keeps
them as the specification witness grows. -/

namespace Database
namespace Recorded

/-- Reflexivity is **free** now. The old proof needed `RowsWF`, because `Out` reads a key
up to congruence and `CongList` is reflexive only on terms the database holds; with the
row clause gone the witness is the equation itself, and `withOperands` puts both of its
endpoints in `terms`. -/
theorem refl {db : Database} : db.Recorded db :=
  ⟨fun p hp => ⟨p, hp, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩⟩

/-- Syntactic containment is recording, and needs no side condition either. -/
theorem of_contained {d₁ d₂ : Database} (h : d₁.Contained d₂) : d₁.Recorded d₂ :=
  ⟨fun p hp => ⟨p, h.eqs hp, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩⟩

/-- `Recorded` reads `sig` and `eqs`; `env` and `rules` may be replaced freely on both
sides. -/
theorem setEnvRules {d₁ d₂ : Database} (h : d₁.Recorded d₂) (σ τ : Env) (rs ss : Set Rule) :
    ({ d₁ with env := σ, rules := rs } : Database).Recorded
      { d₂ with env := τ, rules := ss } :=
  ⟨fun p hp =>
    let ⟨q, hq, hc₁, hc₂⟩ := h.eqs p hp
    ⟨q, hq, congOn_setEnvRules hc₁, congOn_setEnvRules hc₂⟩⟩

/-- Nothing reads the environment through `Recorded`, so both sides may be re-based. -/
theorem setEnv {d₁ d₂ : Database} (h : d₁.Recorded d₂) (σ τ : Env) :
    ({ d₁ with env := σ } : Database).Recorded { d₂ with env := τ } :=
  h.setEnvRules σ τ d₁.rules d₂.rules

/-- **`Recorded` composes**, given that the two later states are well formed.

`d₁`'s equation is matched by one of `d₂`'s in `d₂.withOperands [p.1, p.2]`, and that one
by one of `d₃`'s in `d₃.withOperands [q.1, q.2]` — a *different* extension. Neither list is
the one the conclusion is pinned to, so both derivations are run in `d₃` widened by all of
`d₂`'s terms and `Conservativity.amb_elim` takes the widening off again, which it may
because both endpoints of the composite are `d₃`-side. `hwf₂` covers the subterms of the
equations being composed; `hwf₃` is what conservativity is applied to.

`Conservativity.trans_side` is one endpoint of the composition; the two calls differ only
in which endpoint they follow. -/
theorem trans {d₁ d₂ d₃ : Database} (h₁ : d₁.Recorded d₂) (h₂ : d₂.Recorded d₃)
    (hwf₂ : d₂.WF) (hwf₃ : d₃.WF) : d₁.Recorded d₃ := by
  refine ⟨fun p hp => ?_⟩
  obtain ⟨q, hq, hq₁, hq₂⟩ := h₁.eqs p hp
  obtain ⟨r, hr, hr₁, hr₂⟩ := h₂.eqs q hq
  have hrmem := eqsInTerms_free (Cong.assert hr)
  exact ⟨r, hr, Conservativity.trans_side h₂ hwf₂ hwf₃ hq (by simp) hrmem.1 hq₁ hr₁,
    Conservativity.trans_side h₂ hwf₂ hwf₃ hq (by simp) hrmem.2 hq₂ hr₂⟩

/-- Growing the right-hand side keeps it a recorder: the extension is monotone in `d₂`,
so no re-derivation is needed and this is *not* an instance of `trans`. -/
theorem trans_contained {d₁ d₂ d₃ : Database} (h₁ : d₁.Recorded d₂)
    (h₂ : d₂.Contained d₃) : d₁.Recorded d₃ :=
  ⟨fun p hp =>
    let ⟨q, hq, hc₁, hc₂⟩ := h₁.eqs p hp
    ⟨q, h₂.eqs hq, congOn_mono h₂ hc₁, congOn_mono h₂ hc₂⟩⟩

/-! The same operation applied to both sides, as `Contained` has. The added equations are
the same on both, so they are their own witnesses and only the *old* ones need the
weakening. -/
theorem addTerm_mono {d₁ d₂ : Database} (h : d₁.Recorded d₂) (t : Term) :
    (d₁.addTerm t).Recorded (d₂.addTerm t) := by
  refine ⟨fun p hp => ?_⟩
  rcases hp with hp | ⟨s, hs, rfl⟩
  · obtain ⟨q, hq, hc₁, hc₂⟩ := h.eqs p hp
    exact ⟨q, Or.inl hq, congOn_mono (Database.Contained.addTerm t d₂) hc₁,
      congOn_mono (Database.Contained.addTerm t d₂) hc₂⟩
  · exact ⟨(s, s), Or.inr ⟨s, hs, rfl⟩, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩

theorem addTerms_mono {d₁ d₂ : Database} (h : d₁.Recorded d₂) (ts : List Term) :
    (d₁.addTerms ts).Recorded (d₂.addTerms ts) := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm_mono t)

theorem addEq_mono {d₁ d₂ : Database} (h : d₁.Recorded d₂) (a b : Term) :
    (d₁.addEq a b).Recorded (d₂.addEq a b) := by
  have h' := (h.addTerm_mono a).addTerm_mono b
  refine ⟨fun p hp => ?_⟩
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact ⟨(a, b), Set.mem_insert _ _, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩
  · obtain ⟨q, hq, hc₁, hc₂⟩ := h'.eqs p hp
    have hcc : ((d₂.addTerm a).addTerm b).Contained (d₂.addEq a b) :=
      ⟨Set.subset_insert _ _⟩
    exact ⟨q, Set.mem_insert_of_mem _ hq, congOn_mono hcc hc₁, congOn_mono hcc hc₂⟩

/-- **The combined entry, written at a congruent key.** This is the one place the
weakening earns its keep: the interpreter records `f(as…, vs…)` and the specification
records `f(bs…, vs…)` at the key it found the colliding entry at, and `withOperands` plus
`Cong.congr` is what relates the two.

`hw` is needed for the *strict* subterms of `as`, which are terms of `d₂` but need not be
subterms of `d₂`'s own entry term. -/
theorem addTerm_congr {d₁ d₂ : Database} (h : d₁.Recorded d₂) (hw : d₂.WF)
    {f : FnName} {as bs vs : List Term} (hcong : CongList d₂ as bs) :
    (d₁.addTerm (.app f (as ++ vs))).Recorded (d₂.addTerm (.app f (bs ++ vs))) := by
  set u : Term := .app f (bs ++ vs) with hu
  have hsub : ∀ x ∈ bs ++ vs, ∀ s ∈ x.subterms, (s, s) ∈ (d₂.addTerm u).eqs := by
    intro x hx t ht
    exact Or.inr ⟨t, Term.IsSubterm.arg hx ht, rfl⟩
  have hmemAs : ∀ x ∈ as, ∀ s ∈ x.subterms, (s, s) ∈ (d₂.addTerm u).eqs := by
    intro x hx t ht
    exact Or.inl (hw.eqsRefl t (hw.subtermClosed x (hcong.mem_of.1 x hx) ht))
  refine ⟨fun p hp => ?_⟩
  rcases hp with hp | ⟨t, ht, rfl⟩
  · obtain ⟨q, hq, hc₁, hc₂⟩ := h.eqs p hp
    exact ⟨q, Or.inl hq, congOn_mono (Database.Contained.addTerm u d₂) hc₁,
      congOn_mono (Database.Contained.addTerm u d₂) hc₂⟩
  · cases Term.mem_subterms.mp ht with
    | refl =>
      -- the entry term itself: congruent to the one written at the witness key
      have key : CongOn (d₂.addTerm u) [Term.app f (as ++ vs), Term.app f (as ++ vs)]
          (Term.app f (as ++ vs)) u := by
        refine Cong.congr (mem_congOn_self (by simp)) ?_ ?_
        · exact Cong.mono (Database.Contained.addTerms _ _)
            (Cong.assert (Or.inr ⟨u, Term.self_mem_subterms u, rfl⟩))
        · refine CongList.append (CongList.mono ?_ hcong) (CongList.refl ?_)
          · exact (Database.Contained.addTerm u d₂).trans
              (Database.Contained.addTerms _ _)
          · intro y hy
            exact Cong.assert (Database.Contained.addTerms _ _ |>.eqs
              (hsub y (List.mem_append_right _ hy) y (Term.self_mem_subterms y)))
      exact ⟨(u, u), Or.inr ⟨u, Term.self_mem_subterms u, rfl⟩, key, key⟩
    | @arg x _ _ hx hxt =>
      -- a proper subterm: of a key column, or of a value column
      have hmemq : (t, t) ∈ (d₂.addTerm u).eqs := by
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hmemAs x hx' t (Term.mem_subterms.mpr hxt)
        · exact hsub x (List.mem_append_right _ hx') t (Term.mem_subterms.mpr hxt)
      exact ⟨(t, t), hmemq, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩

end Recorded
end Database

/-- **A merge never shrinks the database.**

Constraint (3), discharged by the representation rather than by an argument: the step
adds the combined row beside the two it merged, so there is nothing to overwrite. This
is what lets `Cong.mono`, `Out.mono` and every `WF`-preservation lemma survive into
M9 unchanged. -/
theorem MergeStep.contained {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₁.Contained d₂ := by
  cases h with
  | @collide d f _ as _ _ _ vs _ _ _ _ _ _ _ _ _ hbody _ =>
    have hb : d₁.Contained d := ⟨(evalActions_contained hbody).eqs⟩
    exact ⟨(hb.trans (Database.Contained.addTerm _ d)).eqs⟩

theorem MergeClosure.contained {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₁.Contained d₂ := by
  induction h with
  | refl => exact Database.Contained.refl _
  | tail _ hstep ih => exact ih.trans (MergeStep.contained hstep)

/-- **Re-adding a term the database already holds is the identity.**

`Database.WF.eqsRefl` is what makes this true: `addTerm` writes one reflexive equation per
subterm, `subtermClosed` puts every subterm in `terms`, and `eqsRefl` says `eqs` already
carried each of those equations. Without that clause the successor is `Cong.of_addTerm`,
which is a statement about the relation and not about the database. -/
theorem Database.addTerm_eq_self {db : Database}
    (hsub : ∀ t ∈ db.terms, t.subterms ⊆ db.terms)
    (hrefl : ∀ t ∈ db.terms, (t, t) ∈ db.eqs) {t : Term}
    (ht : t ∈ db.terms) : db.addTerm t = db := by
  refine Database.ext rfl ?_ rfl rfl
  refine Set.union_eq_self_of_subset_right ?_
  rintro p ⟨s, hs, rfl⟩
  exact hrefl s (hsub t ht hs)

set_option linter.unusedVariables false in
/-- **A vacuous self-collision is the identity step.**

Database equality is available again, and `Database.WF.eqsRefl` is the clause that
restored it: `addTerm` on a term the database already holds is the identity
(`Database.addTerm_eq_self`), so the step's `addTerm` of the combined entry cancels once
the entry is one `db` has and the body changed no equation. That is what makes
`MergeSaturated` — "no merge collision *changes* anything" — reachable at all, since every
entry collides with itself and so a step always applies.

`hsig`, `hdc` and `hres` are not used by the equation — they are what makes the conclusion
an instance of `MergeStep`, so removing them would change what the theorem says. -/
theorem MergeStep.self_id {db d : Database} {f : FnName} {dc : FnDecl} {as a : List Term}
    {body : List Action} {res : List Expr} (hw : db.WF)
    (hrow : Term.app f (as ++ a) ∈ db.terms)
    (hsig : db.sig f = some dc) (hdc : dc.merge = some (MergeSpec.merge body res))
    (hbody : evalActions { db with env := mergeEnv a a } body = some d)
    (hfix : d.eqs = db.eqs)
    (hres : Expr.evalList d.sig res d.env = some a) :
    ({ d.addTerm (.app f (as ++ a)) with env := db.env, rules := db.rules } : Database)
      = db := by
  have hterms : d.terms = db.terms := Database.terms_eq_of_eqs_eq hfix
  have hd : d.addTerm (.app f (as ++ a)) = d :=
    Database.addTerm_eq_self (fun t ht => hterms ▸ hw.subtermClosed t (hterms ▸ ht))
      (fun t ht => hfix ▸ hw.eqsRefl t (hterms ▸ ht)) (hterms ▸ hrow)
  rw [hd]
  refine Database.ext ?_ hfix rfl rfl
  simpa using evalActions_sig hbody

/-! ### The observable value

Constraint (3)'s second half. `PLAN.md` proposes a merge-fold and asks for it to be
well defined; `Current` is that value defined as a maximum instead, which needs only
antisymmetry. It is not what `Expr.eval` reads. -/
/-- The value a *join* merge settles on at the class of `as`: the `le`-greatest
recorded output.

**Not** what a query read matches — that is `Database.Out`, any recorded output.
`Current` exists only when `f`'s merge is a join for `le`, and it is here for the two
places that need to match egglog's answer rather than over-approximate it: differential
testing, and M11's simulation theorem.

A maximum rather than a fold, because a greatest element is unique from antisymmetry
alone (`current_unique`) where a fold over a set needs commutativity and associativity
first. `le` is a parameter rather than an instance because the order is per function —
one `Term` type carries every sort — and it orders whole rows, since a multi-column merge
can settle its columns jointly. See `MERGE.md`, "Why a maximum and not a fold". -/
def Database.Current (db : Database) (le : List Term → List Term → Prop) (f : FnName)
    (as : List Term) (vs : List Term) : Prop :=
  db.Out f as vs ∧ ∀ ws, db.Out f as ws → le ws vs

/-- The observable value is unique. This is "the fold is well defined", with a fold's
commutativity and associativity obligations replaced by antisymmetry of the order —
see `MERGE.md`, "Why a maximum and not a fold". -/
theorem Database.current_unique {db : Database} {le : List Term → List Term → Prop}
    (hanti : ∀ x y, le x y → le y x → x = y) {f : FnName} {as v w : List Term}
    (hv : db.Current le f as v) (hw : db.Current le f as w) : v = w :=
  hanti _ _ (hw.2 v hv.1) (hv.2 w hw.1)

/-! ### The term order

`Term.blt` unfolds definitionally in every case, so the equation lemmas below are `rfl`
and the three order laws are ordinary case analyses over the (length, name, lex) key.
`Term.bltList` is only used at equal lengths, which is why *totality* is the one law
that needs a length hypothesis on the list level — `bltList [] (b :: bs)` and
`bltList (b :: bs) []` are both `false`. -/
namespace Term
@[simp] theorem blt_lit_lit {m n : Int} :
    Term.blt (.lit (.int m)) (.lit (.int n)) = decide (m < n) := rfl

@[simp] theorem blt_lit_app {l : Lit} {f : FnName} {as : List Term} :
    Term.blt (.lit l) (.app f as) = true := by cases l; rfl

@[simp] theorem blt_app_lit {f : FnName} {as : List Term} {l : Lit} :
    Term.blt (.app f as) (.lit l) = false := rfl

theorem blt_app_app {f g : FnName} {as bs : List Term} :
    Term.blt (.app f as) (.app g bs) =
      (if as.length ≠ bs.length then decide (as.length < bs.length)
       else if f ≠ g then decide (f < g) else Term.bltList as bs) := rfl

@[simp] theorem bltList_nil {bs : List Term} : Term.bltList [] bs = false := rfl

@[simp] theorem bltList_cons_nil {a : Term} {as : List Term} :
    Term.bltList (a :: as) [] = false := rfl

theorem bltList_cons_cons {a b : Term} {as bs : List Term} :
    Term.bltList (a :: as) (b :: bs) =
      if a = b then Term.bltList as bs else Term.blt a b := rfl

end Term
mutual

/-- Asymmetry. On the list level this needs no length hypothesis: a `bltList` between
lists of different lengths is `false` in both directions. -/
theorem Term.blt_asymm (s t : Term) (h : Term.blt s t = true) : Term.blt t s = false := by
  match s, t with
  | .lit (.int m), .lit (.int n) =>
    rw [Term.blt_lit_lit] at h
    rw [Term.blt_lit_lit, decide_eq_false_iff_not]
    simp only [decide_eq_true_eq] at h
    omega
  | .lit _, .app _ _ => rfl
  | .app _ _, .lit _ => simp at h
  | .app f as, .app g bs =>
    rw [Term.blt_app_app] at h
    rw [Term.blt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl)] at h
      rw [if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf)] at h
        rw [if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.bltList_asymm as bs h
      · rw [if_pos hf] at h
        rw [if_pos (Ne.symm hf), decide_eq_false_iff_not]
        simp only [decide_eq_true_eq] at h
        exact String.lt_asymm h
    · rw [if_pos hl] at h
      rw [if_pos (Ne.symm hl), decide_eq_false_iff_not]
      simp only [decide_eq_true_eq] at h
      omega

theorem Term.bltList_asymm (as bs : List Term) (h : Term.bltList as bs = true) :
    Term.bltList bs as = false := by
  match as, bs with
  | [], _ => simp at h
  | _ :: _, [] => simp at h
  | a :: as, b :: bs =>
    rw [Term.bltList_cons_cons] at h
    rw [Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h
      rw [if_pos hab.symm]
      exact Term.bltList_asymm as bs h
    · rw [if_neg hab] at h
      rw [if_neg (Ne.symm hab)]
      exact Term.blt_asymm a b h

end

mutual

/-- Totality. `bltList` gets the length hypothesis `blt` guarantees at every call. -/
theorem Term.blt_total (s t : Term) (h : s ≠ t) :
    Term.blt s t = true ∨ Term.blt t s = true := by
  match s, t with
  | .lit (.int m), .lit (.int n) =>
    have hmn : m ≠ n := fun hmn => h (by rw [hmn])
    have : m < n ∨ n < m := by omega
    rcases this with hh | hh
    · exact Or.inl (by simp [hh])
    · exact Or.inr (by simp [hh])
  | .lit _, .app _ _ => exact Or.inl (by simp)
  | .app _ _, .lit _ => exact Or.inr (by simp)
  | .app f as, .app g bs =>
    rw [Term.blt_app_app, Term.blt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl), if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf), if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.bltList_total as bs hl fun hab => h (by rw [hab])
      · rw [if_pos hf, if_pos (Ne.symm hf)]
        simp only [decide_eq_true_eq]
        by_cases hfg : f < g
        · exact Or.inl hfg
        · refine Or.inr ?_
          by_contra hgf
          exact hf (String.le_antisymm (String.not_lt.mp hgf) (String.not_lt.mp hfg))
    · rw [if_pos hl, if_pos (Ne.symm hl)]
      simp only [decide_eq_true_eq]
      omega

theorem Term.bltList_total (as bs : List Term) (hlen : as.length = bs.length)
    (h : as ≠ bs) : Term.bltList as bs = true ∨ Term.bltList bs as = true := by
  match as, bs with
  | [], [] => exact absurd rfl h
  | [], _ :: _ => simp at hlen
  | _ :: _, [] => simp at hlen
  | a :: as, b :: bs =>
    rw [Term.bltList_cons_cons, Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab.symm]
      subst hab
      exact Term.bltList_total as bs (by simpa using hlen) fun hh => h (by rw [hh])
    · rw [if_neg hab, if_neg (Ne.symm hab)]
      exact Term.blt_total a b hab

end

mutual

/-- Transitivity. The only case that needs asymmetry is the list one: `a ≠ c` has to be
derived from `blt a b` and `blt b c` before the lexicographic step can fire. -/
theorem Term.blt_trans (s t u : Term) (h₁ : Term.blt s t = true)
    (h₂ : Term.blt t u = true) : Term.blt s u = true := by
  match s, t, u with
  | .lit (.int m), .lit (.int n), .lit (.int p) =>
    rw [Term.blt_lit_lit] at h₁ h₂ ⊢
    simp only [decide_eq_true_eq] at h₁ h₂ ⊢
    omega
  | .lit _, .lit _, .app _ _ => simp
  | .lit _, .app _ _, .lit _ => simp at h₂
  | .lit _, .app _ _, .app _ _ => simp
  | .app _ _, .lit _, _ => simp at h₁
  | .app _ _, .app _ _, .lit _ => simp at h₂
  | .app f as, .app g bs, .app e cs =>
    rw [Term.blt_app_app] at h₁ h₂
    rw [Term.blt_app_app]
    by_cases hab : as.length = bs.length
    · rw [if_neg (not_not_intro hab)] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        rw [if_neg (not_not_intro (hab.trans hbc))]
        by_cases hfg : f = g
        · rw [if_neg (not_not_intro hfg)] at h₁
          by_cases hge : g = e
          · rw [if_neg (not_not_intro hge)] at h₂
            rw [if_neg (not_not_intro (hfg.trans hge))]
            subst hfg; subst hge
            exact Term.bltList_trans as bs cs h₁ h₂
          · rw [if_pos hge] at h₂
            have hfe : f ≠ e := by rintro rfl; exact hge hfg.symm
            rw [if_pos hfe]
            subst hfg
            exact h₂
        · rw [if_pos hfg] at h₁
          by_cases hge : g = e
          · have hfe : f ≠ e := by rintro rfl; exact hfg hge.symm
            rw [if_pos hfe]
            subst hge
            exact h₁
          · rw [if_pos hge] at h₂
            simp only [decide_eq_true_eq] at h₁ h₂
            have hlt : f < e := String.lt_trans h₁ h₂
            have hfe : f ≠ e := by rintro rfl; exact String.lt_irrefl f hlt
            rw [if_pos hfe, decide_eq_true_eq]
            exact hlt
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
    · rw [if_pos hab] at h₁
      simp only [decide_eq_true_eq] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega

theorem Term.bltList_trans (as bs cs : List Term) (h₁ : Term.bltList as bs = true)
    (h₂ : Term.bltList bs cs = true) : Term.bltList as cs = true := by
  match as, bs, cs with
  | [], _, _ => simp at h₁
  | _ :: _, [], _ => simp at h₁
  | _ :: _, _ :: _, [] => simp at h₂
  | a :: as, b :: bs, c :: cs =>
    rw [Term.bltList_cons_cons] at h₁ h₂
    rw [Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h₁
      by_cases hbc : b = c
      · rw [if_pos hbc] at h₂
        rw [if_pos (hab.trans hbc)]
        exact Term.bltList_trans as bs cs h₁ h₂
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by rintro rfl; exact hbc hab.symm
        rw [if_neg hac, hab]
        exact h₂
    · rw [if_neg hab] at h₁
      by_cases hbc : b = c
      · have hac : a ≠ c := by rintro rfl; exact hab hbc.symm
        rw [if_neg hac, ← hbc]
        exact h₁
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by
          rintro rfl
          rw [Term.blt_asymm a b h₁] at h₂
          simp at h₂
        rw [if_neg hac]
        exact Term.blt_trans a b c h₁ h₂

end

/-- `Term.blt` is a strict linear order. Needed for `ordering-min`/`ordering-max` to be
a deterministic choice, and for "keep the smaller side" to descend. -/
theorem Term.blt_linear : (∀ s t : Term, Term.blt s t = true → Term.blt t s = false) ∧
    (∀ s t : Term, s ≠ t → Term.blt s t = true ∨ Term.blt t s = true) ∧
    (∀ s t u : Term, Term.blt s t = true → Term.blt t u = true → Term.blt s u = true) :=
  ⟨Term.blt_asymm, Term.blt_total, Term.blt_trans⟩

/-! ### Invariants over the step relation

The shape every M11 safety theorem takes, and the reason termination and confluence are
*not* in the spec: an invariant holds at every reachable state, so a run that diverges
satisfies it throughout and a run that merges in a different order satisfies it too.
"Every proof row the encoding writes is checker-valid" is one of these. -/
/-- Reachable states satisfy any invariant preserved by one command. -/
theorem invariant_of_step {I : Database → Prop}
    (hstep : ∀ db c db', I db → CmdStep db c db' → I db')
    {db db' : Database} {p : Program} (hinit : I db) (h : ProgramStep db p db') :
    I db' := by
  induction h with
  | nil => exact hinit
  | cons hc _ ih => exact ih (hstep _ _ _ hinit hc)

/-- **Every command only adds.**

The formal content of "never delete a term row or a proof row", which the encoding
depends on and which the invariant argument needs: anything the checker reads is
positive in the state, so once true it stays true. `.rule` and `.decl` touch only
fields `Contained` ignores.

`CmdStep` is a `def` now — an effect followed by a merge phase — so the case split is on
the command rather than on the step. -/
theorem RunStep.contained {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db.Contained db' :=
  Database.Contained.trans (Database.Contained.sUnion _ _) (MergeClosure.contained h)

theorem RunReach.contained {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : db.Contained d :=
  RunReach.induction (P := fun x => db.Contained x)
    (fun _ _ hp hs => hp.trans hs.contained) h (Database.Contained.refl _)

theorem CmdStep.contained {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db.Contained db' := by
  obtain ⟨d, hreach, hcl⟩ := h
  refine Database.Contained.trans ?_ (MergeClosure.contained hcl)
  cases c with
  | saturate R => exact RunReach.contained (show SaturateReach R db d from hreach).1
  | action a => exact evalAction_contained hreach
  | rule r =>
    replace hreach : cmdEffect db (.rule r) = some d := hreach
    rw [cmdEffect, Option.some.injEq] at hreach; subst hreach; exact ⟨subset_rfl⟩
  | run R =>
    replace hreach : cmdEffect db (.run R) = some d := hreach
    rw [cmdEffect, Option.some.injEq] at hreach
    subst hreach; exact Database.Contained.sUnion _ _
  | decl f dc =>
    replace hreach : cmdEffect db (.decl f dc) = some d := hreach
    rw [cmdEffect, Option.some.injEq] at hreach; subst hreach; exact ⟨subset_rfl⟩

theorem ProgramStep.contained {db db' : Database} {p : Program}
    (h : ProgramStep db p db') : db.Contained db' := by
  induction h with
  | nil => exact Database.Contained.refl _
  | cons hc _ ih => exact (CmdStep.contained hc).trans ih

/-! ### Determinism

Demoted. Confluence is not needed by any safety theorem — see `invariant_of_step`. It
buys one thing only: strengthening M10's refinement from "the interpreter's result is
spec-reachable" to an equality. -/
/-! **Evaluation reads the database only through its signature**, which after M12 is
literally the type of `Expr.eval`: with one evaluator taking a `Signature`, "two databases
with the same signature admit the same evaluations" is a rewrite rather than a theorem.
Monotonicity in `Contained` — half of what a diamond proof for `MergeStep` needs, see
`MergeStep.diamond_of_join` — follows the same way. -/

/-- A saturated state is a fixpoint of the whole closure, not only of one step. -/
theorem MergeSaturated.closure_eq {db d : Database} (hs : MergeSaturated db)
    (h : MergeClosure db d) : d = db := by
  induction h with
  | refl => rfl
  | @tail _ _ _ hstep ih => subst ih; exact hs _ hstep

/-- **Two saturated states of one merge closure coincide.** With a confluent merge the
saturated states a command's merge phase can reach are the same state, so an interpreter
that runs merges to a fixpoint computes the one answer the specification allows that
egglog also allows.

The hypothesis is `Relation.church_rosser`'s: one of the two joining paths has to be at
most a *single* step.

`MergeStep.diamond_of_join` used to stand beside this as the lemma that would discharge
`hdiamond`; it is **deleted**, because its `hjoin` was vacuous — instantiate
`le := fun _ _ => False` and `db.Current le f as v` unfolds to a self-contradiction, so
`hjoin` held for every `db` and the statement was unconditional local confluence.
Unconditional local confluence may well be true — a step's *effect* is fixed by the
evaluation, which reads only `sig`, so it stays available in a larger database — but the
diamond needs the result pinned to the join, and `evalActions_mono` gives only the
existential form.

`RunStep.unique_of_confluent` went with `RunStep`, which no longer exists. -/
theorem MergeClosure.unique_of_diamond {db d₁ d₂ : Database}
    (hdiamond : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', Relation.ReflGen MergeStep e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : MergeClosure db d₁) (h₂ : MergeClosure db d₂) : d₁ = d₂ := by
  obtain ⟨e, he₁, he₂⟩ := Relation.church_rosser hdiamond h₁ h₂
  exact (hs₁.closure_eq he₁).symm.trans (hs₂.closure_eq he₂)

/-! ### Fewer rows mean fewer matches

The other half of the containment contract. `mergeRound_confined` says the implementation
deletes only what it may; this says that deleting can only *lose* results, never invent
them — there is no negation anywhere in the fragment, so every premise of a match is
positive in the state. Together they are "the implementation may find fewer results, never
more", which is the safe direction for M11: a safety property is positive in the state, so
it transfers downward. `Database.Contained`'s `addTerm_mono` family, in
`Proofs/Database.lean`, is what carries a match along. -/
theorem ValidEnv.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => h.terms (hv.2 b hb)⟩

/-- **A larger database admits every match a smaller one does.** Read contrapositively —
which is how the containment contract uses it — a database missing entries finds at most
the matches the full one finds.

All three atoms read the same way now: the pattern's instance is congruent, in the
database extended by that instance, to a term the database holds. So each case is
`congOn_mono` and the re-evaluation of the operands under the same signature. -/
theorem ValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    (henv : d₂.env = d₁.env) {p : Pattern} {σ : Env} (h : ValidSubst d₁ p σ) :
    ValidSubst d₂ p σ := by
  refine ⟨by rw [henv]; exact h.1.mono hc, ?_⟩
  cases h.2 with
  | expr hw he hcong =>
    exact .expr (hc.terms hw) (by rw [henv, ← hsig]; exact he) (congOn_mono hc hcong)
  | eq hw he₁ he₂ hc₁ hc₂ =>
    exact .eq (hc.terms hw) (by rw [henv, ← hsig]; exact he₁)
      (by rw [henv, ← hsig]; exact he₂) (congOn_mono hc hc₁) (congOn_mono hc hc₂)
  | values hw ht hu hcong =>
    exact .values (hc.terms hw) (by rw [henv, ← hsig]; exact ht)
      (by rw [henv, ← hsig]; exact hu) (congOn_mono hc hcong)

theorem ValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {q : Query} {σ : Env}
    (h : ValidQuerySubst d₁ q σ) : ValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, hall.imp fun _ _ hv => ValidSubst.mono hc hsig henv hv, hu⟩

/-! ### There is no same-`σ` transport along `Recorded`

`ValidEnv.mono_recorded`, `ValidSubst.mono_recorded` and `ValidQuerySubst.mono_recorded`
are **deleted**, because they are false and not merely unproved.

`ValidEnv vars d₂ σ` asks that each of `σ`'s values be a term `d₂` holds, and `Recorded`
does not give that — it gives a *congruent* term. `Cong.mono_recorded`'s counterexample is
already a witness: `d₁.eqs = {(F c, F c)}`, `d₂.eqs = {(F e, F e), (c, e)}`, the query
`[.expr (.var "x")]` and `σ = [("x", F c)]`. `ValidQuerySubst d₁ q σ` holds with `F c` as
its own witness, and `F c ∉ d₂.terms`.

The replacement has to be `σ` with each **value** replaced by a congruent one, keeping the
domain and its order. Against that form the consumers split three ways.

*Indifferent*, because `σ` is existentially quantified before they see it, so they only
compose: `RunRules.mono_recorded`, `CmdStep.mono_recorded`, `ProgramStep.mono_recorded`,
`execCmdM_contained'`, `execProgramM_contained_aux`.

*Needs the choice made once for the whole query*: a per-pattern transport re-establishing
`Env.UnionAll σs σ`, whose `Union2` requires the pieces to agree wherever two of them bind
the same variable; per-pattern transports may pick different congruent representatives. The
answer is a single witness **function** `Term → Term` rather than a witness per use site —
then equal terms get equal images and `Union2` still joins.

*Costs a lemma that is false*: `RuleResults.mono_recorded`. It re-evaluates under the
substitution, and `Expr.eval` is **not** congruence-stable at `ordering-min`/`ordering-max`,
which choose by `Term.blt`. It *is* stable at `min`/`max`, which answer only on literals
(`Prim.apply_cong`), so restricting the transported positions to ordering-free expressions
is a fix — and it is a fix for `MergeStep.transport_recorded` too, whose body runs under a
`mergeEnv` that `Recorded` may have moved: a moved environment is congruent, and congruent
environments give congruent results.

This file carries both fixes. On a **diagonal** recorder there is no congruent-but-distinct
term for any of this to go wrong at, so `Database.Recorded.contained_of_diag` hands both
lemmas back to `ValidQuerySubst.mono` and `MergeStep.transport` above, and
`Program.UnionFree` is what keeps every reachable state diagonal. Under
`Program.OrderingFree` the substitution is instead *moved*, by the single witness function
of `exists_witness`, and `Env.mapVals` keeps `Env.Union2` joinable because equal terms get
equal images. -/

/-! ### Transporting a step

A step's *effect* is fixed by the evaluation witnesses it carries, and those witnesses
depend on the state only through `sig` and on the environment only through
`Env.lookup`. Two transports follow, and the containment contract spends both.

Along `Contained`: the same block re-run on a larger state lands on a state containing
the smaller run's result. That is `evalActions_mono`, and it is the weak — but
sufficient — form of what `MergeStep.diamond_of_join` wants.

Along `Env.Agree`: two environments no `lookup` can tell apart give runs differing only
in the `env` field, which `Database.EnvAgree.eq_of_env_rules` then collapses once the
caller's environment is restored. This is `Proofs/Eval.lean`'s `evalActions_envAgree`
for the relational semantics, and it is what lets a rule fire under the substitution the
specification admits rather than the one the enumerator emitted. -/

/-- Agreement survives a shared innermost binding, which is the `letBind` case of
`evalAction_envAgree`. -/
theorem Env.Agree.cons {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (w : Var) (t : Term) :
    Env.Agree ((w, t) :: σ₁) ((w, t) :: σ₂) := by
  intro v
  simp only [Env.lookup_cons]
  split
  · rfl
  · exact h v

/-- `EnvAgree` fixes `eqs`, so it is `Contained` in both directions. This is how the
`Contained`-indexed monotonicity lemmas apply to it. -/
theorem Database.EnvAgree.contained {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) :
    d₁.Contained d₂ :=
  ⟨fun _ hx => h.eqs ▸ hx⟩

/-- The `union` case of `evalAction_envAgree`; companion of
`Database.EnvAgree.addTerm` and `.addRow` in `Proofs/Database.lean`. -/
theorem Database.EnvAgree.addEq {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (a b : Term) :
    (d₁.addEq a b).EnvAgree (d₂.addEq a b) :=
  let h' := (h.addTerm a).addTerm b
  ⟨h'.sig, by simp only [Database.addEq]; rw [h'.eqs], h'.rules, h'.env⟩

/-- `evalActions_envAgree` in the shape the transports use: a run under one environment
gives a run under any environment agreeing with it. -/
theorem evalActions_envAgree_exists {d₁ d₂ c : Database} (h : d₁.EnvAgree d₂)
    {as : List Action} (hs : evalActions d₁ as = some c) :
    ∃ c', evalActions d₂ as = some c' ∧ c.EnvAgree c' := by
  have hrel := evalActions_envAgree h as
  rw [hs] at hrel
  cases hx : evalActions d₂ as with
  | none => rw [hx] at hrel; cases hrel
  | some c' => rw [hx] at hrel; cases hrel with | some hc => exact ⟨c', rfl, hc⟩

/-- **An action available at `db` is available at any `D` containing it, with the same
effect.** The result is an existential over a database containing the smaller one, not
the exact join `MergeStep.diamond_of_join` asks for; the evaluation reads only `sig` and
`env`, which is what makes the witnesses survive. -/
theorem evalAction_mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {a : Action}
    (h : evalAction db a = some d) :
    ∃ D', evalAction D a = some D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  rcases evalAction_eq_some h with ⟨e, t, rfl, hv, rfl⟩ | ⟨v, e, t, rfl, hv, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, hlit, rfl⟩ | ⟨f, args, out, as, vs, rfl, hv₁, hv₂, rfl⟩
  · refine ⟨D.addTerm t, ?_, hc.addTerm_mono t, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · simpa using hsig
    · simpa using henv
  · refine ⟨{ D.addTerm t with env := (v, t) :: D.env }, ?_, ?_, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · exact ⟨(hc.addTerm_mono t).eqs⟩
    · simpa using hsig
    · simp [henv]
  · refine ⟨D.addEq t₁ t₂, ?_, hc.addEq_mono t₁ t₂, ?_, ?_⟩
    · simp only [not_or, Bool.not_eq_true] at hlit
      simp [evalAction, ← hsig, ← henv, hv₁, hv₂, hlit.1, hlit.2]
    · simpa using hsig
    · simpa using henv
  · refine ⟨D.addTerm (.app f (as ++ vs)), ?_, hc.addTerm_mono _, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv₁, hv₂]
    · simpa using hsig
    · simpa using henv

/-- `evalAction_mono` over a block: each step re-bases onto the previous one's larger
result. -/
theorem evalActions_mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {as : List Action}
    (h : evalActions db as = some d) :
    ∃ D', evalActions D as = some D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  induction as generalizing db D with
  | nil =>
    rw [evalActions_nil, Option.some.injEq] at h
    exact ⟨D, rfl, h ▸ hc, h ▸ hsig, h ▸ henv⟩
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      obtain ⟨D₀, hD₀, hc₀, hs₀, he₀⟩ := evalAction_mono hc hsig henv hv
      obtain ⟨D₁, hD₁, hc₁, hs₁, he₁⟩ := ih hc₀ hs₀ he₀ h
      exact ⟨D₁, by rw [evalActions_cons, hD₀, Option.bind_some]; exact hD₁, hc₁, hs₁, he₁⟩

/-- `evalAction_mono` along `Recorded`. An action never *reads* a row — `Expr.eval` takes
only a signature — so the proof is the `Contained` one with `Database.Recorded`'s
`addTerm`/`addEq`/`addRow` monotonicity in place of `Contained`'s. -/
theorem evalAction_mono_recorded {db D d : Database} (hc : db.Recorded D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {a : Action}
    (h : evalAction db a = some d) :
    ∃ D', evalAction D a = some D' ∧ d.Recorded D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  rcases evalAction_eq_some h with ⟨e, t, rfl, hv, rfl⟩ | ⟨v, e, t, rfl, hv, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, hlit, rfl⟩ | ⟨f, args, out, as, vs, rfl, hv₁, hv₂, rfl⟩
  · refine ⟨D.addTerm t, ?_, hc.addTerm_mono t, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · simpa using hsig
    · simpa using henv
  · refine ⟨{ D.addTerm t with env := (v, t) :: D.env }, ?_, ?_, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · exact (hc.addTerm_mono t).setEnv _ _
    · simpa using hsig
    · simp [henv]
  · refine ⟨D.addEq t₁ t₂, ?_, hc.addEq_mono t₁ t₂, ?_, ?_⟩
    · simp only [not_or, Bool.not_eq_true] at hlit
      simp [evalAction, ← hsig, ← henv, hv₁, hv₂, hlit.1, hlit.2]
    · simpa using hsig
    · simpa using henv
  · refine ⟨D.addTerm (.app f (as ++ vs)), ?_, hc.addTerm_mono _, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv₁, hv₂]
    · simpa using hsig
    · simpa using henv

/-- `evalActions_mono` along `Recorded`. -/
theorem evalActions_mono_recorded {db D d : Database} (hc : db.Recorded D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {as : List Action}
    (h : evalActions db as = some d) :
    ∃ D', evalActions D as = some D' ∧ d.Recorded D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  induction as generalizing db D with
  | nil =>
    rw [evalActions_nil, Option.some.injEq] at h
    exact ⟨D, rfl, h ▸ hc, h ▸ hsig, h ▸ henv⟩
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      obtain ⟨D₀, hD₀, hc₀, hs₀, he₀⟩ := evalAction_mono_recorded hc hsig henv hv
      obtain ⟨D₁, hD₁, hc₁, hs₁, he₁⟩ := ih hc₀ hs₀ he₀ h
      exact ⟨D₁, by rw [evalActions_cons, hD₀, Option.bind_some]; exact hD₁, hc₁, hs₁, he₁⟩

/-- **A merge collision available at `A` is available at any `C` containing it.**

No `env`/`rules` hypothesis is needed: a `MergeStep` overwrites the environment with
`mergeEnv a b` before running the body and restores the caller's `env`/`rules`
afterwards, so neither field is ever read. `sig` is needed, because `CongList.mono` is.
-/
theorem MergeStep.transport {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (h : MergeStep A B) : ∃ D, MergeStep C D ∧ B.Contained D ∧ B.sig = D.sig := by
  cases h with
  | @collide dA f dc as bs a b vs body res hdc hmg hla hlb hra hrb hcong hbody hres =>
    have hc0 : ({ A with env := mergeEnv a b } : Database).Contained
        { C with env := mergeEnv a b } := ⟨hc.eqs⟩
    obtain ⟨dC, hstepC, hcont, hsig', henv'⟩ := evalActions_mono hc0 hsig rfl hbody
    refine ⟨{ dC.addTerm (.app f (as ++ vs)) with env := C.env, rules := C.rules },
      .collide (by rw [← hsig]; exact hdc) hmg hla hlb (hc.terms hra) (hc.terms hrb)
        (CongList.mono hc hcong) hstepC (hsig' ▸ henv' ▸ hres), ?_, ?_⟩
    · exact ⟨(hcont.addTerm_mono (.app f (as ++ vs))).eqs⟩
    · simpa using hsig'

/-- `MergeStep.transport` iterated: a closure from `A` re-bases onto one from any `C`
containing `A`. This is the composition step of `mergeSaturateF_contained`. -/
theorem MergeClosure.transport {A C B : Database} (hc : A.Contained C)
    (hsig : A.sig = C.sig) (h : MergeClosure A B) :
    ∃ D, MergeClosure C D ∧ B.Contained D ∧ B.sig = D.sig := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, hc, hsig⟩
  | tail _ hstep ih =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ := ih
    obtain ⟨D', hstepD', hcont', hsig'⟩ := hstep.transport hcontD hsigD
    exact ⟨D', hclD.tail hstepD', hcont', hsig'⟩

/-! ### The interpreter

`Impl/Merge.lean` runs the M9 semantics. The refinement is weaker than `exec`'s on
purpose: with a `:merge` function in play the spec admits several results, so the
interpreter's is one of them rather than *the* one. -/
/-- **The constructor interpreter lands where the specification does.** `exec_programStep`
proves the two directions at once; this is the half the merge interpreter below cannot
have, kept under its own name because that contrast is the point.

**The one hypothesis**, not removable: `Program.CtorDecls` gives
`Signature.AllConstructors` at every intermediate state
(`Signature.AllConstructors.sigBind`), which is what makes `MergeStep` vacuous and so how
the `MergeClosure` phase of `CmdStep.action` gets discharged
(`MergeClosure.eq_of_allConstructors`). `Falsity.exec_programStep_needs_ctorDecls` is the
witness that dropping it is false. -/
theorem execM_reachable {p : Program} {d : FDatabase} (hdecl : p.CtorDecls)
    (h : exec p = some d) :
    ProgramStep FDatabase.empty.toDatabase p d.toDatabase := by
  rw [FDatabase.toDatabase_empty]
  exact (exec_programStep hdecl (by rw [h]; simp)).mp (by rw [h, Option.map_some])

/-! ### The contract for `execM`: containment, not reachability

`execM_reachable`'s shape is unavailable for `execM`, and not because it is hard —
because it is **false**. The implementation's merge phase deletes the rows it merged and
the specification never deletes, so no `ProgramStep` state equals the implementation's:
a spec run that performed the same merges still holds the two originals, and a spec run
that performed none holds no combined row. `execM_reachable` above survives only because
`exec` is `Impl/Interp.lean`'s constructor interpreter, which has no merge phase at all
(`FDatabase.mergeRound_eq_self` and `hasMergeRow_eq_false`) — the layering is intact.

What replaces it is that every row the implementation holds is one the specification
*records* — `Database.Recorded` — so the implementation may find **fewer** results, never
more. That is the safe direction, because everything the M11 safety theorem reads is
positive in the state, so safety transfers downward. `ValidSubst.mono_recorded` is the
step that makes "fewer rows" mean "fewer matches" rather than merely "a different
database".

Two things push the contract off plain `Database.Contained`, and each buys one clause of
`Recorded`. The **deletion** adds the obligation that the witness `db` can be chosen to
have performed *at least* the merges the implementation did, which is where
`MergeClosure`'s freedom to take any number of steps is spent. The **rebuild** moves a row
onto the canonical key of its class, where no specification row is, so the row clause has
to be read through `Database.Out` — which searches the class and therefore sees it. Nothing
semantically new is claimed: `Out` is the only read there is.

#### The refinement chain

A step-by-step account of the merge interpreter against the merge specification. It runs
from `Inv` preservation through evaluation, actions and matching to containment, and it
is proved all the way to `execM_contained` — under `Program.UnionFree`, which is what the
two `Recorded` transports the file header lists need and which they carry up the chain.
What is *not* here at all is completeness — see "Two statements removed rather than
carried" below.

`execCmdM_contained` was once false, and the defect was in the *specification*:
`CmdStep.action` had no merge phase and `execCmdM` runs one, so the interpreter reached a
state holding a merge result no `CmdStep` state held. `CmdStep.action` now carries a
`MergeClosure`, which is what egglog does — a bare top-level action is compiled into a
one-rule run and every rule-set run ends in `merge_all`.

The chain needs no bridge at the congruence step, and that is the point of keeping one
relation: `patternHolds` compares keys with `congrKeys` at the closure of the database
extended with the atom's operands, `closureF` closes over `eqsF` and `congrPair` with no
notion of a row, and the specification's row atom compares them with the same `Cong`.

What the induction does have to carry is `Inv` — the well-formedness the merge passes
consume. Prove its preservation lemmas first; the rest of the chain is structural
recursion once they are available. -/

/-! ### The invariant the refinement chain carries

`Database.Inv0` is gone: it existed to state the `sig`/`terms`/`rows` half of `FDatabase.Inv`
on a spec database and transport it through the `toDatabase_*` bridges, and there is no such
half any more. `rows` is an index over `FDatabase`, not a component of the denotation, so
what has to be said about it is a property of the `FDatabase` and is said here directly. -/

/-- `env` and `rules` are invisible to `WF`, as they are to `Cong`. -/
theorem Database.WF.setEnvRules {db : Database} (hw : db.WF) {σ : Env} {R : Set Rule}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) :
    ({ db with env := σ, rules := R } : Database).WF := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun b hb => ?_, hw.litsIsolated⟩
  · rw [Database.terms_setEnvRules] at ht; exact hw.eqsRefl t ht
  · rw [Database.terms_setEnvRules] at ht ⊢; exact hw.subtermClosed t ht
  · rw [Database.terms_setEnvRules]; exact hσ b hb

/-- Membership in `terms` reads only `eqs`. -/
theorem Database.mem_terms_of_eqs {d₁ d₂ : Database} (h : d₁.eqs ⊆ d₂.eqs) {t : Term}
    (ht : t ∈ d₁.terms) : t ∈ d₂.terms := Cong.mono ⟨h⟩ ht

/-- **`Out` at a row's own key.** The only reflexivity `Out` has: `CongList` is reflexive
exactly on terms the database holds. -/
theorem Database.out_self {db : Database} {f : FnName} {as vs : List Term}
    (hmem : Term.app f (as ++ vs) ∈ db.terms) (hargs : ∀ a ∈ as, a ∈ db.terms) :
    db.Out f as vs := ⟨as, CongList.refl hargs, hmem⟩

/-! ### The column widths

`Action.SetLegal` asks that a `set`'s head be a merge function and says nothing about how
many columns it writes. `MergeStep.collide` carries two `arity` premises — without them the
key/value split `key = []` fires every entry of `f` against every other — so the widths have
to come from somewhere, and the only place they can come from is the front end.
`Impl/Check.lean`'s `arityOk` is where egglog checks them.

**This is a hypothesis the refinement chain did not carry before**, because before the split
there was nothing to split: a row was `⟨f, as, vs⟩` and `MergeStep` read the two halves off
it. It is threaded as `Action.SetWidthOk`, bundled with `Action.SetLegal` into
`Action.WriteLegal`, and it is what `FDatabase.IndexOk.width` records.

It is the `set` clause of `Spec/Scope.lean`'s `Action.WidthOk` and **not** that check:
`Action.WidthOk` also constrains every application inside an *expression*, and that half is
not preserved by `Function.update` at a fresh name — an action applying an as-yet
undeclared `f` satisfies it vacuously and stops satisfying it the moment `f` is declared,
which would make `Action.WriteLegal.update` false. The interpreter's chain needs a check
that survives a declaration, so it carries only the clause it spends. -/
def Action.SetWidthOk : Action → Signature → Prop
  | .set f args out, sig =>
      ∀ dc, sig f = some dc → args.length = dc.arity ∧ out.length = dc.outArity
  | _, _ => True

@[simp] def Actions.SetWidthOk : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetWidthOk sig ∧ Actions.SetWidthOk as sig

/-- `Action.SetLegal` and `Action.SetWidthOk` together: a `set` writes a merge function's
table, at that declaration's column widths. -/
def Action.WriteLegal (a : Action) (sig : Signature) : Prop :=
  a.SetLegal sig ∧ a.SetWidthOk sig

@[simp] def Actions.WriteLegal (as : List Action) (sig : Signature) : Prop :=
  Actions.SetLegal as sig ∧ Actions.SetWidthOk as sig

@[simp] def Cmd.WriteLegal : Cmd → Signature → Prop
  | .action a, sig => a.WriteLegal sig
  | .rule r, sig => Actions.WriteLegal r.actions sig
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

theorem Actions.WriteLegal.head {a : Action} {as : List Action} {sig : Signature}
    (h : Actions.WriteLegal (a :: as) sig) : a.WriteLegal sig := ⟨h.1.1, h.2.1⟩

theorem Actions.WriteLegal.tail {a : Action} {as : List Action} {sig : Signature}
    (h : Actions.WriteLegal (a :: as) sig) : Actions.WriteLegal as sig := ⟨h.1.2, h.2.2⟩

/-- **The index is a faithful index of `terms`.**

Three clauses, because a constructor's row and a merge function's row are indexed
differently and `Database.Out` is provably wrong for the first of them.

`ctor` — a constructor has no value column (`FnDecl.entryWidth` is its `arity`), so its row
is `⟨f, as, []⟩` and the term it indexes is the application `f(as)` itself. Reading it
through `Out` would ask for `f(as ++ [])`'s *value* columns and there are none.

`entry` — a merge function's row is read up to congruence on its key, which is exactly what
`FDatabase.rebuild` needs: a rebuild moves a row onto its class's canonical key and adds no
term, so the entry term stays where it was and only `Out` still finds it.

`width` — the key/value split `MergeStep.collide` asks for. -/
structure FDatabase.IndexOk (d : FDatabase) : Prop where
  ctor : ∀ r ∈ d.rows, d.sig.mergeOf r.fn = none →
    r.out = [] ∧ Term.app r.fn r.args ∈ d.terms
  entry : ∀ r ∈ d.rows, d.sig.mergeOf r.fn ≠ none →
    d.toDatabase.Out r.fn r.args r.out
  width : ∀ r ∈ d.rows, ∀ dc, d.sig r.fn = some dc → d.sig.mergeOf r.fn ≠ none →
    r.args.length = dc.arity ∧ r.out.length = dc.outArity

/-- The invariant the refinement chain carries: the denotation is well formed, the equation
list names only terms the term list holds, and the index is faithful.

`ctorTerms`, `rowsComplete` and `rowsWF` are gone with their subjects. `WF.subtermClosed`
absorbs `rowsWF`: an entry *is* a term now, so its key and value columns are subterms of a
term the database holds and are held themselves. `eqs` is the one field the five-field
version did not have; it is what every `toDatabase_*` bridge needs, and carrying it here is
what keeps it off the statements of `execCmdM_contained` and `execM_contained`. -/
structure FDatabase.Inv (d : FDatabase) : Prop where
  wf : d.WF
  eqs : d.EqsInTerms
  index : d.IndexOk

namespace FDatabase

/-- A row of `ctorRowList` is a constructor row of a subterm. -/
theorem mem_ctorRowList {sig : Signature} {t : Term} {r : Row}
    (h : r ∈ Term.ctorRowList sig t) :
    r.out = [] ∧ sig.mergeOf r.fn = none ∧ Term.app r.fn r.args ∈ t.subtermList := by
  rw [Term.ctorRowList, List.mem_filterMap] at h
  obtain ⟨s, hs, hr⟩ := h
  cases s with
  | lit l => exact absurd hr (by simp)
  | app f as =>
    simp only at hr
    split at hr
    · exact absurd hr (by simp)
    · next hm =>
      rw [Option.some.injEq] at hr
      subst hr
      exact ⟨rfl, Option.not_isSome_iff_eq_none.mp (by simpa using hm), hs⟩

@[simp] theorem mem_addTerm_terms {d : FDatabase} {t s : Term} :
    s ∈ (d.addTerm t).terms ↔ s ∈ t.subtermList ∨ s ∈ d.terms := by
  simp [FDatabase.addTerm, List.mem_dedup]

@[simp] theorem mem_addTerm_rows {d : FDatabase} {t : Term} {r : Row} :
    r ∈ (d.addTerm t).rows ↔ r ∈ Term.ctorRowList d.sig t ∨ r ∈ d.rows := by
  simp [FDatabase.addTerm, List.mem_dedup]

@[simp] theorem addTerm_sig {d : FDatabase} {t : Term} : (d.addTerm t).sig = d.sig := rfl

/-- `IndexOk` reads `sig`, `terms`, `rows` and `eqs`; `env` and `rules` may be replaced
freely. -/
theorem IndexOk.setEnvRules {d : FDatabase} (h : d.IndexOk) (σ : Env) (rs : List Rule) :
    ({ d with env := σ, rules := rs } : FDatabase).IndexOk where
  ctor := h.ctor
  entry := fun r hr hm =>
    Database.Out.mono (⟨subset_rfl⟩ : d.toDatabase.Contained
      ({ d with env := σ, rules := rs } : FDatabase).toDatabase) (h.entry r hr hm)
  width := h.width

theorem WF.setEnvRules {d : FDatabase} (h : d.WF) {σ : Env} {rs : List Rule}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ({ d with env := σ, rules := rs } : FDatabase).WF := by
  change ({ d.toDatabase with env := σ, rules := { r | r ∈ rs } } : Database).WF
  refine ⟨fun t htm => ?_, fun t htm => ?_, fun b hb => ?_, h.litsIsolated⟩
  · rw [Database.terms_setEnvRules] at htm; exact h.eqsRefl t htm
  · rw [Database.terms_setEnvRules] at htm ⊢; exact h.subtermClosed t htm
  · rw [Database.terms_setEnvRules]; exact hσ b hb

theorem Inv.setEnv {d : FDatabase} (h : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ({ d with env := σ } : FDatabase).Inv where
  wf := h.wf.setEnvRules (rs := d.rules) hσ
  eqs := h.eqs
  index := h.index.setEnvRules σ d.rules

theorem Inv.setEnvRules {d : FDatabase} (h : d.Inv) {σ : Env} {rs : List Rule}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ({ d with env := σ, rules := rs } : FDatabase).Inv where
  wf := h.wf.setEnvRules hσ
  eqs := h.eqs
  index := h.index.setEnvRules σ rs

end FDatabase

theorem FDatabase.Inv.empty : FDatabase.empty.Inv where
  wf := FDatabase.empty_wf
  eqs := FDatabase.empty_eqsInTerms
  index := ⟨by simp [FDatabase.empty], by simp [FDatabase.empty], by simp [FDatabase.empty]⟩

@[simp] theorem FDatabase.addTerms_sig {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).sig = d.sig := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

/-- **`addTerm` needs no side condition.** It used to need `Term.CtorTerm`, because
`ctorTerms` demanded every application in `terms` be a constructor's; the invariant does not
say that any more, and `ctorRowList` filters a merge function's application out of the index
rather than synthesising a bogus row for it. -/
theorem FDatabase.Inv.addTerm {d : FDatabase} (h : d.Inv) (t : Term) :
    (d.addTerm t).Inv where
  wf := h.wf.addTerm h.eqs t
  eqs := h.eqs.addTerm t
  index := by
    have hcont : d.toDatabase.Contained (d.addTerm t).toDatabase := by
      rw [FDatabase.toDatabase_addTerm h.eqs]; exact Database.Contained.addTerm t d.toDatabase
    refine ⟨fun r hr hm => ?_, fun r hr hm => ?_, fun r hr dc hdc hm => ?_⟩
    · rcases FDatabase.mem_addTerm_rows.mp hr with hr' | hr'
      · obtain ⟨hout, -, hmem⟩ := FDatabase.mem_ctorRowList hr'
        exact ⟨hout, FDatabase.mem_addTerm_terms.mpr (Or.inl hmem)⟩
      · exact ⟨(h.index.ctor r hr' hm).1,
          FDatabase.mem_addTerm_terms.mpr (Or.inr (h.index.ctor r hr' hm).2)⟩
    · rcases FDatabase.mem_addTerm_rows.mp hr with hr' | hr'
      · exact absurd (FDatabase.mem_ctorRowList hr').2.1 hm
      · exact Database.Out.mono hcont (h.index.entry r hr' hm)
    · rcases FDatabase.mem_addTerm_rows.mp hr with hr' | hr'
      · exact absurd (FDatabase.mem_ctorRowList hr').2.1 hm
      · exact h.index.width r hr' dc hdc hm

theorem FDatabase.Inv.addTerms {d : FDatabase} (h : d.Inv) (ts : List Term) :
    (d.addTerms ts).Inv := by
  induction ts generalizing d with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem FDatabase.Inv.addEq {d : FDatabase} (h : d.Inv) (a b : Term)
    (hlit : a.isLit ∨ b.isLit → a = b) : (d.addEq a b).Inv where
  wf := h.wf.addEq h.eqs a b hlit
  eqs := h.eqs.addEq a b
  index := by
    have hbase := (h.addTerm a).addTerm b
    have hcont : ((d.addTerm a).addTerm b).toDatabase.Contained (d.addEq a b).toDatabase := by
      rw [FDatabase.toDatabase_addEq h.eqs,
        FDatabase.toDatabase_addTerm (h.eqs.addTerm a), FDatabase.toDatabase_addTerm h.eqs]
      exact ⟨Set.subset_insert _ _⟩
    refine ⟨fun r hr hm => hbase.index.ctor r hr hm, fun r hr hm => ?_,
      fun r hr dc hdc hm => hbase.index.width r hr dc hdc hm⟩
    exact Database.Out.mono hcont (hbase.index.entry r hr hm)

/-- `hf` is what keeps `ctor` true: a `set` on anything but a merge function would add a row
whose `out` is not `[]`, which is exactly what `Action.SetLegal` rules out. `hw` is
`Action.SetWidthOk`, and it is what `IndexOk.width` records. -/
theorem FDatabase.Inv.addRow {d : FDatabase} (h : d.Inv) {f : FnName} {as vs : List Term}
    (hf : d.sig.mergeOf f ≠ none)
    (hw : ∀ dc, d.sig f = some dc → as.length = dc.arity ∧ vs.length = dc.outArity) :
    (d.addRow f as vs).Inv := by
  have hbase : (d.addTerm (.app f (as ++ vs))).Inv := h.addTerm _
  have hmem : Term.app f (as ++ vs) ∈ (d.addTerm (.app f (as ++ vs))).toDatabase.terms := by
    rw [FDatabase.mem_toDatabase_terms]
    exact FDatabase.mem_addTerm_terms.mpr (Or.inl ((Term.mem_subtermList _).mpr (.refl _)))
  have hargs : ∀ x ∈ as, x ∈ (d.addTerm (.app f (as ++ vs))).toDatabase.terms := by
    intro x hx
    refine hbase.wf.subtermClosed _ hmem ?_
    exact Term.mem_subterms.mpr (Term.IsSubterm.arg (List.mem_append_left _ hx)
      (Term.IsSubterm.refl x))
  have hrow : ∀ {r : Row}, r ∈ (d.addRow f as vs).rows →
      r = ⟨f, as, vs⟩ ∨ r ∈ (d.addTerm (.app f (as ++ vs))).rows := by
    intro r hr
    exact List.mem_cons.mp (List.mem_dedup.mp hr)
  refine ⟨hbase.wf, hbase.eqs, ⟨fun r hr hm => ?_, fun r hr hm => ?_, fun r hr dc hdc hm => ?_⟩⟩
  · rcases hrow hr with rfl | hr'
    · exact absurd hm hf
    · exact hbase.index.ctor r hr' hm
  · rcases hrow hr with rfl | hr'
    · exact Database.out_self hmem hargs
    · exact hbase.index.entry r hr' hm
  · rcases hrow hr with rfl | hr'
    · exact hw dc hdc
    · exact hbase.index.width r hr' dc hdc hm

theorem FDatabase.Inv.execAction {d d' : FDatabase} (h : d.Inv) {a : Action}
    (hlegal : a.WriteLegal d.sig) (hs : execAction d a = some d') : d'.Inv := by
  match a with
  | .expr e =>
    simp only [Egglog.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, -, rfl⟩ := hs
    exact h.addTerm t
  | .letBind v e =>
    simp only [Egglog.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, -, rfl⟩ := hs
    have hbase := h.addTerm t
    refine hbase.setEnv ?_
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rw [FDatabase.mem_toDatabase_terms]
      exact FDatabase.mem_addTerm_terms.mpr (Or.inl ((Term.mem_subtermList _).mpr (.refl _)))
    · exact hbase.wf.envInTerms b hb
  | .union e₁ e₂ =>
    simp only [Egglog.execAction, Option.bind_eq_some_iff] at hs
    obtain ⟨t₁, -, t₂, -, hs⟩ := hs
    split at hs
    · simp at hs
    · rename_i hlit
      simp only [Option.some.injEq] at hs
      exact hs ▸ h.addEq t₁ t₂ (by simp_all)
  | .set f args out =>
    simp only [Egglog.execAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨ts, hts, vs, hvs, rfl⟩ := hs
    refine h.addRow hlegal.1 fun dc hdc => ?_
    obtain ⟨h₁, h₂⟩ := hlegal.2 dc hdc
    exact ⟨(Expr.evalList_length hts).trans h₁, (Expr.evalList_length hvs).trans h₂⟩

/-! #### Actions

There is nothing here any more. `Impl/Interp.lean`'s `execAction` and `execActions` are
the merge interpreter's action semantics too, and `Proofs/Interp.lean`'s
`execAction_toDatabase` already says they compute `evalAction`/`evalActions` — which
after M12 is what `CmdStep.action`, `RuleResults` and `MergeStep.collide` read. -/
/-- `execAction_toDatabase` in the `some` shape the merge proofs use. -/
theorem FDatabase.execAction_evalAction {d d' : FDatabase} (he : d.EqsInTerms) {a : Action}
    (hs : execAction d a = some d') : evalAction d.toDatabase a = some d'.toDatabase := by
  rw [← execAction_toDatabase he, hs, Option.map_some]

/-- `execActions_toDatabase` in the `some` shape the merge proofs use. -/
theorem FDatabase.execActions_evalActions {d d' : FDatabase} (he : d.EqsInTerms)
    {as : List Action} (hs : execActions d as = some d') :
    evalActions d.toDatabase as = some d'.toDatabase := by
  rw [← execActions_toDatabase he, hs, Option.map_some]

/-! #### Matching -/

/-- Positing a list of terms is contained in positing anything that has them all as
subterms. -/
theorem Database.addTerms_contained_of_subterms {db e : Database} {l : List Term}
    (hsub : db.eqs ⊆ e.eqs) (h : ∀ x ∈ l, ∀ s ∈ x.subterms, (s, s) ∈ e.eqs) :
    (db.addTerms l).Contained e := by
  induction l generalizing db with
  | nil => exact ⟨hsub⟩
  | cons x l ih =>
    refine ih ?_ (fun y hy => h y (by simp [hy]))
    rintro p (hp | ⟨t, ht, rfl⟩)
    · exact hsub hp
    · exact h x (by simp) t ht

/-- The database an entry atom's test closes over sits inside the one `Matches.values`
names: the atom adds its key and value operands separately, and the instance
`f(ts…, us…)` has every one of them as a subterm. -/
theorem Database.addTerms_contained_withOperands {db : Database} {f : FnName}
    {ts us : List Term} :
    ((db.addTerms ts).addTerms us).Contained
      (db.withOperands [Term.app f (ts ++ us)]) := by
  have hmem : ∀ x ∈ ts ++ us, ∀ s ∈ x.subterms,
      (s, s) ∈ (db.withOperands [Term.app f (ts ++ us)]).eqs := by
    intro x hx t ht
    exact Or.inr ⟨t, Term.IsSubterm.arg hx ht, rfl⟩
  have hfirst : (db.addTerms ts).Contained (db.withOperands [Term.app f (ts ++ us)]) :=
    Database.addTerms_contained_of_subterms
      (e := db.withOperands [Term.app f (ts ++ us)]) (fun p hp => Or.inl hp)
      (fun x hx => hmem x (by simp [hx]))
  exact Database.addTerms_contained_of_subterms hfirst.eqs
    (fun x hx => hmem x (by simp [hx]))

/-- **`patternHolds` is sound for `ValidSubst`.**

`Interp.lean`'s `patternHolds_iff` proves both directions, but only on the constructor
fragment — its entry-atom case reads `Signature.AllConstructors` off the signature. This is
the forward direction with a `:merge` function in play, and `FDatabase.IndexOk` is what
replaces that hypothesis: the row the scan found is either a constructor's, whose entry
term is the application itself (`IndexOk.ctor`), or a merge function's, whose entry term
sits at a congruent key (`IndexOk.entry`). Either way there is a term the database holds to
serve as `Matches`' witness.

`ValidEnv (p.freeVars d.env) d.toDatabase σ` is load-bearing, not decoration:
`patternHolds` reads `σ` only through `d.env ++ σ`, so a `σ` carrying bindings the pattern
never mentions still passes the test, while `ValidSubst`'s `ValidEnv` pins `Env.dom σ` to a
permutation of the pattern's free variables. -/
theorem FDatabase.patternHolds_validSubst {d : FDatabase} (h : d.Inv) {p : Pattern}
    {σ : Env} (hv : ValidEnv (p.freeVars d.env) d.toDatabase σ)
    (hs : patternHolds d p σ = true) : ValidSubst d.toDatabase p σ := by
  cases p with
  | expr e =>
    rw [patternHolds] at hs
    split at hs
    · exact absurd hs (by simp)
    · next t hev =>
      rw [decide_eq_true_eq] at hs
      obtain ⟨w, hwm, hcl⟩ := hs
      exact ⟨hv, .expr (FDatabase.mem_toDatabase_terms.mpr hwm) hev
        (congOn_singleton.mpr ((FDatabase.mem_closureF_addTerm h.eqs).mp hcl))⟩
  | eq e₁ e₂ =>
    rw [patternHolds] at hs
    split at hs
    · next t₁ t₂ hev₁ hev₂ =>
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hs
      obtain ⟨heq, w, hwm, hcl⟩ := hs
      exact ⟨hv, .eq (FDatabase.mem_toDatabase_terms.mpr hwm) hev₁ hev₂
        (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ h.eqs).mp hcl))
        (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ h.eqs).mp heq))⟩
    · exact absurd hs (by simp)
  | values vs f as =>
    rw [patternHolds] at hs
    split at hs
    · next us ts hu ht =>
      -- The interpreter splits on the head: a constructor's entry is its own application
      -- and is tested as a term, a merge function's is looked up in the index.
      split at hs
      · next hm =>
        rw [List.any_eq_true] at hs
        obtain ⟨r, hr, hcond⟩ := hs
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨hfn, hkey⟩, hval⟩ := hcond
        subst hfn
        have hne : d.sig.mergeOf r.fn ≠ none := by
          intro hz; rw [hz] at hm; simp at hm
        have hkeyC : CongListOn d.toDatabase [Term.app r.fn (ts ++ us)] ts r.args :=
          CongList.mono Database.addTerms_contained_withOperands
            ((FDatabase.congrTuple_addTerms_iff h.eqs).mp hkey)
        have hvalC : CongListOn d.toDatabase [Term.app r.fn (ts ++ us)] us r.out :=
          CongList.mono Database.addTerms_contained_withOperands
            ((FDatabase.congrTuple_addTerms_iff h.eqs).mp hval)
        have hop : Term.app r.fn (ts ++ us) ∈
            (d.toDatabase.withOperands [Term.app r.fn (ts ++ us)]).terms :=
          Database.mem_addTerms (by simp)
        obtain ⟨bs, hbs, hmem⟩ := h.index.entry r hr hne
        have hbsC : CongListOn d.toDatabase [Term.app r.fn (ts ++ us)] r.args bs :=
          CongList.mono (Database.Contained.addTerms _ _) hbs
        refine ⟨hv, .values hmem ht hu (Cong.congr ?_ hop ?_)⟩
        · exact Cong.mono (Database.Contained.addTerms _ _) hmem
        · exact CongList.append (hkeyC.trans hbsC).symm hvalC.symm
      · rw [decide_eq_true_eq] at hs
        obtain ⟨w, hwm, hcl⟩ := hs
        exact ⟨hv, .values (FDatabase.mem_toDatabase_terms.mpr hwm) ht hu
          (congOn_singleton.mpr ((FDatabase.mem_closureF_addTerm h.eqs).mp hcl))⟩
    · exact absurd hs (by simp)

/-- **Every substitution the enumerator produces is, up to `Env.Agree`, one
`ValidQuerySubst` admits.**

The `Env.Agree` is forced: `Query.freeVars` deduplicates, so `matchQuery` binds a variable
two patterns share exactly **once**, while `ValidQuerySubst` demands `Env.UnionAll σs σ`,
which is literal concatenation of one substitution per pattern. -/
theorem FDatabase.matchQuery_validQuerySubst {d : FDatabase} (h : d.Inv) {q : Query}
    {σ : Env} (hs : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  rw [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true] at hs
  obtain ⟨⟨hdom, hval⟩, hall⟩ := hs
  have hall' : ∀ p ∈ q, ValidSubst d.toDatabase p (Env.canon (p.freeVars d.env) σ) :=
    fun p hp =>
      FDatabase.patternHolds_validSubst h (validEnv_canon hp hdom hval) (hall p hp)
  obtain ⟨τ, hu, hr⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars d.env) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact Env.refines_canon)
  refine ⟨τ, ⟨_, List.forall₂_map_self hall', hu⟩, Env.agree_of_refines hr ?_⟩
  -- `σ` binds only the query's free variables, and each is bound by some restriction
  intro v hv
  rw [hdom] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars d.env) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  exact hvp

/-! #### The merge phase and the round

These are the two containment steps, and the only places the *witness* has to be chosen
rather than computed. A merge pass deletes, so its result is not a `MergeClosure` state;
the specification state to compare against is one that took at least the same merges, and
`MergeClosure`'s freedom to take any number of steps is what pays for that.

`FDatabase.mergeRound_contained`, `mergeSaturateF_contained` and
`execRunRules_contained` are proved at the end of the file, under "Containment for the
merge interpreter": they read `mergeOneWith_inv`, `mergeOneWith_confined`,
`mergeRound_confined`, `mem_mergeEnv`, `Inv.setEnv` and `Inv.mergeRound_of_legalMerges`,
all of which are stated below. -/

/-! #### Commands and programs

`FDatabase.execCmdM_contained`, `FDatabase.execProgramM_contained` and `execM_contained`
are proved at the end of the file, under "Containment for a whole program", because they
read the whole chain. What is worth reading here is their **side conditions**, which are
this section's real output:

* a merge body is an action block nothing type-checks — `Cmd.SetLegal (.decl _ _)` is
  `True`, so `Program.SetLegal` says nothing about one, and without
  `Signature.MergesLegal` the accumulator's `Inv` fails at the first body that writes an
  illegal `set` or one of the wrong width;
* `FDatabase.Inv` does **not** survive an arbitrary declaration — declaring `g` `:merge`
  after `g ()` is already a term moves `g`'s rows from `IndexOk.ctor` to `IndexOk.entry`
  — so a declaration has to name something the state does not yet mention
  (`FDatabase.Unused`), which is egglog's own "declare before use".

`FDatabase.ProgramLegal` bundles those two with `Cmd.WriteLegal` and checks them at the
state each command actually runs in. -/

/-! ### Two statements removed rather than carried

**`execM_current_of_lattice` is deleted.** It was completeness — "the implementation keeps
the *right* value and not merely a subset" — stated as `Database.Current`, and
`Proofs/Lattice.lean` refutes it three independent ways, all machine-checked, and it stays
false under the obvious repairs. Its `hjoin` is an *implication*, so a merge that never
fires satisfies it vacuously while `Current` still demands `le vs vs`; giving `le` a
genuine partial order does not save it (`currentOfLattice_false_partialOrder`), since a
stuck merge body makes `mergeOneWith` return `none`, `settled` holds with two rows at one
key class, and `Current` is unsatisfiable at either; nor does a total merge with reflexive
`le` (`currentOfLattice_false_total`), since `hjoin` bounds one collision and a class that
collides twice needs them to compose. A corrected statement needs `hrefl`, `htrans`,
`hjoin` strengthened from an implication to the existence of a resolving merge, and
`ProgramLegal` — and may still be false for programs with rules, since `MergeStep` never
removes an entry and `Matches.values` lets a rule read a superseded one.

**`mergeRound_closure` is deleted.** It was `FDatabase.mergeRound_contained` with no
hypotheses at all, and both of that theorem's hypotheses are forced: `mergeOne` gates on
`congrKeys d.closureF` while `MergeStep` gates on `CongList`, and without `hlegal` the
accumulator's `Inv` fails at the first merge body that writes an illegal `set`. The
hypothesised statement is proved, below, under its own name. -/

/-! ### The implementation deletes, the specification does not

`Spec/` is append-only and stays so: the M11 safety theorem is an invariant over
`MergeStep`, which needs neither termination nor confluence exactly because nothing is
removed, and the encoding depends on the same property to let proofs refer to terms after
they leave the e-graph. `Impl/Merge.lean`'s merge phase does **not** stay append-only,
because egglog's merge replaces the row: an append-only reference implementation is
faithful to our spec and unfaithful to the system the spec models.

So the contract between them weakens from an equality to a **containment**, which is the
safe direction — everything M11 reads is positive in the state, so an implementation that
finds fewer results cannot make a safety claim false. Two theorems carry that:
`FDatabase.mergeRound_confined`, that deletion touches nothing it must not, and
`ValidSubst.mono`, that fewer rows really do mean fewer matches. -/
namespace FDatabase

@[simp] theorem addRow_sig {d : FDatabase} {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).sig = d.sig := rfl

/-- Every `FDatabase` denotation records the diagonal of what it holds. `Database.WF`'s
`eqsRefl` clause is definitional here, which is why `FDatabase.Inv` never has to prove it.
-/
theorem eqsRefl (d : FDatabase) : ∀ t ∈ d.toDatabase.terms, (t, t) ∈ d.toDatabase.eqs :=
  fun _ ht => Or.inl ⟨rfl, FDatabase.mem_toDatabase_terms.mp ht⟩

/-- Containment of denotations, read off the two lists. Unconditional, where the
`toDatabase_*` bridges need `EqsInTerms`: this asks only that both lists grow, and
`toDatabase` is monotone in each. -/
theorem toDatabase_contained_of_lists {d e : FDatabase}
    (ht : ∀ t ∈ d.terms, t ∈ e.terms) (hq : ∀ p ∈ d.eqs, p ∈ e.eqs) :
    d.toDatabase.Contained e.toDatabase := by
  refine ⟨fun p hp => ?_⟩
  rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
  · exact Or.inl ⟨h₁, ht _ h₂⟩
  · exact Or.inr ⟨hq _ h₁, ht _ h₂, ht _ h₃⟩

@[simp] theorem addTerms_eqs {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).eqs = d.eqs := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

theorem mem_addTerms_terms {d : FDatabase} {ts : List Term} {t : Term} (h : t ∈ d.terms) :
    t ∈ (d.addTerms ts).terms := by
  induction ts generalizing d with
  | nil => exact h
  | cons u ts ih => exact ih (FDatabase.mem_addTerm_terms.mpr (Or.inr h))

theorem contained_addTerm {d : FDatabase} {t : Term} :
    d.toDatabase.Contained (d.addTerm t).toDatabase :=
  toDatabase_contained_of_lists (fun _ hx => FDatabase.mem_addTerm_terms.mpr (Or.inr hx))
    (fun _ hp => hp)

/-- The action interpreter only adds, at the list level. -/
theorem execAction_lists {d e : FDatabase} {a : Action} (h : execAction d a = some e) :
    (∀ t ∈ d.terms, t ∈ e.terms) ∧ (∀ p ∈ d.eqs, p ∈ e.eqs) := by
  rcases execAction_eq_some h with ⟨t, rfl⟩ | ⟨v, t, rfl⟩ | ⟨t₁, t₂, -, rfl⟩ |
    ⟨f, as, vs, rfl⟩ <;>
    exact ⟨fun x hx => by
        simp [FDatabase.addTerm, FDatabase.addEq, FDatabase.addRow, List.mem_dedup, hx],
      fun q hq => by
        simp [FDatabase.addTerm, FDatabase.addEq, FDatabase.addRow, List.mem_dedup, hq]⟩

theorem execAction_rows {d e : FDatabase} {a : Action} (h : execAction d a = some e) :
    ∀ r ∈ d.rows, r ∈ e.rows := by
  rcases execAction_eq_some h with ⟨t, rfl⟩ | ⟨v, t, rfl⟩ | ⟨t₁, t₂, -, rfl⟩ |
    ⟨f, as, vs, rfl⟩ <;>
    intro r hr <;>
    simp [FDatabase.addTerm, FDatabase.addEq, FDatabase.addRow, List.mem_dedup, hr]

theorem execActions_lists {as : List Action} : ∀ {d e : FDatabase},
    execActions d as = some e →
      (∀ t ∈ d.terms, t ∈ e.terms) ∧ (∀ p ∈ d.eqs, p ∈ e.eqs) ∧ (∀ r ∈ d.rows, r ∈ e.rows) := by
  induction as with
  | nil =>
    intro d e h
    rw [execActions, Option.some.injEq] at h
    exact h ▸ ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩
  | cons a as ih =>
    intro d e h
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some d' =>
      rw [execActions, hv, Option.bind_some] at h
      exact ⟨fun x hx => (ih h).1 x ((execAction_lists hv).1 x hx),
        fun q hq => (ih h).2.1 q ((execAction_lists hv).2 q hq),
        fun r hr => (ih h).2.2 r (execAction_rows hv r hr)⟩

theorem execAction_contained {d e : FDatabase} {a : Action}
    (h : execAction d a = some e) : d.toDatabase.Contained e.toDatabase :=
  toDatabase_contained_of_lists (execAction_lists h).1 (execAction_lists h).2

/-- The interpreter's actions do not touch the signature either, so which functions are
`.merge` functions is stable across a merge pass. -/
theorem execAction_sig {d e : FDatabase} {a : Action} (h : execAction d a = some e) :
    e.sig = d.sig := by
  cases a with
  | expr e₀ =>
    cases hv : Expr.eval d.sig e₀ d.env with
    | none => rw [execAction, hv] at h; simp at h
    | some t =>
      rw [execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | letBind v e₀ =>
    cases hv : Expr.eval d.sig e₀ d.env with
    | none => rw [execAction, hv] at h; simp at h
    | some t =>
      rw [execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | union e₁ e₂ =>
    cases hv₁ : Expr.eval d.sig e₁ d.env with
    | none => rw [execAction, hv₁] at h; simp at h
    | some t₁ =>
      cases hv₂ : Expr.eval d.sig e₂ d.env with
      | none => rw [execAction, hv₁, hv₂] at h; simp at h
      | some t₂ =>
        rw [execAction, hv₁, hv₂, Option.bind_some, Option.bind_some] at h
        split at h
        · simp at h
        · simp only [Option.some.injEq] at h
          exact h ▸ rfl
  | set f args out =>
    cases hv₁ : Expr.evalList d.sig args d.env with
    | none => rw [execAction, hv₁] at h; simp at h
    | some ts =>
      cases hv₂ : Expr.evalList d.sig out d.env with
      | none => rw [execAction, hv₁, hv₂] at h; simp at h
      | some vs =>
        rw [execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact h ▸ addRow_sig

theorem execActions_contained {d e : FDatabase} {as : List Action}
    (h : execActions d as = some e) : d.toDatabase.Contained e.toDatabase :=
  toDatabase_contained_of_lists (execActions_lists h).1 (execActions_lists h).2.1

theorem execActions_rows {d e : FDatabase} {as : List Action}
    (h : execActions d as = some e) : ∀ r ∈ d.rows, r ∈ e.rows := (execActions_lists h).2.2

theorem execActions_sig {d e : FDatabase} {as : List Action}
    (h : execActions d as = some e) : e.sig = d.sig := by
  induction as generalizing d with
  | nil => rw [execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some d' =>
      rw [execActions, hv, Option.bind_some] at h
      exact (ih h).trans (execAction_sig hv)

/-- `addRow` only adds, at the interpreter level: all it records in the denotation is the
entry term. -/
theorem contained_addRow {d : FDatabase} {f : FnName} {as vs : List Term} :
    d.toDatabase.Contained (d.addRow f as vs).toDatabase := contained_addTerm

/-- `addTerms` only adds, at the interpreter level. This is `contained_addRow` without the
index row, which is what a merge firing needs: it inserts the combined row itself, in the
slot the row it replaces occupied. -/
theorem contained_addTerms {d : FDatabase} {ts : List Term} :
    d.toDatabase.Contained (d.addTerms ts).toDatabase :=
  toDatabase_contained_of_lists (fun _ hx => mem_addTerms_terms hx) (by simp)

/-- The rows a merge firing leaves in place: everything but `r₁`, with `r₂` overwritten by
the combined row. Membership in one direction; `mem_mergeRows` is the other. -/
theorem mem_mergeRows_of {rs : List Row} {r₁ r₂ r : Row} {vs : List Term} (hr : r ∈ rs)
    (h₁ : r ≠ r₁) (h₂ : r ≠ r₂) :
    r ∈ (rs.filter fun x => x ≠ r₁).map fun x =>
      if x = r₂ then (⟨r₂.fn, r₂.args, vs⟩ : Row) else x :=
  List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [h₁]⟩, by simp [h₂]⟩

/-- The rows a **no-conflict** firing leaves: everything but `r₁`. `mergeOneOriented`'s
`noConflict` branch runs no body and overwrites nothing, so the row list only shrinks.
Membership in one direction; `mem_dropRow` is the other. -/
theorem mem_dropRow_of {rs : List Row} {r₁ r : Row} (hr : r ∈ rs) (h₁ : r ≠ r₁) :
    r ∈ rs.filter fun x => x ≠ r₁ :=
  List.mem_filter.mpr ⟨hr, by simp [h₁]⟩

/-- A no-conflict firing leaves only rows that were already there. -/
theorem mem_dropRow {rs : List Row} {r₁ r : Row} (hr : r ∈ rs.filter fun x => x ≠ r₁) :
    r ∈ rs := (List.mem_filter.mp hr).1

/-- Every row a merge firing leaves is one that was there or the combined row. -/
theorem mem_mergeRows {rs : List Row} {r₁ r₂ r : Row} {vs : List Term}
    (hr : r ∈ (rs.filter fun x => x ≠ r₁).map fun x =>
      if x = r₂ then (⟨r₂.fn, r₂.args, vs⟩ : Row) else x) :
    r ∈ rs ∨ r = ⟨r₂.fn, r₂.args, vs⟩ := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  by_cases hq : s = r₂
  · exact Or.inr (by simp [hq])
  · exact Or.inl (by simpa [hq] using (List.mem_filter.mp hs).1)

/-- **One merge firing removes nothing it must not.**

The three prohibitions of the design, discharged: a merge deletes no term, no equality,
and no row of a function that is not the `.merge` function being merged. The last covers
both a constructor's rows, which `FDatabase.IndexOk.ctor` reads back as entry terms, and
`.noMerge`, which is how the proof encoding declares its proof nodes, so deleting one
would delete a proof.

The reason it holds is one line: the only rows dropped or overwritten are `r₁` and `r₂`
themselves, whose function is `r₁.fn`, and the branch was taken only because
`d.sig.mergeOf r₁.fn = .merge body res`. A row of any other kind of function is therefore
distinct from both. The `noConflict` branch drops `r₁` and nothing else, so the same line
covers it with `r₂` to spare. -/
theorem mergeOneOriented_confined {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (h : d.mergeOneOriented cl r₁ r₂ = some e) :
    (∀ t ∈ d.terms, t ∈ e.terms) ∧ (∀ p ∈ d.eqs, p ∈ e.eqs) ∧ e.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ e.rows := by
  unfold FDatabase.mergeOneOriented at h
  match hm : d.sig.mergeOf r₁.fn with
  | none => rw [hm] at h; simp at h
  | some .noMerge => rw [hm] at h; simp at h
  | some (.merge body res) =>
    rw [hm] at h
    simp only at h
    split at h
    case isFalse => simp at h
    case isTrue hcond =>
      split at h
      case isTrue =>
        -- The no-conflict skip: `r₁` is dropped and nothing else moves.
        rw [Option.some.injEq] at h
        subst h
        refine ⟨fun _ h => h, fun _ h => h, rfl, fun r hr hnm => ?_⟩
        exact mem_dropRow_of hr fun hq => hnm body res (by rw [hq]; exact hm)
      case isFalse =>
        cases hb : execActions { d with env := mergeEnv r₂.out r₁.out } body with
        | none => rw [hb] at h; simp at h
        | some eb =>
          rw [hb, Option.bind_some] at h
          cases hv : Expr.evalList eb.sig res eb.env with
          | none => rw [hv] at h; simp at h
          | some vs =>
            rw [hv, Option.map_some, Option.some.injEq] at h
            subst h
            have hcb := execActions_lists hb
            have hsb := execActions_sig hb
            refine ⟨fun x hx => FDatabase.mem_addTerm_terms.mpr (Or.inr (hcb.1 x hx)),
              fun q hq => hcb.2.1 q hq, ?_, fun r hr hnm => ?_⟩
            · change (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).sig = d.sig
              exact hsb
            · have hrb : r ∈ (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).rows :=
                FDatabase.mem_addTerm_rows.mpr (Or.inr ((execActions_rows hb) r hr))
              have hfn : r₁.fn = r₂.fn := by
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
                exact hcond.1.1.1
              have hne : r ≠ r₁ ∧ r ≠ r₂ := by
                refine ⟨fun hq => hnm body res ?_, fun hq => hnm body res ?_⟩
                · rw [hq]; exact hm
                · rw [hq, ← hfn]; exact hm
              exact mem_mergeRows_of hrb hne.1 hne.2

/-- **A firing is a firing on one of the two orientations, and nothing else.**

`mergeOneWith` only chooses which colliding row is the one already in the table — that
is `swapForCanon`, and every fact below is indifferent to it, so each is proved once for
`mergeOneOriented` and transported through this. What the choice *does* change is which
`MergeStep` the firing refines, and `MergeStep.collide` has the two rows as premises in
both orders, so either is available. -/
theorem mergeOneWith_eq_oriented {cl : Finset (Term × Term)} {d : FDatabase} (r₁ r₂ : Row) :
    d.mergeOneWith cl r₁ r₂ = d.mergeOneOriented cl r₂ r₁ ∨
      d.mergeOneWith cl r₁ r₂ = d.mergeOneOriented cl r₁ r₂ := by
  unfold FDatabase.mergeOneWith
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `mergeOneOriented_confined` at whichever orientation the firing took. -/
theorem mergeOneWith_confined {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.mergeOneWith cl r₁ r₂ = some e) :
    (∀ t ∈ d.terms, t ∈ e.terms) ∧ (∀ p ∈ d.eqs, p ∈ e.eqs) ∧ e.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ e.rows := by
  rcases mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he <;>
    exact mergeOneOriented_confined (he ▸ h)

/-! #### The rebuild

`FDatabase.rebuild` re-keys every `:merge` row onto its class's canonical key, drops the
duplicates that creates and moves the re-keyed rows to the front. It writes `rows` and
nothing else, so `terms`, `eqs`, `sig`, `env` and `rules` come out untouched by `rfl` and
what has to be proved is only about rows: which they are, that the ones a merge may not
delete are still there, and that the specification records them. -/

/-- A fold that only ever keeps its accumulator or takes the new element lands on the
accumulator or on an element of the list that satisfies whatever the choice required.
`canonOf` is such a fold, and its two facts — the representative is a term the database
holds, and it is congruent to what it represents — are this lemma twice. -/
theorem foldl_pick {α : Type _} {P : α → Prop} {f : α → α → α}
    (hf : ∀ a u, f a u = a ∨ (f a u = u ∧ P u)) :
    ∀ (l : List α) (a : α), l.foldl f a = a ∨ (l.foldl f a ∈ l ∧ P (l.foldl f a)) := by
  intro l
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons u l ih =>
    intro a
    rcases ih (f a u) with hh | ⟨hm, hp⟩
    · rcases hf a u with he | ⟨he, hpu⟩
      · exact Or.inl (by rw [List.foldl_cons, hh, he])
      · exact Or.inr ⟨by rw [List.foldl_cons, hh, he]; simp,
          by rw [List.foldl_cons, hh, he]; exact hpu⟩
    · exact Or.inr ⟨by rw [List.foldl_cons]; exact List.mem_cons_of_mem _ hm,
        by rw [List.foldl_cons]; exact hp⟩

/-- The representative is either the term itself, or a term the list holds and the closure
relates to it. -/
theorem canonOf_spec {cl : Finset (Term × Term)} {ts : List Term} {t : Term} :
    FDatabase.canonOf cl ts t = t ∨
      (FDatabase.canonOf cl ts t ∈ ts ∧
        (FDatabase.canonOf cl ts t = t ∨ (t, FDatabase.canonOf cl ts t) ∈ cl)) := by
  refine foldl_pick (P := fun u => u = t ∨ (t, u) ∈ cl) (fun a u => ?_) ts t
  by_cases hu : u == t || decide ((t, u) ∈ cl)
  · refine Or.inr ⟨by simp [hu], ?_⟩
    rcases Bool.or_eq_true .. |>.mp hu with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  · exact Or.inl (by simp [hu])

/-- A row of a function without a `:merge` body is not re-keyed. -/
theorem rebuildRow_of_not_merge {cl : Finset (Term × Term)} {d : FDatabase} {r : Row}
    (h : ∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) :
    d.rebuildRow cl r = r := by
  unfold FDatabase.rebuildRow
  split
  · rename_i body res hm; exact absurd hm (h body res)
  · rfl

/-- A rebuilt row is a row of `d`, re-keyed — and every row of `d` contributes one. -/
theorem mem_rebuild_rows {cl : Finset (Term × Term)} {d : FDatabase} {r : Row} :
    r ∈ (FDatabase.rebuild cl d).rows ↔ ∃ s ∈ d.rows, r = d.rebuildRow cl s := by
  have hmap : ∀ b : Bool, (∃ p ∈ (d.rows.map fun s => (d.rebuildRow cl s, s)).filter
      fun p => (p.1 == p.2) == b, r = p.1) → ∃ s ∈ d.rows, r = d.rebuildRow cl s := by
    intro b ⟨p, hp, hr⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hp).1
    exact ⟨s, hs, hr⟩
  constructor
  · intro hr
    simp only [FDatabase.rebuild, List.mem_dedup, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨p, hp, hr⟩ | ⟨p, hp, hr⟩
    · exact hmap false ⟨p, by simpa using hp, hr.symm⟩
    · exact hmap true ⟨p, by simpa using hp, hr.symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hp : (d.rebuildRow cl s, s) ∈ d.rows.map fun x => (d.rebuildRow cl x, x) :=
      List.mem_map_of_mem hs
    simp only [FDatabase.rebuild, List.mem_dedup, List.mem_append, List.mem_map]
    by_cases hq : d.rebuildRow cl s = s
    · exact Or.inr ⟨(d.rebuildRow cl s, s), List.mem_filter.mpr ⟨hp, by simp [hq]⟩, rfl⟩
    · exact Or.inl ⟨(d.rebuildRow cl s, s), List.mem_filter.mpr ⟨hp, by simp [hq]⟩, rfl⟩

/-- **A rebuild removes nothing it must not.** Same three prohibitions as
`mergeOneOriented_confined`, and the reason is the same one line: only a `.merge`
function's rows are re-keyed, so a row of any other kind is its own image. -/
theorem rebuild_confined {cl : Finset (Term × Term)} {d : FDatabase} :
    (∀ t ∈ d.terms, t ∈ (FDatabase.rebuild cl d).terms) ∧
      (∀ p ∈ d.eqs, p ∈ (FDatabase.rebuild cl d).eqs) ∧
      (FDatabase.rebuild cl d).sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ (FDatabase.rebuild cl d).rows :=
  ⟨fun _ h => h, fun _ h => h, rfl,
    fun r hr hnm => mem_rebuild_rows.mpr ⟨r, hr, (rebuildRow_of_not_merge hnm).symm⟩⟩

/-- **A rebuild does not move the denotation at all.** It writes `rows`, which `toDatabase`
drops, so this is `rfl` — which is why `rebuild_recorded` is deleted: it was
`Database.Recorded.refl` composed with this, and needed no invariant. -/
@[simp] theorem rebuild_toDatabase {cl : Finset (Term × Term)} {d : FDatabase} :
    (FDatabase.rebuild cl d).toDatabase = d.toDatabase := rfl

/-- A rebuild restores the caller's environment and rule list, having never left them. -/
theorem rebuild_envRules {cl : Finset (Term × Term)} {d : FDatabase} :
    (FDatabase.rebuild cl d).env = d.env ∧ (FDatabase.rebuild cl d).rules = d.rules :=
  ⟨rfl, rfl⟩

/-- The closure argument the merge phase carries is sound for the database it is used on.
`mergeRound` computes it once per pass with `FDatabase.closureF`, where
`FDatabase.mem_closureF_iff` discharges this unconditionally. -/
def ClosureSound (d : FDatabase) (cl : Finset (Term × Term)) : Prop :=
  ∀ p ∈ cl, Cong d.toDatabase p.1 p.2

theorem closureSound_closureF {d : FDatabase} : d.ClosureSound d.closureF :=
  fun _ hp => FDatabase.mem_closureF_iff.mp hp

/-- `canonOf` moves a term inside its congruence class. -/
theorem cong_canonOf {cl : Finset (Term × Term)} {d : FDatabase}
    (hcl : d.ClosureSound cl) {t : Term} (ht : t ∈ d.toDatabase.terms) :
    Cong d.toDatabase t (FDatabase.canonOf cl d.terms t) := by
  rcases canonOf_spec (cl := cl) (ts := d.terms) (t := t) with he | ⟨-, hp⟩
  · rw [he]; exact ht
  · rcases hp with he | hmem
    · rw [he]; exact ht
    · exact hcl _ hmem

theorem congList_canonKeyOf {cl : Finset (Term × Term)} {d : FDatabase}
    (hcl : d.ClosureSound cl) : ∀ {l : List Term}, (∀ t ∈ l, t ∈ d.toDatabase.terms) →
      CongList d.toDatabase (FDatabase.canonKeyOf cl d.terms l) l
  | [], _ => .nil
  | t :: l, hl =>
    .cons (cong_canonOf hcl (hl t (by simp))).symm
      (congList_canonKeyOf hcl fun x hx => hl x (by simp [hx]))

/-- **A rebuild preserves the refinement-chain invariant.**

`wf` and `eqs` are `rfl`: a rebuild writes `rows` and nothing else, and `toDatabase` drops
`rows`. What is left is the index, and only the re-keyed rows move — `ctor` never fires on
one, since only a `.merge` function's rows are re-keyed; `entry` reads the new key through
`Database.Out`, which is exactly the search the re-keying is invisible to; and `width` is
preserved because `canonKeyOf` is a `map`. -/
theorem Inv.rebuild {cl : Finset (Term × Term)} {d : FDatabase} (h : d.Inv)
    (hcl : d.ClosureSound cl) : (FDatabase.rebuild cl d).Inv where
  wf := h.wf
  eqs := h.eqs
  index := by
    refine ⟨fun r hr hm => ?_, fun r hr hm => ?_, fun r hr dc hdc hm => ?_⟩
    · obtain ⟨s, hs, rfl⟩ := mem_rebuild_rows.mp hr
      have hfn : (d.rebuildRow cl s).fn = s.fn := by
        unfold FDatabase.rebuildRow; split <;> rfl
      have hsame : d.rebuildRow cl s = s :=
        rebuildRow_of_not_merge fun body res hb => by
          rw [← hfn] at hb; rw [show (FDatabase.rebuild cl d).sig = d.sig from rfl, hb] at hm
          exact absurd hm (by simp)
      rw [hsame] at hm ⊢
      exact h.index.ctor s hs hm
    · obtain ⟨s, hs, rfl⟩ := mem_rebuild_rows.mp hr
      have hfn : (d.rebuildRow cl s).fn = s.fn := by
        unfold FDatabase.rebuildRow; split <;> rfl
      have hm' : d.sig.mergeOf s.fn ≠ none := by rw [← hfn]; exact hm
      obtain ⟨bs, hbs, hmem⟩ := h.index.entry s hs hm'
      have hargs : ∀ x ∈ s.args, x ∈ d.toDatabase.terms := hbs.mem_of.1
      unfold FDatabase.rebuildRow
      split
      · exact ⟨bs, (congList_canonKeyOf hcl hargs).trans hbs, hmem⟩
      · exact ⟨bs, hbs, hmem⟩
    · obtain ⟨s, hs, rfl⟩ := mem_rebuild_rows.mp hr
      have hfn : (d.rebuildRow cl s).fn = s.fn := by
        unfold FDatabase.rebuildRow; split <;> rfl
      have hm' : d.sig.mergeOf s.fn ≠ none := by rw [← hfn]; exact hm
      have hdc' : d.sig s.fn = some dc := by rw [← hfn]; exact hdc
      obtain ⟨h₁, h₂⟩ := h.index.width s hs dc hdc' hm'
      unfold FDatabase.rebuildRow
      split
      · exact ⟨by simpa [FDatabase.canonKeyOf] using h₁, h₂⟩
      · exact ⟨h₁, h₂⟩

/-! `rebuild_recorded` is **deleted**. `(FDatabase.rebuild cl d).toDatabase = d.toDatabase`
by `rfl` (`rebuild_toDatabase`), so it was `Database.Recorded.refl` composed with an
identity and needed no invariant at all. The re-keying it used to pay for is now paid for
inside `FDatabase.IndexOk.entry`, which reads a row's key through `Database.Out`. -/

/-- **A merge pass removes nothing it must not.** `rebuild_confined`, then
`mergeOneWith_confined` through the two folds. This is the formal content of "`Impl/`
deletes merge rows only". -/
theorem mergeRound_confined {d : FDatabase} :
    (∀ t ∈ d.terms, t ∈ d.mergeRound.terms) ∧ (∀ p ∈ d.eqs, p ∈ d.mergeRound.eqs) ∧
      d.mergeRound.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ d.mergeRound.rows := by
  -- The invariant is exactly the conclusion, relative to the fixed starting database.
  let P : FDatabase → Prop := fun x =>
    (∀ t ∈ d.terms, t ∈ x.terms) ∧ (∀ p ∈ d.eqs, p ∈ x.eqs) ∧
      x.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) → r ∈ x.rows
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y =>
      obtain ⟨ht, hq, hs, hr⟩ := mergeOneWith_confined hy
      refine ⟨fun t htm => ht t (hx.1 t htm), fun q hqm => hq q (hx.2.1 q hqm),
        hs.trans hx.2.2.1, fun r hrd hnm => ?_⟩
      exact hr r (hx.2.2.2 r hrd hnm) (by rw [hx.2.2.1]; exact hnm)
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hb : r₁ == r₂
      · simpa [hb] using hx
      · simpa [hb] using hstep x r₁ r₂ hx
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold m r₁ x hx)
  have hinit : P d := ⟨fun _ h => h, fun _ h => h, rfl, fun r hr _ => hr⟩
  have hreb : P (FDatabase.rebuild d.closureF d) :=
    ⟨rebuild_confined.1, rebuild_confined.2.1, rebuild_confined.2.2.1,
      fun r hr hnm => rebuild_confined.2.2.2 r hr hnm⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter _ _ _ hreb

/-- **On the constructor fragment nothing is deleted, because nothing merges.** With every
function a constructor no row belongs to a `.merge` function, `hasMergeRow` is false and
the pass is the identity — which is why `Impl/Interp.lean`'s `exec` and the equality
`exec_programStep` are untouched by any of this, and, via `execM_eq_exec` below, why the
differential test constrains them. -/
theorem hasMergeRow_eq_false {d : FDatabase} (hsig : d.sig.AllConstructors) :
    d.hasMergeRow = false := by
  simp only [FDatabase.hasMergeRow, List.any_eq_false]
  intro r _
  rw [hsig r.fn]
  simp

theorem mergeRound_eq_self {d : FDatabase} (h : d.hasMergeRow = false) :
    d.mergeRound = d := by
  unfold FDatabase.mergeRound
  simp [h]

theorem mergeSaturateF_eq_self {d : FDatabase} (h : d.hasMergeRow = false) {n : Nat} :
    FDatabase.mergeSaturateF n d = some d := by
  have hs : d.settled = true := by
    simp [FDatabase.settled, FDatabase.sameData, mergeRound_eq_self h]
  cases n <;> simp [FDatabase.mergeSaturateF, hs]

end FDatabase

/-! ### The two interpreters agree on the constructor fragment

`Program.expectedSizes` — what the differential test runs — calls `execM`, and
`exec_programStep` is stated about `exec`. Without an equation between them the chain from
a passing difftest case back to `Spec/` has a hole in it. `execCmdM` differs from
`execCmd` only by a `mergeSaturateF` after each command, and with no `:merge` function
declared there is no merge row for a pass to fire on, so that call is the identity. -/
namespace FDatabase

/-- **A round has no merge phase on the constructor fragment**, so `Impl/Merge.lean`'s round
is `Impl/Interp.lean`'s. -/
theorem runRoundM_eq_round {R : RulesetName} {d : FDatabase} (hsig : d.sig.AllConstructors) :
    d.runRoundM R = some (execRunRules R d) :=
  FDatabase.mergeSaturateF_eq_self
    (FDatabase.hasMergeRow_eq_false (by rw [sig_execRunRules]; exact hsig))

/-- And so the two saturating runs are the same partial function there. -/
theorem runSaturateM_eq_runSaturateF {R : RulesetName} : ∀ (n : Nat) {d : FDatabase},
    d.sig.AllConstructors → d.runSaturateM R n = d.runSaturateF R n := by
  intro n
  induction n with
  | zero =>
    intro d hsig
    rw [FDatabase.runSaturateM, runRoundM_eq_round hsig, Option.bind_some,
      FDatabase.runSaturateF]
  | succ n ih =>
    intro d hsig
    rw [FDatabase.runSaturateM, runRoundM_eq_round hsig, Option.bind_some,
      FDatabase.runSaturateF]
    split
    · rfl
    · exact ih (by rw [sig_execRunRules]; exact hsig)

end FDatabase

/-- The signature a command leaves, for `Impl/Interp.lean`'s interpreter. This is what
carries `Signature.AllConstructors` along a run. -/
theorem execCmd_sigBind {d d' : FDatabase} {c : Cmd} (hs : execCmd d c = some d') :
    d'.sig = c.sigBind d.sig := by
  cases c with
  | action a => exact FDatabase.execAction_sig hs
  | rule r => simp only [execCmd, Option.some.injEq] at hs; exact hs ▸ rfl
  | run R => simp only [execCmd, Option.some.injEq] at hs; exact hs ▸ sig_execRunRules
  | saturate R =>
    obtain ⟨k, hk⟩ :=
      runSaturateF_iterate runFuel (show d.runSaturateF R runFuel = some d' from hs)
    exact hk ▸ (execRunRules_iterate_sig k)
  | decl f dc => simp only [execCmd, Option.some.injEq] at hs; exact hs ▸ rfl

theorem execProgramM_eq_execProgram {d : FDatabase} (hsig : d.sig.AllConstructors)
    {p : Program} (hdecl : p.CtorDecls) : d.execProgramM p = execProgram d p := by
  induction p generalizing d with
  | nil => rfl
  | cons c cs ih =>
    have hc : d.execCmdM c = execCmd d c := by
      cases c with
      | action a =>
        change (execAction d a).bind (FDatabase.mergeSaturateF mergeFuel) = execAction d a
        cases hv : execAction d a with
        | none => rfl
        | some e =>
          rw [Option.bind_some, FDatabase.mergeSaturateF_eq_self
            (FDatabase.hasMergeRow_eq_false (by rw [FDatabase.execAction_sig hv]; exact hsig))]
      | rule r => rfl
      | run R => exact FDatabase.runRoundM_eq_round hsig
      | saturate R => exact FDatabase.runSaturateM_eq_runSaturateF runFuel hsig
      | decl f dc => rfl
    change (d.execCmdM c).bind (fun d' => d'.execProgramM cs)
      = (execCmd d c).bind fun d' => execProgram d' cs
    rw [hc]
    cases hv : execCmd d c with
    | none => rfl
    | some e =>
      rw [Option.bind_some, Option.bind_some]
      exact ih (by rw [execCmd_sigBind hv]; exact hsig.sigBind (hdecl c (by simp)))
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-- **`execM` is `exec` on the constructor fragment.** This is the link that makes a
differential-test case say something about `Spec/`: `Program.expectedSizes` runs `execM`,
this carries it to `exec`, and `exec_programStep` carries that to `ProgramStep`. -/
theorem execM_eq_exec {p : Program} (hdecl : p.CtorDecls) : execM p = exec p :=
  execProgramM_eq_execProgram (d := FDatabase.empty)
    (by intro f; simp [Signature.mergeOf, FDatabase.empty]) hdecl


/-! ### `mergeRound_rowCount` is deleted

It said row counts do not observe the merge phase — `keyRowCount` counts congruence classes
of *keys*, a merge step writes its combined entry at a key already present, so a pass leaves
every count alone — and it is **false as stated**. `hpure` bounds the merge's *action
block* but not its *result*, and `FDatabase.addRow` inserts the result's terms together with
their index rows, so a merge whose result builds an application adds a key class to a
*different* function's table. With `k` any term:

```
d.sig  = fun n => if n = "f" then some ⟨1, 1, .merge [] [.app "F" [.var "old"]]⟩ else none
d.terms = [k],  d.rows = [⟨"f", [k], [k]⟩],  d.eqs = []
```

`hpure` holds (the only block is `[]`). The row collides with itself, `mergeRound` fires,
the result evaluates to `F k`, and `addRow "f" [k] [F k]` writes the index row for `F k`.
Then `d.mergeRound.keyRowCount "F" = 1` while `d.keyRowCount "F" = 0`.

The theorem the difftest actually relies on is the same statement with `hpure` strengthened
to "the merge result is a term the database already holds", under which `addRow` adds no key
class anywhere. Every generated merge case satisfies it, results being `i64` literals. -/

/-! ### Well-formedness -/
/-- Every binding a merge body's environment provides is one of the two colliding rows'
outputs. `MergeStep.wf` and `mergeOneOriented_inv` both need it, because `WF.envInTerms`
has to hold of `mergeEnv a b` before the body runs — and an entry is a term now, so
`WF.subtermClosed` supplies the outputs where `RowsWF` used to. -/
theorem mem_mergeEnvIdx {i : Nat} {os ns : List Term} {p : Var × Term}
    (h : p ∈ mergeEnvIdx i os ns) : p.2 ∈ os ∨ p.2 ∈ ns := by
  induction os generalizing i ns with
  | nil => simp [mergeEnvIdx] at h
  | cons o os ih =>
    cases ns with
    | nil => simp [mergeEnvIdx] at h
    | cons n ns =>
      simp only [mergeEnvIdx, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih h).imp (fun hm => by simp [hm]) fun hm => by simp [hm]

theorem mem_mergeEnv {os ns : List Term} {p : Var × Term} (h : p ∈ mergeEnv os ns) :
    p.2 ∈ os ∨ p.2 ∈ ns := by
  unfold mergeEnv at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · exact mem_mergeEnvIdx h

/-- Every declared `:merge` obeys the discipline every other action block obeys — its body
writes only legal `set`s, at the declared column widths — and its result has one expression
per value column.

`Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about a merge body
and this has to be carried separately. The `res.length` half is **new**: it is what
`FDatabase.IndexOk.width` needs of the row a firing writes, which is `MergeStep.collide`'s
`arity` premises reaching back into the declaration. -/
def Signature.MergesLegal (sig : Signature) : Prop :=
  ∀ g dc body res, sig g = some dc → dc.merge = some (MergeSpec.merge body res) →
    Actions.WriteLegal body sig ∧ res.length = dc.outArity

/-! #### The merge phase

`mergeRound` does **not** preserve `Inv` unconditionally, and `FDatabase.IndexOk` is where
it fails. A merge body is an arbitrary `List Action` carrying no `Action.SetLegal`
obligation, so a `(set (F) …)` inside one, on a constructor `F`, writes a row whose `out`
is not `[]` — which is exactly what `IndexOk.ctor` forbids. The widths fail the same way:
nothing makes a body's `set` write the declared number of columns, which is what
`IndexOk.width` records.

`Signature.MergesLegal` is the repair, and it patches a gap in the specification:
`Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about a merge
body. -/

namespace FDatabase

/-- **`Inv` survives a merge firing's rewrite of the row list**: `r₁` dropped, and `r₂`
overwritten where it stands by the combined row.

`h₂` is about the *signature*, not about the two rows, and that is the whole argument for
`ctor`: a `.merge` function's row is never a constructor's — the dropped row `r₁` needs no
hypothesis at all, since `IndexOk` is a condition on each row separately. `hout` is what
`entry` needs of the combined row, and `hvs` what `width` does — the merge result has one
expression per value column, which is `Signature.MergesLegal`'s second half. -/
theorem Inv.mergeRows {d : FDatabase} (h : d.Inv) {r₁ r₂ : Row} {vs : List Term}
    (h₂ : d.sig.mergeOf r₂.fn ≠ none)
    (hout : d.toDatabase.Out r₂.fn r₂.args vs)
    (hwidth : ∀ dc, d.sig r₂.fn = some dc →
      r₂.args.length = dc.arity ∧ vs.length = dc.outArity) :
    ({ d with rows := (d.rows.filter fun r => r ≠ r₁).map fun r =>
        if r = r₂ then ⟨r₂.fn, r₂.args, vs⟩ else r } : FDatabase).Inv where
  wf := h.wf
  eqs := h.eqs
  index := by
    refine ⟨fun r hr hm => ?_, fun r hr hm => ?_, fun r hr dc hdc hm => ?_⟩
    · rcases mem_mergeRows hr with hr' | rfl
      · exact h.index.ctor r hr' hm
      · exact absurd hm h₂
    · rcases mem_mergeRows hr with hr' | rfl
      · exact h.index.entry r hr' hm
      · exact hout
    · rcases mem_mergeRows hr with hr' | rfl
      · exact h.index.width r hr' dc hdc hm
      · exact hwidth dc hdc

/-- **`Inv` survives a no-conflict firing's rewrite of the row list**: `r₁` dropped, and
nothing put back. Needs **no** hypothesis at all — the rows that remain were already there,
and `IndexOk` is a condition on each row separately. -/
theorem Inv.dropRow {d : FDatabase} (h : d.Inv) {r₁ : Row} :
    ({ d with rows := d.rows.filter fun r => r ≠ r₁ } : FDatabase).Inv where
  wf := h.wf
  eqs := h.eqs
  index :=
    ⟨fun r hr => h.index.ctor r (mem_dropRow hr), fun r hr => h.index.entry r (mem_dropRow hr),
      fun r hr => h.index.width r (mem_dropRow hr)⟩

/-- `Inv` through a whole action block, given every `set` in it is legal and writes the
declared column widths. `Inv.execAction` iterated; `execAction_sig` is what keeps
`WriteLegal` — a condition on the signature — applicable at each step. -/
theorem Inv.execActions {as : List Action} : ∀ {d d' : FDatabase}, d.Inv →
    Actions.WriteLegal as d.sig → execActions d as = some d' → d'.Inv := by
  induction as with
  | nil =>
    intro d d' h _ hs
    rw [Egglog.execActions, Option.some.injEq] at hs
    exact hs ▸ h
  | cons a as ih =>
    intro d d' h hlegal hs
    cases hv : Egglog.execAction d a with
    | none => rw [Egglog.execActions, hv] at hs; simp at hs
    | some d₁ =>
      rw [Egglog.execActions, hv, Option.bind_some] at hs
      refine ih (h.execAction hlegal.head hv) ?_ hs
      rw [execAction_sig hv]
      exact hlegal.tail

set_option maxHeartbeats 1000000 in
-- Four `Inv` preservation steps composed over one `execActions`/`addTerm`/row-rewrite
-- chain, with `mergeOneOriented` unfolded twice; the default budget is short.
/-- **One merge firing preserves `Inv`, provided the declared merges are legal.**

Four steps. Rebinding `env` to `mergeEnv r₂.out r₁.out` is harmless because
`WF.subtermClosed` puts both rows' outputs in `terms` — an entry *is* a term now, so this
is what `rowsWF` used to say and no longer has to. Running the body is `Inv.execActions`,
which is where `hlegal`'s `WriteLegal` half is spent. The combined entry term goes in by
`Inv.addTerm`, which needs nothing. And rewriting the row list is `Inv.mergeRows`, whose
`Out` premise is discharged at the entry term just added and whose width premise is
`hlegal`'s second half. The `noConflict` branch runs none of the four: it only drops `r₁`,
which is `Inv.dropRow`. -/
theorem mergeOneOriented_inv {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.Inv) (hlegal : Signature.MergesLegal d.sig)
    (hm : d.mergeOneOriented cl r₁ r₂ = some e) : e.Inv := by
  unfold FDatabase.mergeOneOriented at hm
  match hmo : d.sig.mergeOf r₁.fn with
  | none => rw [hmo] at hm; simp at hm
  | some .noMerge => rw [hmo] at hm; simp at hm
  | some (.merge body res) =>
    rw [hmo] at hm
    simp only at hm
    split at hm
    case isFalse => simp at hm
    case isTrue hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨hfn, -⟩, hr₁⟩, hr₂⟩ := hcond
      obtain ⟨dc₁, hdc₁, hdcm₁⟩ : ∃ dc, d.sig r₁.fn = some dc ∧
          dc.merge = some (MergeSpec.merge body res) := by
        rw [Signature.mergeOf] at hmo
        cases hd : d.sig r₁.fn with
        | none => rw [hd] at hmo; simp at hmo
        | some dc => exact ⟨dc, rfl, by rw [hd] at hmo; simpa using hmo⟩
      obtain ⟨hbodyLegal, hresLen⟩ := hlegal r₁.fn dc₁ body res hdc₁ hdcm₁
      split at hm
      case isTrue =>
        rw [Option.some.injEq] at hm
        subst hm
        exact h.dropRow
      case isFalse =>
      have hmemRow : ∀ (r : Row), r ∈ d.rows → ∀ x ∈ r.out, x ∈ d.toDatabase.terms := by
        intro r hr x hx
        by_cases hu : d.sig.mergeOf r.fn = none
        · rw [(h.index.ctor r hr hu).1] at hx; simp at hx
        · obtain ⟨bs, -, hmem⟩ := h.index.entry r hr hu
          exact h.wf.subtermClosed _ hmem
            (Term.mem_subterms.mpr (Term.IsSubterm.arg (List.mem_append_right _ hx)
              (Term.IsSubterm.refl x)))
      have hσ : ∀ b ∈ mergeEnv r₂.out r₁.out, b.2 ∈ d.toDatabase.terms := by
        intro b hb
        rcases mem_mergeEnv hb with hb' | hb'
        · exact hmemRow r₂ hr₂ b.2 hb'
        · exact hmemRow r₁ hr₁ b.2 hb'
      have h₀ : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).Inv := h.setEnv hσ
      cases hb : execActions { d with env := mergeEnv r₂.out r₁.out } body with
      | none => rw [hb] at hm; simp at hm
      | some eb =>
        rw [hb, Option.bind_some, Option.map_eq_some_iff] at hm
        obtain ⟨vs, hv, rfl⟩ := hm
        have hsig : eb.sig = d.sig :=
          execActions_sig (d := { d with env := mergeEnv r₂.out r₁.out }) hb
        have hebInv : eb.Inv :=
          h₀.execActions (show Actions.WriteLegal body d.sig from hbodyLegal) hb
        have hbase : (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).Inv := hebInv.addTerm _
        have hsig₀ : (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).sig = d.sig := hsig
        have hmemT : Term.app r₂.fn (r₂.args ++ vs) ∈
            (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).toDatabase.terms := by
          rw [FDatabase.mem_toDatabase_terms]
          exact FDatabase.mem_addTerm_terms.mpr (Or.inl ((Term.mem_subtermList _).mpr (.refl _)))
        have hargs : ∀ x ∈ r₂.args,
            x ∈ (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).toDatabase.terms := by
          intro x hx
          exact hbase.wf.subtermClosed _ hmemT
            (Term.mem_subterms.mpr (Term.IsSubterm.arg (List.mem_append_left _ hx)
              (Term.IsSubterm.refl x)))
        have hne₁ : (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).sig.mergeOf r₁.fn ≠ none := by
          rw [hsig₀, hmo]; simp
        have hne₂ : (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).sig.mergeOf r₂.fn ≠ none := by
          rw [← hfn]; exact hne₁
        have hr₂' : r₂ ∈ (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).rows :=
          FDatabase.mem_addTerm_rows.mpr (Or.inr (execActions_rows hb r₂ hr₂))
        refine (hbase.mergeRows hne₂ (Database.out_self hmemT hargs) ?_).setEnvRules ?_
        · intro dc hdc
          have hdceq : dc₁ = dc := by
            have hx := hdc
            rw [hsig₀, ← hfn, hdc₁, Option.some.injEq] at hx
            exact hx
          refine ⟨(hbase.index.width r₂ hr₂' dc hdc hne₂).1, ?_⟩
          rw [Expr.evalList_length hv, ← hdceq]
          exact hresLen
        · intro b hb'
          refine (contained_addTerm (d := eb) (t := .app r₂.fn (r₂.args ++ vs))).terms ?_
          refine (execActions_contained (d := { d with env := mergeEnv r₂.out r₁.out }) hb).terms
            ?_
          exact Database.mem_terms_of_eqs
            (d₁ := d.toDatabase)
            (d₂ := ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).toDatabase)
            (fun _ hp => hp) (h.wf.envInTerms b hb')

/-- `mergeOneOriented_inv` at whichever orientation the firing took. -/
theorem mergeOneWith_inv {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.Inv) (hlegal : Signature.MergesLegal d.sig)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) : e.Inv := by
  rcases mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he <;>
    exact mergeOneOriented_inv h hlegal (he ▸ hm)

/-- **A merge pass preserves the refinement-chain invariant, provided every declared merge
is legal.** `mergeOneWith_inv` through the two folds of `mergeRound`, exactly as
`mergeRound_confined` threads `mergeOneWith_confined`. The accumulator also carries
`sig = d.sig`, which is what lets `hlegal` — a statement about the *pre-pass* signature —
apply at every intermediate state. -/
theorem Inv.mergeRound_of_legalMerges {d : FDatabase} (h : d.Inv)
    (hlegal : Signature.MergesLegal d.sig) : d.mergeRound.Inv := by
  let P : FDatabase → Prop := fun x => x.Inv ∧ x.sig = d.sig
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y =>
      have hs : y.sig = x.sig := (mergeOneWith_confined hy).2.2.1
      exact ⟨mergeOneWith_inv hx.1 (hx.2 ▸ hlegal) hy, hs.trans hx.2⟩
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep x r₁ r₂ hx
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold m r₁ x hx)
  have hinit : P d := ⟨h, rfl⟩
  have hreb : P (FDatabase.rebuild d.closureF d) :=
    ⟨h.rebuild closureSound_closureF, rfl⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit.1
  · exact (houter _ _ _ hreb).1

end FDatabase

/-- A merge preserves the invariants. `RowsWF` is gone as a hypothesis: an entry is a term,
so `WF.subtermClosed` already puts the colliding entries' value columns in `terms`, which
is what `WF.envInTerms` needs of `mergeEnv a b` before the body runs. -/
theorem MergeStep.wf {d₁ d₂ : Database} (hw : d₁.WF) (h : MergeStep d₁ d₂) : d₂.WF := by
  cases h with
  | @collide d f dc as bs a b vs body res hdc hmg hla hlb hra hrb hcong hbody hres =>
    have hout : ∀ (cs os : List Term), Term.app f (cs ++ os) ∈ d₁.terms →
        ∀ x ∈ os, x ∈ d₁.terms := by
      intro cs os hmem x hx
      exact hw.subtermClosed _ hmem
        (Term.mem_subterms.mpr (Term.IsSubterm.arg (List.mem_append_right _ hx)
          (Term.IsSubterm.refl x)))
    have hw0 : ({ d₁ with env := mergeEnv a b } : Database).WF :=
      hw.setEnv fun p hp => by
        rcases mem_mergeEnv hp with hpa | hpb
        · exact hout as a hra _ hpa
        · exact hout bs b hrb _ hpb
    have hd : d.WF := evalActions_wf hw0 hbody
    have hr : (d.addTerm (.app f (as ++ vs))).WF := hd.addTerm _
    have hb : d₁.Contained d := ⟨(evalActions_contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addTerm (.app f (as ++ vs)) d)
    exact hr.setEnvRules fun p hp => hc.terms (hw.envInTerms p hp)

theorem MergeClosure.wf {d₁ d₂ : Database} (hw : d₁.WF) (h : MergeClosure d₁ d₂) : d₂.WF := by
  induction h with
  | refl => exact hw
  | tail _ hstep ih => exact MergeStep.wf ih hstep

/-- One command preserves `Database.WF`: `cmdEffect_wf` for the effect, `MergeClosure.wf`
for the merge phase. -/
theorem RunStep.wf {R : RulesetName} {db db' : Database} (hw : db.WF)
    (h : RunStep R db db') : db'.WF := MergeClosure.wf (RunRules.wf hw) h

theorem cmdReach_wf {db d : Database} (hw : db.WF) {c : Cmd} (h : cmdReach db c d) :
    d.WF := by
  cases c with
  | saturate R =>
    exact RunReach.induction (P := Database.WF) (fun _ _ hp hs => hs.wf hp)
      (show SaturateReach R db d from h).1 hw
  | _ => exact cmdEffect_wf hw h

theorem CmdStep.wf {db db' : Database} (hw : db.WF) {c : Cmd} (h : CmdStep db c db') :
    db'.WF := by
  obtain ⟨d, hreach, hcl⟩ := h
  exact MergeClosure.wf (cmdReach_wf hw hreach) hcl

/-- A whole run preserves `Database.WF`, `CmdStep.wf` per command. It is what pays for
`Database.Recorded.trans`'s two `WF` premises where the refinement chain composes two
containments. -/
theorem ProgramStep.wf {db db' : Database} {p : Program} (h : ProgramStep db p db') :
    db.WF → db'.WF := by
  induction h with
  | nil => exact id
  | cons hcmd _ ih => exact fun hw => ih (CmdStep.wf hw hcmd)

/-! ### `DeclaredTerms` over the step relations

Every application a reachable state holds is a declared function's entry, `entryWidth`
children wide. `Proofs/Eval.lean` carries the action half; what is left is the merge phase,
the rule phase, and a declaration.

Three front-end checks pay for it: `Program.WidthOk` for the terms a command builds,
`Program.SetLegal` for the entries a `set` records, and `Program.DeclsFresh` for the
signature a `.decl` writes. Two conditions no signature-level check can deliver are carried
by `Database.RunLegal`. -/

/-- Every declared `:merge`'s body and result pass the width check, read of a *signature*
because a `MergeStep` reads the body it runs from one. `Signature.MergesLegal`'s width twin,
and what `Cmd.WidthOk (.decl _ _)` establishes of the signature a declaration installs. -/
def Signature.MergesWidthOk (sig : Signature) : Prop :=
  ∀ g dc ms, sig g = some dc → dc.merge = some ms → MergeSpec.WidthOk ms dc.outArity sig

/-- **`DeclaredTerms` is preserved by a merge firing**, under the two signature-level
invariants and no premise on the firing itself. `MergesLegal` supplies the body's
`Actions.SetLegal` and `MergesWidthOk` its `Actions.WidthOk`, which is what running the body
needs; the combined entry is `arity + outArity` wide because `res` has one expression per
value column. -/
theorem mergeStep_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hml : db.sig.MergesLegal) (hmw : db.sig.MergesWidthOk) (h : MergeStep db db') :
    db'.DeclaredTerms := by
  cases h with
  | @collide d f decl as bs a b vs body res hd hmerge hasl _ hae hbe _ hbody hres =>
  have hmemab : ∀ p ∈ mergeEnv a b, p.2 ∈ db.terms := by
    intro p hp
    rcases mem_mergeEnv hp with hp' | hp'
    · exact Database.mem_terms_of_arg hwf hae (List.mem_append_right as hp')
    · exact Database.mem_terms_of_arg hwf hbe (List.mem_append_right bs hp')
  have hwf₀ : ({ db with env := mergeEnv a b } : Database).WF := hwf.setEnv hmemab
  have hdt₀ : ({ db with env := mergeEnv a b } : Database).DeclaredTerms := by
    intro g cs hmem; rw [Database.terms_setEnv] at hmem; exact hdt g cs hmem
  have hspec := hmw f decl _ hd hmerge
  have hlegal : Actions.SetLegal body db.sig := (hml f decl body res hd hmerge).1.1
  have hdsig : d.sig = db.sig :=
    evalActions_sig (db := { db with env := mergeEnv a b }) hbody
  have hdwf : d.WF := evalActions_wf hwf₀ hbody
  have hddt : d.DeclaredTerms := evalActions_declaredTerms hwf₀ hdt₀ hspec.2.1 hlegal hbody
  have hvsd : ∀ t ∈ vs, Term.DeclaredTerm db.sig t := by
    have := Expr.evalList_declaredTerm (Database.env_declaredTerm hdwf hddt)
      (sig := d.sig) (by rw [hdsig]; exact hspec.2.2) hres
    intro t ht; rw [← hdsig]; exact this t ht
  have hvsl : vs.length = decl.outArity := (Expr.evalList_length hres).trans hspec.1
  have hentry : Term.DeclaredTerm db.sig (.app f (as ++ vs)) := by
    intro g cs hsub
    rw [Term.subterms_app] at hsub
    rcases Set.mem_insert_iff.mp hsub with heq | hmem
    · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
      refine ⟨decl, hd, ?_⟩
      rw [List.length_append, hasl, hvsl, FnDecl.entryWidth, if_neg]
      simp [hmerge]
    · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
      rcases List.mem_append.mp hx with hx | hx
      · exact Database.declaredTerm_of_mem hwf hdt
          (Database.mem_terms_of_arg hwf hae (List.mem_append_left a hx)) g cs hxs
      · exact hvsd x hx g cs hxs
  intro g cs hmem
  rw [Database.terms_setEnvRules, Database.addTerm_terms] at hmem
  rcases hmem with hmem | hmem
  · exact hdsig ▸ hddt g cs hmem
  · exact hdsig ▸ hentry g cs hmem

theorem mergeClosure_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hml : db.sig.MergesLegal) (hmw : db.sig.MergesWidthOk) (h : MergeClosure db db') :
    db'.DeclaredTerms := by
  induction h with
  | refl => exact hdt
  | @tail x y hcl hstep ih =>
    have hsx : x.sig = db.sig := MergeClosure.sig hcl
    exact mergeStep_declaredTerms (MergeClosure.wf hwf hcl) ih
      (by rw [hsx]; exact hml) (by rw [hsx]; exact hmw) hstep

/-- The rules the state holds obey the two checks `evalLocalActions_declaredTerms` asks of an
action block. `RunRules` fires the rules in `db.rules`, which no signature-level check
reaches. -/
def Database.RulesOk (db : Database) : Prop :=
  ∀ r ∈ db.rules, Actions.WidthOk r.actions db.sig ∧ Actions.SetLegal r.actions db.sig

theorem runRules_declaredTerms {R : RulesetName} {db : Database} (hwf : db.WF)
    (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) : (RunRules R db).DeclaredTerms := by
  intro g cs hmem
  rw [RunRules, Database.sUnion_terms] at hmem
  rcases hmem with hmem | hmem
  · exact hdt g cs hmem
  · obtain ⟨e, he, hmem⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨r, hrmem, -, σ, hq, hstep⟩ := he
    have hes : e.sig = db.sig := evalLocalActions_sig hstep
    change ∃ x, db.sig g = some x ∧ cs.length = x.entryWidth
    rw [← hes]
    exact evalLocalActions_declaredTerms hwf hdt hq.mem_terms (hr r hrmem).1 (hr r hrmem).2
      hstep g cs hmem

/-- **A declaration preserves `DeclaredTerms` exactly when it is fresh**, and needs nothing
else. A `DeclaredTerms` state holds no application of an undeclared name, so writing the
signature at a fresh name cannot invalidate a term it already holds. -/
theorem decl_declaredTerms {db : Database} (hdt : db.DeclaredTerms) {f : FnName}
    {dc : FnDecl} (hf : db.sig f = none) :
    ({ db with sig := Function.update db.sig f (some dc) } : Database).DeclaredTerms := by
  intro g cs hmem
  rw [Database.terms_setSig] at hmem
  obtain ⟨d, hd, hlen⟩ := hdt g cs hmem
  have hgf : g ≠ f := by rintro rfl; rw [hf] at hd; exact absurd hd (by simp)
  refine ⟨d, ?_, hlen⟩
  change Function.update db.sig f (some dc) g = some d
  rw [Function.update_of_ne hgf]; exact hd

theorem cmdEffect_declaredTerms {db d : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) {c : Cmd} (hw : c.WidthOk db.sig) (hsl : c.SetLegal db.sig)
    (hfresh : c.DeclFresh db.sig) (h : cmdEffect db c = some d) : d.DeclaredTerms := by
  cases c with
  | action a => exact evalAction_declaredTerms hwf hdt hw hsl h
  | rule r =>
    rw [cmdEffect, Option.some_inj] at h
    subst h
    intro g cs hmem
    rw [Database.terms_setRules] at hmem
    exact hdt g cs hmem
  | run R =>
    rw [cmdEffect, Option.some_inj] at h
    subst h; exact runRules_declaredTerms hwf hdt hr
  | saturate R => exact absurd h (by simp [cmdEffect])
  | decl f dc =>
    rw [cmdEffect, Option.some_inj] at h
    subst h; exact decl_declaredTerms hdt hfresh

/-- **A saturating run preserves `DeclaredTerms`.** Each round is `runRules_declaredTerms`
then `mergeClosure_declaredTerms`; what makes the induction go through is that a round moves
neither `sig` nor `rules`, so `Database.RulesOk` and the two signature-level checks hold
verbatim at every intermediate state. -/
theorem runReach_declaredTerms {R : RulesetName} {db d : Database} (hwf : db.WF)
    (hdt : db.DeclaredTerms) (hr : db.RulesOk) (hml : db.sig.MergesLegal)
    (hmw : db.sig.MergesWidthOk) (h : Relation.ReflTransGen (RunStep R) db d) :
    d.DeclaredTerms := by
  refine (RunReach.induction
    (P := fun x => x.WF ∧ x.DeclaredTerms ∧ x.sig = db.sig ∧ x.rules = db.rules)
    ?_ h ⟨hwf, hdt, rfl, rfl⟩).2.1
  rintro x y ⟨hxw, hxd, hxs, hxr⟩ hstep
  have hro : x.RulesOk := fun r hr' => hxs ▸ hr r (hxr ▸ hr')
  have hxml : Signature.MergesLegal (RunRules R x).sig := by
    rw [RunRules.sig (R := R) (db := x), hxs]; exact hml
  have hxmw : Signature.MergesWidthOk (RunRules R x).sig := by
    rw [RunRules.sig (R := R) (db := x), hxs]; exact hmw
  have hyr : y.rules = db.rules := by
    rw [(MergeClosure.envRules hstep).2]
    simpa only [RunRules, Database.sUnion_rules] using hxr
  exact ⟨hstep.wf hxw, mergeClosure_declaredTerms (RunRules.wf hxw)
      (runRules_declaredTerms hxw hxd hro) hxml hxmw hstep,
    by rw [hstep.sig]; exact hxs, hyr⟩

theorem cmdReach_declaredTerms {db d : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) {c : Cmd} (hw : c.WidthOk db.sig) (hsl : c.SetLegal db.sig)
    (hfresh : c.DeclFresh db.sig) (hml : (c.sigBind db.sig).MergesLegal)
    (hmw : (c.sigBind db.sig).MergesWidthOk) (h : cmdReach db c d) : d.DeclaredTerms := by
  cases c with
  | saturate R =>
    exact runReach_declaredTerms hwf hdt hr hml hmw (show SaturateReach R db d from h).1
  | _ => exact cmdEffect_declaredTerms hwf hdt hr hw hsl hfresh h

/-- The two signature-level invariants are read at the signature the command *installs*, as
`Cmd.WidthOk` and `Cmd.MergeDeclared` are: that is the signature the merge phase runs
against. -/
theorem cmdStep_declaredTerms {db d : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) {c : Cmd} (hw : c.WidthOk db.sig) (hsl : c.SetLegal db.sig)
    (hfresh : c.DeclFresh db.sig) (hml : (c.sigBind db.sig).MergesLegal)
    (hmw : (c.sigBind db.sig).MergesWidthOk) (h : CmdStep db c d) : d.DeclaredTerms := by
  obtain ⟨x, hx, hcl⟩ := h
  have hxs : x.sig = c.sigBind db.sig := cmdReach_sig hx
  exact mergeClosure_declaredTerms (cmdReach_wf hwf hx)
    (cmdReach_declaredTerms hwf hdt hr hw hsl hfresh hml hmw hx)
    (by rw [hxs]; exact hml) (by rw [hxs]; exact hmw) hcl

/-- What `Program.WidthOk`, `Program.SetLegal` and `Program.DeclsFresh` cannot say, checked
at the state each command actually runs in — the weakest place to check it, as
`FDatabase.ProgramLegal` does. Two things: the rules the state holds pass the action-block
checks, and the signature the command leaves has width-checked, `set`-legal `:merge` bodies.
Neither is a condition on the program text — a rule outlives the signature it was added
under, and `Cmd.WidthOk` reaches a `:merge` only at the declaration that installs it. -/
def Database.RunLegal : Database → Program → Prop
  | _, [] => True
  | db, c :: cs =>
      db.RulesOk ∧ Signature.MergesLegal (c.sigBind db.sig) ∧
        Signature.MergesWidthOk (c.sigBind db.sig) ∧
        ∀ d, CmdStep db c d → Database.RunLegal d cs

/-- **A run preserves `DeclaredTerms`.** The three front-end checks thread through the
induction on their own: each is read at the signature the earlier commands leave, which is
the signature the run has reached by `CmdStep.sig`. -/
theorem programStep_declaredTerms {db db' : Database} {p : Program}
    (h : ProgramStep db p db') :
    db.WF → db.DeclaredTerms → Program.WidthOk p db.sig → Program.SetLegal p db.sig →
      Program.DeclsFresh p db.sig → db.RunLegal p → db'.DeclaredTerms := by
  induction h with
  | nil => exact fun _ hdt _ _ _ _ => hdt
  | @cons db x d' c cs hstep _ ih =>
    intro hwf hdt hw hsl hfresh hl
    have hxs : x.sig = c.sigBind db.sig := CmdStep.sig hstep
    exact ih (CmdStep.wf hwf hstep)
      (cmdStep_declaredTerms hwf hdt hl.1 hw.1 hsl.1 hfresh.1 hl.2.1 hl.2.2.1 hstep)
      (by rw [hxs]; exact hw.2) (by rw [hxs]; exact hsl.2) (by rw [hxs]; exact hfresh.2)
      (hl.2.2.2 x hstep)

/-- **Every state a legal run reaches from `Database.empty` is `DeclaredTerms`.** -/
theorem reachable_declaredTerms {p : Program} {db : Database}
    (hw : Program.WidthOk p Database.empty.sig)
    (hsl : Program.SetLegal p Database.empty.sig)
    (hfresh : Program.DeclsFresh p Database.empty.sig)
    (hl : Database.empty.RunLegal p) (h : ProgramStep Database.empty p db) :
    db.DeclaredTerms :=
  programStep_declaredTerms h Database.WF.empty Database.empty_declaredTerms hw hsl hfresh hl

/-! ### Union-freedom, and where it puts `Recorded`

The two transports below move a *specification* fact along `Database.Recorded`, and both
are false in general for one reason: `Recorded` matches an equation only up to congruence,
so the run on the right-hand side happens under a *congruent* environment, and
`ordering-min`/`ordering-max` choose by `Term.blt` rather than by e-class, so they are not
stable there.

One of the two things that buys them back is `Action.UnionFree`. A `union` is the only
action that asserts an equation between distinct terms, so a program with none keeps every
state's `eqs` **diagonal**; on a diagonal state `Cong` is the identity, and
`Database.Recorded` collapses to `Database.Contained` — along which both transports are
already proved (`MergeStep.transport`, `MergeClosure.transport`). Nothing is congruent but
equal, so no choice operator is ever asked to be stable.

This is where `Encoding/Encode.lean` lives: `encodeAction` turns a source `union` into
`.set @UF [ordering-max x₁ x₂] [ordering-min x₁ x₂]`, so `encode` emits `ordering-max`
inside a rule action and *no* `Action.union` at all. The other thing that buys them back —
ordering-freedom, which covers the programs this one excludes and vice versa — is the
section "Ordering-freedom, and where it puts `Recorded`" below.

`Database.Diag` is the state-level reading; `Signature.UnionFree` and `Database.NoUnions`
are what carry it across a merge phase and a rule phase, which read their actions from the
signature and the rule set rather than from the command. -/

/-- Every asserted equation is reflexive. -/
def Database.Diag (db : Database) : Prop := ∀ p ∈ db.eqs, p.1 = p.2

/-- A state whose merge bodies and rule heads assert nothing either. The three fields are
what the three phases read: `diag` is the state, `sig` is what a `MergeStep` runs, `rules`
is what a `RunRules` runs. -/
structure Database.NoUnions (db : Database) : Prop where
  diag : db.Diag
  sig : Signature.UnionFree db.sig
  rules : ∀ r ∈ db.rules, Actions.UnionFree r.actions

/-- The ordering-free arm's state-level reading. Two fields rather than three, and no
clause about `eqs`: the condition is about *positions* — where a choice primitive may be
applied — so nothing has to be said about what the state asserts. `sig` is what a
`MergeStep` runs, `rules` is what a `RunRules` runs. -/
structure Database.NoOrdering (db : Database) : Prop where
  sig : Signature.OrderingFree db.sig
  rules : ∀ r ∈ db.rules, Rule.OrderingFree r

namespace Database

/-- A subset of a diagonal is diagonal. -/
theorem Diag.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hd : d₂.Diag) : d₁.Diag :=
  fun p hp => hd p (h.eqs hp)

theorem Diag.addTerm {db : Database} (h : db.Diag) (t : Term) : (db.addTerm t).Diag := by
  rintro p (hp | ⟨s, -, rfl⟩)
  · exact h p hp
  · rfl

theorem Diag.addTerms {db : Database} (h : db.Diag) (ts : List Term) :
    (db.addTerms ts).Diag := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

/-- `withOperands` posits its operands reflexively, so it cannot break diagonality. -/
theorem Diag.withOperands {db : Database} (h : db.Diag) (ts : List Term) :
    (db.withOperands ts).Diag := h.addTerms ts

end Database

/-- **On a diagonal state congruence is equality.** No equation relates two distinct terms,
so `assert` cannot and neither can `congr`, whose arguments are equal by the pointwise
hypothesis. -/
theorem Cong.eq_of_diag {E : Database} (h : E.Diag) : ∀ {a b : Term}, Cong E a b → a = b := by
  intro a b hc
  induction hc using Cong.rec (motive_2 := fun as bs _ => as = bs) with
  | assert hab => exact h _ hab
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ _ _ ihl => exact congrArg _ ihl
  | nil => rfl
  | cons _ _ ih ihl => exact congrArg₂ List.cons ih ihl

theorem congOn_eq_of_diag {E : Database} (h : E.Diag) {ts : List Term} {a b : Term}
    (hc : CongOn E ts a b) : a = b := Cong.eq_of_diag (h.withOperands ts) hc

/-- **`Recorded` is `Contained` on a diagonal recorder.** The witness equation is congruent
to the recorded one, and on a diagonal state that means equal. This is the whole content of
union-freedom: each of the two `Recorded` transports is the proved `Contained` one composed
with this and with `Database.Recorded.of_contained`. -/
theorem Database.Recorded.contained_of_diag {A C : Database} (hc : A.Recorded C)
    (hd : C.Diag) : A.Contained C := by
  refine ⟨fun p hp => ?_⟩
  obtain ⟨q, hq, h₁, h₂⟩ := hc.eqs p hp
  have : p = q := Prod.ext (congOn_eq_of_diag hd h₁) (congOn_eq_of_diag hd h₂)
  exact this ▸ hq

/-- What the interpreter's own state inherits: it records into a diagonal witness, so its
equations are among that witness's and diagonal too. -/
theorem Database.NoUnions.of_recorded {A C : Database} (hn : C.NoUnions) (hc : A.Recorded C)
    (hsig : A.sig = C.sig) (hrules : A.rules = C.rules) : A.NoUnions where
  diag := Diag.mono (hc.contained_of_diag hn.diag) hn.diag
  sig := by rw [hsig]; exact hn.sig
  rules := by rw [hrules]; exact hn.rules

/-! #### Diagonality is preserved

One clause per way the specification writes `eqs`. Only `evalAction`'s `.union` writes a
pair between distinct terms, so each of these is the corresponding case analysis with that
case discharged by the hypothesis. -/

/-- Every action but `union` writes through `addTerm`. -/
theorem evalAction_diag {db db' : Database} {a : Action} (hu : a.UnionFree)
    (hd : db.Diag) (h : evalAction db a = some db') : db'.Diag := by
  cases a with
  | expr e =>
    rw [evalAction, Option.map_eq_some_iff] at h
    obtain ⟨t, -, rfl⟩ := h
    exact hd.addTerm t
  | letBind v e =>
    rw [evalAction, Option.map_eq_some_iff] at h
    obtain ⟨t, -, rfl⟩ := h
    exact hd.addTerm t
  | union e₁ e₂ => exact absurd hu id
  | set f args out =>
    rw [evalAction, Option.bind_eq_some_iff] at h
    obtain ⟨as, -, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨vs, -, rfl⟩ := h
    exact hd.addTerm _

theorem evalActions_diag {db db' : Database} {as : List Action} (hu : Actions.UnionFree as)
    (hd : db.Diag) (h : evalActions db as = some db') : db'.Diag := by
  induction as generalizing db with
  | nil => rw [evalActions_nil, Option.some.injEq] at h; exact h ▸ hd
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      exact ih hu.2 (evalAction_diag hu.1 hd hv) h

theorem evalLocalActions_diag {db db' : Database} {as : List Action} {σ : Env}
    (hu : Actions.UnionFree as) (hd : db.Diag) (h : evalLocalActions db as σ = some db') :
    db'.Diag := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  exact evalActions_diag (db := { db with env := db.env ++ σ }) (db' := d) hu hd hv

/-- A merge phase runs the body the *signature* names, so this is where
`Signature.UnionFree` is spent. -/
theorem MergeStep.diag {d₁ d₂ : Database} (hs : Signature.UnionFree d₁.sig)
    (hd : d₁.Diag) (h : MergeStep d₁ d₂) : d₂.Diag := by
  cases h with
  | @collide d f dc as bs a b vs body res hdc hmg _ _ _ _ _ hbody _ =>
    exact (evalActions_diag (db := { d₁ with env := mergeEnv a b })
      (hs f dc hdc _ hmg) hd hbody).addTerm _

theorem MergeClosure.diag {d₁ d₂ : Database} (hs : Signature.UnionFree d₁.sig)
    (hd : d₁.Diag) (h : MergeClosure d₁ d₂) : d₂.Diag := by
  induction h with
  | refl => exact hd
  | @tail b c hcl hstep ih =>
    exact hstep.diag (by rw [MergeClosure.sig hcl]; exact hs) ih

/-- A round's rule phase runs every rule the state carries, so this is where the `rules`
clause is spent. -/
theorem RunRules.diag {R : RulesetName} {db : Database} (hn : db.NoUnions) :
    (RunRules R db).Diag := by
  rintro p (hp | hp)
  · exact hn.diag p hp
  · obtain ⟨d, ⟨r, hr, -, σ, -, hσ⟩, hp'⟩ := Set.mem_iUnion₂.mp hp
    exact evalLocalActions_diag (hn.rules r hr) hn.diag hσ p hp'

/-! ### Ordering-freedom, and where it puts `Recorded`

The other condition that buys the two transports, and the one that admits `union`.

`Recorded` matches an equation only up to congruence, so the run on the right-hand side
happens under a *congruent* environment. Everything `Expr.eval` does is stable there except
the two choice primitives: `ordering-min`/`ordering-max` read `Term.blt`. `min`/`max` are
**not** a problem — `Database.WF.litsIsolated` and `Cong.eq_of_isLit` make a literal's class
a singleton, so congruent operands to them *are* those operands (`Prim.apply_cong`).

So `Spec/Scope.lean`'s `Program.OrderingFree` is enough, and unlike `Program.UnionFree` it
restricts no `union` at all. Four things carry it:

* `Owes` — what the specification owes one value the implementation computed: the two are
  congruent, and every *subterm* of the implementation's value is congruent to a term the
  specification holds. The second clause is what `Database.Recorded` asks of the reflexive
  equations `Database.addTerm` writes, and it is why the relation is about subterms rather
  than about the value alone.
* `cong_pin` — **conservativity, sharpened**: a derivation ending in a term the database
  holds needs no phantom operand but the *source's own* subterms. `Conservativity`'s model
  proves it, and it is what pins every congruence below into the one-term ambient
  `Database.Recorded` and `Matches` are stated in.
* `recorded_entry` — **head extraction**: an entry of `f` the implementation holds is
  matched by an entry of `f` the specification holds, column by column. `Recorded` matches
  the *equation*, and it takes an induction over the derivation (`reach_iff`) to see that
  the witness can be taken to have the same head. Without this a `MergeStep` cannot even be
  *stated* at the specification, let alone run.
* `eval_owes` — **ordering-free evaluation is congruence-stable**, which is the fact the
  whole condition exists to supply.

The consequence is the two transports at ordering-free positions:
`MergeStep.transport_owes` and `RuleResults.mono_owes`. Note where the merge one lands: a
`:merge` body runs under `mergeEnv`, built from value columns `Recorded` moves *before* any
body expression is evaluated — and that is not an obstruction, because a moved environment
is congruent and evaluation respects congruence. -/

section OrderingFree
open Conservativity

/-- `x` is an application whose head names an entry of `C` at `E`-congruent arguments. -/
def Reach (C E : Database) (x : Term) : Prop :=
  ∃ f args args', x = .app f args ∧ Term.app f args' ∈ C.terms ∧ CongList E args args'

theorem reach_self {C E : Database} (hCE : C.Contained E)
    (hsub : ∀ t ∈ C.terms, t.subterms ⊆ C.terms) {f : FnName} {args : List Term}
    (hx : Term.app f args ∈ C.terms) : Reach C E (.app f args) :=
  ⟨f, args, args, rfl, hx, CongList.refl fun a ha =>
    hCE.terms (hsub _ hx (Term.IsSubterm.arg ha (.refl a)))⟩

/-- **Head extraction.** In an ambient that adds only reflexive equations to `C`, a term
that reaches an entry of `C` stays one along every derivation. -/
theorem reach_iff {C E : Database} (hCE : C.Contained E)
    (hE : ∀ p ∈ E.eqs, p ∈ C.eqs ∨ p.1 = p.2)
    (hsub : ∀ t ∈ C.terms, t.subterms ⊆ C.terms) (hlit : C.LitsIsolated)
    {x y : Term} (h : Cong E x y) : Reach C E x ↔ Reach C E y := by
  have hforall : ∀ {as bs : List Term},
      List.Forall₂ (fun a b => Cong E a b ∧ (Reach C E a ↔ Reach C E b)) as bs →
      List.Forall₂ (Cong E) as bs := fun h => h.imp (fun {_ _} h => h.1)
  refine (Cong.le (R := fun a b => Cong E a b ∧ (Reach C E a ↔ Reach C E b))
    (fun a b hab => ⟨.assert hab, ?_⟩) (fun _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩)
    (fun f as bs hma hmb hl => ⟨Cong.congr' hma hmb (hforall hl), ?_⟩) h).2
  · -- an asserted pair: either `C`'s own, or reflexive
    rcases hE _ hab with hp | hp
    · have hm := eqsInTerms_free (Cong.assert (db := C) hp)
      cases a with
      | lit l => rw [show b = Term.lit l from (hlit _ hp (Or.inl rfl)).symm]
      | app f args =>
        cases b with
        | lit m => exact absurd (hlit _ hp (Or.inr rfl)) (by simp)
        | app g brgs => exact iff_of_true (reach_self hCE hsub hm.1) (reach_self hCE hsub hm.2)
    · simp only at hp; rw [hp]
  · -- a congruence step: the same entry serves both sides
    have hcl : CongList E as bs := CongList.ofForall₂ (hforall hl)
    constructor
    · rintro ⟨f', args, args', heq, hmem, hc⟩
      obtain ⟨rfl, rfl⟩ := Term.app.inj heq
      exact ⟨f, bs, args', rfl, hmem, hcl.symm.trans hc⟩
    · rintro ⟨f', args, args', heq, hmem, hc⟩
      obtain ⟨rfl, rfl⟩ := Term.app.inj heq
      exact ⟨f, as, args', rfl, hmem, hcl.trans hc⟩

/-! #### Congruence-stable evaluation -/

/-- Widening a pinned ambient to a term the pinned one occurs in. -/
theorem congOn_subterm {D : Database} {s t a b : Term} (hs : s ∈ t.subterms)
    (h : CongOn D [s] a b) : CongOn D [t] a b := by
  refine Cong.mono ⟨fun p hp => ?_⟩ h
  rcases mem_addTerms_eqs' [s] D p hp with hq | ⟨u, hu, x, hx, rfl⟩
  · exact eqs_subset_addTerms [t] D hq
  · rw [List.mem_singleton] at hu
    exact refl_mem_addTerms (Term.subterms_subset_of_mem (hu ▸ hs) hx) [t] D (by simp)

/-- **What a recorder owes one evaluated value.** At every ambient holding the recorder's
own value, the two values are congruent and each subterm of the recorded one is congruent
to a term the ambient holds — which is exactly the clause `Database.Recorded` asks of the
reflexive equations `Database.addTerm` writes. -/
def Owes (E : Database) (t t' : Term) : Prop :=
  ∀ F : Database, E.Contained F → (∀ s ∈ t'.subterms, s ∈ F.terms) →
    CongOn F [t] t t' ∧ ∀ s ∈ t.subterms, ∃ u ∈ F.terms, CongOn F [s] s u

theorem Owes.mono {E E' : Database} (h : E.Contained E') {t t' : Term} (ho : Owes E t t') :
    Owes E' t t' := fun F hF hsub => ho F (h.trans hF) hsub

/-- `Owes` reads `eqs` alone, so the recorder's environment may be replaced. -/
theorem Owes.setEnv {E : Database} {σ : Env} {t t' : Term} (ho : Owes E t t') :
    Owes ({ E with env := σ } : Database) t t' := fun F hF hsub => ho F ⟨hF.eqs⟩ hsub

/-- A value the recorder holds verbatim owes nothing: the ambient posits it. -/
theorem Owes.refl {E : Database} {t : Term} : Owes E t t := fun _ _ hsub =>
  ⟨mem_congOn_self (by simp), fun s hs => ⟨s, hsub s hs, mem_congOn_self (by simp)⟩⟩

theorem owes_list {E F : Database} (hF : E.Contained F) {u : Term} :
    ∀ {ts ts' : List Term}, List.Forall₂ (Owes E) ts ts' →
      (∀ a' ∈ ts', ∀ s ∈ a'.subterms, s ∈ F.terms) → (∀ a ∈ ts, a ∈ u.subterms) →
      (∀ a ∈ ts, ∀ s ∈ a.subterms, ∃ x ∈ F.terms, CongOn F [s] s x) ∧
        CongList (F.withOperands [u]) ts ts'
  | _, _, .nil, _, _ => ⟨by simp, .nil⟩
  | a :: ts, a' :: ts', .cons ho hrest, hsub, hu => by
      obtain ⟨hc, hm⟩ := ho F hF (fun s hs => hsub a' (by simp) s hs)
      obtain ⟨hms, hcs⟩ := owes_list hF hrest (fun x hx => hsub x (by simp [hx]))
        (fun x hx => hu x (by simp [hx]))
      refine ⟨fun x hx => ?_, .cons (congOn_subterm (hu a (by simp)) hc) hcs⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hm
      · exact hms x hx

theorem Owes.app {E : Database} {f : FnName} {ts ts' : List Term}
    (h : List.Forall₂ (Owes E) ts ts') : Owes E (.app f ts) (.app f ts') := by
  intro F hF hsub
  have hmem' : Term.app f ts' ∈ F.terms := hsub _ (Term.self_mem_subterms _)
  obtain ⟨hms, hlist⟩ := owes_list (u := Term.app f ts) hF h
    (fun a' ha' s hs => hsub s (Term.subterms_app ▸
      Set.mem_insert_of_mem _ (Set.mem_biUnion ha' hs)))
    (fun a ha => Term.arg_subterms ha (Term.self_mem_subterms a))
  have hcong : CongOn F [Term.app f ts] (.app f ts) (.app f ts') :=
    Cong.congr (mem_congOn_self (by simp))
      (Cong.mono (Database.Contained.addTerms _ _) hmem') hlist
  refine ⟨hcong, fun s hs => ?_⟩
  rw [Term.subterms_app] at hs
  rcases Set.mem_insert_iff.mp hs with rfl | hs
  · exact ⟨.app f ts', hmem', hcong⟩
  · obtain ⟨a, ha, hsa⟩ := Set.mem_iUnion₂.mp hs
    exact hms a ha s hsa

theorem litsIsolated_addTerms {db : Database} (h : db.LitsIsolated) (ts : List Term) :
    (db.addTerms ts).LitsIsolated := fun p hp =>
  (mem_addTerms_eqs ts db p hp).elim (h p) (fun hq _ => hq)

/-- The two `i64` primitives are the ordering-free ones. -/
theorem prim_int_of_orderingFree {f : FnName} {p : Prim} (hp : Prim.ofName f = some p)
    (hof : Prim.ofName f ≠ some .orderingMin ∧ Prim.ofName f ≠ some .orderingMax) :
    p = .intMin ∨ p = .intMax := by
  cases p with
  | orderingMin => exact absurd hp hof.1
  | orderingMax => exact absurd hp hof.2
  | intMin => exact Or.inl rfl
  | intMax => exact Or.inr rfl

/-- A value the recorder owes and that is a **literal** it holds verbatim: a literal's
class is a singleton, so the two values are equal. -/
theorem owes_eq_of_isLit {E : Database} (hlit : E.LitsIsolated) : ∀ {ts ts' : List Term},
    List.Forall₂ (Owes E) ts ts' → (∀ a ∈ ts, a.isLit) → ts = ts'
  | _, _, .nil, _ => rfl
  | a :: ts, a' :: ts', .cons ho hrest, hl => by
      have hsub : ∀ s ∈ a'.subterms, s ∈ (E.withOperands [a']).terms := fun s hs =>
        Database.addTerms_terms ▸ Or.inr ⟨a', by simp, hs⟩
      have hc := (ho (E.withOperands [a']) (Database.Contained.addTerms _ _) hsub).1
      have : a = a' := Cong.eq_of_isLit
        (litsIsolated_addTerms (litsIsolated_addTerms hlit [a']) [a]) hc
        (Or.inl (hl a (by simp)))
      rw [this, owes_eq_of_isLit hlit hrest (fun x hx => hl x (by simp [hx]))]

mutual

/-- **Ordering-free evaluation is congruence-stable.** Under an environment whose values
the recorder owes, the expression evaluates there too, and the recorder owes its value.
`min`/`max` survive: they answer only on literals, a literal's class is a singleton, so
congruent operands *are* the operands. `ordering-min`/`ordering-max` are what the
hypothesis excludes. -/
theorem eval_owes {E : Database} (hlit : E.LitsIsolated) {sig : Signature} {σ σ' : Env}
    (henv : ∀ (v : Var) (t : Term), Env.lookup v σ = some t →
      ∃ t', Env.lookup v σ' = some t' ∧ Owes E t t')
    {e : Expr} (hof : Expr.OrderingFree e) {t : Term} (he : e.eval sig σ = some t) :
    ∃ t', e.eval sig σ' = some t' ∧ Owes E t t' := by
  match e with
  | .lit l =>
    rw [Expr.eval_lit, Option.some_inj] at he
    exact ⟨.lit l, rfl, he ▸ Owes.refl⟩
  | .var v =>
    rw [Expr.eval_var] at he
    exact henv v t he
  | .app f args =>
    have hargs : Expr.OrderingFreeList args := fun g hg => hof g (by simp [Expr.fns, hg])
    cases hp : Prim.ofName f with
    | some p =>
      rw [Expr.eval_app_prim hp, Option.bind_eq_some_iff] at he
      obtain ⟨ts, hts, happ⟩ := he
      obtain ⟨ts', hts', hall⟩ := evalList_owes hlit henv hargs hts
      have hpm := prim_int_of_orderingFree hp (hof f (by simp [Expr.fns]))
      have heq : ts = ts' :=
        owes_eq_of_isLit hlit hall (Prim.isLit_of_apply hpm happ)
      refine ⟨t, ?_, Owes.refl⟩
      rw [Expr.eval_app_prim hp, hts', Option.bind_some, ← heq, happ]
    | none =>
      by_cases hc : sig.IsCtor f
      · rw [Expr.eval_app_ctor hp hc, Option.map_eq_some_iff] at he
        obtain ⟨ts, hts, rfl⟩ := he
        obtain ⟨ts', hts', hall⟩ := evalList_owes hlit henv hargs hts
        exact ⟨.app f ts', by rw [Expr.eval_app_ctor hp hc, hts', Option.map_some],
          Owes.app hall⟩
      · rw [Expr.eval_app_not_ctor hp hc] at he; exact absurd he (by simp)

theorem evalList_owes {E : Database} (hlit : E.LitsIsolated) {sig : Signature} {σ σ' : Env}
    (henv : ∀ (v : Var) (t : Term), Env.lookup v σ = some t →
      ∃ t', Env.lookup v σ' = some t' ∧ Owes E t t')
    {es : List Expr} (hof : Expr.OrderingFreeList es) {ts : List Term}
    (he : Expr.evalList sig es σ = some ts) :
    ∃ ts', Expr.evalList sig es σ' = some ts' ∧ List.Forall₂ (Owes E) ts ts' := by
  match es with
  | [] =>
    rw [Expr.evalList_nil, Option.some_inj] at he
    exact ⟨[], rfl, he ▸ List.Forall₂.nil⟩
  | e :: es =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
    obtain ⟨u, hu, hmap⟩ := he
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hmap
    obtain ⟨u', hu', ho⟩ := eval_owes hlit henv
      (fun g hg => hof g (List.mem_union_iff.mpr (Or.inl hg))) hu
    obtain ⟨us', hus', hall⟩ := evalList_owes hlit henv
      (fun g hg => hof g (List.mem_union_iff.mpr (Or.inr hg))) hus
    exact ⟨u' :: us', by rw [Expr.evalList_cons, hu', Option.bind_some, hus', Option.map_some],
      .cons ho hall⟩

end

/-- `Database.Recorded` after adding a term on each side, where the recorder's term is one
the recorder **owes** rather than the same one. This is `Recorded.addTerm_congr` with the
value columns free to move as well as the key. -/
theorem recorded_addTerm_owes {A C : Database} (hc : A.Recorded C) (hwf : C.WF)
    {t t' : Term} (ho : Owes C t t') : (A.addTerm t).Recorded (C.addTerm t') := by
  have hsub : ∀ s ∈ t'.subterms, s ∈ (C.addTerm t').terms := fun s hs =>
    Database.addTerm_terms ▸ Or.inr hs
  obtain ⟨-, hm⟩ := ho (C.addTerm t') (Database.Contained.addTerm t' C) hsub
  refine ⟨fun p hp => ?_⟩
  rcases hp with hp | ⟨s, hs, rfl⟩
  · obtain ⟨q, hq, hc₁, hc₂⟩ := hc.eqs p hp
    exact ⟨q, Or.inl hq, congOn_mono (Database.Contained.addTerm t' C) hc₁,
      congOn_mono (Database.Contained.addTerm t' C) hc₂⟩
  · obtain ⟨u, hu, hcu⟩ := hm s hs
    have hq : (u, u) ∈ (C.addTerm t').eqs := (hwf.addTerm t').eqsRefl u hu
    have hwiden : CongOn (C.addTerm t') [s, s] s u :=
      Cong.mono ⟨withOperands_mono_list (by simp)⟩ hcu
    exact ⟨(u, u), hq, hwiden, hwiden⟩

/-- The environment clause: every binding the recorder can be asked for, it owes. -/
def EnvOwes (E : Database) (σ σ' : Env) : Prop :=
  ∀ (v : Var) (t : Term), Env.lookup v σ = some t →
    ∃ t', Env.lookup v σ' = some t' ∧ Owes E t t'

theorem EnvOwes.mono {E E' : Database} (h : E.Contained E') {σ σ' : Env}
    (ho : EnvOwes E σ σ') : EnvOwes E' σ σ' := fun v t ht =>
  let ⟨t', ht', how⟩ := ho v t ht
  ⟨t', ht', how.mono h⟩

theorem EnvOwes.setEnv {E : Database} {τ : Env} {σ σ' : Env} (ho : EnvOwes E σ σ') :
    EnvOwes ({ E with env := τ } : Database) σ σ' := fun v t ht =>
  let ⟨t', ht', how⟩ := ho v t ht
  ⟨t', ht', how.setEnv⟩

theorem EnvOwes.cons {E : Database} {σ σ' : Env} (ho : EnvOwes E σ σ') (v : Var)
    {t t' : Term} (h : Owes E t t') : EnvOwes E ((v, t) :: σ) ((v, t') :: σ') := by
  intro u x hx
  rw [Env.lookup_cons] at hx
  split at hx
  · exact ⟨t', by rw [Env.lookup_cons, if_pos (by assumption)], Option.some.inj hx ▸ h⟩
  · obtain ⟨y, hy, hoy⟩ := ho u x hx
    exact ⟨y, by rw [Env.lookup_cons, if_neg (by assumption)]; exact hy, hoy⟩

/-- **The state relation the ordering-free transport maintains**: the recorder records the
run, agrees on the signature the run reads, and owes every value the run can look up. -/
structure StateOwes (d d' : Database) : Prop where
  recorded : d.Recorded d'
  sig : d.sig = d'.sig
  env : EnvOwes d' d.env d'.env

theorem forall₂_append {α β : Type} {R : α → β → Prop} : ∀ {as as' : List α} {bs bs' : List β},
    List.Forall₂ R as bs → List.Forall₂ R as' bs' → List.Forall₂ R (as ++ as') (bs ++ bs')
  | _, _, _, _, .nil, h₂ => h₂
  | _ :: _, _, _, _, .cons hab hl, h₂ => .cons hab (forall₂_append hl h₂)

/-- `Owes` for a whole application: the concatenated columns. -/
theorem owes_append {E : Database} {f : FnName} {as as' vs vs' : List Term}
    (h₁ : List.Forall₂ (Owes E) as as') (h₂ : List.Forall₂ (Owes E) vs vs') :
    Owes E (.app f (as ++ vs)) (.app f (as' ++ vs')) :=
  Owes.app (forall₂_append h₁ h₂)

/-- **One ordering-free action transports along `StateOwes`.** -/
theorem evalAction_owes {A C d : Database} (hf : StateOwes A C) (hwf : C.WF)
    {a : Action} (hof : Action.OrderingFree a) (h : evalAction A a = some d) :
    ∃ d', evalAction C a = some d' ∧ StateOwes d d' := by
  have hlit := hwf.litsIsolated
  rcases evalAction_eq_some h with ⟨e, t, rfl, hv, rfl⟩ | ⟨v, e, t, rfl, hv, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, hnl, rfl⟩ | ⟨f, args, out, as, vs, rfl, hv₁, hv₂, rfl⟩
  · obtain ⟨t', hv', ho⟩ := eval_owes hlit hf.env hof (hf.sig ▸ hv)
    refine ⟨C.addTerm t', by simp [evalAction, hv'], ?_⟩
    exact ⟨recorded_addTerm_owes hf.recorded hwf ho, hf.sig,
      hf.env.mono (Database.Contained.addTerm t' C)⟩
  · obtain ⟨t', hv', ho⟩ := eval_owes hlit hf.env hof (hf.sig ▸ hv)
    refine ⟨{ C.addTerm t' with env := (v, t') :: C.env }, by simp [evalAction, hv'], ?_⟩
    refine ⟨(recorded_addTerm_owes hf.recorded hwf ho).setEnv _ _, hf.sig, ?_⟩
    exact ((hf.env.mono (Database.Contained.addTerm t' C)).cons v
      (ho.mono (Database.Contained.addTerm t' C))).setEnv
  · obtain ⟨t₁', hv₁', ho₁⟩ := eval_owes hlit hf.env hof.1 (hf.sig ▸ hv₁)
    obtain ⟨t₂', hv₂', ho₂⟩ := eval_owes hlit hf.env hof.2 (hf.sig ▸ hv₂)
    -- the recorder's operands are not literals either: a literal's class is a singleton
    have hpair : ∀ {x x' : Term}, Owes C x x' → ¬ x.isLit → ¬ x'.isLit := by
      intro x x' ho hx hx'
      have hsub : ∀ s ∈ x'.subterms, s ∈ (C.withOperands [x']).terms := fun s hs =>
        Database.addTerms_terms ▸ Or.inr ⟨x', by simp, hs⟩
      have hc := (ho (C.withOperands [x']) (Database.Contained.addTerms _ _) hsub).1
      exact hx ((Cong.eq_of_isLit (litsIsolated_addTerms
        (litsIsolated_addTerms hlit [x']) [x]) hc (Or.inr hx')) ▸ hx')
    simp only [not_or, Bool.not_eq_true] at hnl
    have hnl₁ : ¬ t₁'.isLit := hpair ho₁ (by simp [hnl.1])
    have hnl₂ : ¬ t₂'.isLit := hpair ho₂ (by simp [hnl.2])
    refine ⟨C.addEq t₁' t₂', by
      simp only [evalAction, hv₁', hv₂', Option.bind_some]
      rw [if_neg (by simp [Bool.eq_false_iff.mpr, hnl₁, hnl₂])], ?_⟩
    refine ⟨?_, hf.sig, hf.env.mono (Database.Contained.addEq t₁' t₂' C)⟩
    have hsub : ∀ {x' : Term}, x' = t₁' ∨ x' = t₂' → ∀ s ∈ x'.subterms,
        s ∈ (C.addEq t₁' t₂').terms := by
      rintro x' (rfl | rfl) s hs
      · exact Database.addEq_terms ▸ Or.inl (Or.inr hs)
      · exact Database.addEq_terms ▸ Or.inr hs
    have hstep : ((A.addTerm t₁).addTerm t₂).Recorded ((C.addTerm t₁').addTerm t₂') :=
      recorded_addTerm_owes (recorded_addTerm_owes hf.recorded hwf ho₁) (hwf.addTerm t₁')
        (ho₂.mono (Database.Contained.addTerm t₁' C))
    have hins : ((C.addTerm t₁').addTerm t₂').Contained (C.addEq t₁' t₂') :=
      ⟨Set.subset_insert _ _⟩
    refine ⟨fun p hp => ?_⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · refine ⟨(t₁', t₂'), Set.mem_insert _ _, ?_, ?_⟩
      · exact Cong.mono ⟨withOperands_mono_list (by simp)⟩
          ((ho₁ (C.addEq t₁' t₂') (Database.Contained.addEq t₁' t₂' C)
            (hsub (Or.inl rfl))).1)
      · exact Cong.mono ⟨withOperands_mono_list (by simp)⟩
          ((ho₂ (C.addEq t₁' t₂') (Database.Contained.addEq t₁' t₂' C)
            (hsub (Or.inr rfl))).1)
    · obtain ⟨q, hq, hc₁, hc₂⟩ := hstep.eqs p hp
      exact ⟨q, Set.mem_insert_of_mem _ hq, congOn_mono hins hc₁, congOn_mono hins hc₂⟩
  · obtain ⟨as', hv₁', ho₁⟩ := evalList_owes hlit hf.env hof.1 (hf.sig ▸ hv₁)
    obtain ⟨vs', hv₂', ho₂⟩ := evalList_owes hlit hf.env hof.2 (hf.sig ▸ hv₂)
    refine ⟨C.addTerm (.app f (as' ++ vs')), by simp [evalAction, hv₁', hv₂'], ?_⟩
    exact ⟨recorded_addTerm_owes hf.recorded hwf (owes_append ho₁ ho₂), hf.sig,
      hf.env.mono (Database.Contained.addTerm _ C)⟩

/-- **A whole ordering-free action block transports along `StateOwes`.** -/
theorem evalActions_owes {A C d : Database} (hf : StateOwes A C) (hwf : C.WF)
    {as : List Action} (hof : Actions.OrderingFree as) (h : evalActions A as = some d) :
    ∃ d', evalActions C as = some d' ∧ StateOwes d d' := by
  induction as generalizing A C with
  | nil =>
    rw [evalActions_nil, Option.some.injEq] at h
    exact ⟨C, rfl, h ▸ hf⟩
  | cons a as ih =>
    cases hv : evalAction A a with
    | none => simp [hv] at h
    | some A₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      obtain ⟨C₁, hC₁, hf₁⟩ := evalAction_owes hf hwf hof.1 hv
      obtain ⟨d', hd', hfd⟩ := ih hf₁ (evalAction_wf hwf hC₁) hof.2 h
      exact ⟨d', by rw [evalActions_cons, hC₁, Option.bind_some]; exact hd', hfd⟩

/-- **The pinning lemma.** A derivation ending in a term the database holds needs no
phantom operand but the *source's own* subterms: the interpretation of the source already
lands in the target's class, and the model's application branch is exactly a `Cong.congr`
against a database entry. -/
theorem cong_of_I {C : Database} (hsub : ∀ t ∈ C.terms, t.subterms ⊆ C.terms) :
    ∀ (x : Term) (y : Term), y ∈ C.terms → I C x = Quot.mk (Cong C) y → CongOn C [x] x y := by
  intro x
  induction x using Term.rec (motive_2 := fun us => ∀ (bs : List Term) (parent : Term),
      (∀ u ∈ us, u ∈ parent.subterms) → (∀ b ∈ bs, b ∈ C.terms) →
      IList C us = bs.map (Quot.mk (Cong C)) →
      CongList (C.withOperands [parent]) us bs) with
  | lit l =>
    intro y hy hI
    rcases eq_or_cong_of_cls_eq (hI : Quot.mk (Cong C) (.lit l) = Quot.mk (Cong C) y) with
      rfl | hc
    · exact mem_congOn_self (by simp)
    · exact Cong.mono (Database.Contained.addTerms _ _) hc
  | app f us ih =>
    intro y hy hI
    change Iapp C f (IList C us) = _ at hI
    by_cases hex : ∃ bs : List Term, Term.app f bs ∈ C.terms ∧
        IList C us = bs.map (Quot.mk (Cong C))
    · rw [Iapp, dif_pos hex] at hI
      obtain ⟨hmem, hmap⟩ := hex.choose_spec
      have hbs : ∀ b ∈ hex.choose, b ∈ C.terms := fun b hb =>
        hsub _ hmem (Term.IsSubterm.arg hb (.refl b))
      have hl := ih hex.choose (.app f us)
        (fun u hu => Term.arg_subterms hu (Term.self_mem_subterms u)) hbs hmap
      have hstep : CongOn C [Term.app f us] (.app f us) (.app f hex.choose) :=
        Cong.congr (mem_congOn_self (by simp))
          (Cong.mono (Database.Contained.addTerms _ _) hmem) hl
      rcases eq_or_cong_of_cls_eq hI with heq | hc
      · exact heq ▸ hstep
      · exact hstep.trans (Cong.mono (Database.Contained.addTerms _ _) hc)
    · exfalso
      rw [Iapp, dif_neg hex] at hI
      refine hex ⟨(IList C us).map Quot.out, ?_, ?_⟩
      · rcases eq_or_cong_of_cls_eq hI with heq | hc
        · exact heq ▸ hy
        · exact hc.mem_left
      · rw [List.map_map, show (Quot.mk (Cong C) ∘ Quot.out) = (id : Cls C → Cls C) from
          funext fun q => Quot.out_eq q, List.map_id]
  | nil =>
    rename_i bs parent _ _ hmap
    cases bs with
    | nil => exact .nil
    | cons b bs => simp [IList] at hmap
  | cons u us ihu ihus =>
    rename_i bs parent hpar hbs hmap
    cases bs with
    | nil => simp [IList] at hmap
    | cons b bs =>
      rw [show IList C (u :: us) = I C u :: IList C us from rfl, List.map_cons,
        List.cons.injEq] at hmap
      refine .cons ?_ (ihus bs parent (fun x hx => hpar x (by simp [hx]))
        (fun x hx => hbs x (by simp [hx])) hmap.2)
      exact congOn_subterm (hpar u (by simp))
        (ihu b (hbs b (by simp)) hmap.1)

/-- **Conservativity, sharpened.** A phantom ambient may be replaced by the source term's
own subterms whenever the target is a term the database holds. -/
theorem cong_pin {C E : Database} (hsub : ∀ t ∈ C.terms, t.subterms ⊆ C.terms)
    (hE : ∀ p ∈ E.eqs, p ∈ C.eqs ∨ p.1 = p.2) {x y : Term} (hy : y ∈ C.terms)
    (h : Cong E x y) : CongOn C [x] x y :=
  cong_of_I hsub x y hy ((I_congr hsub hE h).trans (I_eq_of_mem hsub y hy))

theorem operands_pair_subset {db : Database} {t : Term} :
    (db.withOperands [t, t]).eqs ⊆ (db.withOperands [t]).eqs := by
  rintro x ((h | h) | h)
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h

/-- **The `terms` clause of `Recorded`.** Every term the implementation holds is congruent
to one the specification holds, in the ambient pinned to that term alone. -/
theorem terms_clause {A C : Database} (h : A.Recorded C) (hwf : A.WF) {t : Term}
    (ht : t ∈ A.terms) : ∃ t' ∈ C.terms, CongOn C [t] t t' := by
  obtain ⟨q, hq, h₁, -⟩ := h.eqs (t, t) (hwf.eqsRefl t ht)
  exact ⟨q.1, (Cong.assert hq).trans (Cong.assert hq).symm,
    Cong.mono ⟨operands_pair_subset⟩ h₁⟩

theorem owes_of_congOn {C : Database} {x u : Term} (h : CongOn C [x] x u)
    (hall : ∀ s ∈ x.subterms, ∃ v ∈ C.terms, CongOn C [s] s v) : Owes C x u :=
  fun _ hF _ => ⟨congOn_mono hF h, fun s hs =>
    let ⟨v, hv, hcv⟩ := hall s hs
    ⟨v, hF.terms hv, congOn_mono hF hcv⟩⟩

/-- **Every term the implementation holds, the specification owes.** -/
theorem recorded_owes {A C : Database} (hc : A.Recorded C) (hwf : A.WF) {x : Term}
    (hx : x ∈ A.terms) : ∃ u ∈ C.terms, Owes C x u := by
  obtain ⟨u, hu, hcu⟩ := terms_clause hc hwf hx
  exact ⟨u, hu, owes_of_congOn hcu fun s hs =>
    terms_clause hc hwf (hwf.subtermClosed x hx hs)⟩

/-- Pointwise: a congruence in a phantom ambient between implementation terms and
specification terms is a pointwise `Owes`. -/
theorem owes_list_of_congList {A C : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) {E : Database} (hE : ∀ p ∈ E.eqs, p ∈ C.eqs ∨ p.1 = p.2) :
    ∀ {as bs : List Term}, CongList E as bs → (∀ a ∈ as, a ∈ A.terms) →
      (∀ b ∈ bs, b ∈ C.terms) → List.Forall₂ (Owes C) as bs
  | _, _, .nil, _, _ => .nil
  | a :: as, b :: bs, .cons hab hrest, hA, hC => by
      refine .cons ?_ (owes_list_of_congList hc hwfA hwfC hE hrest
        (fun x hx => hA x (by simp [hx])) (fun x hx => hC x (by simp [hx])))
      refine owes_of_congOn (cong_pin hwfC.subtermClosed hE (hC b (by simp)) hab)
        (fun s hs => terms_clause hc hwfA (hwfA.subtermClosed a (hA a (by simp)) hs))

/-- **The entry clause.** An entry of `f` the implementation holds is matched by an entry
of `f` the specification holds, column by column. This is what a `MergeStep` needs and what
`Database.Recorded` does not say outright: `Recorded` matches the *equation*, and it takes
the head-extraction argument to see that the witness can be taken to have the same head. -/
theorem recorded_entry {A C : Database} (hc : A.Recorded C) (hwfA : A.WF) (hwfC : C.WF)
    {f : FnName} {args : List Term} (ht : Term.app f args ∈ A.terms) :
    ∃ args', Term.app f args' ∈ C.terms ∧ List.Forall₂ (Owes C) args args' := by
  obtain ⟨t', ht', hcong⟩ := terms_clause hc hwfA ht
  have hE : ∀ p ∈ (C.withOperands [Term.app f args]).eqs, p ∈ C.eqs ∨ p.1 = p.2 :=
    fun p hp => mem_addTerms_eqs _ C p hp
  have hlit : (C.withOperands [Term.app f args]).LitsIsolated :=
    litsIsolated_addTerms hwfC.litsIsolated _
  have hRt : Reach C (C.withOperands [Term.app f args]) (.app f args) := by
    refine (reach_iff (Database.Contained.addTerms _ _) hE hwfC.subtermClosed
      hwfC.litsIsolated hcong).mpr ?_
    cases t' with
    | lit l => exact absurd (Cong.eq_of_isLit hlit hcong (Or.inr rfl)) (by simp)
    | app g cs =>
      exact reach_self (Database.Contained.addTerms _ _) hwfC.subtermClosed ht'
  obtain ⟨f', args₀, args', heq, hmem, hcl⟩ := hRt
  obtain ⟨rfl, rfl⟩ := Term.app.inj heq
  exact ⟨args', hmem, owes_list_of_congList hc hwfA hwfC hE hcl
    (fun x hx => hwfA.subtermClosed _ ht (Term.IsSubterm.arg hx (.refl x)))
    (fun x hx => hwfC.subtermClosed _ hmem (Term.IsSubterm.arg hx (.refl x)))⟩

theorem envOwes_nil {C : Database} : EnvOwes C [] [] := by
  intro v t ht; simp [Env.lookup] at ht

theorem mergeEnvIdx_owes {C : Database} : ∀ {os os' ns ns' : List Term} (i : Nat),
    List.Forall₂ (Owes C) os os' → List.Forall₂ (Owes C) ns ns' →
    EnvOwes C (mergeEnvIdx i os ns) (mergeEnvIdx i os' ns')
  | [], [], _, _, _, .nil, _ => envOwes_nil
  | _ :: _, _ :: _, [], [], _, .cons _ _, .nil => envOwes_nil
  | o :: os, o' :: os', n :: ns, n' :: ns', i, .cons ho hos, .cons hn hns => by
      show EnvOwes C (("old" ++ toString i, o) :: ("new" ++ toString i, n) ::
          mergeEnvIdx (i + 1) os ns)
        (("old" ++ toString i, o') :: ("new" ++ toString i, n') ::
          mergeEnvIdx (i + 1) os' ns')
      exact ((mergeEnvIdx_owes (i + 1) hos hns).cons _ hn).cons _ ho

theorem mergeEnv_owes {C : Database} : ∀ {os os' ns ns' : List Term},
    List.Forall₂ (Owes C) os os' → List.Forall₂ (Owes C) ns ns' →
    EnvOwes C (mergeEnv os ns) (mergeEnv os' ns')
  | [o], [o'], [n], [n'], .cons ho .nil, .cons hn .nil => by
      show EnvOwes C [("old", o), ("new", n)] [("old", o'), ("new", n')]
      exact ((envOwes_nil).cons "new" hn).cons "old" ho
  | [], [], _, _, .nil, hn => mergeEnvIdx_owes 0 .nil hn
  | _ :: _ :: _, _ :: _ :: _, _, _, .cons h₁ (.cons h₂ h₃), hn =>
      mergeEnvIdx_owes 0 (.cons h₁ (.cons h₂ h₃)) hn
  | [_], [_], [], [], .cons ho .nil, .nil => mergeEnvIdx_owes 0 (.cons ho .nil) .nil
  | [_], [_], _ :: _ :: _, _ :: _ :: _, .cons ho .nil, .cons h₁ (.cons h₂ h₃) =>
      mergeEnvIdx_owes 0 (.cons ho .nil) (.cons h₁ (.cons h₂ h₃))

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β},
    List.Forall₂ R as bs → ∀ {a : α}, a ∈ as → ∃ b ∈ bs, R a b
  | _, _, .cons hab hrest, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨_, by simp, hab⟩
      · obtain ⟨b, hb, hR⟩ := forall₂_mem_left hrest hx'
        exact ⟨b, by simp [hb], hR⟩

theorem forall₂_split {α β : Type} {R : α → β → Prop} : ∀ {as vs : List α} {cs : List β},
    List.Forall₂ R (as ++ vs) cs →
    ∃ as' vs', cs = as' ++ vs' ∧ List.Forall₂ R as as' ∧ List.Forall₂ R vs vs'
  | [], vs, cs, h => ⟨[], cs, rfl, .nil, h⟩
  | a :: as, vs, _ :: cs, .cons hab hrest => by
      obtain ⟨as', vs', rfl, h₁, h₂⟩ := forall₂_split hrest
      exact ⟨_ :: as', vs', rfl, .cons hab h₁, h₂⟩

/-- Two implementation terms congruent at `A` have specification witnesses congruent at
`C` proper: the three links compose in the pinned ambient and conservativity takes it
off. -/
theorem cong_of_owes {A C : Database} (hc : A.Recorded C) (hwfA : A.WF) (hwfC : C.WF)
    {x y x' y' : Term} (hxy : Cong A x y) (hx : Owes C x x') (hy : Owes C y y')
    (hx' : x' ∈ C.terms) (hy' : y' ∈ C.terms) : Cong C x' y' := by
  have hcx : CongOn C [x] x x' :=
    (hx C (Database.Contained.refl C) fun s hs => hwfC.subtermClosed x' hx' hs).1
  have hcy : CongOn C [y] y y' :=
    (hy C (Database.Contained.refl C) fun s hs => hwfC.subtermClosed y' hy' hs).1
  exact congOn_elim hwfC.subtermClosed hx' hy'
    ((Cong.mono ⟨withOperands_mono_list (by simp)⟩ hcx).symm.trans
      ((Cong.mono_recorded hc hwfA hwfC hxy).trans
        (Cong.mono ⟨withOperands_mono_list (by simp)⟩ hcy)))

theorem congList_of_owes {A C : Database} (hc : A.Recorded C) (hwfA : A.WF) (hwfC : C.WF) :
    ∀ {xs ys xs' ys' : List Term}, CongList A xs ys →
      List.Forall₂ (Owes C) xs xs' → List.Forall₂ (Owes C) ys ys' →
      (∀ x ∈ xs', x ∈ C.terms) → (∀ y ∈ ys', y ∈ C.terms) → CongList C xs' ys'
  | _, _, _, _, .nil, .nil, .nil, _, _ => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons hxy hrest, .cons hx hxs, .cons hy hys, hxm, hym =>
      .cons (cong_of_owes hc hwfA hwfC hxy hx hy (hxm _ (by simp)) (hym _ (by simp)))
        (congList_of_owes hc hwfA hwfC hrest hxs hys (fun x hx => hxm x (by simp [hx]))
          (fun y hy => hym y (by simp [hy])))

/-- **A merge collision available at `A` is available at any `C` that records it — when the
`:merge` bodies are ordering-free.** -/
theorem MergeStep.transport_owes {A C B : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig) (hof : Signature.OrderingFree C.sig)
    (h : MergeStep A B) : ∃ D, MergeStep C D ∧ B.Recorded D ∧ B.sig = D.sig := by
  cases h with
  | @collide dA f dc as bs a b vs body res hdc hmg hla hlb hra hrb hcong hbody hres =>
    -- the two colliding entries, matched column by column at `C`
    obtain ⟨cs, hcs, howcs⟩ := recorded_entry hc hwfA hwfC hra
    obtain ⟨es, hes, howes⟩ := recorded_entry hc hwfA hwfC hrb
    obtain ⟨as', a', rfl, howas, howa⟩ := forall₂_split howcs
    obtain ⟨bs', b', rfl, howbs, howb⟩ := forall₂_split howes
    have hmemC : ∀ {gs : List Term}, Term.app f gs ∈ C.terms → ∀ x ∈ gs, x ∈ C.terms :=
      fun hg x hx => hwfC.subtermClosed _ hg (Term.IsSubterm.arg hx (.refl x))
    -- the specification's two keys are congruent to each other
    have hkey : CongList C as' bs' :=
      congList_of_owes hc hwfA hwfC hcong howas howbs
        (fun x hx => hmemC hcs x (List.mem_append_left _ hx))
        (fun y hy => hmemC hes y (List.mem_append_left _ hy))
    -- the body runs at `C` under the congruent merge environment
    have hwfCe : Database.WF { C with env := mergeEnv a' b' } :=
      hwfC.setEnv fun p hp => (mem_mergeEnv hp).elim
        (fun hm => hmemC hcs p.2 (List.mem_append_right _ hm))
        (fun hm => hmemC hes p.2 (List.mem_append_right _ hm))
    have hfollows : StateOwes { A with env := mergeEnv a b } { C with env := mergeEnv a' b' } :=
      ⟨hc.setEnv _ _, hsig, (mergeEnv_owes howa howb).setEnv⟩
    obtain ⟨hbodyof, hresof⟩ : Actions.OrderingFree body ∧ Expr.OrderingFreeList res := by
      have := hof f dc (hsig ▸ hdc) (MergeSpec.merge body res) (by rw [hmg]; rfl)
      exact this
    obtain ⟨dC, hdC, hfd⟩ := evalActions_owes hfollows hwfCe hbodyof hbody
    have hwfdC : dC.WF := evalActions_wf hwfCe hdC
    -- the result columns follow
    obtain ⟨vs', hvs', howvs⟩ :=
      evalList_owes hwfdC.litsIsolated hfd.env hresof (hfd.sig ▸ hres)
    -- the combined entry
    have hcontCd : ({ C with env := mergeEnv a' b' } : Database).Contained dC :=
      evalActions_contained hdC
    have howentry : Owes dC (.app f (as ++ vs)) (.app f (as' ++ vs')) :=
      owes_append (howas.imp (fun {_ _} ho => Owes.mono ⟨hcontCd.eqs⟩ (Owes.setEnv ho))) howvs
    refine ⟨{ dC.addTerm (.app f (as' ++ vs')) with env := C.env, rules := C.rules },
      .collide (hsig ▸ hdc) hmg ?_ ?_ ?_ ?_ hkey hdC hvs', ?_, ?_⟩
    · rw [← hla]; exact (howas.length_eq).symm
    · rw [← hlb]; exact (howbs.length_eq).symm
    · exact hcs
    · exact hes
    · exact (recorded_addTerm_owes hfd.recorded hwfdC howentry).setEnvRules _ _ _ _
    · show dA.sig = dC.sig
      exact hfd.sig

/-- The `Owes` clause, read off at the ambient that posits the recorder's own values. -/
theorem owes_at {C : Database} {ts' : List Term} :
    ∀ {t t' : Term}, Owes C t t' → t' ∈ ts' →
      CongOn (C.withOperands ts') [t] t t' ∧
      ∀ s ∈ t.subterms, ∃ u ∈ (C.withOperands ts').terms,
        CongOn (C.withOperands ts') [s] s u := by
  intro t t' ho ht'
  exact ho (C.withOperands ts') (Database.Contained.addTerms _ _)
    (fun s hs => Database.addTerms_terms ▸ Or.inr ⟨t', ht', hs⟩)

/-- **`Recorded` survives matched phantom operands.** The reflexive equations
`withOperands` writes on the implementation's side are matched by the `Owes` clause. -/
theorem recorded_withOperands {A C : Database} (hc : A.Recorded C) (hwfC : C.WF)
    {ts ts' : List Term} (hall : List.Forall₂ (Owes C) ts ts') :
    (A.withOperands ts).Recorded (C.withOperands ts') := by
  have hwf' : (C.withOperands ts').WF := hwfC.addTerms ts'
  refine ⟨fun p hp => ?_⟩
  rcases mem_addTerms_eqs' ts A p hp with hq | ⟨x, hx, s, hs, rfl⟩
  · obtain ⟨q, hq', hc₁, hc₂⟩ := hc.eqs p hq
    exact ⟨q, eqs_subset_addTerms ts' C hq',
      congOn_mono (Database.Contained.addTerms _ _) hc₁,
      congOn_mono (Database.Contained.addTerms _ _) hc₂⟩
  · obtain ⟨x', hx', hox⟩ := forall₂_mem_left hall hx
    obtain ⟨u, hu, hcu⟩ := (owes_at hox hx').2 s hs
    have hwiden : CongOn (C.withOperands ts') [s, s] s u :=
      Cong.mono ⟨withOperands_mono_list (by simp)⟩ hcu
    exact ⟨(u, u), hwf'.eqsRefl u hu, hwiden, hwiden⟩

/-- **The instance clause.** A pattern instance the implementation matches against a term
it holds is matched, at the specification, by the specification's witness for that term. -/
theorem cong_instance {A C : Database} (hc : A.Recorded C) (hwfA : A.WF) (hwfC : C.WF)
    {ts ts' : List Term} (hall : List.Forall₂ (Owes C) ts ts')
    {w u : Term} (hou : Owes C w u) (hu : u ∈ C.terms)
    {x x' : Term} (hx' : x' ∈ ts') (hox : Owes C x x') (hcong : CongOn A ts w x) :
    CongOn C [x'] u x' := by
  set E : Database := (C.withOperands ts').withOperands [w, x] with hE
  have hrefl : ∀ p ∈ E.eqs, p ∈ C.eqs ∨ p.1 = p.2 := by
    intro p hp
    rcases mem_addTerms_eqs [w, x] (C.withOperands ts') p hp with hq | hq
    · exact mem_addTerms_eqs ts' C p hq
    · exact Or.inr hq
  have h₁ : Cong E w x :=
    Cong.mono_recorded (recorded_withOperands hc hwfC hall) (hwfA.addTerms ts)
      (hwfC.addTerms ts') hcong
  have h₂ : Cong E x x' :=
    Cong.mono ⟨withOperands_mono_list (by simp)⟩ (owes_at hox hx').1
  have h₃ : Cong E w u := by
    refine Cong.mono ⟨?_⟩ ((hou C (Database.Contained.refl C)
      (fun s hs => hwfC.subtermClosed u hu hs)).1)
    exact (addTerms_eqs_mono (eqs_subset_addTerms ts' C) [w]).trans
      (withOperands_mono_list (by simp))
  exact (cong_pin hwfC.subtermClosed hrefl hu (h₂.symm.trans (h₁.symm.trans h₃))).symm

/-- **An ordering-free pattern matches at the recorder, under the moved substitution.** -/
theorem matches_owes {A C : Database} (hc : A.Recorded C) (hwfA : A.WF) (hwfC : C.WF)
    (hsig : A.sig = C.sig) {p : Pattern} (hof : Pattern.OrderingFree p) {σ σ' : Env}
    (henv : EnvOwes C (A.env ++ σ) (C.env ++ σ')) (h : Matches A p σ) : Matches C p σ' := by
  cases h with
  | @expr e _ w t hw he hcong =>
    obtain ⟨t', he', ho⟩ := eval_owes hwfC.litsIsolated henv hof (hsig ▸ he)
    obtain ⟨u, hu, hou⟩ := recorded_owes hc hwfA hw
    exact .expr hu he'
      (cong_instance hc hwfA hwfC (List.Forall₂.cons ho .nil) hou hu (by simp) ho hcong)
  | @eq e₁ e₂ _ w t₁ t₂ hw he₁ he₂ hcw hc₁₂ =>
    obtain ⟨t₁', he₁', ho₁⟩ := eval_owes hwfC.litsIsolated henv hof.1 (hsig ▸ he₁)
    obtain ⟨t₂', he₂', ho₂⟩ := eval_owes hwfC.litsIsolated henv hof.2 (hsig ▸ he₂)
    obtain ⟨u, hu, hou⟩ := recorded_owes hc hwfA hw
    have hall : List.Forall₂ (Owes C) [t₁, t₂] [t₁', t₂'] :=
      .cons ho₁ (.cons ho₂ .nil)
    have hk₁ : CongOn C [t₁'] u t₁' :=
      cong_instance hc hwfA hwfC hall hou hu (by simp) ho₁ hcw
    have hk₂ : CongOn C [t₂'] u t₂' :=
      cong_instance hc hwfA hwfC hall hou hu (by simp) ho₂ (hcw.trans hc₁₂)
    refine .eq hu he₁' he₂' (Cong.mono ⟨withOperands_mono_list (by simp)⟩ hk₁) ?_
    exact (Cong.mono ⟨withOperands_mono_list (by simp)⟩ hk₁).symm.trans
      (Cong.mono ⟨withOperands_mono_list (by simp)⟩ hk₂)
  | @values vs f as _ us ts w hw hts hus hcw =>
    obtain ⟨ts', hts', hots⟩ := evalList_owes hwfC.litsIsolated henv hof.2 (hsig ▸ hts)
    obtain ⟨us', hus', hous⟩ := evalList_owes hwfC.litsIsolated henv hof.1 (hsig ▸ hus)
    obtain ⟨u, hu, hou⟩ := recorded_owes hc hwfA hw
    have hox : Owes C (.app f (ts ++ us)) (.app f (ts' ++ us')) := owes_append hots hous
    exact .values hu hts' hus'
      (cong_instance hc hwfA hwfC (List.Forall₂.cons hox .nil) hou hu (by simp) hox hcw)

/-! ### The witness function and the query join -/

/-- **The witness.** One function, chosen once, sending each term of `A` to a term of `C`
that `C` owes it. Choosing a *function* rather than a term per use site is what keeps
`Env.Union2` joinable: equal terms get equal images. -/
theorem exists_witness {A C : Database} (hc : A.Recorded C) (hwf : A.WF) :
    ∃ w : Term → Term, ∀ t ∈ A.terms, w t ∈ C.terms ∧ Owes C t (w t) := by
  classical
  refine ⟨fun t => if ht : t ∈ A.terms then (recorded_owes hc hwf ht).choose else t,
    fun t ht => ?_⟩
  simpa only [dif_pos ht] using (recorded_owes hc hwf ht).choose_spec

/-- `σ` with every value rewritten by `w`. Domain and order untouched. -/
def Env.mapVals (w : Term → Term) (σ : Env) : Env := σ.map fun b => (b.1, w b.2)

theorem dom_mapVals (w : Term → Term) : ∀ σ : Env, Env.dom (Env.mapVals w σ) = Env.dom σ
  | [] => rfl
  | b :: σ => by
      show (b.1, w b.2).1 :: (Env.mapVals w σ).map Prod.fst = b.1 :: σ.map Prod.fst
      rw [show (Env.mapVals w σ).map Prod.fst = σ.map Prod.fst from dom_mapVals w σ]

theorem lookup_mapVals (w : Term → Term) (v : Var) : ∀ σ : Env,
    Env.lookup v (Env.mapVals w σ) = (Env.lookup v σ).map w
  | [] => rfl
  | (u, t) :: σ => by
      show (if v = u then some (w t) else Env.lookup v (Env.mapVals w σ)) =
        Option.map w (if v = u then some t else Env.lookup v σ)
      split
      · rfl
      · exact lookup_mapVals w v σ

theorem mem_mapVals {w : Term → Term} {b : Var × Term} : ∀ {σ : Env},
    b ∈ Env.mapVals w σ → ∃ a ∈ σ, b = (a.1, w a.2)
  | [], hb => by simp [Env.mapVals] at hb
  | a :: σ, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨a, List.mem_cons_self .., rfl⟩
      · obtain ⟨c, hc, rfl⟩ := mem_mapVals hb
        exact ⟨c, List.mem_cons_of_mem a hc, rfl⟩

theorem mapVals_append (w : Term → Term) (σ₁ σ₂ : Env) :
    Env.mapVals w (σ₁ ++ σ₂) = Env.mapVals w σ₁ ++ Env.mapVals w σ₂ := List.map_append

/-- **`Env.Union2` survives a witness function.** -/
theorem union2_mapVals (w : Term → Term) {σ₁ σ₂ σ : Env} (h : Env.Union2 σ₁ σ₂ σ) :
    Env.Union2 (Env.mapVals w σ₁) (Env.mapVals w σ₂) (Env.mapVals w σ) := by
  refine ⟨fun b hb t ht => ?_, by rw [h.2, mapVals_append]⟩
  obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
  rw [lookup_mapVals] at ht
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact congrArg w (h.1 a ha u hu)

theorem unionAll_mapVals (w : Term → Term) {σs : List Env} {σ : Env}
    (h : Env.UnionAll σs σ) : Env.UnionAll (σs.map (Env.mapVals w)) (Env.mapVals w σ) := by
  induction h with
  | nil => exact .nil
  | single σ => exact .single _
  | step h₂ _ ih => exact .step (union2_mapVals w h₂) ih

/-- Every value the join produces came from one of the pieces. -/
theorem unionAll_vals {S : Set Term} : ∀ {σs : List Env} {σ : Env}, Env.UnionAll σs σ →
    (∀ τ ∈ σs, ∀ b ∈ τ, b.2 ∈ S) → ∀ b ∈ σ, b.2 ∈ S := by
  intro σs σ hu
  induction hu with
  | nil => simp
  | single τ => exact fun h => h τ (by simp)
  | @step σ₁ σ₂ σr σ σs h₂ _ ih =>
    intro h
    refine ih fun τ hτ => ?_
    rcases List.mem_cons.mp hτ with rfl | hτ'
    · rw [h₂.2]
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      exacts [h σ₁ (by simp) b hb, h σ₂ (by simp) b hb]
    · exact h τ (by simp [hτ'])

/-- The environment clause for a moved substitution. -/
theorem envOwes_mapVals {A C : Database} {w : Term → Term}
    (hw : ∀ t ∈ A.terms, w t ∈ C.terms ∧ Owes C t (w t)) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ A.terms) : EnvOwes C σ (Env.mapVals w σ) := by
  intro v t ht
  refine ⟨w t, by rw [lookup_mapVals, ht]; rfl, (hw t ?_).2⟩
  induction σ with
  | nil => simp [Env.lookup] at ht
  | cons b σ ih =>
    rw [Env.lookup_cons] at ht
    split at ht
    · exact Option.some.inj ht ▸ hσ b (by simp)
    · exact ih (fun x hx => hσ x (by simp [hx])) ht

/-- Appending environments whose domains agree keeps the clause: `lookup` is left-biased,
so the two sides fall through together. -/
theorem envOwes_append {C : Database} {σ₁ σ₁' σ₂ σ₂' : Env}
    (h₁ : EnvOwes C σ₁ σ₁') (hdom : Env.dom σ₁ = Env.dom σ₁') (h₂ : EnvOwes C σ₂ σ₂') :
    EnvOwes C (σ₁ ++ σ₂) (σ₁' ++ σ₂') := by
  intro v t ht
  by_cases hv : v ∈ Env.dom σ₁
  · rw [Env.lookup_append_of_mem hv] at ht
    obtain ⟨t', ht', ho⟩ := h₁ v t ht
    exact ⟨t', by rw [Env.lookup_append_of_mem (hdom ▸ hv)]; exact ht', ho⟩
  · rw [Env.lookup_append_of_not_mem hv] at ht
    obtain ⟨t', ht', ho⟩ := h₂ v t ht
    exact ⟨t', by rw [Env.lookup_append_of_not_mem (hdom ▸ hv)]; exact ht', ho⟩

theorem validSubst_mapVals {A C : Database} (hc : A.Recorded C) (hwfA : A.WF) (hwfC : C.WF)
    (hsig : A.sig = C.sig) (henv : A.env = C.env) {w : Term → Term}
    (hw : ∀ t ∈ A.terms, w t ∈ C.terms ∧ Owes C t (w t))
    {p : Pattern} (hof : Pattern.OrderingFree p) {τ : Env} (h : ValidSubst A p τ) :
    ValidSubst C p (Env.mapVals w τ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [dom_mapVals, ← henv]; exact h.1.1
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
    exact (hw a.2 (h.1.2 a ha)).1
  · refine matches_owes hc hwfA hwfC hsig hof ?_ h.2
    exact envOwes_append (fun v t ht => ⟨t, henv ▸ ht, Owes.refl⟩) (by rw [henv])
      (envOwes_mapVals hw h.1.2)

theorem forall₂_validSubst {A C : Database} (hc : A.Recorded C) (hwfA : A.WF) (hwfC : C.WF)
    (hsig : A.sig = C.sig) (henv : A.env = C.env) {w : Term → Term}
    (hw : ∀ t ∈ A.terms, w t ∈ C.terms ∧ Owes C t (w t)) :
    ∀ {q : Query} {σs : List Env}, List.Forall₂ (ValidSubst A) q σs →
      (∀ p ∈ q, Pattern.OrderingFree p) →
      List.Forall₂ (ValidSubst C) q (σs.map (Env.mapVals w))
  | _, _, .nil, _ => .nil
  | p :: ps, τ :: τs, .cons hv hrest, hof =>
      .cons (validSubst_mapVals hc hwfA hwfC hsig henv hw (hof p (by simp)) hv)
        (forall₂_validSubst hc hwfA hwfC hsig henv hw hrest fun x hx => hof x (by simp [hx]))

theorem forall₂_vals {A : Database} {q : Query} {σs : List Env}
    (hall : List.Forall₂ (ValidSubst A) q σs) : ∀ τ ∈ σs, ∀ b ∈ τ, b.2 ∈ A.terms := by
  induction hall with
  | nil => simp
  | @cons p τ ps τs hv _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    exacts [hv.1.2, ih x hx']

/-- **A rule firing at `A` is matched by one at any `C` that records it — when the rule is
ordering-free.** -/
theorem RuleResults.mono_owes {A C : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig) (henv : A.env = C.env) {r : Rule}
    (hof : Rule.OrderingFree r) {d : Database} (hd : d ∈ RuleResults A r) :
    ∃ D ∈ RuleResults C r, d.Recorded D ∧ D.sig = C.sig := by
  obtain ⟨σ, hq, hstep⟩ := hd
  obtain ⟨w, hw⟩ := exists_witness hc hwfA
  obtain ⟨σs, hall, hu⟩ := hq
  have hvals : ∀ b ∈ σ, b.2 ∈ A.terms := unionAll_vals hu (forall₂_vals hall)
  have hq' : ValidQuerySubst C r.query (Env.mapVals w σ) :=
    ⟨σs.map (Env.mapVals w), forall₂_validSubst hc hwfA hwfC hsig henv hw hall hof.1,
      unionAll_mapVals w hu⟩
  obtain ⟨dA, hv, rfl⟩ := evalLocalActions_eq_some hstep
  have hwfCe : Database.WF { C with env := C.env ++ Env.mapVals w σ } :=
    hwfC.appendEnv fun b hb => by
      obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
      exact (hw a.2 (hvals a ha)).1
  have hfollows : StateOwes { A with env := A.env ++ σ }
      { C with env := C.env ++ Env.mapVals w σ } :=
    ⟨hc.setEnv _ _, hsig,
      (envOwes_append (fun v t ht => ⟨t, henv ▸ ht, Owes.refl⟩) (by rw [henv])
        (envOwes_mapVals hw hvals)).setEnv⟩
  obtain ⟨D, hD, hfd⟩ := evalActions_owes hfollows hwfCe hof.2 hv
  refine ⟨{ D with env := C.env, rules := C.rules },
    ⟨Env.mapVals w σ, hq', by rw [evalLocalActions, hD, Option.map_some]⟩,
    hfd.recorded.setEnvRules _ _ _ _, ?_⟩
  exact (evalActions_sig hD : _ = ({ C with env := C.env ++ Env.mapVals w σ } : Database).sig)

/-- **A round's rule phase transports along `Recorded`.** -/
theorem RunRules.mono_owes {R : RulesetName} {A C : Database} (hc : A.Recorded C)
    (hwfA : A.WF) (hwfC : C.WF)
    (hsig : A.sig = C.sig) (henv : A.env = C.env) (hrules : A.rules = C.rules)
    (hof : ∀ r ∈ C.rules, Rule.OrderingFree r) :
    (RunRules R A).Recorded (RunRules R C) := by
  have key : ∀ d ∈ {d | ∃ r ∈ A.rules, r.ruleset = R ∧ d ∈ RuleResults A r},
      d.Recorded (RunRules R C) := by
    rintro d ⟨r, hr, hR, hdr⟩
    obtain ⟨D, hD, hcd, -⟩ :=
      RuleResults.mono_owes hc hwfA hwfC hsig henv (hof r (hrules ▸ hr)) hdr
    exact hcd.trans_contained (Database.Contained.mem_sUnion ⟨r, hrules ▸ hr, hR, hD⟩)
  refine ⟨fun p hp => ?_⟩
  rcases hp with hx | hx
  · obtain ⟨q, hq, hc₁, hc₂⟩ := (hc.trans_contained (Database.Contained.sUnion C _)).eqs p hx
    exact ⟨q, hq, hc₁, hc₂⟩
  · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
    exact (key d hd).eqs p hx'
/-- `MergeStep.transport_owes` iterated. The condition is about the signature, which no
merge step writes, so it survives to every intermediate state. -/
theorem MergeClosure.transport_owes {A C B : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig) (hof : Signature.OrderingFree C.sig)
    (h : MergeClosure A B) : ∃ D, MergeClosure C D ∧ B.Recorded D ∧ B.sig = D.sig := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, hc, hsig⟩
  | @tail b c hcl hstep ih =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ := ih
    obtain ⟨D', hstepD', hcont', hsig'⟩ :=
      MergeStep.transport_owes hcontD (MergeClosure.wf hwfA hcl) (MergeClosure.wf hwfC hclD)
        hsigD (by rw [MergeClosure.sig hclD]; exact hof) hstep
    exact ⟨D', hclD.tail hstepD', hcont', hsig'⟩

end OrderingFree

/-- **A merge collision available at `A` is available at any `C` that *records* it.**

`hcond` is not bookkeeping: **without it the statement is false**, and not merely unproved.
`Recorded` moves an entry's value columns as well as its key, so the body runs under a
*congruent* `mergeEnv` on the `C` side, and `ordering-min`/`ordering-max` are not stable
there: the two runs settle on incongruent parents and the union-find edge one writes is
congruent to nothing the other can write. The counterexample is at the encoding's own
`mergeBody`/`mergeResult` and one `viewDecl`, with `A.Recorded C`, both states well formed
and one signature: `A` holds `@fView(k) ↦ p` alongside `@fView(k) ↦ r`, `C` holds the first
re-keyed to the congruent `s`, and with `p < r < s` the step from `A` writes `@UF(r) ↦ p`
while every step from `C` writes `@UF(s) ↦ s`, `@UF(s) ↦ r` or `@UF(r) ↦ r`. A merge
asserts no equation, so nothing relates `r` to `p` afterwards either. Adding `C.WF` does
not rescue it.

Either arm of `hcond` does. Under `C.Diag` there is nothing left to prove:
`Database.Recorded.contained_of_diag` turns `hc` into a `Database.Contained` and
`MergeStep.transport` is the proved transport along that — `p` and `s` could not have been
congruent there in the first place. Under `Signature.OrderingFree` the counterexample is
excluded at its own primitive, and `MergeStep.transport_owes` is the proof: the moved
environment is congruent, and ordering-free evaluation respects congruence, so the two runs
land on congruent results. That the environment moves *before* any body expression runs is
not an obstruction, since nothing about the moved values is read except through
`Expr.eval`.

`Database.Recorded.addRow_congr`, which used to supply the first arm, is deleted: it rested
on `addTerms_eq_self` at a row-shaped `Recorded` that no longer exists. -/
theorem MergeStep.transport_recorded {A C B : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig)
    (hcond : C.Diag ∨ Signature.OrderingFree C.sig) (h : MergeStep A B) :
    ∃ D, MergeStep C D ∧ B.Recorded D ∧ B.sig = D.sig := by
  rcases hcond with hdiag | hof
  · obtain ⟨D, hstep, hcont, hsig'⟩ := h.transport (hc.contained_of_diag hdiag) hsig
    exact ⟨D, hstep, .of_contained hcont, hsig'⟩
  · exact MergeStep.transport_owes hc hwfA hwfC hsig hof h

/-- `MergeStep.transport_recorded` iterated. Both arms are about `C` alone — `Diag` because
`MergeClosure.transport` closes the whole closure in one go, `Signature.OrderingFree`
because no merge step writes `sig` — so nothing has to be re-established at the intermediate
states. -/
theorem MergeClosure.transport_recorded {A C B : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig)
    (hcond : C.Diag ∨ Signature.OrderingFree C.sig) (h : MergeClosure A B) :
    ∃ D, MergeClosure C D ∧ B.Recorded D ∧ B.sig = D.sig := by
  rcases hcond with hdiag | hof
  · obtain ⟨D, hcl, hcont, hsig'⟩ := h.transport (hc.contained_of_diag hdiag) hsig
    exact ⟨D, hcl, .of_contained hcont, hsig'⟩
  · exact MergeClosure.transport_owes hc hwfA hwfC hsig hof h

/-! ### Containment for the merge interpreter

Stage 4 of the refinement chain, together with the `execActions` refinement it rests on.
It sits here rather than beside the statements it discharges because every part of it
reads something stated above: `execAction_sig`, `mergeOneWith_inv`,
`mergeOneWith_confined`, `mergeRound_confined`, `mem_mergeEnv`, `Inv.setEnv`,
`Inv.execActions` and `Inv.mergeRound_of_legalMerges`.

`Signature.MergesLegal` — every declared merge's body writes only legal `set`s at the
declared widths, and its result has one expression per value column — recurs throughout,
for `Inv.mergeRound_of_legalMerges`'s reason. -/

namespace FDatabase

/-- **One firing of the pass lands in a state the merge closure reaches.**

`x` is the accumulator, `D` a specification state the closure has already reached that
contains it. The firing's congruence test is against the *pre-pass* closure `d.closureF`,
which is why `d`'s invariant appears alongside `x`'s. `evalActions_mono` is what
re-runs the merge body at `D`.

The witness takes the two rows in the order `(r₂, r₁)`, which is the whole reason
`MergeStep.collide` lines up with the implementation: `collide` runs the body under
`mergeEnv a b` and writes the combined row at the *first* row's key, and
`mergeOneOriented` binds `old` from `r₂` and overwrites `r₂`. Both facts are the one fact
that `r₂` is the row already in the table — which of the two colliding rows that is,
`mergeOneWith` decides, and `mergeOneWith_mergeStep` says the decision is free.

**Why the conclusion is `MergeClosure` and not `MergeStep`.** A firing takes exactly one
`MergeStep` — *except* at a `noConflict` collision, which egglog resolves by running
nothing, and which this therefore has to model by taking **no** step: the implementation
never evaluates the body there, so the `evalActions` and `Expr.evalList` premises
`MergeStep.collide` demands are not available and in general do not hold (nothing
scope-checks a merge body, so a body with a free variable makes `evalActions` fail while
the skip still fires). Zero-or-one steps is `MergeClosure`, so that is what this states.
Nothing downstream notices: `mergeRound_contained` consumed the step with
`ReflTransGen.tail` and now consumes the closure with `.trans`, and its statement — the
containment contract the interpreter is actually held to — is unchanged.

**`hO₁` and `hO₂` are premises rather than consequences of `hxc`.** `Recorded` does not
carry them — see "There is no `Out.mono` along `Recorded`" above — and what they say is
exactly what the body needs: the specification holds each colliding entry with the *same*
value columns, so `MergeStep.collide` runs the body under the same `mergeEnv` the
implementation does and only the key moves. `mergeRound_contained` supplies them. -/
theorem mergeOneOriented_mergeStep {d x y : FDatabase} {r₁ r₂ : Row} {D : Database}
    (h : d.Inv) (hx : x.Inv) (hxs : x.sig = d.sig)
    (hcl : MergeClosure d.toDatabase D) (hxc : x.toDatabase.Recorded D)
    (hO₁ : x.sig.mergeOf r₁.fn ≠ none → D.Out r₁.fn r₁.args r₁.out)
    (hO₂ : x.sig.mergeOf r₂.fn ≠ none → D.Out r₂.fn r₂.args r₂.out)
    (hm : FDatabase.mergeOneOriented d.closureF x r₁ r₂ = some y) :
    ∃ D', MergeClosure D D' ∧ y.toDatabase.Recorded D' := by
  have hDsig : D.sig = d.sig := MergeClosure.sig hcl
  have hDwf : D.WF := MergeClosure.wf h.wf hcl
  unfold FDatabase.mergeOneOriented at hm
  match hmo : x.sig.mergeOf r₁.fn with
  | none => rw [hmo] at hm; simp at hm
  | some .noMerge => rw [hmo] at hm; simp at hm
  | some (.merge body res) =>
    rw [hmo] at hm
    simp only at hm
    split at hm
    case isFalse => simp at hm
    case isTrue hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨hfn, hck⟩, hr₁⟩, hr₂⟩ := hcond
      obtain ⟨dc, hdc, hdcm⟩ : ∃ dc, x.sig r₁.fn = some dc ∧
          dc.merge = some (MergeSpec.merge body res) := by
        rw [Signature.mergeOf] at hmo
        cases hd : x.sig r₁.fn with
        | none => rw [hd] at hmo; simp at hmo
        | some dc => exact ⟨dc, rfl, by rw [hd] at hmo; simpa using hmo⟩
      have hne₁ : x.sig.mergeOf r₁.fn ≠ none := by rw [hmo]; simp
      have hne₂ : x.sig.mergeOf r₂.fn ≠ none := by rw [← hfn]; exact hne₁
      have hmemRow : ∀ (r : Row), r ∈ x.rows → ∀ z ∈ r.out, z ∈ x.toDatabase.terms := by
        intro r hr z hz
        by_cases hu : x.sig.mergeOf r.fn = none
        · rw [(hx.index.ctor r hr hu).1] at hz; simp at hz
        · obtain ⟨bs, -, hmem⟩ := hx.index.entry r hr hu
          exact hx.wf.subtermClosed _ hmem
            (Term.mem_subterms.mpr (Term.IsSubterm.arg (List.mem_append_right _ hz)
              (Term.IsSubterm.refl z)))
      have hσ : ∀ b ∈ mergeEnv r₂.out r₁.out, b.2 ∈ x.toDatabase.terms := by
        intro b hb
        rcases mem_mergeEnv hb with hb' | hb'
        · exact hmemRow r₂ hr₂ b.2 hb'
        · exact hmemRow r₁ hr₁ b.2 hb'
      have h₀ : ({ x with env := mergeEnv r₂.out r₁.out } : FDatabase).Inv := hx.setEnv hσ
      split at hm
      case isTrue =>
        -- The no-conflict skip takes no specification step: `y` only drops a row of `x`.
        rw [Option.some.injEq] at hm
        subst hm
        exact ⟨D, Relation.ReflTransGen.refl, hxc⟩
      case isFalse =>
      cases hb : execActions { x with env := mergeEnv r₂.out r₁.out } body with
      | none => rw [hb] at hm; simp at hm
      | some eb =>
        rw [hb, Option.bind_some, Option.map_eq_some_iff] at hm
        obtain ⟨vs, hv, rfl⟩ := hm
        -- The two entries, found in `D` at *congruent* keys and the same value columns.
        obtain ⟨bs₂, hb₂, hr₂D⟩ : D.Out r₂.fn r₂.args r₂.out := hO₂ hne₂
        obtain ⟨bs₁, hb₁, hr₁D⟩ : D.Out r₂.fn r₁.args r₁.out := by
          rw [← hfn]; exact hO₁ hne₁
        have hcongD : CongList D r₂.args r₁.args :=
          (CongList.mono (MergeClosure.contained hcl)
            (FDatabase.congrTuple_iff.mp hck)).symm
        have hcongB : CongList D bs₂ bs₁ := hb₂.symm.trans (hcongD.trans hb₁)
        have hdcD : D.sig r₂.fn = some dc := by rw [hDsig, ← hxs, ← hfn]; exact hdc
        have hlen₂ : bs₂.length = dc.arity := by
          rw [← hb₂.length_eq]; exact (hx.index.width r₂ hr₂ dc (by rw [← hfn]; exact hdc)
            hne₂).1
        have hlen₁ : bs₁.length = dc.arity := by
          rw [← hb₁.length_eq]; exact (hx.index.width r₁ hr₁ dc hdc hne₁).1
        -- The body, re-run at `D`.
        have hbodyStep : evalActions
            ({ x with env := mergeEnv r₂.out r₁.out } : FDatabase).toDatabase body
            = some eb.toDatabase := FDatabase.execActions_evalActions h₀.eqs hb
        obtain ⟨D₁, hD₁step, hD₁c, hD₁sig, hD₁env⟩ :=
          evalActions_mono_recorded
            (db := ({ x with env := mergeEnv r₂.out r₁.out } : FDatabase).toDatabase)
            (D := { D with env := mergeEnv r₂.out r₁.out })
            (hxc.setEnv _ _) (hxs.trans hDsig.symm) rfl hbodyStep
        have hmlD : Expr.evalList D₁.sig res D₁.env = some vs := by
          rw [← hD₁env, ← hD₁sig]; exact hv
        have houtD : ∀ (r : Row) (cs : List Term), Term.app r.fn (cs ++ r.out) ∈ D.terms →
            ∀ z ∈ r.out, z ∈ D.terms := by
          intro r cs hmem z hz
          exact hDwf.subtermClosed _ hmem
            (Term.mem_subterms.mpr (Term.IsSubterm.arg (List.mem_append_right _ hz)
              (Term.IsSubterm.refl z)))
        have hσD : ∀ b ∈ mergeEnv r₂.out r₁.out, b.2 ∈ D.terms := by
          intro b hb
          rcases mem_mergeEnv hb with hb' | hb'
          · exact houtD r₂ bs₂ hr₂D b.2 hb'
          · exact houtD r₁ bs₁ (by rw [hfn]; exact hr₁D) b.2 hb'
        have hD₁wf : D₁.WF := evalActions_wf (hDwf.setEnvRules (R := D.rules) hσD) hD₁step
        refine ⟨{ D₁.addTerm (.app r₂.fn (bs₂ ++ vs)) with env := D.env, rules := D.rules },
          Relation.ReflTransGen.single
            (MergeStep.collide hdcD hdcm hlen₂ hlen₁ hr₂D hr₁D hcongB hD₁step hmlD), ?_⟩
        -- The interpreter records the combined entry at `r₂.args`, the specification at
        -- `bs₂`; `Recorded.addTerm_congr` is exactly that slack.
        have hDD₁ : D.Contained D₁ := ⟨(evalActions_contained hD₁step).eqs⟩
        have hb₂' : CongList D₁ r₂.args bs₂ := CongList.mono hDD₁ hb₂
        have hbridge : (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).toDatabase
            = eb.toDatabase.addTerm (.app r₂.fn (r₂.args ++ vs)) :=
          FDatabase.toDatabase_addTerm (execActions_eqsInTerms h₀.eqs hb)
        have hmemD₁ : Term.app r₂.fn (bs₂ ++ vs) ∈ (D₁.addTerm (.app r₂.fn (bs₂ ++ vs))).terms :=
          Database.mem_addTerm _ D₁
        have hrec : (eb.addTerm (.app r₂.fn (r₂.args ++ vs))).toDatabase.Recorded
            (D₁.addTerm (.app r₂.fn (bs₂ ++ vs))) := by
          rw [hbridge]; exact hD₁c.addTerm_congr hD₁wf hb₂'
        exact hrec.setEnvRules _ _ _ _

/-- **Either orientation stays inside the closure, so the choice between them is free.**

`mergeOneOriented_mergeStep` instantiates `MergeStep.collide` with the two rows in one
order; `collide` takes them in both, so `swapForCanon`'s answer never has to be justified
against the specification. That is what makes matching egglog's `old`/`new` an
implementation question — settled by `Impl/Merge.lean`'s `canonTerm` against the binary —
rather than a change to the semantics. -/
theorem mergeOneWith_mergeStep {d x y : FDatabase} {r₁ r₂ : Row} {D : Database}
    (h : d.Inv) (hx : x.Inv) (hxs : x.sig = d.sig)
    (hcl : MergeClosure d.toDatabase D) (hxc : x.toDatabase.Recorded D)
    (hO₁ : x.sig.mergeOf r₁.fn ≠ none → D.Out r₁.fn r₁.args r₁.out)
    (hO₂ : x.sig.mergeOf r₂.fn ≠ none → D.Out r₂.fn r₂.args r₂.out)
    (hm : FDatabase.mergeOneWith d.closureF x r₁ r₂ = some y) :
    ∃ D', MergeClosure D D' ∧ y.toDatabase.Recorded D' := by
  rcases mergeOneWith_eq_oriented (cl := d.closureF) (d := x) r₁ r₂ with he | he
  · exact mergeOneOriented_mergeStep h hx hxs hcl hxc hO₂ hO₁ (he ▸ hm)
  · exact mergeOneOriented_mergeStep h hx hxs hcl hxc hO₁ hO₂ (he ▸ hm)

/-- **The merge pass lands inside a state the merge closure reaches.**

The pass deletes the two rows it merged, so its result is not itself a `MergeClosure`
state; the witness is a specification state that took the same collisions and kept the
originals. The fold invariant is "the accumulator is `Inv`, has the pre-pass signature,
and is contained in some state the closure has reached"; each firing extends the closure
by one `MergeStep.collide`.

The invariant carries a fourth clause, and it is what pays for `mergeOneWith_mergeStep`'s
two `Database.Out` premises: **the witness holds every pre-pass row's entry at its own
value columns.** It is stated about the rebuilt row list rather than about the accumulator
because that list is what both folds range over — a merge body's own `set`s land in the
accumulator and are never collided — so the clause is established once, by
`FDatabase.IndexOk.entry` at the rebuild, and thereafter only has to survive a growing
witness, which is `Database.Out.mono`. -/
theorem mergeRound_contained {d : FDatabase} (h : d.Inv)
    (hlegal : Signature.MergesLegal d.sig) :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Recorded db := by
  let P : FDatabase → Prop := fun x => x.Inv ∧ x.sig = d.sig ∧
    ∃ D, MergeClosure d.toDatabase D ∧ x.toDatabase.Recorded D ∧
      ∀ r ∈ (FDatabase.rebuild d.closureF d).rows, d.sig.mergeOf r.fn ≠ none →
        D.Out r.fn r.args r.out
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      r₁ ∈ (FDatabase.rebuild d.closureF d).rows →
      r₂ ∈ (FDatabase.rebuild d.closureF d).rows →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx hr₁ hr₂
    obtain ⟨hxInv, hxs, D, hcl, hxc, hOut⟩ := hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => exact ⟨hxInv, hxs, D, hcl, hxc, hOut⟩
    | some y =>
      obtain ⟨D', hstepD, hyc⟩ :=
        mergeOneWith_mergeStep h hxInv hxs hcl hxc
          (fun hne => hOut r₁ hr₁ (hxs ▸ hne)) (fun hne => hOut r₂ hr₂ (hxs ▸ hne)) hy
      exact ⟨mergeOneWith_inv hxInv (hxs ▸ hlegal) hy,
        ((mergeOneWith_confined hy).2.2.1).trans hxs, D', hcl.trans hstepD, hyc,
        fun r hr hne =>
          Database.Out.mono (MergeClosure.contained hstepD) (hOut r hr hne)⟩
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      r₁ ∈ (FDatabase.rebuild d.closureF d).rows →
      (∀ r ∈ l, r ∈ (FDatabase.rebuild d.closureF d).rows) →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx _ _; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx hr₁ hl
      refine ih r₁ _ ?_ hr₁ (fun r hr => hl r (List.mem_cons_of_mem r₂ hr))
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep x r₁ r₂ hx hr₁ (hl r₂ (List.mem_cons_self ..))
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      (∀ r ∈ m, r ∈ (FDatabase.rebuild d.closureF d).rows) →
      (∀ r ∈ l, r ∈ (FDatabase.rebuild d.closureF d).rows) →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx _ _; exact hx
    | cons r₁ l ih =>
      intro x hx hm hl
      exact ih _ (hfold m r₁ x hx (hl r₁ (List.mem_cons_self ..)) hm) hm
        (fun r hr => hl r (List.mem_cons_of_mem r₁ hr))
  -- The rebuild is the pass's first step and the one place the witness stands still: it
  -- writes `rows`, which `toDatabase` drops, so no `MergeStep` is taken and the witness is
  -- reflexivity. It is also where the `Out` clause is discharged, by the rebuilt state's
  -- own index.
  have hreb : P (FDatabase.rebuild d.closureF d) :=
    ⟨h.rebuild closureSound_closureF, rfl, d.toDatabase, Relation.ReflTransGen.refl,
      Database.Recorded.refl,
      fun r hr hne => (h.rebuild closureSound_closureF).index.entry r hr hne⟩
  unfold FDatabase.mergeRound
  split
  · exact ⟨d.toDatabase, Relation.ReflTransGen.refl, Database.Recorded.refl⟩
  · obtain ⟨-, -, D, hcl, hc, -⟩ :=
      houter _ _ _ hreb (fun _ hr => hr) (fun _ hr => hr)
    exact ⟨D, hcl, hc⟩

/-- `mergeSaturateF_contained`, with the fuel first so the induction can generalize the
database.

`hcond` is `MergeClosure.transport_recorded`'s premise, pulled back one step. Its first arm
needs both halves: the witness `db₁` this re-bases onto is reached from `d.toDatabase` by a
merge closure, so it is diagonal as soon as `d.toDatabase` is *and* the merge bodies assert
nothing. Its second arm needs only the signature, which no round writes. Either carries
itself across a round — `mergeRound_confined` pins `sig`, and the round's own `Recorded`
conclusion pushes diagonality back down onto the interpreter's state. -/
theorem mergeSaturateF_contained_aux {n : Nat} : ∀ {d e : FDatabase}, d.Inv →
    Signature.MergesLegal d.sig →
    ((Signature.UnionFree d.sig ∧ d.toDatabase.Diag) ∨ Signature.OrderingFree d.sig) →
    d.mergeSaturateF n = some e →
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Recorded db := by
  induction n with
  | zero =>
    intro d e h _ _ hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Recorded.refl⟩
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e h hlegal hcond hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Recorded.refl⟩
    · have hsigR : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
      have hlegal' : Signature.MergesLegal d.mergeRound.sig := by rw [hsigR]; exact hlegal
      have hround : d.mergeRound.Inv := h.mergeRound_of_legalMerges hlegal
      obtain ⟨db₁, hcl₁, hcont₁⟩ := mergeRound_contained h hlegal
      have hsig₁ : d.mergeRound.toDatabase.sig = db₁.sig := by
        change d.mergeRound.sig = db₁.sig
        rw [hsigR]
        exact (MergeClosure.sig hcl₁).symm
      have hcond₁ : db₁.Diag ∨ Signature.OrderingFree db₁.sig := by
        rcases hcond with ⟨hufree, hdiag⟩ | hof
        · exact Or.inl (MergeClosure.diag hufree hdiag hcl₁)
        · exact Or.inr (by rw [MergeClosure.sig hcl₁]; exact hof)
      have hnext : (Signature.UnionFree d.mergeRound.sig ∧ d.mergeRound.toDatabase.Diag) ∨
          Signature.OrderingFree d.mergeRound.sig := by
        rcases hcond with ⟨hufree, hdiag⟩ | hof
        · refine Or.inl ⟨by rw [hsigR]; exact hufree, ?_⟩
          have hdiag₁ : db₁.Diag := MergeClosure.diag hufree hdiag hcl₁
          exact Database.Diag.mono (hcont₁.contained_of_diag hdiag₁) hdiag₁
        · exact Or.inr (by rw [hsigR]; exact hof)
      obtain ⟨db₂, hcl₂, hcont₂⟩ := ih hround hlegal' hnext hs
      obtain ⟨db₃, hcl₃, hcont₃, hsig₃⟩ :=
        MergeClosure.transport_recorded hcont₁ hround.wf (MergeClosure.wf h.wf hcl₁) hsig₁
          hcond₁ hcl₂
      exact ⟨db₃, hcl₁.trans hcl₃, hcont₂.trans hcont₃ (MergeClosure.wf hround.wf hcl₂)
        (MergeClosure.wf (MergeClosure.wf h.wf hcl₁) hcl₃)⟩

/-- **The merge phase run to a fixpoint stays inside the merge closure.**

`mergeRound_contained` once per round, with `MergeClosure.transport_recorded` re-basing the
tail's closure onto the head's witness. `mergeRound_confined` is what keeps `hlegal` and
`hcond` applicable at the next round: a pass does not touch `sig`. -/
theorem mergeSaturateF_contained {d e : FDatabase} (h : d.Inv)
    (hlegal : Signature.MergesLegal d.sig)
    (hcond : (Signature.UnionFree d.sig ∧ d.toDatabase.Diag) ∨ Signature.OrderingFree d.sig)
    (hs : d.mergeSaturateF mergeFuel = some e) :
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Recorded db :=
  mergeSaturateF_contained_aux h hlegal hcond hs

/-- **A round's rule firings stay inside `RunRules`.**

The witness is `RunRules d.toDatabase` itself and the merge closure is the reflexive one:
`execRunRules` runs no merge phase (`Impl/Merge.lean` defers it to `execCmdM`), so
nothing has to be re-based here.

**Rule legality is not needed.** Containment only asks that every row the enumerator
writes is one the specification writes, and `execActions_evalActions` matches the two
action interpreters on every action block, legal or not. `FDatabase.Inv.execRunRules` is
where legality is spent — keeping the invariant, which is a stronger conclusion than this
one.

The enumerator's substitution is transported to the specification's by
`evalActions_envAgree`: `matchQuery_validQuerySubst` only produces one that
`Env.Agree`s, and `Database.EnvAgree.eq_of_env_rules` turns that back into equality once
`fireInto` restores the caller's environment. -/
theorem union_contained {d₁ d₂ : FDatabase} (he₁ : d₁.EqsInTerms) (he₂ : d₂.EqsInTerms)
    {R : Database} (h₁ : d₁.toDatabase.Contained R) (h₂ : d₂.toDatabase.Contained R) :
    (d₁.union d₂).toDatabase.Contained R := by
  refine ⟨fun p hp => ?_⟩
  rcases hp with ⟨hpe, hpm⟩ | ⟨hq, -, -⟩
  · rcases mem_terms_union.mp hpm with hx | hx
    · exact h₁.eqs (Or.inl ⟨hpe, hx⟩)
    · exact h₂.eqs (Or.inl ⟨hpe, hx⟩)
  · rcases mem_eqs_union.mp hq with hq' | hq'
    · exact h₁.eqs (Or.inr ⟨hq', (he₁ p hq').1, (he₁ p hq').2⟩)
    · exact h₂.eqs (Or.inr ⟨hq', (he₂ p hq').1, (he₂ p hq').2⟩)

theorem execRunRules_contained {R : RulesetName} {d : FDatabase} (h : d.Inv) :
    (execRunRules R d).toDatabase.Contained (RunRules R d.toDatabase) := by
  set S : Database := RunRules R d.toDatabase with hS
  -- One firing lands inside `RunRules`, and keeps the accumulator's `EqsInTerms`.
  have hone : ∀ (r : Rule), r ∈ d.rules → r.ruleset = R → ∀ (σ : Env),
      σ ∈ matchQuery d r.query →
      ∀ acc : FDatabase, acc.EqsInTerms → acc.toDatabase.Contained S →
      (fireInto d r acc σ).EqsInTerms ∧ (fireInto d r acc σ).toDatabase.Contained S := by
    intro r hr hR σ hσ acc hacce hacc
    rw [fireInto, execLocalActions]
    cases hv : execActions { d with env := d.env ++ σ } r.actions with
    | none => simpa using ⟨hacce, hacc⟩
    | some e =>
      have hee : e.EqsInTerms := execActions_eqsInTerms (h.eqs.setEnv (d.env ++ σ)) hv
      have hmemS : ({ e with env := d.env, rules := d.rules } : FDatabase).toDatabase ∈
          {D | ∃ r' ∈ d.toDatabase.rules, r'.ruleset = R ∧ D ∈ RuleResults d.toDatabase r'} := by
        obtain ⟨τ, hτ, hag⟩ := matchQuery_validQuerySubst h hσ
        have hstep : evalActions
            ({ d.toDatabase with env := d.toDatabase.env ++ σ } : Database) r.actions
            = some e.toDatabase := by
          have := FDatabase.execActions_evalActions (h.eqs.setEnv (d.env ++ σ)) hv
          simpa using this
        have hEA : ({ d.toDatabase with env := d.toDatabase.env ++ σ } : Database).EnvAgree
            { d.toDatabase with env := d.toDatabase.env ++ τ } :=
          ⟨rfl, rfl, rfl, Env.Agree.append_left _ hag.symm⟩
        exact
          let ⟨e', hstep', hag'⟩ := evalActions_envAgree_exists hEA hstep
          ⟨r, hr, hR, τ, hτ, by
            rw [evalLocalActions, hstep', Option.map_some, FDatabase.toDatabase_restore,
              ← hag'.eq_of_env_rules d.toDatabase.env d.toDatabase.rules]
            rfl⟩
      have hsub :
          ({ e with env := d.env, rules := d.rules } : FDatabase).toDatabase.Contained S :=
        Database.Contained.mem_sUnion hmemS
      simp only [Option.map_some]
      exact ⟨EqsInTerms.union hacce (hee.restore), union_contained hacce hee.restore hacc hsub⟩
  -- The two folds.
  have hinner : ∀ (r : Rule), r ∈ d.rules → r.ruleset = R → ∀ (σs : List Env),
      (∀ σ ∈ σs, σ ∈ matchQuery d r.query) → ∀ acc : FDatabase, acc.EqsInTerms →
      acc.toDatabase.Contained S →
      (σs.foldl (fireInto d r) acc).EqsInTerms ∧
        (σs.foldl (fireInto d r) acc).toDatabase.Contained S := by
    intro r hr hR σs
    induction σs with
    | nil => intro _ acc hacce hacc; exact ⟨hacce, hacc⟩
    | cons σ σs ih =>
      intro hall acc hacce hacc
      rw [List.foldl_cons]
      obtain ⟨h₁, h₂⟩ := hone r hr hR σ (hall σ List.mem_cons_self) acc hacce hacc
      exact ih (fun τ hτ => hall τ (List.mem_cons_of_mem _ hτ)) _ h₁ h₂
  have houter : ∀ (l : List Rule), (∀ r ∈ l, r ∈ d.rules ∧ r.ruleset = R) →
      ∀ acc : FDatabase, acc.EqsInTerms → acc.toDatabase.Contained S →
      (l.foldl (fireRule d) acc).EqsInTerms ∧
        (l.foldl (fireRule d) acc).toDatabase.Contained S := by
    intro l
    induction l with
    | nil => intro _ acc hacce hacc; exact ⟨hacce, hacc⟩
    | cons r l ih =>
      intro hall acc hacce hacc
      rw [List.foldl_cons]
      refine ih (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr')) _ ?_ ?_ <;>
      · rw [fireRule]
        first
        | exact (hinner r (hall r List.mem_cons_self).1 (hall r List.mem_cons_self).2 _
            (fun _ hσ => hσ) acc hacce hacc).1
        | exact (hinner r (hall r List.mem_cons_self).1 (hall r List.mem_cons_self).2 _
            (fun _ hσ => hσ) acc hacce hacc).2
  rw [execRunRules]
  exact (houter _ (fun _ hr => mem_rules_filter.mp hr) d h.eqs
    (Database.Contained.sUnion _ _)).2

/-- **`execCmdM_contained`'s `.action` case**, with `CmdStep.action`'s two premises spelled
out rather than packaged.

It needs no transport at all: `execAction_evalAction` lands on the specification's
`evalAction` result exactly, and `mergeSaturateF_contained` continues from there. That
pairing *is* `CmdStep.action` — the specification's merge phase is what pays for the
interpreter's, and without it this statement is false. -/
theorem execCmdM_action_contained {d e : FDatabase} (h : d.Inv) {a : Action}
    (halegal : a.WriteLegal d.sig)
    (hlegal : Signature.MergesLegal d.sig)
    (hcond : (Signature.UnionFree d.sig ∧ d.toDatabase.Diag ∧ a.UnionFree) ∨
      Signature.OrderingFree d.sig)
    (hs : d.execCmdM (.action a) = some e) :
    ∃ d₁ db, evalAction d.toDatabase a = some d₁ ∧ MergeClosure d₁ db ∧
      e.toDatabase.Recorded db := by
  rw [FDatabase.execCmdM] at hs
  obtain ⟨d₁, hd₁, hsat⟩ := Option.bind_eq_some_iff.mp hs
  have hsig₁ : d₁.sig = d.sig := execAction_sig hd₁
  have hlegal₁ : Signature.MergesLegal d₁.sig := by rw [hsig₁]; exact hlegal
  have heval : evalAction d.toDatabase a = some d₁.toDatabase :=
    FDatabase.execAction_evalAction h.eqs hd₁
  obtain ⟨db, hcl, hcont⟩ :=
    mergeSaturateF_contained (h.execAction halegal hd₁) hlegal₁ (by
      rcases hcond with ⟨hufree, hdiag, hau⟩ | hof
      · exact Or.inl ⟨by rw [hsig₁]; exact hufree, evalAction_diag hau hdiag heval⟩
      · exact Or.inr (by rw [hsig₁]; exact hof)) hsat
  exact ⟨d₁.toDatabase, db, heval, hcl, hcont⟩

end FDatabase

/-! ### Containment for a whole program

`execRunRules_contained` and `mergeSaturateF_contained` cover the two phases of a round.
What is left is the bookkeeping that turns them into a statement about `execCmdM`,
`execProgramM` and `execM`, and it is bookkeeping of exactly two kinds.

**Transport.** The specification witness for a command is a state *containing* the
interpreter's, so the next command's witness has to be re-based onto it. `CmdStep.mono`
and `ProgramStep.mono` are that, and they are `ValidQuerySubst.mono` (a larger state
admits every match), `evalActions_mono` (a block re-run on a larger state lands
on a larger result) and `MergeClosure.transport` composed. They carry `sig`, `env` and
`rules` equalities alongside the containment because all three are read: `mono` needs the
signature, a rule fires in `d.env ++ σ`, and `RunRules` ranges over `rules`.

**Preservation.** The induction carries `FDatabase.Inv`, so every command has to
re-establish it. `.action` and `.run` are the lemmas above run to a fixpoint; `.rule`
touches no field `Inv` reads; `.decl` is the one that needs a hypothesis of its own, and
`Falsity.claim1` is why. -/

/-- **A round preserves union-freedom.** Its rule phase is the `.run` case of
`CmdStep.noUnions` and its merge phase is `MergeClosure.diag`, so a saturating run only has
to iterate it. -/
theorem RunStep.noUnions {R : RulesetName} {A B : Database} (h : RunStep R A B)
    (hn : A.NoUnions) : B.NoUnions :=
  ⟨MergeClosure.diag (by rw [RunRules.sig]; exact hn.sig) (RunRules.diag hn) h,
    by rw [MergeClosure.sig h, RunRules.sig]; exact hn.sig,
    by rw [(MergeClosure.envRules h).2]
       simpa only [RunRules, Database.sUnion_rules] using hn.rules⟩

/-- A round moves neither `sig` nor `rules`, which is all ordering-freedom is about. -/
theorem RunStep.noOrdering {R : RulesetName} {A B : Database} (h : RunStep R A B)
    (hn : A.NoOrdering) : B.NoOrdering :=
  ⟨by rw [MergeClosure.sig h, RunRules.sig]; exact hn.sig,
    by rw [(MergeClosure.envRules h).2]
       simpa only [RunRules, Database.sUnion_rules] using hn.rules⟩

/-- **One command preserves union-freedom, all three clauses.** `.decl` is the only case
that moves `sig` and `.rule` the only one that moves `rules`, which is why `Cmd.UnionFree`
constrains exactly those two alongside a top-level action; the merge phase every command
ends with moves neither, and `MergeClosure.diag` is what keeps the state diagonal across
it. -/
theorem CmdStep.noUnions {A B : Database} (hn : A.NoUnions) {c : Cmd} (hu : c.UnionFree)
    (h : CmdStep A c B) : B.NoUnions := by
  obtain ⟨e, hreach, hcl⟩ := h
  have hE : e.NoUnions := by
    cases c with
    | saturate R =>
      exact RunReach.induction (P := Database.NoUnions)
        (fun _ _ hp hs => RunStep.noUnions hs hp)
        (show SaturateReach R A e from hreach).1 hn
    | action a =>
      replace heff : cmdEffect A (.action a) = some e := hreach
      exact ⟨evalAction_diag hu hn.diag heff, by rw [evalAction_sig heff]; exact hn.sig,
        by rw [evalAction_rules heff]; exact hn.rules⟩
    | rule r =>
      replace heff : cmdEffect A (.rule r) = some e := hreach
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      refine ⟨hn.diag, hn.sig, fun r' hr' => ?_⟩
      rcases hr' with rfl | hr'
      exacts [hu, hn.rules r' hr']
    | run R =>
      replace heff : cmdEffect A (.run R) = some e := hreach
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      exact ⟨RunRules.diag hn, hn.sig, hn.rules⟩
    | decl f dc =>
      replace heff : cmdEffect A (.decl f dc) = some e := hreach
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      refine ⟨hn.diag, fun g dc' hg => ?_, hn.rules⟩
      have hg' : Function.update A.sig f (some dc) g = some dc' := hg
      by_cases hgf : g = f
      · rw [hgf, Function.update_self, Option.some.injEq] at hg'
        exact hg' ▸ hu
      · rw [Function.update_of_ne hgf] at hg'
        exact hn.sig g dc' hg'
  exact ⟨MergeClosure.diag hE.sig hE.diag hcl,
    by rw [MergeClosure.sig hcl]; exact hE.sig,
    by rw [(MergeClosure.envRules hcl).2]; exact hE.rules⟩

/-- **One command preserves ordering-freedom, both clauses.** `.decl` is the only case that
moves `sig` and `.rule` the only one that moves `rules`; the merge phase every command ends
with moves neither, and a top-level action moves neither either. -/
theorem cmdEffect_noOrdering {A e : Database} (hn : A.NoOrdering) {c : Cmd}
    (hu : c.OrderingFree) (heff : cmdEffect A c = some e) : e.NoOrdering := by
  cases c with
  | action a =>
    exact ⟨by rw [evalAction_sig heff]; exact hn.sig,
      by rw [evalAction_rules heff]; exact hn.rules⟩
  | rule r =>
    rw [cmdEffect, Option.some.injEq] at heff
    subst heff
    refine ⟨hn.sig, fun r' hr' => ?_⟩
    rcases hr' with rfl | hr'
    exacts [hu, hn.rules r' hr']
  | run R =>
    rw [cmdEffect, Option.some.injEq] at heff
    subst heff
    exact ⟨hn.sig, hn.rules⟩
  | saturate R => exact absurd heff (by simp [cmdEffect])
  | decl f dc =>
    rw [cmdEffect, Option.some.injEq] at heff
    subst heff
    refine ⟨fun g dc' hg => ?_, hn.rules⟩
    have hg' : Function.update A.sig f (some dc) g = some dc' := hg
    by_cases hgf : g = f
    · rw [hgf, Function.update_self, Option.some.injEq] at hg'
      exact hg' ▸ hu
    · rw [Function.update_of_ne hgf] at hg'
      exact hn.sig g dc' hg'

theorem CmdStep.noOrdering {A B : Database} (hn : A.NoOrdering) {c : Cmd}
    (hu : c.OrderingFree) (h : CmdStep A c B) : B.NoOrdering := by
  obtain ⟨e, hreach, hcl⟩ := h
  have hE : e.NoOrdering := by
    cases c with
    | saturate R =>
      exact RunReach.induction (P := Database.NoOrdering)
        (fun _ _ hp hs => RunStep.noOrdering hs hp)
        (show SaturateReach R A e from hreach).1 hn
    | _ => exact cmdEffect_noOrdering hn hu hreach
  exact ⟨by rw [MergeClosure.sig hcl]; exact hE.sig,
    by rw [(MergeClosure.envRules hcl).2]; exact hE.rules⟩

/-- What the interpreter's own state inherits: it agrees with a witness that is
ordering-free in the two fields the condition reads. -/
theorem Database.NoOrdering.of_eq {A C : Database} (hn : C.NoOrdering) (hsig : A.sig = C.sig)
    (hrules : A.rules = C.rules) : A.NoOrdering where
  sig := by rw [hsig]; exact hn.sig
  rules := by rw [hrules]; exact hn.rules

/-- **A firing available at `A` is available at any `C` containing it.**
`ValidQuerySubst.mono` finds the same match and `evalActions_mono` re-runs the
head on the larger state. The result is an existential, not the join: that is all
containment needs, and it is all `evalActions_mono` gives. -/
theorem RuleResults.mono {A C : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) {r : Rule} {d : Database} (hd : d ∈ RuleResults A r) :
    ∃ D ∈ RuleResults C r, d.Contained D := by
  obtain ⟨σ, hq, hstep⟩ := hd
  obtain ⟨d', hv, rfl⟩ := evalLocalActions_eq_some hstep
  have hc0 : ({ A with env := A.env ++ σ } : Database).Contained
      { C with env := C.env ++ σ } := ⟨hc.eqs⟩
  obtain ⟨D', hD', hcont, -, -⟩ := evalActions_mono hc0 hsig (by simp [henv]) hv
  exact ⟨{ D' with env := C.env, rules := C.rules },
    ⟨σ, ValidQuerySubst.mono hc hsig henv.symm hq,
      by rw [evalLocalActions, hD', Option.map_some]⟩,
    ⟨hcont.eqs⟩⟩

/-- **A round's rule phase is monotone.** Every database one rule contributes at `A` is
contained in one the same rule contributes at `C`, so the two unions are ordered. -/
theorem RunRules.mono {R : RulesetName} {A C : Database} (hc : A.Contained C)
    (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) :
    (RunRules R A).Contained (RunRules R C) := by
  have key : ∀ d ∈ {d | ∃ r ∈ A.rules, r.ruleset = R ∧ d ∈ RuleResults A r},
      d.Contained (RunRules R C) := by
    rintro d ⟨r, hr, hR, hdr⟩
    obtain ⟨D, hD, hcd⟩ := RuleResults.mono hc hsig henv hdr
    exact hcd.trans (Database.Contained.mem_sUnion ⟨r, hrules ▸ hr, hR, hD⟩)
  refine ⟨?_⟩
  rintro x (hx | hx)
  · exact (Database.Contained.sUnion C _).eqs (hc.eqs hx)
  · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
    exact (key d hd).eqs hx'

/-- **A command available at `A` is available at any `C` containing it, and its result
still contains the smaller run's.** The four cases are `evalAction_mono`,
nothing, `RunRules.mono`, and nothing; `MergeClosure.transport` re-bases the merge phase
in the two that have one. -/
theorem CmdStep.mono {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) {c : Cmd} (hns : c.NoSaturate)
    (h : CmdStep A c B) :
    ∃ D, CmdStep C c D ∧ B.Contained D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  obtain ⟨e, hreach, hcl⟩ := h
  replace heff := cmdEffect_of_cmdReach hns hreach
  have key : ∃ E, cmdEffect C c = some E ∧ e.Contained E ∧ e.sig = E.sig ∧ e.env = E.env ∧
      e.rules = E.rules := by
    cases c with
    | action a =>
      obtain ⟨E, hE, hcont, hs, he⟩ := evalAction_mono hc hsig henv heff
      exact ⟨E, hE, hcont, hs, he,
        by rw [evalAction_rules heff, evalAction_rules hE, hrules]⟩
    | rule r =>
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      exact ⟨_, rfl, ⟨hc.eqs⟩, hsig, henv, by
        change insert r A.rules = insert r C.rules
        rw [hrules]⟩
    | run R =>
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      refine ⟨_, rfl, RunRules.mono hc hsig henv hrules, ?_, ?_, ?_⟩
      · show (RunRules R A).sig = (RunRules R C).sig
        simp only [RunRules, Database.sUnion_sig]; exact hsig
      · show (RunRules R A).env = (RunRules R C).env
        simp only [RunRules, Database.sUnion_env]; exact henv
      · show (RunRules R A).rules = (RunRules R C).rules
        simp only [RunRules, Database.sUnion_rules]; exact hrules
    | saturate R => exact (hns : False).elim
    | decl f dc =>
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      exact ⟨_, rfl, ⟨hc.eqs⟩, by
        change Function.update A.sig f (some dc) = Function.update C.sig f (some dc)
        rw [hsig], henv, hrules⟩
  obtain ⟨E, hE, hcont, hs, he, hr⟩ := key
  obtain ⟨D, hclD, hcontD, hsigD⟩ := MergeClosure.transport hcont hs hcl
  exact ⟨D, ⟨E, cmdReach_of_cmdEffect hns hE, hclD⟩, hcontD, hsigD,
    by rw [(MergeClosure.envRules hcl).1, (MergeClosure.envRules hclD).1, he],
    by rw [(MergeClosure.envRules hcl).2, (MergeClosure.envRules hclD).2, hr]⟩

/-- `CmdStep.mono` iterated. This is what makes the containment contract compose: the
specification witness for the tail of a program starts from the witness the head
produced, which contains — but need not equal — the interpreter's state. -/
theorem ProgramStep.mono {A B : Database} {p : Program} (h : ProgramStep A p B) :
    ∀ {C : Database}, A.Contained C → A.sig = C.sig → A.env = C.env → A.rules = C.rules →
      p.NoSaturate →
      ∃ D, ProgramStep C p D ∧ B.Contained D ∧ B.sig = D.sig ∧ B.env = D.env ∧
        B.rules = D.rules := by
  induction h with
  | nil => exact fun hc hsig henv hrules _ => ⟨_, .nil, hc, hsig, henv, hrules⟩
  | @cons A e B c cs hcmd _ ih =>
    intro C hc hsig henv hrules hns
    obtain ⟨D₀, hD₀, hc₀, hs₀, he₀, hr₀⟩ :=
      hcmd.mono hc hsig henv hrules (hns c List.mem_cons_self)
    obtain ⟨D₁, hD₁, hc₁, hs₁, he₁, hr₁⟩ :=
      ih hc₀ hs₀ he₀ hr₀ (fun c' hc' => hns c' (List.mem_cons_of_mem c hc'))
    exact ⟨D₁, .cons hD₀ hD₁, hc₁, hs₁, he₁, hr₁⟩

/-! #### The same, along `Recorded`

The re-keying contract needs the transport lemmas again, and **`hcond` is what makes them
true**. `ValidSubst.mono_recorded` is **deleted** — see the heading above `ValidEnv.mono`,
it is false — so these cannot be proved by transporting the same substitution at an
arbitrary recorder; `MergeStep.transport_recorded` is false at an arbitrary recorder too,
for the reason its own docstring gives.

Two conditions repair them, and each closes both. On a **diagonal** `C` there is nothing
congruent but equal, so `Database.Recorded.contained_of_diag` turns the hypothesis into a
`Database.Contained` and the four `mono`/`transport` lemmas above are the proofs. Under
**ordering-freedom** the substitution is moved by a single witness function and the head
re-run under it: `RuleResults.mono_owes` and `MergeStep.transport_owes` are the proofs, and
`union` is not restricted at all.

`Database.Recorded.trans`, which used to be a third open obligation, is proved from
`Conservativity` under two `WF` premises. The two `WF` premises the lemmas below now carry
are the ordering-free arm's: `Owes` is a statement about the *subterms* of a value, and
both `Database.WF.subtermClosed` and `Database.WF.eqsRefl` are read to establish it. -/

/-- `RuleResults.mono` along `Recorded`.

`hcond` is not bookkeeping: without it this is **not provable**, and the obstruction is
double. `ValidQuerySubst.mono_recorded` is false at the same `σ`, so the substitution the
firing runs under has to be replaced by a congruent one — chosen once for the whole query,
because `Env.UnionAll` makes the per-pattern choices agree — and then the head re-run under
it; and `Expr.eval` is not congruence-stable at `ordering-min`/`ordering-max`, so "a
congruent environment gives a recording result" is itself **false** with `ordering-max` in
the rule. `Rule.OrderingFree` is exactly what closes the second gap, and `Env.mapVals` over
the witness of `exists_witness` closes the first.

The general form is what the consumer needs — `RunRules.mono_recorded` transports every
member of `RuleResults A r`, at a `Recorded` reaching back to `execProgramM_contained_aux`
— so this cannot be narrowed to a special case. -/
theorem RuleResults.mono_recorded {A C : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig) (henv : A.env = C.env) {r : Rule}
    (hcond : C.Diag ∨ Rule.OrderingFree r) {d : Database} (hd : d ∈ RuleResults A r) :
    ∃ D ∈ RuleResults C r, d.Recorded D ∧ D.sig = C.sig := by
  rcases hcond with hdiag | hof
  · obtain ⟨D, hD, hcont⟩ := RuleResults.mono (hc.contained_of_diag hdiag) hsig henv hd
    obtain ⟨σ, hq, hσ⟩ := hD
    exact ⟨D, ⟨σ, hq, hσ⟩, .of_contained hcont, evalLocalActions_sig hσ⟩
  · exact RuleResults.mono_owes hc hwfA hwfC hsig henv hof hd

/-- `RunRules.mono` along `Recorded`. -/
theorem RunRules.mono_recorded {R : RulesetName} {A C : Database} (hc : A.Recorded C)
    (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig) (henv : A.env = C.env) (hrules : A.rules = C.rules)
    (hcond : C.Diag ∨ ∀ r ∈ C.rules, Rule.OrderingFree r) :
    (RunRules R A).Recorded (RunRules R C) := by
  rcases hcond with hdiag | hof
  · exact .of_contained (RunRules.mono (hc.contained_of_diag hdiag) hsig henv hrules)
  · exact RunRules.mono_owes hc hwfA hwfC hsig henv hrules hof

/-- `CmdStep.mono` along `Recorded`. The four cases are `evalAction_mono_recorded`, which
needs no condition because the two environments are equal there, nothing,
`RunRules.mono_recorded`, and nothing; `MergeClosure.transport_recorded` re-bases the merge
phase in all four. -/
theorem CmdStep.mono_recorded {A C B : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig) (henv : A.env = C.env) (hrules : A.rules = C.rules)
    {c : Cmd} (hns : c.NoSaturate)
    (hcond : C.Diag ∨ (C.NoOrdering ∧ c.OrderingFree)) (h : CmdStep A c B) :
    ∃ D, CmdStep C c D ∧ B.Recorded D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  rcases hcond with hdiag | ⟨hno, hcof⟩
  · obtain ⟨D, hstep, hcont, hs, he, hr⟩ :=
      h.mono (hc.contained_of_diag hdiag) hsig henv hrules hns
    exact ⟨D, hstep, .of_contained hcont, hs, he, hr⟩
  obtain ⟨e, hreach, hcl⟩ := h
  replace heff := cmdEffect_of_cmdReach hns hreach
  have key : ∃ E, cmdEffect C c = some E ∧ e.Recorded E ∧ e.sig = E.sig ∧ e.env = E.env ∧
      e.rules = E.rules ∧ E.WF ∧ e.WF := by
    have hwfe : e.WF := cmdEffect_wf hwfA heff
    cases c with
    | action a =>
      obtain ⟨E, hE, hcont, hs, he⟩ := evalAction_mono_recorded hc hsig henv heff
      exact ⟨E, hE, hcont, hs, he,
        by rw [evalAction_rules heff, evalAction_rules hE, hrules],
        evalAction_wf hwfC hE, hwfe⟩
    | rule r =>
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      exact ⟨_, rfl, hc.setEnvRules _ _ _ _, hsig, henv, by
        change insert r A.rules = insert r C.rules
        rw [hrules], hwfC.congr rfl rfl, hwfe⟩
    | run R =>
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      refine ⟨_, rfl, RunRules.mono_recorded hc hwfA hwfC hsig henv hrules (Or.inr hno.rules),
        ?_, ?_, ?_, RunRules.wf hwfC, hwfe⟩
      · show (RunRules R A).sig = (RunRules R C).sig
        simp only [RunRules, Database.sUnion_sig]; exact hsig
      · show (RunRules R A).env = (RunRules R C).env
        simp only [RunRules, Database.sUnion_env]; exact henv
      · show (RunRules R A).rules = (RunRules R C).rules
        simp only [RunRules, Database.sUnion_rules]; exact hrules
    | saturate R => exact (hns : False).elim
    | decl f dc =>
      rw [cmdEffect, Option.some.injEq] at heff
      subst heff
      refine ⟨_, rfl, ⟨fun p hp => ?_⟩, ?_, henv, hrules, hwfC.congr rfl rfl, hwfe⟩
      · obtain ⟨q, hq, hc₁, hc₂⟩ := hc.eqs p hp
        exact ⟨q, hq, congOn_setSig hc₁, congOn_setSig hc₂⟩
      · change Function.update A.sig f (some dc) = Function.update C.sig f (some dc)
        rw [hsig]
  obtain ⟨E, hE, hcont, hs, he, hr, hwfE, hwfe⟩ := key
  obtain ⟨D, hclD, hcontD, hsigD⟩ :=
    MergeClosure.transport_recorded hcont hwfe hwfE hs
      (Or.inr (cmdEffect_noOrdering hno hcof hE).sig) hcl
  exact ⟨D, ⟨E, cmdReach_of_cmdEffect hns hE, hclD⟩, hcontD, hsigD,
    by rw [(MergeClosure.envRules hcl).1, (MergeClosure.envRules hclD).1, he],
    by rw [(MergeClosure.envRules hcl).2, (MergeClosure.envRules hclD).2, hr]⟩

/-- `CmdStep.mono_recorded` iterated, under ordering-freedom. The condition is
re-established per command by `CmdStep.noOrdering`, which is why the program's own
condition appears; the `Database.WF`s are re-established by `CmdStep.wf`. -/
theorem ProgramStep.mono_owes {A B : Database} {p : Program} (h : ProgramStep A p B) :
    ∀ {C : Database}, A.WF → C.WF → A.Recorded C → A.sig = C.sig → A.env = C.env →
      A.rules = C.rules → C.NoOrdering → p.NoSaturate → p.OrderingFree →
      ∃ D, ProgramStep C p D ∧ B.Recorded D ∧ B.sig = D.sig ∧ B.env = D.env ∧
        B.rules = D.rules := by
  induction h with
  | nil => exact fun _ _ hc hsig henv hrules _ _ _ => ⟨_, .nil, hc, hsig, henv, hrules⟩
  | @cons A e B c cs hcmd _ ih =>
    intro C hwfA hwfC hc hsig henv hrules hno hns hof
    obtain ⟨D₀, hD₀, hc₀, hs₀, he₀, hr₀⟩ :=
      hcmd.mono_recorded hc hwfA hwfC hsig henv hrules (hns c List.mem_cons_self)
        (Or.inr ⟨hno, hof.1⟩)
    obtain ⟨D₁, hD₁, hc₁, hs₁, he₁, hr₁⟩ :=
      ih (CmdStep.wf hwfA hcmd) (CmdStep.wf hwfC hD₀) hc₀ hs₀ he₀ hr₀
        (CmdStep.noOrdering hno hof.1 hD₀) (fun c' hc' => hns c' (List.mem_cons_of_mem c hc'))
        hof.2
    exact ⟨D₁, .cons hD₀ hD₁, hc₁, hs₁, he₁, hr₁⟩

/-- `ProgramStep.mono` along `Recorded`. In the diagonal arm `hcond` is about `C` alone, so
nothing has to be re-established at the intermediate witnesses; in the ordering-free arm
`ProgramStep.mono_owes` re-establishes it per command. -/
theorem ProgramStep.mono_recorded {A C B : Database} (hc : A.Recorded C) (hwfA : A.WF)
    (hwfC : C.WF) (hsig : A.sig = C.sig) (henv : A.env = C.env) (hrules : A.rules = C.rules)
    {p : Program} (hns : p.NoSaturate) (hcond : C.Diag ∨ (C.NoOrdering ∧ p.OrderingFree))
    (h : ProgramStep A p B) :
    ∃ D, ProgramStep C p D ∧ B.Recorded D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  rcases hcond with hdiag | ⟨hno, hof⟩
  · obtain ⟨D, hstep, hcont, hs, he, hr⟩ :=
      h.mono (hc.contained_of_diag hdiag) hsig henv hrules hns
    exact ⟨D, hstep, .of_contained hcont, hs, he, hr⟩
  · exact h.mono_owes hwfA hwfC hc hsig henv hrules hno hns hof

/-! #### Declaring a fresh name

The facts a `.decl` needs, all of them about a name the signature does not yet mention. -/

/-- `Signature.mergeOf` is read pointwise, so a declaration at `f` is invisible at every
other name. -/
theorem Signature.mergeOf_update_of_ne {sig : Signature} {f g : FnName} {dc : FnDecl}
    (h : g ≠ f) :
    Signature.mergeOf (Function.update sig f (some dc)) g = Signature.mergeOf sig g := by
  unfold Signature.mergeOf
  rw [Function.update_of_ne h]

/-- An undeclared name has no merge specification either — which is *not* the same as
being a constructor, and is the half of the old reading that survives. -/
theorem Signature.mergeOf_of_none {sig : Signature} {f : FnName}
    (h : sig f = none) : Signature.mergeOf sig f = none := by
  rw [Signature.mergeOf, h]; rfl

/-- Declaring a name the signature does not yet mention can only make a `set` *more*
legal: `Action.SetLegal` asks for a merge specification and an undeclared name has none,
so no legal `set` names `f`. -/
theorem Action.SetLegal.update {a : Action} {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) (h : a.SetLegal sig) :
    a.SetLegal (Function.update sig f (some dc)) := by
  cases a with
  | expr _ => trivial
  | letBind _ _ => trivial
  | union _ _ => trivial
  | set g _ _ =>
    have hg : g ≠ f := by
      rintro rfl
      exact h (Signature.mergeOf_of_none hf)
    change Signature.mergeOf (Function.update sig f (some dc)) g ≠ none
    rw [Signature.mergeOf_update_of_ne hg]
    exact h

theorem Actions.SetLegal.update {as : List Action} {sig : Signature} {f : FnName}
    {dc : FnDecl} (hf : sig f = none) (h : Actions.SetLegal as sig) :
    Actions.SetLegal as (Function.update sig f (some dc)) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨Action.SetLegal.update hf h.1, ih h.2⟩

/-- Declaring a fresh name cannot make a legal `set` illegal, nor its widths wrong: no
legal `set` names `f`, since an undeclared name has no merge specification. -/
theorem Action.WriteLegal.update {a : Action} {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) (h : a.WriteLegal sig) :
    a.WriteLegal (Function.update sig f (some dc)) := by
  refine ⟨Action.SetLegal.update hf h.1, ?_⟩
  cases a with
  | expr _ => trivial
  | letBind _ _ => trivial
  | union _ _ => trivial
  | set g args out =>
    intro dc' hdc'
    have hg : g ≠ f := by
      rintro rfl
      exact h.1 (Signature.mergeOf_of_none hf)
    refine h.2 dc' ?_
    have hx : Function.update sig f (some dc) g = some dc' := hdc'
    rwa [Function.update_of_ne hg] at hx

theorem Actions.WriteLegal.update {as : List Action} {sig : Signature} {f : FnName}
    {dc : FnDecl} (hf : sig f = none) (h : Actions.WriteLegal as sig) :
    Actions.WriteLegal as (Function.update sig f (some dc)) := by
  induction as with
  | nil => exact ⟨trivial, trivial⟩
  | cons a as ih =>
    exact ⟨⟨(Action.WriteLegal.update hf h.head).1, (ih h.tail).1⟩,
      ⟨(Action.WriteLegal.update hf h.head).2, (ih h.tail).2⟩⟩

namespace FDatabase

/-! #### The interpreter's phases, field by field

`mergeRound_confined` records what a merge pass does to `terms`, `rows`, `eqs` and `sig`.
The transport lemmas above additionally read `env` and `rules`, and the same is needed of
`execRunRules`, so both folds are factored into an induction principle and instantiated
twice — once for the fields, once for `Inv`. -/

/-- Anything true of `d`, preserved by the rebuild and by one `mergeOneWith` firing, is
true after a whole pass. The rebuild and the two folds of `mergeRound`, factored out. -/
theorem mergeRound_induction {d : FDatabase} {P : FDatabase → Prop} (hinit : P d)
    (hreb : P (FDatabase.rebuild d.closureF d))
    (hstep : ∀ x y : FDatabase, ∀ r₁ r₂ : Row, P x →
      FDatabase.mergeOneWith d.closureF x r₁ r₂ = some y → P y) :
    P d.mergeRound := by
  have hstep' : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y => simpa [hy] using hstep x y r₁ r₂ hx hy
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep' x r₁ r₂ hx
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold m r₁ x hx)
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter _ _ _ hreb

/-- A firing restores the caller's environment and rule list. -/
theorem mergeOneOriented_envRules {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (h : d.mergeOneOriented cl r₁ r₂ = some e) :
    e.env = d.env ∧ e.rules = d.rules := by
  unfold FDatabase.mergeOneOriented at h
  match hmo : d.sig.mergeOf r₁.fn with
  | none => rw [hmo] at h; simp at h
  | some .noMerge => rw [hmo] at h; simp at h
  | some (.merge body res) =>
    rw [hmo] at h
    simp only at h
    split at h
    case isFalse => simp at h
    case isTrue =>
      split at h
      case isTrue => rw [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      case isFalse =>
        cases hb : execActions { d with env := mergeEnv r₂.out r₁.out } body with
        | none => rw [hb] at h; simp at h
        | some eb =>
          rw [hb, Option.bind_some, Option.map_eq_some_iff] at h
          obtain ⟨vs, hv, rfl⟩ := h
          exact ⟨rfl, rfl⟩

/-- `mergeOneOriented_envRules` at whichever orientation the firing took. -/
theorem mergeOneWith_envRules {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.mergeOneWith cl r₁ r₂ = some e) : e.env = d.env ∧ e.rules = d.rules := by
  rcases mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he <;>
    exact mergeOneOriented_envRules (he ▸ h)

/-- A merge pass touches neither the environment nor the rule list. -/
theorem mergeRound_envRules {d : FDatabase} :
    d.mergeRound.env = d.env ∧ d.mergeRound.rules = d.rules :=
  mergeRound_induction (P := fun x => x.env = d.env ∧ x.rules = d.rules) ⟨rfl, rfl⟩
    ⟨rebuild_envRules.1, rebuild_envRules.2⟩
    fun _ _ _ _ hx hy =>
      ⟨(mergeOneWith_envRules hy).1.trans hx.1, (mergeOneWith_envRules hy).2.trans hx.2⟩

/-- The merge phase leaves `sig`, `env` and `rules` alone. -/
theorem mergeSaturateF_fields {n : Nat} : ∀ {d e : FDatabase},
    d.mergeSaturateF n = some e → e.sig = d.sig ∧ e.env = d.env ∧ e.rules = d.rules := by
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ ⟨rfl, rfl, rfl⟩
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ ⟨rfl, rfl, rfl⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih hs
      exact ⟨h₁.trans mergeRound_confined.2.2.1, h₂.trans mergeRound_envRules.1,
        h₃.trans mergeRound_envRules.2⟩

/-- `Inv.mergeRound_of_legalMerges` run to a fixpoint. `mergeRound_confined` is what keeps
`hlegal` — a statement about the pre-phase signature — applicable at the next round. -/
theorem Inv.mergeSaturateF {n : Nat} : ∀ {d e : FDatabase}, d.Inv →
    Signature.MergesLegal d.sig →
    d.mergeSaturateF n = some e → e.Inv := by
  induction n with
  | zero =>
    intro d e h _ hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ h
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e h hlegal hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ h
    · refine ih (h.mergeRound_of_legalMerges hlegal) ?_ hs
      rw [mergeRound_confined.2.2.1]; exact hlegal

/-- Unioning two states preserves the refinement-chain invariant, provided they agree on
the signature: every field of `Inv` is a positive condition on `terms`, `rows` and `eqs`
relative to `sig`, and a union takes `sig`, `env` and `rules` from the left. -/
theorem Inv.union {d e : FDatabase} (hd : d.Inv) (he : e.Inv) (hsig : e.sig = d.sig) :
    (d.union e).Inv := by
  have hcd : d.toDatabase.Contained (d.union e).toDatabase :=
    toDatabase_contained_of_lists (fun _ hx => mem_terms_union.mpr (Or.inl hx))
      (fun _ hx => mem_eqs_union.mpr (Or.inl hx))
  have hce : e.toDatabase.Contained (d.union e).toDatabase :=
    toDatabase_contained_of_lists (fun _ hx => mem_terms_union.mpr (Or.inr hx))
      (fun _ hx => mem_eqs_union.mpr (Or.inr hx))
  refine ⟨⟨eqsRefl _, fun t ht s hs => ?_, fun b hb => ?_, fun p hp => ?_⟩,
    EqsInTerms.union hd.eqs he.eqs, ⟨fun r hr hm => ?_, fun r hr hm => ?_,
      fun r hr dc hdc hm => ?_⟩⟩
  · rw [FDatabase.mem_toDatabase_terms] at ht
    rw [FDatabase.mem_toDatabase_terms]
    rcases mem_terms_union.mp ht with ht' | ht'
    · refine mem_terms_union.mpr (Or.inl ?_)
      exact FDatabase.mem_toDatabase_terms.mp
        (hd.wf.subtermClosed t (FDatabase.mem_toDatabase_terms.mpr ht') hs)
    · refine mem_terms_union.mpr (Or.inr ?_)
      exact FDatabase.mem_toDatabase_terms.mp
        (he.wf.subtermClosed t (FDatabase.mem_toDatabase_terms.mpr ht') hs)
  · exact hcd.terms (hd.wf.envInTerms b hb)
  · rcases FDatabase.mem_toDatabase_eqs.mp hp with ⟨heq, -⟩ | ⟨hp', -, -⟩
    · exact fun _ => heq
    · rcases mem_eqs_union.mp hp' with hp'' | hp''
      · exact hd.wf.litsIsolated p
          ((FDatabase.mem_toDatabase_eqs_of_eqsInTerms hd.eqs).mpr (Or.inr hp''))
      · exact he.wf.litsIsolated p
          ((FDatabase.mem_toDatabase_eqs_of_eqsInTerms he.eqs).mpr (Or.inr hp''))
  · rcases mem_rows_union.mp hr with hr' | hr'
    · exact ⟨(hd.index.ctor r hr' hm).1,
        mem_terms_union.mpr (Or.inl (hd.index.ctor r hr' hm).2)⟩
    · have hm' : e.sig.mergeOf r.fn = none := by rw [hsig]; exact hm
      exact ⟨(he.index.ctor r hr' hm').1,
        mem_terms_union.mpr (Or.inr (he.index.ctor r hr' hm').2)⟩
  · rcases mem_rows_union.mp hr with hr' | hr'
    · exact Database.Out.mono hcd (hd.index.entry r hr' hm)
    · have hm' : e.sig.mergeOf r.fn ≠ none := by rw [hsig]; exact hm
      exact Database.Out.mono hce (he.index.entry r hr' hm')
  · rcases mem_rows_union.mp hr with hr' | hr'
    · exact hd.index.width r hr' dc hdc hm
    · have hm' : e.sig.mergeOf r.fn ≠ none := by rw [hsig]; exact hm
      exact he.index.width r hr' dc (by rw [hsig]; exact hdc) hm'

/-- Anything true of `d` and preserved by one rule firing is true of a whole round's rule
phase. The three folds of `execRunRules`, factored out. -/
theorem execRunRules_induction {R : RulesetName} {d : FDatabase} {P : FDatabase → Prop}
    (hinit : P d)
    (hstep : ∀ (acc e : FDatabase) (r : Rule) (σ : Env), P acc → r ∈ d.rules →
      σ ∈ matchQuery d r.query →
      execActions { d with env := d.env ++ σ } r.actions = some e →
      P (acc.union { e with env := d.env, rules := d.rules })) :
    P (execRunRules R d) := by
  have hone : ∀ (r : Rule), r ∈ d.rules → ∀ (σ : Env), σ ∈ matchQuery d r.query →
      ∀ acc : FDatabase, P acc → P (fireInto d r acc σ) := by
    intro r hr σ hσ acc hacc
    rw [fireInto, execLocalActions]
    cases hv : execActions { d with env := d.env ++ σ } r.actions with
    | none => simpa using hacc
    | some e => simpa using hstep acc e r σ hacc hr hσ hv
  have hinner : ∀ (r : Rule), r ∈ d.rules → ∀ (σs : List Env),
      (∀ σ ∈ σs, σ ∈ matchQuery d r.query) → ∀ acc : FDatabase, P acc →
      P (σs.foldl (fireInto d r) acc) := by
    intro r hr σs
    induction σs with
    | nil => intro _ acc hacc; exact hacc
    | cons σ σs ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      exact ih (fun τ hτ => hall τ (List.mem_cons_of_mem _ hτ)) _
        (hone r hr σ (hall σ List.mem_cons_self) acc hacc)
  have houter : ∀ (l : List Rule), (∀ r ∈ l, r ∈ d.rules) → ∀ acc : FDatabase, P acc →
      P (l.foldl (fireRule d) acc) := by
    intro l
    induction l with
    | nil => intro _ acc hacc; exact hacc
    | cons r l ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      refine ih (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr')) _ ?_
      rw [fireRule]
      exact hinner r (hall r List.mem_cons_self) _ (fun _ hσ => hσ) acc hacc
  rw [execRunRules]
  exact houter _ (fun _ hr => (mem_rules_filter.mp hr).1) d hinit

/-- A round's rule phase leaves `sig`, `env` and `rules` alone: every firing is unioned
into the accumulator, and a union takes those three fields from the left. -/
theorem execRunRules_fields {R : RulesetName} {d : FDatabase} :
    (execRunRules R d).sig = d.sig ∧ (execRunRules R d).env = d.env ∧
      (execRunRules R d).rules = d.rules :=
  execRunRules_induction (P := fun x => x.sig = d.sig ∧ x.env = d.env ∧ x.rules = d.rules)
    ⟨rfl, rfl, rfl⟩ fun _ _ _ _ hacc _ _ _ => hacc

/-- Every value a match assigns is a term the database already holds, so extending `d.env`
by one keeps `Inv`. -/
theorem Inv.setEnvMatch {d : FDatabase} (h : d.Inv) {q : Query} {σ : Env}
    (hσ : σ ∈ matchQuery d q) : ({ d with env := d.env ++ σ } : FDatabase).Inv := by
  refine h.setEnv ?_
  intro b hb
  rcases List.mem_append.mp hb with hb' | hb'
  · exact h.wf.envInTerms b hb'
  · have hmem : σ ∈ assignments d.valueTerms (Query.freeVars q d.env) :=
      (List.mem_filter.mp (by rwa [matchQuery] at hσ)).1
    exact FDatabase.mem_toDatabase_terms.mpr
      (mem_terms_of_mem_valueTerms ((mem_assignments.mp hmem).2 b hb'))

/-- **A round's rule phase preserves `Inv`.** Each firing runs a rule head, which is an
action block like any other, so `hrules` is `Inv.execActions`'s premise per rule; the
result is unioned in, which `Inv.union` covers. -/
theorem Inv.execRunRules {R : RulesetName} {d : FDatabase} (h : d.Inv)
    (hrules : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig) :
    (execRunRules R d).Inv := by
  have := execRunRules_induction (R := R) (d := d) (P := fun x => x.Inv ∧ x.sig = d.sig)
    ⟨h, rfl⟩
    (fun acc e r σ hacc hr hσ hv => ?_)
  · exact this.1
  refine ⟨hacc.1.union ?_ ?_, hacc.2⟩
  · refine Inv.setEnvRules ((h.setEnvMatch hσ).execActions (hrules r hr) hv) ?_
    intro b hb
    refine (execActions_contained (d := { d with env := d.env ++ σ }) hv).terms ?_
    exact Database.mem_terms_of_eqs (d₁ := d.toDatabase)
      (d₂ := ({ d with env := d.env ++ σ } : FDatabase).toDatabase)
      (fun _ hp => hp) (h.wf.envInTerms b hb)
  · change e.sig = acc.sig
    rw [execActions_sig hv, hacc.2]

@[simp] theorem addTerms_rules {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).rules = d.rules := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addRow_rules {d : FDatabase} {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).rules = d.rules := rfl

/-- No action touches the rule list; only `Cmd.rule` does. -/
theorem execAction_rules {d e : FDatabase} {a : Action} (h : execAction d a = some e) :
    e.rules = d.rules := by
  cases a with
  | expr e₀ =>
    rw [execAction] at h
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | letBind v e₀ =>
    rw [execAction] at h
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | union e₁ e₂ =>
    rw [execAction] at h
    obtain ⟨t₁, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t₂, -, h''⟩ := Option.bind_eq_some_iff.mp h'
    split at h''
    · simp at h''
    · simp only [Option.some.injEq] at h''
      exact h'' ▸ rfl
  | set f args out =>
    rw [execAction] at h
    obtain ⟨ts, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs, -, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact addRow_rules

theorem execActions_rules {d e : FDatabase} {as : List Action}
    (h : execActions d as = some e) : e.rules = d.rules := by
  induction as generalizing d with
  | nil => rw [execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some d' =>
      rw [execActions, hv, Option.bind_some] at h
      exact (ih h).trans (execAction_rules hv)

/-- **`Inv` survives a declaration of a name the state does not yet mention.**

There is no unconditional preservation lemma, and `IndexOk` is where it fails: `ctor` and
`entry` split on `d.sig.mergeOf r.fn`, so a declaration that turns a name from undeclared
into a merge function moves a row from one clause to the other. `hterms` rules that out —
an undeclared `f` has `mergeOf f = none`, so `ctor` already puts `f(r.args)` in `terms`,
which `hterms` forbids, so no row is headed by `f` at all. -/
theorem Inv.decl {d : FDatabase} (h : d.Inv) {f : FnName} {dc : FnDecl}
    (hf : d.sig f = none) (hterms : ∀ as, Term.app f as ∉ d.terms) :
    ({ d with sig := Function.update d.sig f (some dc) } : FDatabase).Inv := by
  have hne : ∀ r ∈ d.rows, r.fn ≠ f := by
    rintro r hr rfl
    exact hterms r.args (h.index.ctor r hr (Signature.mergeOf_of_none hf)).2
  have hmerge : ∀ r ∈ d.rows,
      Signature.mergeOf (Function.update d.sig f (some dc)) r.fn = d.sig.mergeOf r.fn :=
    fun r hr => Signature.mergeOf_update_of_ne (hne r hr)
  have hcont : d.toDatabase.Contained
      ({ d with sig := Function.update d.sig f (some dc) } : FDatabase).toDatabase :=
    ⟨fun _ hp => hp⟩
  refine ⟨h.wf.congr rfl rfl, h.eqs, ⟨fun r hr hm => ?_, fun r hr hm => ?_,
    fun r hr dc' hdc hm => ?_⟩⟩
  · exact h.index.ctor r hr (by rw [← hmerge r hr]; exact hm)
  · exact Database.Out.mono hcont (h.index.entry r hr (by rw [← hmerge r hr]; exact hm))
  · refine h.index.width r hr dc' ?_ (by rw [← hmerge r hr]; exact hm)
    have : Function.update d.sig f (some dc) r.fn = some dc' := hdc
    rwa [Function.update_of_ne (hne r hr)] at this

end FDatabase

/-! #### The side conditions

Two of them, and neither is avoidable. `Signature.MergesLegal` is what
`FDatabase.IndexOk` forces of a merge body; `FDatabase.Unused` is what it forces of a
declaration (`FDatabase.Inv.decl`). `FDatabase.ProgramLegal` checks both at the state each
command runs in, which is the weakest place to check them: a declaration only has to be
fresh *when it happens*. -/

/-- `f` is a name `d` does not mention: not declared, and not the head of any application
`d` holds. This is "declare before use", which egglog enforces in its front end. -/
def FDatabase.Unused (d : FDatabase) (f : FnName) : Prop :=
  d.sig f = none ∧ ∀ as, Term.app f as ∉ d.terms

/-- The one thing a command may not do to the state it runs in: declare a name that state
already uses. Only `.decl` is constrained. -/
def Cmd.DeclUnused : Cmd → FDatabase → Prop
  | .decl f _, d => d.Unused f
  | _, _ => True

/-- The side conditions a run has to satisfy, checked at the state each command actually
reaches: its head is a legal `set`, it declares nothing already in use, and the signature
it leaves behind has legal merge bodies. -/
def FDatabase.ProgramLegal (d : FDatabase) : Program → Prop
  | [] => True
  | c :: cs => c.WriteLegal d.sig ∧ c.DeclUnused d ∧
      Signature.MergesLegal (c.sigBind d.sig) ∧
      ∀ d', d.execCmdM c = some d' → FDatabase.ProgramLegal d' cs

namespace FDatabase

/-! #### A saturating run, on the interpreter side

`runSaturateM` is `runRoundM` iterated and `runRoundM` is a rule phase followed by a merge
phase, so each fact below is the corresponding fact about those two carried along the fuel
by an induction. -/
theorem runRoundM_fields {R : RulesetName} {d e : FDatabase} (hs : d.runRoundM R = some e) :
    e.sig = d.sig ∧ e.env = d.env ∧ e.rules = d.rules := by
  obtain ⟨h₁, h₂, h₃⟩ := mergeSaturateF_fields hs
  exact ⟨h₁.trans execRunRules_fields.1, h₂.trans execRunRules_fields.2.1,
    h₃.trans execRunRules_fields.2.2⟩

theorem Inv.runRoundM {R : RulesetName} {d e : FDatabase} (h : d.Inv)
    (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hs : d.runRoundM R = some e) : e.Inv :=
  Inv.mergeSaturateF (h.execRunRules hrules)
    (by rw [execRunRules_fields.1]; exact hmerges) hs

theorem runSaturateM_fields {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateM R n = some e → e.sig = d.sig ∧ e.env = d.env ∧ e.rules = d.rules := by
  intro n
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, hx, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ ⟨rfl, rfl, rfl⟩
    · exact absurd hxe (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, hx, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ ⟨rfl, rfl, rfl⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih hxe
      obtain ⟨g₁, g₂, g₃⟩ := runRoundM_fields hx
      exact ⟨h₁.trans g₁, h₂.trans g₂, h₃.trans g₃⟩

theorem Inv.runSaturateM {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase}, d.Inv →
    Signature.MergesLegal d.sig → (∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig) →
    d.runSaturateM R n = some e → e.Inv := by
  intro n
  induction n with
  | zero =>
    intro d e h _ _ hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, -, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ h
    · exact absurd hxe (by simp)
  | succ n ih =>
    intro d e h hmerges hrules hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, hx, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ h
    · obtain ⟨g₁, -, g₃⟩ := runRoundM_fields hx
      exact ih (h.runRoundM hmerges hrules hx) (by rw [g₁]; exact hmerges)
        (fun r hr => by rw [g₁]; exact hrules r (g₃ ▸ hr)) hxe

/-- The signature after a command is the one `Cmd.sigBind` predicts: only `.decl` moves
it, and neither an action nor a merge phase does. -/
theorem execCmdM_sig {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    d'.sig = c.sigBind d.sig := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [(mergeSaturateF_fields h₂).1, execAction_sig h₁]
    rfl
  | rule r => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl
  | run R =>
    rw [FDatabase.execCmdM] at hs
    rw [(runRoundM_fields hs).1]
    rfl
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    rw [(runSaturateM_fields runFuel hs).1]
    rfl
  | decl f dc => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl

/-- **A legal run declares each name once, and freshly.**

`FDatabase.ProgramLegal` checks `Cmd.DeclUnused` at the state each command reaches, which
is a fact about the interpreter's database; `Program.DeclsFresh` is the same fact read off
the signature alone, which is the form `ProgramStep.mono_recorded` can carry across a
specification run. The two agree because `execCmdM` moves the signature exactly as
`Cmd.sigBind` predicts. -/
theorem ProgramLegal.declsFresh {p : Program} : ∀ {d d' : FDatabase},
    d.ProgramLegal p → d.execProgramM p = some d' → Program.DeclsFresh p d.sig := by
  induction p with
  | nil => intro _ _ _ _; trivial
  | cons c cs ih =>
    intro d d' hp hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, hd₁, hcs⟩ := Option.bind_eq_some_iff.mp hs
    refine ⟨?_, ?_⟩
    · cases c with
      | decl f dc => exact hp.2.1.1
      | action a => trivial
      | rule r => trivial
      | run R => trivial
      | saturate R => trivial
    · show Program.DeclsFresh cs (c.sigBind d.sig)
      rw [← execCmdM_sig hd₁]
      exact ih (hp.2.2.2 d₁ hd₁) hcs

/-- **`Inv` through one command.** `.action` and `.run` are the phase lemmas composed with
`Inv.mergeSaturateF`; `.rule` touches no field `Inv` reads; `.decl` is `Inv.decl`, and is
the only case with a side condition of its own. -/
theorem Inv.execCmdM {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hlegal : c.WriteLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hunused : c.DeclUnused d)
    (hrules : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') : d'.Inv := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine Inv.mergeSaturateF (h.execAction hlegal h₁) ?_ h₂
    rw [execAction_sig h₁]; exact hmerges
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ ⟨h.wf.setEnvRules (rs := r :: d.rules) h.wf.envInTerms, h.eqs,
      h.index.setEnvRules d.env (r :: d.rules)⟩
  | run R =>
    rw [FDatabase.execCmdM] at hs
    exact h.runRoundM hmerges hrules hs
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    exact Inv.runSaturateM runFuel h hmerges hrules hs
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ h.decl hunused.1 hunused.2

/-- Rule-head legality is preserved: `.rule` installs a head `Cmd.SetLegal` has already
checked, and `.decl` only ever declares a name no head can legally have `set`
(`Actions.SetLegal.update`). -/
theorem execCmdM_rulesLegal {d d' : FDatabase} {c : Cmd}
    (hlegal : c.WriteLegal d.sig) (hunused : c.DeclUnused d)
    (hrules : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') :
    ∀ r ∈ d'.rules, Actions.WriteLegal r.actions d'.sig := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [(mergeSaturateF_fields h₂).1, (mergeSaturateF_fields h₂).2.2,
      execAction_sig h₁, execAction_rules h₁]
    exact hrules
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr''
    · exact ⟨hlegal.1, hlegal.2⟩
    · exact hrules r' hr''
  | run R =>
    rw [FDatabase.execCmdM] at hs
    rw [(runRoundM_fields hs).1, (runRoundM_fields hs).2.2]
    exact hrules
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    rw [(runSaturateM_fields runFuel hs).1, (runSaturateM_fields runFuel hs).2.2]
    exact hrules
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    exact fun r hr => Actions.WriteLegal.update hunused.1 (hrules r hr)

/-! #### The three containment theorems -/

/-- `execCmdM_contained` with the three fields `Database.Contained` ignores. The extra
equalities are what `CmdStep.mono` consumes, so the program induction can start its tail
from the witness the head produced. -/
theorem execCmdM_contained' {d d' : FDatabase} (h : d.Inv) {c : Cmd} (hns : c.NoSaturate)
    (hlegal : c.WriteLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hcond : (d.toDatabase.NoUnions ∧ c.UnionFree) ∨
      (d.toDatabase.NoOrdering ∧ c.OrderingFree))
    (hs : d.execCmdM c = some d') :
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Recorded db ∧
      d'.toDatabase.sig = db.sig ∧ d'.toDatabase.env = db.env ∧
      d'.toDatabase.rules = db.rules := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, hd₁, hsat⟩ := Option.bind_eq_some_iff.mp hs
    have hmerges₁ : Signature.MergesLegal d₁.sig := by
      rw [execAction_sig hd₁]; exact hmerges
    have heval : evalAction d.toDatabase a = some d₁.toDatabase :=
      FDatabase.execAction_evalAction h.eqs hd₁
    obtain ⟨db, hcl, hcont⟩ :=
      mergeSaturateF_contained (h.execAction hlegal hd₁) hmerges₁ (by
        rcases hcond with ⟨hnu, hcu⟩ | ⟨hno, hcof⟩
        · exact Or.inl ⟨by rw [execAction_sig hd₁]; exact hnu.sig,
            evalAction_diag hcu hnu.diag heval⟩
        · exact Or.inr (by rw [execAction_sig hd₁]; exact hno.sig)) hsat
    refine ⟨db, ⟨d₁.toDatabase, heval, hcl⟩, hcont,
      ?_, ?_, ?_⟩
    · change d'.sig = db.sig
      rw [MergeClosure.sig hcl]; exact (mergeSaturateF_fields hsat).1
    · change d'.env = db.env
      rw [(MergeClosure.envRules hcl).1]; exact (mergeSaturateF_fields hsat).2.1
    · change ({r | r ∈ d'.rules} : Set Rule) = db.rules
      rw [(MergeClosure.envRules hcl).2, (mergeSaturateF_fields hsat).2.2]
      rfl
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    refine ⟨{ d.toDatabase with rules := insert r d.toDatabase.rules },
      ⟨_, rfl, Relation.ReflTransGen.refl⟩,
      ⟨fun p hp => ?_⟩, rfl, rfl, ?_⟩
    · obtain ⟨q, hq, hc₁, hc₂⟩ := (Database.Recorded.refl (db := d.toDatabase)).eqs p hp
      exact ⟨q, hq, congOn_setEnvRules hc₁, congOn_setEnvRules hc₂⟩
    change ({r' | r' ∈ r :: d.rules} : Set Rule) = insert r {r' | r' ∈ d.rules}
    ext r'
    simp
  | run R =>
    rw [FDatabase.execCmdM, FDatabase.runRoundM] at hs
    have hRcont : (execRunRules R d).toDatabase.Contained (RunRules R d.toDatabase) :=
      execRunRules_contained h
    have hmerges₁ : Signature.MergesLegal (execRunRules R d).sig := by
      rw [execRunRules_fields.1]; exact hmerges
    obtain ⟨db₂, hcl₂, hcont₂⟩ :=
      mergeSaturateF_contained (h.execRunRules hrules) hmerges₁ (by
        rcases hcond with ⟨hnu, -⟩ | ⟨hno, -⟩
        · exact Or.inl ⟨by rw [execRunRules_fields.1]; exact hnu.sig,
            Database.Diag.mono hRcont (RunRules.diag hnu)⟩
        · exact Or.inr (by rw [execRunRules_fields.1]; exact hno.sig)) hs
    obtain ⟨db₃, hcl₃, hcont₃, hsig₃⟩ :=
      MergeClosure.transport hRcont (by
        change (execRunRules R d).sig = (RunRules R d.toDatabase).sig
        simp only [RunRules, Database.sUnion_sig]
        exact execRunRules_fields.1) hcl₂
    refine ⟨db₃, ⟨RunRules R d.toDatabase, rfl, hcl₃⟩, hcont₂.trans_contained hcont₃,
      ?_, ?_, ?_⟩
    · change d'.sig = db₃.sig
      rw [MergeClosure.sig hcl₃, (mergeSaturateF_fields hs).1, execRunRules_fields.1]
      simp only [RunRules, Database.sUnion_sig]
      rfl
    · change d'.env = db₃.env
      rw [(MergeClosure.envRules hcl₃).1, (mergeSaturateF_fields hs).2.1,
        execRunRules_fields.2.1]
      simp only [RunRules, Database.sUnion_env]
      rfl
    · change ({r | r ∈ d'.rules} : Set Rule) = db₃.rules
      rw [(MergeClosure.envRules hcl₃).2, (mergeSaturateF_fields hs).2.2,
        execRunRules_fields.2.2]
      simp only [RunRules, Database.sUnion_rules]
      rfl
  | saturate R => exact (hns : False).elim
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    refine ⟨{ d.toDatabase with sig := Function.update d.toDatabase.sig f (some dc) },
      ⟨_, rfl, Relation.ReflTransGen.refl⟩, ⟨fun p hp => ?_⟩, rfl, rfl, rfl⟩
    -- The interpreter's own state is `Recorded` in it *syntactically*: no equation has
    -- moved, so the witness is the equation itself and the signature change is invisible
    -- to `Cong`.
    obtain ⟨q, hq, hc₁, hc₂⟩ := (Database.Recorded.refl (db := d.toDatabase)).eqs p hp
    exact ⟨q, hq, congOn_setSig hc₁, congOn_setSig hc₂⟩

/-- **The interpreter's answer to one command is contained in one the specification
reaches.**

`.action` is `execAction_evalAction` followed by `mergeSaturateF_contained`, which is
`CmdStep.action`'s two premises exactly — the specification's merge phase is what pays
for the interpreter's, and before every command carried one this theorem was **false**.
`.run` is `execRunRules_contained` re-based by `MergeClosure.transport`. `.rule` and
`.decl` land on the specification's state on the nose.

`hlegal` and `hrules` are `Inv.execAction`'s and `Inv.execActions`'s premises; `hmerges`
is what a merge body needs and `Program.SetLegal` does not supply; `hnu` and `hcu` are what
`MergeStep.transport_recorded` needs, since the merge phase is where the interpreter's
re-keying has to be matched at a *congruent* key. -/
theorem execCmdM_contained {d d' : FDatabase} (h : d.Inv) {c : Cmd} (hns : c.NoSaturate)
    (hlegal : c.WriteLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hcond : (d.toDatabase.NoUnions ∧ c.UnionFree) ∨
      (d.toDatabase.NoOrdering ∧ c.OrderingFree))
    (hs : d.execCmdM c = some d') :
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Recorded db := by
  obtain ⟨db, hstep, hcont, -, -, -⟩ :=
    execCmdM_contained' h hns hlegal hmerges hrules hcond hs
  exact ⟨db, hstep, hcont⟩

/-- `execProgramM_contained`, with the program first so the induction can generalize the
database.

`Database.NoUnions` carries itself: `CmdStep.noUnions` moves it onto the *specification*
witness `db₁`, and `Database.NoUnions.of_recorded` pushes it back down onto the
interpreter's `d₁`, which records into `db₁` and so has a subset of its equations. That is
why no union-freedom lemma about the interpreter is needed anywhere. -/
theorem execProgramM_contained_aux {p : Program} : ∀ {d d' : FDatabase}, d.Inv →
    p.NoSaturate → Signature.MergesLegal d.sig →
    (∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig) →
    ((d.toDatabase.NoUnions ∧ p.UnionFree) ∨ (d.toDatabase.NoOrdering ∧ p.OrderingFree)) →
    d.ProgramLegal p → d.execProgramM p = some d' →
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Recorded db := by
  induction p with
  | nil =>
    intro d d' hinv _ _ _ _ _ hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact ⟨d.toDatabase, .nil, hs ▸ Database.Recorded.refl⟩
  | cons c cs ih =>
    intro d d' h hns hmerges hrules hcond hp hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, hd₁, hcs⟩ := Option.bind_eq_some_iff.mp hs
    rw [FDatabase.ProgramLegal] at hp
    obtain ⟨hlegal, hunused, hmerges', hnext⟩ := hp
    have hnsc : c.NoSaturate := hns c List.mem_cons_self
    have hnscs : Program.NoSaturate cs := fun c' hc' => hns c' (List.mem_cons_of_mem c hc')
    obtain ⟨db₁, hstep₁, hcont₁, hsig₁, henv₁, hrules₁⟩ :=
      execCmdM_contained' h hnsc hlegal hmerges hrules
        (hcond.imp (fun hu => ⟨hu.1, hu.2.1⟩) fun ho => ⟨ho.1, ho.2.1⟩) hd₁
    have hinv₁ : d₁.Inv := h.execCmdM hlegal hmerges hunused hrules hd₁
    -- the condition at the interpreter's next state, and at the specification's witness
    have hnext₁ : ((d₁.toDatabase.NoUnions ∧ Program.UnionFree cs) ∨
        (d₁.toDatabase.NoOrdering ∧ Program.OrderingFree cs)) ∧
        (db₁.Diag ∨ (db₁.NoOrdering ∧ Program.OrderingFree cs)) := by
      rcases hcond with ⟨hnu, hcu⟩ | ⟨hno, hcof⟩
      · have hnu₁ := CmdStep.noUnions hnu hcu.1 hstep₁
        exact ⟨Or.inl ⟨hnu₁.of_recorded hcont₁ hsig₁ hrules₁, hcu.2⟩, Or.inl hnu₁.diag⟩
      · have hno₁ := CmdStep.noOrdering hno hcof.1 hstep₁
        exact ⟨Or.inr ⟨hno₁.of_eq hsig₁ hrules₁, hcof.2⟩, Or.inr ⟨hno₁, hcof.2⟩⟩
    obtain ⟨db₂, hstep₂, hcont₂⟩ :=
      ih hinv₁ hnscs (by rw [execCmdM_sig hd₁]; exact hmerges')
        (execCmdM_rulesLegal hlegal hunused hrules hd₁) hnext₁.1 (hnext d₁ hd₁) hcs
    obtain ⟨db₃, hstep₃, hcont₃, hsig₃, -, -⟩ :=
      ProgramStep.mono_recorded hcont₁ hinv₁.wf (CmdStep.wf h.wf hstep₁) hsig₁ henv₁ hrules₁
        hnscs hnext₁.2 hstep₂
    exact ⟨db₃, .cons hstep₁ hstep₃, hcont₂.trans hcont₃ (hstep₂.wf hinv₁.wf)
      (hstep₃.wf (CmdStep.wf h.wf hstep₁))⟩

/-- **The interpreter's answer to a whole program is contained in one the specification
reaches.**

`execCmdM_contained'` per command, with `ProgramStep.mono_recorded` re-basing the tail's
witness onto the head's — which is where `ValidSubst.mono` is spent, read forwards: a
larger specification state still admits every match, so the specification can follow along.

`hp` is the per-command bundle. It is what carries the induction across a `.decl`:
`FDatabase.Inv` is not preserved by an arbitrary declaration (`FDatabase.Inv.decl`), and
`FDatabase.Unused` is the weakest thing that restores it — the declaration names
something the state does not yet mention, which is what egglog's front end requires
anyway. It does not restrict which `:merge` functions a program may declare, so the
merge fragment is not excluded.

`hcond` is the side condition, in either of its two arms; see the sections
"Union-freedom, and where it puts `Recorded`" and "Ordering-freedom, and where it puts
`Recorded`". It *does* restrict which programs are covered, and it is the price of the
re-keying contract: without it the two `Recorded` transports the induction runs on are
false.

`hns` is what `Cmd.saturate` costs here; `execM_contained` says what a version without it
would need. -/
theorem execProgramM_contained {d d' : FDatabase} (h : d.Inv) {p : Program}
    (hns : p.NoSaturate) (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hcond : (d.toDatabase.NoUnions ∧ p.UnionFree) ∨
      (d.toDatabase.NoOrdering ∧ p.OrderingFree))
    (hp : d.ProgramLegal p) (hs : d.execProgramM p = some d') :
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Recorded db :=
  execProgramM_contained_aux h hns hmerges hrules hcond hp hs

end FDatabase

/-- **The contract for `execM`.** `execProgramM_contained` from `FDatabase.empty`, whose
three global side conditions discharge themselves: the empty signature declares no merge
body, the empty state has no rules, and it asserts no equation. `hp` and `hcond` are what
remain, and `FDatabase.ProgramLegal` is stated so that a front end which declares before use
and type-checks its merge bodies satisfies it.

`hcond` — **the program is union-free, or ordering-free** — is the legality condition the
two `Recorded` transports need, and it is not removable: both are false without it,
`MergeStep.transport_recorded` refutably so. The two arms buy it differently.

*Union-free* — the program emits no `Action.union`, in a command, a rule head or a `:merge`
body. Then every state it reaches is diagonal, and there `Database.Recorded` and
`Database.Contained` agree, so the proved `Contained` transports serve. It does not exclude
`Encoding/Encode.lean`: `encodeAction` turns a source `union` into a `set` of a `@UF` edge,
and no `encode` output — prelude, maintenance rule, merge body or encoded head — contains
an `Action.union`.

*Ordering-free* — no expression the program evaluates applies `ordering-min` or
`ordering-max`, in a rule's query or head, in a command, or in a `:merge` body or result.
Then evaluation is congruence-stable (`eval_owes`), so a run under the congruent
environment a `Recorded` witness supplies produces a congruent result, which is what
recording asks for. This arm restricts **no** `union`: `(union (add a b) (add b a))` and
every other equational program is covered, as is every `:merge` body built from `min`/`max`
— those two are stable, since `Database.WF.litsIsolated` makes a literal's class a
singleton. What it excludes is `Encoding/Encode.lean`, whose `encodeAction` emits
`ordering-max`; that encoding is what the first arm is for.

See the section header above for why the contract is `Database.Recorded` rather than the
equality `exec_programStep` enjoys, and `Spec/Merge.lean` for why it is that rather than
`Database.Contained`.

**`hns` — the program runs no `Cmd.saturate`** — is the one restriction this branch adds,
and unlike `hcond` it is not known to be necessary; it is what the present proof needs.
The obstacle is exact. `execCmdM`'s `.saturate` case would have to produce a
`SaturateReach R d.toDatabase db` witness out of `runSaturateM` returning an answer, and
`runSaturateM` returning an answer says only that the *interpreter's* round added nothing.
`execRunRules_contained` is a containment, not an equality — the enumerator under-fires,
because `valueTerms` is stricter than `Spec/Match.lean`'s `ValidEnv` — so an interpreter
fixpoint need not be a specification fixpoint, and `RunSaturated`'s first conjunct is
exactly a specification fixpoint. On the constructor fragment there is no gap
(`execRunRules_RunRules` is an equality, which is how `Proofs/Interp.lean`'s
`runSaturateF_saturateReach` goes through), but encoded programs are not in that fragment:
`@UF` and every `@fView` are `.merge` functions. Closing it needs either an enumerator that
is complete for `ValidEnv` on merge functions, or a `SaturateReach` weakened to the
substitutions the interpreter can see — a change to `Spec/`, not to this proof. -/
theorem execM_contained {p : Program} (hns : p.NoSaturate)
    (hp : FDatabase.empty.ProgramLegal p)
    (hcond : p.UnionFree ∨ p.OrderingFree) {d : FDatabase} (h : execM p = some d) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ d.toDatabase.Recorded db :=
  FDatabase.execProgramM_contained FDatabase.Inv.empty hns
    (fun g dc body res hg _ => absurd hg (by simp [FDatabase.empty]))
    (fun r hr => absurd hr (by simp [FDatabase.empty]))
    (hcond.imp
      (fun hu => ⟨⟨by simp [FDatabase.toDatabase_empty, Database.Diag, Database.empty],
        by simp [FDatabase.toDatabase_empty, Database.empty, Signature.UnionFree],
        by simp [FDatabase.toDatabase_empty, Database.empty]⟩, hu⟩)
      fun ho => ⟨⟨by simp [FDatabase.toDatabase_empty, Database.empty,
        Signature.OrderingFree], by simp [FDatabase.toDatabase_empty, Database.empty]⟩, ho⟩)
    hp h

end Egglog
