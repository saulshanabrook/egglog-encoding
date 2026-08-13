import EgglogSemantics.Impl.Check
import EgglogSemantics.Proofs.Merge

/-!
# Machine-checked falsity witnesses

Every hypothesis the refinement chain carries costs something, and the way to show one is
not decoration is to exhibit a state or a program where dropping it makes the statement
false. This file is those witnesses. Nothing here is admitted, nothing uses `native_decide`,
and no `Classical.choice` enters beyond what `Mathlib` already pulls in.

What each section refutes:

* `claim1` — there is no unconditional `FDatabase.Inv.decl`, so `FDatabase.Unused` is what
  that lemma and `FDatabase.ProgramLegal` have to carry.
* `actTuple_*` — `Action.SetLegal` bounds a write's *head*, not its width;
  `Action.WidthOk` and `Impl/Check.lean`'s `arityOk` are what bound the width.
* `mergeRound_inv_false` — `FDatabase.Inv.mergeRound_of_legalMerges` needs
  `Signature.MergesLegal`; a merge body is an arbitrary action block and `Program.SetLegal`
  says nothing about one.
* `patternHolds_validSubst_false`, `matchQuery_validQuerySubst_false` — the two matching
  statements are false without the `ValidEnv` hypothesis and the `Env.Agree` conclusion
  they now carry.
* `exec_programStep_needs_ctorDecls` — **the one `exec_programStep` and `execM_reachable`
  cite.** With a `:merge` declared, the merge phase after an action gives the specification
  two reachable states where the interpreter returns one.
* `setCtor_not_declaredTerms` — `Program.SetLegal` is not implied by `Program.CtorDecls`
  and `Program.WidthOk`, and it is what keeps `Database.DeclaredTerms`.
* `staleProgram_*` — `Program.Evaluable` is what rejects a rule head naming an undeclared
  function, and the row that head used to write is no longer reachable.
* `decl_enables_merge` — `Spec/Scope.lean`'s `MergeDeclared` is what makes the merge phase
  after a `.decl` neutral; without it a declaration *enables* a merge step.

Three guards against the opposite failure — a witness that compiles while saying nothing —
are `not_matches_empty`, `recorded_empty` and `not_mergeStep_empty` at the end: `Cong` has
no `refl` rule, so the definitions that read "there is a witness term the database already
holds" are checked against a database that holds none.

Every witness that asks the *kernel* to compute a merge pass keeps its `:merge` function
**nullary**. That is not cosmetic: a nullary key makes `congrKeys cl [] []` reduce to `true`
through `List.all []` without ever forcing `cl`, and `cl` is `closureF`, whose well-founded
recursion the kernel cannot unfold.
-/

namespace Egglog
namespace Falsity

/-! ## Shared vocabulary -/

/-- `(function f () i64 :merge 7)`: a nullary `:merge` function with an empty merge body
whose merged value is the constant `7`. -/
def fDecl : FnDecl :=
  { arity := 0, outArity := 1, merge := some (.merge [] [.lit (.int 7)]) }

/-- `(datatype S (c))`, at `n` argument columns. Declaration is required, so every witness
below that *builds* a term has to declare its constructor first. -/
def ctorDecl (n : Nat) : FnDecl := { arity := n, outArity := 1, merge := none }

/-! ## Claim 1 — a redeclaration destroys `FDatabase.Inv`

`FDatabase.IndexOk` reads the *declaration* to say what shape a row of `f` may have — `ctor`
and `entry` split on `d.sig.mergeOf r.fn`, and `width` reads `arity` and `outArity` off the
entry — while `execCmdM (.decl f dc)` rewrites `sig` and leaves every row where it is. So a
database already holding `g`'s constructor row stops satisfying `Inv` the moment `g` is
*re*declared `:merge`.

The field that breaks is **`IndexOk.width`**: a constructor's row has no value column and
`fDecl` declares one. `ctor` goes vacuous and `entry` survives — `Database.Out` finds `g()`
at its own key — so `width` is the sharp field rather than an incidental one. -/

/-- `(constructor g) (g)`: `g` declared a constructor, and its entry recorded. Built through
the interpreter's own writers, so its `Inv` is the library's rather than hand-rolled. -/
def dG : FDatabase :=
  ({ FDatabase.empty with
      sig := Function.update FDatabase.empty.sig "g" (some (ctorDecl 0)) } :
    FDatabase).addTerm (.app "g" [])

/-- `dG` after `(function g () i64 :merge 7)`. -/
def dG' : FDatabase := { dG with sig := Function.update dG.sig "g" (some fDecl) }

theorem dG_inv : dG.Inv :=
  (FDatabase.Inv.empty.decl (dc := ctorDecl 0) (by simp [FDatabase.empty])
    (by simp [FDatabase.empty])).addTerm _

/-- `g`'s constructor row: no value column, which is what `fDecl` then contradicts. -/
theorem dG_row : (⟨"g", [], []⟩ : Row) ∈ dG.rows := by decide

theorem dG'_row : (⟨"g", [], []⟩ : Row) ∈ dG'.rows := dG_row

/-- `mergeOf` at `g` really has changed. -/
theorem dG'_mergeOf : dG'.sig.mergeOf "g" = some (MergeSpec.merge [] [.lit (.int 7)]) := rfl

/-- **Claim 1, CONFIRMED.** `Cmd.decl` takes a database satisfying `FDatabase.Inv` to one
that does not.

Precisely what this does and does not show. It shows there is no **unconditional**
`FDatabase.Inv.decl`, so `execProgramM_contained`'s induction — which carries `Inv` and must
re-establish it after every command — cannot get past a `.decl` for free. It does **not** by
itself refute `execCmdM_contained` at the `.decl` case: that case's conclusion is a
containment, and `CmdStep`'s effect at a `.decl` reaches exactly the interpreter's state.

This is what forces `FDatabase.Unused` — the hypothesis `FDatabase.Inv.decl` and hence
`FDatabase.ProgramLegal` carry: a declaration names something the state does not yet
mention. `g` here is *declared and used*, and then redeclared `:merge`, which is the one
shape that hypothesis excludes and the one shape egglog's own "declare before use"
excludes too. -/
theorem claim1 : ∃ (d : FDatabase) (f : FnName) (dc : FnDecl) (d' : FDatabase),
    d.Inv ∧ d.execCmdM (.decl f dc) = some d' ∧ ¬ d'.Inv :=
  ⟨dG, "g", fDecl, dG', dG_inv, rfl, fun h => by
    have hw := (h.index.width ⟨"g", [], []⟩ dG'_row fDecl rfl
      (by rw [dG'_mergeOf]; simp)).2
    simp [fDecl] at hw⟩

/-! ## `SetLegal` does not bound a write's width

`Action.SetLegal` constrains only a function's merge kind, so it admits a `set` whose value
list is the wrong width for the declaration. `FnDecl.outArity` is what records the width;
`Spec/Scope.lean`'s `Action.WidthOk` and `Impl/Check.lean`'s `arityOk` are what read it.
The two say the same thing on a `set`, and both are exhibited: the spec-side check and the
front-end one reject the write, and `SetLegal` does not. -/

/-- `(function h () i64 :merge 9)`. -/
def hDecl : FnDecl :=
  { arity := 0, outArity := 1, merge := some (.merge [] [.lit (.int 9)]) }

def sigH : Signature := Function.update (fun _ => none) "h" (some hDecl)

/-- `(set (h) (values 1 2))` — a two-column write to a one-column function. -/
def actTuple : Action := .set "h" [] [.lit (.int 1), .lit (.int 2)]

/-- `SetLegal`, the only condition a `set` carried before the width checks, holds of it. -/
theorem actTuple_legal : actTuple.SetLegal sigH := by
  change Signature.mergeOf sigH "h" ≠ none
  rw [show sigH.mergeOf "h" = some (.merge [] [.lit (.int 9)]) from rfl]
  simp

/-- The spec-side check that rejects it. -/
theorem actTuple_not_widthOk : ¬ actTuple.WidthOk sigH := by
  intro h
  have := (h.1 hDecl rfl).2
  simp [hDecl] at this

/-- The two-column write egglog's typechecker rejects: "Arity mismatch, expected 1 args". -/
theorem actTuple_not_arityOk : actTuple.arityOk sigH = false := rfl

/-- …and the whole program with it, so no state the model accepts holds entries of two
widths at one key. -/
theorem claim3Program_not_arityOk :
    Program.arityOk [.decl "h" hDecl, .action actTuple,
      .action (.expr (.app "h" []))] (fun _ => none) = false := rfl

/-! ## `mergeRound` needs `Signature.MergesLegal`

A merge body is an arbitrary `List Action` carrying no `Action.SetLegal` obligation —
`Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about one — and
`FDatabase.IndexOk` is where that bites. `Signature.MergesLegal` is the repair, and
`FDatabase.Inv.mergeRound_of_legalMerges` is what spends it. This is the witness that it
cannot be dropped.

The field that breaks is **`IndexOk.ctor`**, and the value column is what breaks it: a
body's `(set (F) 3)` on a name with no `:merge` writes a row whose `out` is `[3]`, where
`ctor` requires `[]`. A body writing `(set (F))` would be harmless — `addRow` records the
entry term, which is all `ctor` then asks for. -/

/-- `(function f () i64 :merge ((set (F) 3)) old)`. `F` is declared nowhere, so its row is
read by `IndexOk.ctor` — the clause that requires no value column. -/
def cexDecl : FnDecl := ⟨0, 1, some (.merge [.set "F" [] [.lit (.int 3)]] [.var "old"])⟩

/-- After `(function f () i64 :merge …)`. -/
def cexSig : FDatabase :=
  { FDatabase.empty with
    sig := Function.update FDatabase.empty.sig "f" (some cexDecl) }

/-- Two entries of `f` at the empty key, recording `1` and `2`. Built through the
interpreter's own writers, so its `Inv` is `FDatabase.Inv.addRow`'s rather than
hand-rolled — the counterexample is a state the interpreter actually reaches. -/
def cexD : FDatabase :=
  (cexSig.addRow "f" [] [.lit (.int 1)]).addRow "f" [] [.lit (.int 2)]

theorem cexSig_inv : cexSig.Inv :=
  FDatabase.Inv.empty.decl (dc := cexDecl) (by simp [FDatabase.empty])
    (by simp [FDatabase.empty])

theorem cexD_inv : cexD.Inv :=
  (cexSig_inv.addRow (by rw [show cexSig.sig.mergeOf "f" = some _ from rfl]; simp)
      (fun dc hdc => by obtain rfl : cexDecl = dc := Option.some.inj hdc; exact ⟨rfl, rfl⟩)).addRow
    (by rw [show (cexSig.addRow "f" [] [Term.lit (.int 1)]).sig.mergeOf "f" = some _ from rfl]
        simp)
    (fun dc hdc => by obtain rfl : cexDecl = dc := Option.some.inj hdc; exact ⟨rfl, rfl⟩)

/-- The row the merge body plants: a value column on a name with no `:merge`. -/
theorem cexD_mergeRound_badRow :
    (⟨"F", [], [.lit (.int 3)]⟩ : Row) ∈ cexD.mergeRound.rows := by decide

/-- **The hypothesis is what makes the state legal.** `f`'s body `set`s `F`, which has no
`:merge`, so `Actions.WriteLegal` fails on it. -/
theorem cexSig_not_mergesLegal : ¬ Signature.MergesLegal cexSig.sig := fun h =>
  (h "f" cexDecl [.set "F" [] [.lit (.int 3)]] [.var "old"] rfl rfl).1.1.1 rfl

/-- **`FDatabase.Inv.mergeRound_of_legalMerges` without `Signature.MergesLegal` is false.**
A merge pass takes a database satisfying `Inv` to one that does not. -/
theorem mergeRound_inv_false : ∃ d : FDatabase, d.Inv ∧ ¬ d.mergeRound.Inv := by
  refine ⟨cexD, cexD_inv, fun h => ?_⟩
  have hsig : cexD.mergeRound.sig = cexD.sig := FDatabase.mergeRound_confined.2.2.1
  have hm : cexD.mergeRound.sig.mergeOf "F" = none := by rw [hsig]; rfl
  exact absurd (h.index.ctor _ cexD_mergeRound_badRow hm).1 (by simp)

/-! ## The two matching statements

`FDatabase.patternHolds_validSubst` and `FDatabase.matchQuery_validQuerySubst` are false
without the hypotheses they now carry, for two **independent** reasons: the first needs
`ValidEnv`, and the second's `σ` *is* a valid env at both its patterns. Both witnesses live
in a one-term database — `FDatabase.empty` plus the literal `0`. -/

/-- The only term of the counterexample database. -/
def t0 : Term := .lit (.int 0)

/-- `FDatabase.empty` holding just `t0`. -/
def dEx : FDatabase := FDatabase.empty.addTerm t0

theorem dEx_inv : dEx.Inv := FDatabase.Inv.empty.addTerm t0

theorem t0_mem : t0 ∈ dEx.terms := by
  simp [dEx, FDatabase.addTerm, t0, List.mem_dedup]

/-- `t0` is its own witness. There is no `Cong.refl`, so this is the *asserted* reflexive
equation `addTerm` wrote, read back. -/
theorem t0_cong : (t0, t0) ∈ (dEx.addTerm t0).closureF :=
  (FDatabase.mem_closureF_addTerm dEx_inv.eqs).mpr (Database.mem_addTerm t0 dEx.toDatabase)

/-- The pattern `0` matches under a substitution binding `x`, which the pattern does not
mention: `patternHolds` reads `σ` only through `d.env ++ σ`. -/
theorem holds_lit : patternHolds dEx (.expr (.lit (.int 0))) [("x", t0)] = true := by
  simp only [patternHolds, Expr.eval, decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

/-- **`FDatabase.patternHolds_validSubst` is false without `ValidEnv`.**
`ValidSubst` carries `ValidEnv (p.freeVars db.env) db σ`, which pins `Env.dom σ` to
a permutation of the pattern's free variables; `(Expr.lit _).freeVars` is `[]` and `σ`
binds `x`. -/
theorem patternHolds_validSubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (p : Pattern) (σ : Env),
        patternHolds d p σ = true → ValidSubst d.toDatabase p σ := by
  intro H
  have hbad := H dEx dEx_inv (.expr (.lit (.int 0))) [("x", t0)] holds_lit
  simpa [Env.dom, Pattern.freeVars, Expr.freeVars] using hbad.1.1

/-- Two patterns sharing the variable `x`. `Query.freeVars qEx dEx.env = ["x"]`: the
`∪` in `Query.freeVars` deduplicates, so the enumerator assigns `x` once. -/
def qEx : Query := [Pattern.expr (.var "x"), Pattern.expr (.var "x")]

theorem holds_var : patternHolds dEx (.expr (.var "x")) [("x", t0)] = true := by
  change decide (∃ w ∈ dEx.terms, (w, t0) ∈ (dEx.addTerm t0).closureF) = true
  rw [decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

theorem mem_matchQuery_ex : [("x", t0)] ∈ matchQuery dEx qEx := by
  rw [matchQuery, List.mem_filter]
  constructor
  · refine mem_assignments.mpr ⟨rfl, ?_⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    simp [FDatabase.valueTerms, dEx, FDatabase.addTerm, t0, List.mem_dedup]
  · change (patternHolds dEx (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) &&
      (patternHolds dEx (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) && true)) = true
    rw [show Env.canon ["x"] [("x", t0)] = [("x", t0)] from rfl, holds_var]
    rfl

/-- `Env.UnionAll` is concatenation: `Union2` fixes `σr = σ₁ ++ σ₂` and the fold ends at
`UnionAll [σ] σ`, so lengths add. This is what the enumerator cannot satisfy. -/
theorem unionAll_sum_length {σs : List Env} {σ : Env} (h : Env.UnionAll σs σ) :
    (σs.map List.length).sum = σ.length := by
  induction h with
  | nil => simp
  | single σ => simp
  | step hu _ ih =>
    obtain ⟨-, rfl⟩ := hu
    simp only [List.map_cons, List.sum_cons, List.length_append] at ih ⊢
    omega

/-- **`FDatabase.matchQuery_validQuerySubst` is false without `Env.Agree`.**
`[("x", t0)]` is enumerated for `qEx`, and `ValidEnv` holds for it at *both* patterns — so
this is not the `ValidEnv` defect again. `ValidQuerySubst` needs one substitution per
pattern, each of length `1`, concatenated to give `σ`; that would make `σ` have length
`2`. -/
theorem matchQuery_validQuerySubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (q : Query) (σ : Env),
        σ ∈ matchQuery d q → ValidQuerySubst d.toDatabase q σ := by
  intro H
  obtain ⟨σs, hall, hu⟩ := H dEx dEx_inv qEx [("x", t0)] mem_matchQuery_ex
  have hlen : ∀ ρ, ValidSubst dEx.toDatabase (.expr (.var "x")) ρ → ρ.length = 1 := by
    intro ρ hρ
    have := hρ.1.1.length_eq
    simpa [Env.dom, Pattern.freeVars, Expr.freeVars, show dEx.env = [] from rfl, Env.lookup]
      using this
  cases hall with
  | cons h1 hrest =>
    cases hrest with
    | cons h2 hnil =>
      cases hnil with
      | nil =>
        have := unionAll_sum_length hu
        simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
          hlen _ h1, hlen _ h2] at this
        simp at this

/-! ## `exec_programStep` needs `Program.CtorDecls`

`exec` has no merge phase and `CmdStep` has one after every command, so wherever a merge can
fire the specification reaches states the interpreter does not — and the `←` direction of
`exec_programStep`, which is what makes the refinement an equality rather than a soundness
claim, fails.

`(function f () i64 :merge 7) (set (f) 0)` is the smallest program where it can. There is
no `a ≠ b` guard on `MergeStep.collide`, so the single entry `f(0)` collides with *itself*
and `f`'s body writes `7` at the same key; the merge closure after the action may take that
step or not, and the two results differ. Every other check the front end runs holds of the
program — `mergeDeclProgram_checks` — so `Program.CtorDecls` is isolated as the one thing
that fails. -/

/-- `(function f () i64 :merge 7) (set (f) 0)`. -/
def mergeDeclProgram : Program :=
  [ .decl "f" fDecl, .action (.set "f" [] [.lit (.int 0)]) ]

/-- After the declaration. -/
def mergeSig : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "f" (some fDecl) }

/-- After `(set (f) 0)`: the entry term `f(0)`, and the state the interpreter stops at. -/
def mergeSetDb : Database := mergeSig.addTerm (.app "f" [.lit (.int 0)])

/-- The other state the merge phase allows: the entry collides with itself and `f`'s body
writes `7` at the same key. -/
def mergeCollideDb : Database :=
  { (({ mergeSetDb with env := mergeEnv [.lit (.int 0)] [.lit (.int 0)] } :
        Database).addTerm (.app "f" [.lit (.int 7)])) with
    env := mergeSetDb.env, rules := mergeSetDb.rules }

theorem mergeDecl_eval :
    evalAction mergeSig (.set "f" [] [.lit (.int 0)]) = some mergeSetDb := rfl

theorem mergeSetDb_mem : Term.app "f" [Term.lit (.int 0)] ∈ mergeSetDb.terms :=
  Database.mem_addTerm _ _

/-- The self-collision. `CongList` is reflexive on the empty key, and the body is empty,
so every premise is `rfl` or `.nil`. -/
theorem mergeDecl_mergeStep : MergeStep mergeSetDb mergeCollideDb :=
  MergeStep.collide (f := "f") (decl := fDecl) (as := []) (bs := []) (a := [.lit (.int 0)])
    (b := [.lit (.int 0)]) (vs := [.lit (.int 7)]) (body := []) (res := [.lit (.int 7)])
    rfl rfl rfl rfl mergeSetDb_mem mergeSetDb_mem .nil rfl rfl

/-- **Both states are reachable.** The merge phase after the action is a `MergeClosure`,
which may be reflexive or take the one step. -/
theorem mergeDecl_reaches_set : ProgramStep Database.empty mergeDeclProgram mergeSetDb :=
  .cons ⟨mergeSig, rfl, .refl⟩ (.cons ⟨mergeSetDb, mergeDecl_eval, .refl⟩ .nil)

@[inherit_doc mergeDecl_reaches_set]
theorem mergeDecl_reaches_collide :
    ProgramStep Database.empty mergeDeclProgram mergeCollideDb :=
  .cons ⟨mergeSig, rfl, .refl⟩
    (.cons ⟨mergeSetDb, mergeDecl_eval, .single mergeDecl_mergeStep⟩ .nil)

theorem mergeCollideDb_mem : Term.app "f" [Term.lit (.int 7)] ∈ mergeCollideDb.terms :=
  Cong.assert (Or.inr ⟨_, Term.IsSubterm.refl _, rfl⟩)

/-- …and they are different: only the merged one holds the term recording `7`. -/
theorem mergeDecl_ne : mergeSetDb ≠ mergeCollideDb := by
  intro h
  have hmem : Term.app "f" [Term.lit (.int 7)] ∈ mergeSetDb.terms := by
    rw [h]; exact mergeCollideDb_mem
  rw [show mergeSetDb = mergeSig.addTerm (.app "f" [.lit (.int 0)]) from rfl,
    Database.addTerm_terms] at hmem
  rcases hmem with hmem | hmem
  · simp [mergeSig, Database.mem_terms_iff, Database.empty] at hmem
  · simp at hmem

/-- **The program passes every other check the front end runs.** Scope, evaluability, `set`
legality, column widths, declaration freshness, `:merge` declaredness, and
`Impl/Check.lean`'s two `Bool` checks. -/
theorem mergeDeclProgram_checks :
    WellScoped mergeDeclProgram ∧
      mergeDeclProgram.Evaluable Database.empty.sig ∧
      mergeDeclProgram.SetLegal Database.empty.sig ∧
      mergeDeclProgram.WidthOk Database.empty.sig ∧
      mergeDeclProgram.DeclsFresh Database.empty.sig ∧
      mergeDeclProgram.MergeDeclared Database.empty.sig ∧
      WellArity mergeDeclProgram ∧ ReadsAreAtoms mergeDeclProgram := by
  refine ⟨⟨trivial, ⟨by simp [Expr.Scoped], by simp [Expr.Scoped, Expr.vars]⟩, trivial⟩,
    ⟨trivial, ⟨by simp [Expr.Evaluable], by simp [Expr.Evaluable, Expr.fns]⟩, trivial⟩,
    ⟨trivial, ?_, trivial⟩,
    ⟨?_, ?_, trivial⟩, ⟨rfl, trivial, trivial⟩, ⟨?_, trivial, trivial⟩, rfl, rfl⟩
  · change Signature.mergeOf (Function.update Database.empty.sig "f" (some fDecl)) "f" ≠ none
    rw [show Signature.mergeOf (Function.update Database.empty.sig "f" (some fDecl)) "f"
      = some (.merge [] [.lit (.int 7)]) from rfl]
    simp
  · intro ms hms
    rw [show fDecl.merge = some (MergeSpec.merge [] [.lit (.int 7)]) from rfl,
      Option.mem_def, Option.some.injEq] at hms
    subst hms
    exact ⟨rfl, trivial, ⟨trivial, trivial⟩⟩
  · refine ⟨fun dc hdc => ?_, trivial, ⟨trivial, trivial⟩⟩
    obtain rfl : fDecl = dc := Option.some.inj hdc
    exact ⟨rfl, rfl⟩
  · intro ms hms
    rw [show fDecl.merge = some (MergeSpec.merge [] [.lit (.int 7)]) from rfl,
      Option.mem_def, Option.some.injEq] at hms
    subst hms
    exact ⟨trivial, by simp [Expr.Declared, Expr.fns]⟩

/-- The one check that rejects it. -/
theorem mergeDeclProgram_not_ctorDecls : ¬ mergeDeclProgram.CtorDecls := by
  intro h
  exact absurd (h (.decl "f" fDecl) (by simp [mergeDeclProgram]))
    (by simp [Cmd.CtorDecl, fDecl])

/-- **`exec_programStep` without `Program.CtorDecls` is false.** The interpreter returns
at most one database, and the specification reaches two. -/
theorem exec_programStep_needs_ctorDecls :
    ¬ ∀ (p : Program) (D : Database),
      Option.map FDatabase.toDatabase (exec p) = some D ↔ ProgramStep Database.empty p D := by
  intro h
  exact mergeDecl_ne (Option.some.inj
    (((h mergeDeclProgram mergeSetDb).mpr mergeDecl_reaches_set).symm.trans
      ((h mergeDeclProgram mergeCollideDb).mpr mergeDecl_reaches_collide)))

/-! ## `Program.SetLegal` is what keeps `Database.DeclaredTerms`

A `set` on a *constructor* writes an entry term of the wrong width: a constructor's
`FnDecl.entryWidth` is its `arity` alone, and a `set` appends the value columns anyway. The
program below declares nothing but constructors and passes `Program.WidthOk` — the width
check reads the `set`'s own column counts, which agree with the declaration — so neither
`Program.CtorDecls` nor `Program.WidthOk` catches it. `Program.SetLegal` does.

**Not a functional-dependency witness.** `¬ Cong setCtorDb (c) (d)` holds and says nothing:
every equation this state asserts is reflexive, and on such a state `Cong` *is* equality, so
the claim reduces to `(c) ≠ (d)`. It is not stated here for that reason. -/

/-- `(datatype S (c) (d) (f)) (set (f) (c)) (set (f) (d))`. Declares only constructors,
and its two `set`s are the one thing `Program.SetLegal` forbids. -/
def setCtorProgram : Program :=
  [ .decl "c" (ctorDecl 0), .decl "d" (ctorDecl 0), .decl "f" (ctorDecl 0),
    .action (.set "f" [] [.app "c" []]), .action (.set "f" [] [.app "d" []]) ]

def cTerm : Term := .app "c" []
def dTerm : Term := .app "d" []

def setCtorSig₁ : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "c" (some (ctorDecl 0)) }
def setCtorSig₂ : Database :=
  { setCtorSig₁ with sig := Function.update setCtorSig₁.sig "d" (some (ctorDecl 0)) }
def setCtorSig : Database :=
  { setCtorSig₂ with sig := Function.update setCtorSig₂.sig "f" (some (ctorDecl 0)) }

/-- After `(set (f) (c))`. -/
def setCtorDb₁ : Database := setCtorSig.addTerm (.app "f" [cTerm])

/-- After `(set (f) (d))`: two entry terms of the nullary constructor `f`, each one child
wide where the declaration allows none. -/
def setCtorDb : Database := setCtorDb₁.addTerm (.app "f" [dTerm])

theorem setCtor_eval₁ :
    evalAction setCtorSig (.set "f" [] [.app "c" []]) = some setCtorDb₁ := rfl

theorem setCtor_eval₂ :
    evalAction setCtorDb₁ (.set "f" [] [.app "d" []]) = some setCtorDb := rfl

/-- **The state is reachable.** No merge phase does anything — every declaration is a
constructor — so each command is its own step. -/
theorem setCtor_programStep : ProgramStep Database.empty setCtorProgram setCtorDb :=
  .cons ⟨setCtorSig₁, rfl, .refl⟩ (.cons ⟨setCtorSig₂, rfl, .refl⟩
    (.cons ⟨setCtorSig, rfl, .refl⟩
      (.cons ⟨setCtorDb₁, setCtor_eval₁, .refl⟩
        (.cons ⟨setCtorDb, setCtor_eval₂, .refl⟩ .nil))))

theorem setCtor_mem : Term.app "f" [cTerm] ∈ setCtorDb.terms := by
  rw [show setCtorDb = setCtorDb₁.addTerm (.app "f" [dTerm]) from rfl,
    Database.addTerm_terms]
  exact Or.inl (Database.mem_addTerm _ _)

/-- **`Database.DeclaredTerms` fails at a state the program reaches.** `f` is declared with
no argument column, and the `set` wrote an entry term with one. -/
theorem setCtor_not_declaredTerms : ¬ setCtorDb.DeclaredTerms := by
  intro h
  obtain ⟨dc, hdc, hlen⟩ := h "f" [cTerm] setCtor_mem
  rw [show setCtorDb.sig = setCtorSig.sig from rfl,
    show setCtorSig.sig "f" = some (ctorDecl 0) from rfl, Option.some.injEq] at hdc
  subst hdc
  simp [FnDecl.entryWidth, ctorDecl] at hlen

theorem setCtorProgram_ctorDecls : setCtorProgram.CtorDecls := by
  intro c hc
  simp only [setCtorProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> trivial

/-- The width check does *not* reject it: a `set` fills the declared key and value columns,
and it is the constructor's own `entryWidth` that the entry term then overshoots. -/
theorem setCtorProgram_widthOk : setCtorProgram.WidthOk Database.empty.sig := by
  have hdc : ∀ (sig : Signature) (g : FnName), sig g = some (ctorDecl 0) →
      ∀ dc, sig g = some dc → dc = ctorDecl 0 := by
    intro sig g hg dc h; exact Option.some.inj (hg.symm.trans h) |>.symm
  refine ⟨by simp [ctorDecl], by simp [ctorDecl], by simp [ctorDecl], ?_, ?_, trivial⟩ <;>
    exact ⟨fun dc h => by obtain rfl := hdc _ _ rfl dc h; exact ⟨rfl, rfl⟩, trivial,
      ⟨⟨fun dc h => by obtain rfl := hdc _ _ rfl dc h; rfl, trivial⟩, trivial⟩⟩

/-- The one check that rejects it. -/
theorem setCtorProgram_not_setLegal :
    ¬ setCtorProgram.SetLegal Database.empty.sig := by
  rintro ⟨-, -, -, hs, -⟩
  exact hs (by decide)

/-! ## The rule head that names nothing

`staleProgram`'s rule head applies `f`, which nothing declares. Declaration is required, so
`Expr.eval` has no rule for `(f)`: the head gets stuck at every state the program reaches,
the rule contributes nothing, and no term of `f` is ever built. The program *is*
`Program.SetLegal` and its signature *is* `Signature.MergesLegal` — the two checks the
refinement chain carries — so `Program.Evaluable` is isolated as what rejects it. -/

/-- `(function M () i64 :merge new)`. -/
def staleDecl : FnDecl := ⟨0, 1, some (.merge [] [.var "new"])⟩

/-- `(rule ((= 0 (M))) ((f)))`. Its head names `f`, which nothing has declared; only a
`set` is constrained by `Action.SetLegal`, so the rule is still legal, and it is
`Program.Evaluable` that rejects it. -/
def staleRule : Rule := ⟨[.values [.lit (.int 0)] "M" []], [.expr (.app "f" [])], ""⟩

def staleProgram : Program :=
  [ .decl "M" staleDecl,
    .action (.set "M" [] [.lit (.int 0)]),
    .action (.set "M" [] [.lit (.int 1)]),
    .rule staleRule,
    .run "" ]

def staleSig : Signature := Function.update (fun _ => none) "M" (some staleDecl)

theorem staleSig_mergeOf :
    Signature.mergeOf staleSig "M" = some (.merge [] [.var "new"]) := rfl

/-- The program passes the head condition the refinement chain carries. -/
theorem staleProgram_setLegal : Program.SetLegal staleProgram (fun _ => none) := by
  refine ⟨trivial, ?_, ?_, ⟨trivial, trivial⟩, trivial, trivial⟩ <;>
    · change Signature.mergeOf staleSig "M" ≠ none
      rw [staleSig_mergeOf]
      simp

/-- …and the merge-body condition it carries. -/
theorem staleProgram_mergesLegal : Signature.MergesLegal staleSig := by
  intro g dc body res hg hm
  by_cases hgM : g = "M"
  · subst hgM
    rw [show staleSig "M" = some staleDecl from rfl, Option.some.injEq] at hg
    subst hg
    rw [show staleDecl.merge = some (MergeSpec.merge [] [.var "new"]) from rfl,
      Option.some.injEq, MergeSpec.merge.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨⟨trivial, trivial⟩, rfl⟩
  · rw [staleSig, Function.update_of_ne hgM] at hg
    exact absurd hg (by simp)

/-- **The static check rejects it.** `Program.Evaluable` asks that every applied name be a
declared constructor, and `staleRule`'s head applies `f`. -/
theorem staleProgram_not_evaluable : ¬ Program.Evaluable staleProgram (fun _ => none) := by
  rintro ⟨-, -, -, hrule, -, -⟩
  exact Signature.not_isCtor_of_none (show staleSig "f" = none from rfl)
    (hrule.1 "f" (by simp [Expr.fns, Expr.fnsList])).2

/-- **And the head is stuck wherever the program can get to.** At every state
`staleProgram` reaches, `f` is still undeclared, so the rule's head evaluates under no
environment and the rule can never fire. -/
theorem staleProgram_head_stuck {C : Database}
    (h : ProgramStep Database.empty staleProgram C) :
    C.sig "f" = none ∧ ∀ σ : Env, Expr.eval C.sig (.app "f" []) σ = none := by
  rw [staleProgram] at h
  obtain ⟨C1, h1, h⟩ := h.cons_inv
  obtain ⟨C2, h2, h⟩ := h.cons_inv
  obtain ⟨C3, h3, h⟩ := h.cons_inv
  obtain ⟨C4, h4, h⟩ := h.cons_inv
  obtain ⟨C5, h5, h⟩ := h.cons_inv
  have hf : C5.sig "f" = none := by
    rw [h5.sig, h4.sig, h3.sig, h2.sig, h1.sig]
    rfl
  obtain rfl := h.nil_inv
  exact ⟨hf, fun σ =>
    Expr.eval_app_undeclared (show Prim.ofName "f" = none from rfl) hf⟩

/-! ## `MergeDeclared` is what makes a `.decl`'s merge phase neutral

`CmdStep` runs a merge phase after **every** command, where `.rule` and `.decl` previously
took none. Both additions are neutral — `Scratch/CmdMergePhase.lean` has `ruleStep_iff` and
`declStep_iff` — but `.decl` is neutral only *once `Spec/Scope.lean`'s `MergeDeclared` is
asked*, because a `:merge` result may name a function declared later. This is the witness
that the check cannot be dropped: `g` is a merge function whose result names `f`, `f` is
declared afterwards, and the declaration turns a state where nothing merges into one where
a step applies. -/

/-- The state-level reading of `Program.MergeDeclared`: every declared merge function's body
and result name only functions the signature already has. -/
def SigMergeDeclared (sig : Signature) : Prop :=
  ∀ g d ms, sig g = some d → d.merge = some ms → ms.Declared sig

/-- `(function g (Math) i64 :merge (f))` — a `:merge` whose result names `f`. -/
def gdecl : FnDecl := { arity := 1, outArity := 1, merge := some (.merge [] [.app "f" []]) }

/-- `g`'s one entry: key `0`, value `0`. -/
def entry : Term := .app "g" [t0, t0]

def db₀ : Database where
  sig := fun n => if n = "g" then some gdecl else none
  eqs := {(t0, t0), (entry, entry)}
  env := []
  rules := ∅

/-- What the old `CmdStep` at a `.decl` reached, and the whole of it. -/
def db₁ : Database := { db₀ with sig := Function.update db₀.sig "f" (some (ctorDecl 0)) }

theorem oldDecl : cmdEffect db₀ (.decl "f" (ctorDecl 0)) = some db₁ := rfl

/-- `f` is fresh, so `Cmd.DeclFresh` admits `(constructor f)` here. -/
theorem f_fresh : db₀.sig "f" = none := by simp [db₀]

theorem cong_db₀ {a b : Term} (h : Cong db₀ a b) : a = b ∧ (a = t0 ∨ a = entry) := by
  induction h using Cong.rec (motive_2 := fun as bs _ => as = bs) with
  | assert hab =>
    simp only [db₀, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  | symm _ ih => obtain ⟨rfl, h⟩ := ih; exact ⟨rfl, h⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨rfl, h⟩ := ih₁; obtain ⟨rfl, -⟩ := ih₂; exact ⟨rfl, h⟩
  | congr _ _ _ ih₁ _ ih => subst ih; exact ⟨rfl, ih₁.2⟩
  | nil => rfl
  | cons _ _ ih₁ ih₂ => obtain ⟨rfl, -⟩ := ih₁; rw [ih₂]

theorem terms_db₀ : db₀.terms = {t0, entry} := by
  ext u
  constructor
  · intro h; rcases (cong_db₀ h).2 with rfl | rfl <;> simp
  · rintro (rfl | rfl) <;> exact Cong.assert (by simp [db₀])

/-- The state is well formed, so the counterexample is not a malformed database. -/
theorem wf_db₀ : db₀.WF where
  eqsRefl := by
    intro t ht
    rw [terms_db₀] at ht
    rcases ht with rfl | rfl <;> simp [db₀]
  subtermClosed := by
    intro t ht s hs
    rw [terms_db₀] at ht ⊢
    simp only [t0, entry, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases ht with rfl | rfl
    · simp only [t0, Term.subterms_lit, Set.mem_singleton_iff] at hs
      exact Or.inl hs
    · simp only [entry, t0, Term.subterms_app, Set.mem_insert_iff, Set.mem_iUnion,
        List.mem_cons, List.not_mem_nil, exists_prop, or_false] at hs
      rcases hs with rfl | ⟨i, hi, hs⟩
      · exact Or.inr rfl
      · rcases hi with rfl | rfl <;>
          · rw [Term.subterms_lit, Set.mem_singleton_iff] at hs
            exact Or.inl hs
  envInTerms := by intro b hb; simp [db₀] at hb
  litsIsolated := by
    intro p hp _
    simp only [db₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> rfl

/-- Every application `db₀` holds is `g`'s entry, of the width `g` declares: the state is
`DeclaredTerms` too. -/
theorem declaredTerms_db₀ : db₀.DeclaredTerms := by
  intro f as hmem
  obtain ⟨-, h | h⟩ := cong_db₀ hmem
  · exact absurd h (by simp [t0])
  · obtain ⟨rfl, rfl⟩ : f = "g" ∧ as = [t0, t0] := by simpa [entry] using h
    exact ⟨gdecl, by simp [db₀], rfl⟩

/-- **Nothing merges before the declaration.** `g`'s `:merge` result names `f`, which is
undeclared, so `Expr.evalList` returns `none` and `MergeStep.collide` cannot fire. -/
theorem no_merge_before (x : Database) : ¬ MergeStep db₀ x := by
  intro h
  cases h with
  | @collide d f decl as bs a b vs body res hsig hmerge _ _ _ _ _ heval hres =>
    have hdecl : decl = gdecl := by
      by_cases hf : f = "g"
      · subst hf; simpa [db₀] using hsig.symm
      · simp [db₀, hf] at hsig
    subst hdecl
    simp only [gdecl, Option.some.injEq, MergeSpec.merge.injEq] at hmerge
    obtain ⟨rfl, rfl⟩ := hmerge
    simp only [evalActions, Option.some.injEq] at heval
    subst heval
    simp [Expr.evalList, Expr.eval, Prim.ofName, Signature.IsCtor, db₀] at hres

/-- **The declaration enables a merge step**, so the merge phase `CmdStep` runs after a
`.decl` reaches a database the effect alone does not. `f` fresh and the state well formed
and `DeclaredTerms` do not prevent it. -/
theorem decl_enables_merge :
    ∃ db', CmdStep db₀ (.decl "f" (ctorDecl 0)) db' ∧ db' ≠ db₁ := by
  have hg : db₁.sig "g" = some gdecl := by simp [db₁, db₀]
  have hctor : db₁.sig.IsCtor "f" := ⟨ctorDecl 0, by simp [db₁], rfl⟩
  have hentry : entry ∈ db₁.terms := Cong.assert (by simp [db₁, db₀])
  have ht0 : Cong db₁ t0 t0 := Cong.assert (by simp [db₁, db₀])
  have hres : Expr.evalList db₁.sig [Expr.app "f" []] (mergeEnv [t0] [t0]) =
      some [Term.app "f" []] := by
    simp [Expr.evalList, Expr.eval, Prim.ofName, hctor]
  refine ⟨_, ⟨db₁, rfl, Relation.ReflTransGen.single (MergeStep.collide (f := "g")
    (d := { db₁ with env := mergeEnv [t0] [t0] }) (as := [t0]) (bs := [t0]) (a := [t0])
    (b := [t0]) hg rfl rfl rfl hentry hentry (CongList.cons ht0 CongList.nil) rfl hres)⟩, ?_⟩
  intro hcontra
  have hmem : (Term.app "g" [t0, .app "f" []], Term.app "g" [t0, .app "f" []]) ∈ db₁.eqs := by
    rw [← hcontra]
    exact Or.inr ⟨_, Term.IsSubterm.refl _, rfl⟩
  simp [db₁, db₀, entry, t0] at hmem

/-- **The check excludes it.** `(function g … :merge (f))` fails `Cmd.MergeDeclared` in any
signature `f` is not already in, so no program the checks admit builds `db₀`. -/
theorem gdecl_not_mergeDeclared (sig : Signature) (h : sig "f" = none) :
    ¬ Cmd.MergeDeclared (.decl "g" gdecl) sig := by
  intro hc
  rcases hc (.merge [] [.app "f" []]) rfl |>.2 (.app "f" []) (List.mem_cons_self ..) "f"
    (by simp [Expr.fns, Expr.fnsList]) with hp | hs
  · exact hp (by simp [Prim.ofName])
  · exact hs (show Function.update sig "g" (some gdecl) "f" = none by
      rw [Function.update_of_ne (by simp)]; exact h)

/-- `Scratch/CmdMergePhase.lean`'s `declStep_iff` does not apply to `db₀`, and this is the
hypothesis it fails. -/
theorem db₀_not_sigMergeDeclared : ¬ SigMergeDeclared db₀.sig := by
  intro h
  rcases (h "g" gdecl (.merge [] [.app "f" []]) (by simp [db₀]) rfl).2 (.app "f" [])
    (List.mem_cons_self ..) "f" (by simp [Expr.fns, Expr.fnsList]) with hp | hs
  · exact hp (by simp [Prim.ofName])
  · exact hs (by simp [db₀])

/-! ## Non-vacuity

`Cong` lost its `refl` rule, so a term is present exactly when an equation says so and
`Database.empty` says nothing. Three definitions read "there is a witness term the database
already holds"; each of them would be satisfiable by reflexivity alone, and none of them is.
These are the guards. -/

/-- **Nothing exists by default.** No equations, no terms: `Cong` is not secretly
reflexive. -/
theorem not_cong_of_no_eqs {db : Database} (h : db.eqs = ∅) {a b : Term} :
    ¬ Cong db a b := fun hc => by
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp hc.mem_left
  rw [h] at hu
  exact hu.elim (Set.notMem_empty _) (Set.notMem_empty _)

/-- **`Matches` still says something.** The witness must be a term the database already
holds, and `withOperands` cannot supply one. -/
theorem not_matches_empty {p : Pattern} {σ : Env} : ¬ Matches Database.empty p σ := by
  intro h
  cases h with
  | expr hw _ _ => exact not_cong_of_no_eqs rfl hw
  | eq hw _ _ _ _ => exact not_cong_of_no_eqs rfl hw
  | values hw _ _ _ => exact not_cong_of_no_eqs rfl hw

/-- **`Database.Recorded` still says something.** `withOperands` makes both sides of `p`
self-equal, but the witness `q` has to be one of `d₂`'s own equations. -/
theorem recorded_empty {d : Database} (h : d.Recorded Database.empty) : d.eqs = ∅ :=
  Set.eq_empty_of_forall_notMem fun p hp =>
    absurd (h.eqs p hp).choose_spec.1 (Set.notMem_empty _)

/-- **`MergeStep` still says something**, and so `Database.empty` is `MergeSaturated`
vacuously rather than by a step that changes nothing. -/
theorem not_mergeStep_empty (db' : Database) : ¬ MergeStep Database.empty db' := by
  intro h
  cases h with
  | collide _ _ _ _ hmem _ _ _ _ => exact not_cong_of_no_eqs rfl hmem

end Falsity
end Egglog
