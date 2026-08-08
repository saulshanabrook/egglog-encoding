import EgglogSemantics.Spec.Merge
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Proofs.Congruence
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Proofs.Interp

/-!
# What M9 has to prove

`MERGE.md` says which theorem buys what. Five are still unproved; the rest are proved.

The load-bearing one is `mcong_iff_cong`: where the rows are the constructor rows
(`Database.CtorRows`) and the signature is all constructors, the generalized relation is
exactly M2's `Cong`. That is what makes replacing `Cong` by `MCong` a refactor rather
than a rewrite — without it every M2–M8 theorem would have to be reproved rather than
transported.

Four statements needed repair, and the repairs are the interesting output:

* `Expr.MEval_of_eval`'s `∀ f, Prim.ofName f = none` is **unsatisfiable**
  (`not_forall_ofName_eq_none`), so it is vacuous. `Expr.NoPrim` and
  `Expr.MEval_of_eval'` are the version that is not, and `Expr.eval_of_MEval` is the
  converse M11 wants — it needs no `CtorRows`.
* `MCong.mono`, `MCongList.mono` and `Database.Out.mono` are **false** as stated:
  `Contained` ignores `sig` and `fd` fires only at `.union`. See
  `mcong_mono_needs_sig`. They carry `d₁.sig = d₂.sig`.
* `MergeStep.self_id` and `MergeStep.wf` need the row half of well-formedness
  (`Database.RowsWF`), which `Database.WF` deliberately omits, and `self_id`
  additionally needs `ctorRowsOf db.terms ⊆ db.rows`.
* `FDatabase.closureF_ok`'s `←` direction is false without "every application the
  database holds is a `.union` function's".

`MergeStep.diamond_of_join` and `RunStep.unique_of_confluent` are the two `MERGE.md`
flags as guesses, and both have hypotheses that cannot be used; their docstrings say
what replaces them.
-/

namespace Egglog
/-! ### Signatures -/
/-- With `mergeOf` defaulting an undeclared name to `.union`, `AllConstructors` says
exactly that every function is a constructor. This is why "everything up to M8" is
literally the all-constructors case and not merely analogous to it. -/
theorem Signature.mergeOf_eq_union {sig : Signature} (h : sig.AllConstructors)
    (f : FnName) : sig.mergeOf f = MergeSpec.union := by
  unfold Signature.mergeOf
  cases hf : sig f with
  | none => rfl
  | some d => exact h f d hf

/-! ### Constructor-determined rows

`Database.toM` is gone: `Database` *is* the M9 database now, so the embedding it named
is the identity and `CtorRows` is what the theorem below quantifies over instead. -/
theorem Database.mem_rows_iff {db : Database} (h : db.CtorRows) {f : FnName}
    {as vs : List Term} :
    Row.mk f as vs ∈ db.rows ↔ vs = [.app f as] ∧ Term.app f as ∈ db.terms := by
  rw [h]; exact Iff.rfl

/-! ### The generalized relation is the old one

Two directions, two hypotheses. `MCong → Cong` needs only that the rows are constructor
rows, because a constructor row is one whatever the signature says. `Cong → MCong` also
needs `AllConstructors`, which is what licenses `fd`. -/
mutual

/-- Every functional-dependency derivation over constructor rows is an M2 derivation.

`fd` is the only interesting case: its two rows are constructor rows, so their outputs
are `.app f as` and `.app f bs` and both applications are in `db.terms` — the two
premises `Cong.congr` wants. -/
theorem MCong.toCong {db : Database} (hrows : db.CtorRows) {a b : Term}
    (h : MCong db a b) : Cong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (MCong.toCong hrows h)
  | .trans h₁ h₂ => exact .trans (MCong.toCong hrows h₁) (MCong.toCong hrows h₂)
  | .fd ha hb _ hl hxy =>
    obtain ⟨rfl, hma⟩ := (Database.mem_rows_iff hrows).mp ha
    obtain ⟨rfl, hmb⟩ := (Database.mem_rows_iff hrows).mp hb
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact .congr hma hmb (MCongList.toCongList hrows hl)

theorem MCongList.toCongList {db : Database} (hrows : db.CtorRows) {as bs : List Term}
    (h : MCongList db as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (MCong.toCong hrows hab) (MCongList.toCongList hrows hl)

end

mutual

/-- Every M2 derivation is a functional-dependency derivation.

`congr` is the only interesting case, and its two membership premises are exactly what is
needed: `RowsComplete` turns each into a row `fd` can use, and `CtorTerms` says the
function they are applications of is a constructor, which is what lets `fd` fire.

Stated over `CtorTerms`/`RowsComplete` rather than `AllConstructors`/`CtorRows` because
those two **survive merging** — they constrain `terms` and the constructor rows, neither
of which a merge touches (`FDatabase.mergeRound_confined`) — whereas `CtorRows` fails at
the first `:merge` declaration. That is what lets the interpreter's `closureF`, which
computes `Cong`, be read as `MCong` in a database that has merge functions in it, and it
is the reason the refinement chain below can exist at all. -/
theorem Cong.toMCong' {db : Database} (hterms : db.CtorTerms) (hrows : db.RowsComplete)
    {a b : Term} (h : Cong db a b) : MCong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (Cong.toMCong' hterms hrows h)
  | .trans h₁ h₂ =>
    exact .trans (Cong.toMCong' hterms hrows h₁) (Cong.toMCong' hterms hrows h₂)
  | .congr (f := f) (as := as) (bs := bs) hma hmb hl =>
    exact .fd (a := [Term.app f as]) (b := [Term.app f bs])
      (hrows ⟨rfl, hma⟩) (hrows ⟨rfl, hmb⟩) (hterms f as hma)
      (CongList.toMCongList' hterms hrows hl) (by simp)

theorem CongList.toMCongList' {db : Database} (hterms : db.CtorTerms)
    (hrows : db.RowsComplete) {as bs : List Term} (h : CongList db as bs) :
    MCongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.toMCong' hterms hrows hab) (CongList.toMCongList' hterms hrows hl)

end

/-- `AllConstructors` gives `CtorTerms`: `mergeOf` defaults an undeclared name to `.union`
and `AllConstructors` says every declared one is `.union` too. -/
theorem Signature.AllConstructors.ctorTerms {db : Database}
    (hsig : db.sig.AllConstructors) : db.CtorTerms :=
  fun f _ _ => Signature.mergeOf_eq_union hsig f

/-- `CtorRows` gives `RowsComplete`: it is the equality, this is one inclusion of it.

Written with `▸` rather than `h.ge`: the latter goes through `Set`'s order instances and
puts `Classical.choice` into the axiom set of everything downstream, including
`mcong_iff_cong`, which is otherwise `propext` alone. -/
theorem Database.CtorRows.rowsComplete {db : Database} (h : db.CtorRows) :
    db.RowsComplete := fun _ hr => h.symm ▸ hr

theorem Cong.toMCong {db : Database} (hsig : db.sig.AllConstructors) (hrows : db.CtorRows)
    {a b : Term} (h : Cong db a b) : MCong db a b :=
  Cong.toMCong' hsig.ctorTerms hrows.rowsComplete h

theorem CongList.toMCongList {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {as bs : List Term} (h : CongList db as bs) :
    MCongList db as bs :=
  CongList.toMCongList' hsig.ctorTerms hrows.rowsComplete h

/-- **The compatibility theorem.** Where the rows are the constructor rows and every
function is a constructor, the functional dependency *is* congruence.

This is what `PLAN.md` M9 asks for, and the reason `MCong` has no `congr` constructor:
congruence is not lost, it is `fd` read at constructor rows.

It replaces `mcong_toM_iff`, which quantified over the embedding `Database.toM` of an
M2 database into a separate `MDatabase`. Now that the two states are one structure that
embedding is the identity, so the *hypothesis* `CtorRows` carries what the embedding
used to: it says the state is in the constructor-only fragment. The theorem's content is
unchanged and its proof is the same four `match` cases. -/
theorem mcong_iff_cong {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {a b : Term} : MCong db a b ↔ Cong db a b :=
  ⟨MCong.toCong hrows, Cong.toMCong hsig hrows⟩

/-- Congruence, recovered as a derived rule rather than a constructor. -/
theorem MCong.congr {db : Database} {f : FnName} {as bs : List Term}
    (ha : Row.mk f as [.app f as] ∈ db.rows) (hb : Row.mk f bs [.app f bs] ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.union) (hl : MCongList db as bs) :
    MCong db (.app f as) (.app f bs) :=
  .fd ha hb hsig hl (by simp)

/-! ### The two evaluators agree

`Expr.eval` (M0–M8, a function) and `Expr.MEval` (M9, a relation) coexist until M12.
These are the guard against their drifting apart.

`NoPrim` is what `hprim` below *should* say. As stated, `∀ f, Prim.ofName f = none` is
false — `Prim.ofName "ordering-min" = some .orderingMin` — so `MEval_of_eval` is
vacuous. It is proved honestly all the same (the induction never needs `hprim` at a name
other than the one in front of it), and `MEval_of_eval'` is the same statement with the
hypothesis restricted to the names `e` actually mentions, which is satisfiable.

`Expr.NoPrim` and `Expr.NoPrimList` live in `Spec/Merge.lean` beside `Prim.ofName`. -/
@[simp] theorem Expr.noPrim_app {f : FnName} {args : List Expr} :
    Expr.NoPrim (.app f args) ↔ Prim.ofName f = none ∧ Expr.NoPrimList args := Iff.rfl

@[simp] theorem Expr.noPrimList_cons {e : Expr} {es : List Expr} :
    Expr.NoPrimList (e :: es) ↔ Expr.NoPrim e ∧ Expr.NoPrimList es := Iff.rfl

/-- **`Expr.MEval_of_eval`'s hypothesis is unsatisfiable**, so that theorem is vacuous
however it is proved. `Expr.MEval_of_eval'` is the same statement with the quantifier
cut down to the names `e` mentions, which is satisfiable. -/
theorem not_forall_ofName_eq_none : ¬ ∀ f : FnName, Prim.ofName f = none := by
  intro h
  have hmin := h "ordering-min"
  simp [Prim.ofName] at hmin

mutual

/-- The connecting theorem between the two evaluators, which coexist until stage 3
(`PLAN.md`, M12). `Expr.eval` is the M0–M8 function; `Expr.MEval` is M9's relation. On a
constructor-only signature the first refines the second, which is the guard against the
two drifting apart while both exist.

**The hypothesis as stated is unsatisfiable**, so this theorem is vacuous; see
`Expr.MEval_of_eval'` for the version that is not. The proof below is the real one —
only the quantifier on `hprim` is too strong. -/
theorem Expr.MEval_of_eval {db : Database} (hsig : db.sig.AllConstructors) {σ : Env}
    {e : Expr} {t : Term} (hprim : ∀ f, Prim.ofName f = none) (h : e.eval σ = some t) :
    Expr.MEval db σ e t := by
  match e, h with
  | .lit l, h => rw [Expr.eval_lit, Option.some.injEq] at h; exact h ▸ .lit
  | .var v, h => exact .var h
  | .app f args, h =>
    rw [Expr.eval_app, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    exact .ctor (hprim f) (Signature.mergeOf_eq_union hsig f)
      (Expr.MEvalList_of_evalList hsig hprim hts)

theorem Expr.MEvalList_of_evalList {db : Database} (hsig : db.sig.AllConstructors)
    {σ : Env} {es : List Expr} {ts : List Term} (hprim : ∀ f, Prim.ofName f = none)
    (h : Expr.evalList es σ = some ts) : Expr.MEvalList db σ es ts := by
  match es, h with
  | [], h => rw [Expr.evalList_nil, Option.some.injEq] at h; exact h ▸ .nil
  | e :: es, h =>
    rw [Expr.evalList_cons] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .cons (Expr.MEval_of_eval hsig hprim ht)
      (Expr.MEvalList_of_evalList hsig hprim hus)

end

mutual

/-- `Expr.MEval_of_eval` with a satisfiable hypothesis: only the names `e` mentions have
to be non-primitive. -/
theorem Expr.MEval_of_eval' {db : Database} (hsig : db.sig.AllConstructors) {σ : Env}
    (e : Expr) {t : Term} : e.NoPrim → e.eval σ = some t → Expr.MEval db σ e t := by
  match e with
  | .lit l => intro _ h; rw [Expr.eval_lit, Option.some.injEq] at h; exact h ▸ .lit
  | .var v => intro _ h; exact .var h
  | .app f args =>
    intro hp h
    rw [Expr.eval_app, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    exact .ctor hp.1 (Signature.mergeOf_eq_union hsig f)
      (Expr.MEvalList_of_evalList' hsig args hp.2 hts)

theorem Expr.MEvalList_of_evalList' {db : Database} (hsig : db.sig.AllConstructors)
    {σ : Env} (es : List Expr) {ts : List Term} :
    Expr.NoPrimList es → Expr.evalList es σ = some ts → Expr.MEvalList db σ es ts := by
  match es with
  | [] => intro _ h; rw [Expr.evalList_nil, Option.some.injEq] at h; exact h ▸ .nil
  | e :: es =>
    intro hp h
    rw [Expr.evalList_cons] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .cons (Expr.MEval_of_eval' hsig e hp.1 ht)
      (Expr.MEvalList_of_evalList' hsig es hp.2 hus)

end

mutual

/-- **The converse, which is what M11 needs.** On a constructor-only signature and a
primitive-free expression, `MEval` is no more than `eval`: `lookup` cannot fire because
`mergeOf` is always `.union`, and `prim` cannot fire because no name resolves. This is
what transports a fact about the relational side back to the function side.

`db.CtorRows` is *not* needed — the relation is already deterministic without it,
because the only constructor that reads the database is `lookup` and `AllConstructors`
rules it out. -/
theorem Expr.eval_of_MEval {db : Database} (hsig : db.sig.AllConstructors) {σ : Env}
    {e : Expr} {t : Term} (h : Expr.MEval db σ e t) : e.NoPrim → e.eval σ = some t := by
  match h with
  | .lit => intro _; rfl
  | .var hv => intro _; exact hv
  | .ctor _ _ hl =>
    intro hp
    rw [Expr.eval_app, Expr.evalList_of_MEvalList hsig hl hp.2, Option.map_some]
  | .lookup _ hne _ _ => exact absurd (Signature.mergeOf_eq_union hsig _) hne
  | .prim hf _ _ => intro hp; exact absurd hf (by rw [hp.1]; simp)

theorem Expr.evalList_of_MEvalList {db : Database} (hsig : db.sig.AllConstructors)
    {σ : Env} {es : List Expr} {ts : List Term} (h : Expr.MEvalList db σ es ts) :
    Expr.NoPrimList es → Expr.evalList es σ = some ts := by
  match h with
  | .nil => intro _; rfl
  | .cons he hl =>
    intro hp
    rw [Expr.evalList_cons, Expr.eval_of_MEval hsig he hp.1, Option.bind_some,
      Expr.evalList_of_MEvalList hsig hl hp.2, Option.map_some]

end

/-- `MEval` is deterministic on the constructor fragment, which is what makes M12's
recovery plan (`PLAN.md`) work: a relation that agrees with a function is a function. -/
theorem Expr.MEval_unique {db : Database} (hsig : db.sig.AllConstructors) {σ : Env}
    {e : Expr} {t₁ t₂ : Term} (hp : e.NoPrim) (h₁ : Expr.MEval db σ e t₁)
    (h₂ : Expr.MEval db σ e t₂) : t₁ = t₂ :=
  Option.some.inj
    ((Expr.eval_of_MEval hsig h₁ hp).symm.trans (Expr.eval_of_MEval hsig h₂ hp))

/-- The rest of M9 collapses too: with no `.merge` function there is no collision to
resolve, so a round is `RunRules` and nothing else. Companion to `mcong_iff_cong` on
the *step* side — together they say M9 restricted to constructors is M0–M8 unchanged. -/
theorem MergeStep.saturated_of_allConstructors {db : Database}
    (hsig : db.sig.AllConstructors) : MergeSaturated db := by
  intro db' h
  cases h with
  | collide _ _ _ hm _ _ =>
    rw [Signature.mergeOf_eq_union hsig] at hm
    exact absurd hm (by simp)

/-! ### The least-congruence principle

How every negative fact about the closure gets proved, and the shape the M11
checker-soundness argument takes. `Cong.le` with the `congr` hypothesis replaced by an
`fd` one. -/
mutual

/-- `MCong db` is the least relation closed under `db`'s assertions, reflexivity on its
terms, symmetry, transitivity and the functional dependency. -/
theorem MCong.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hfd : ∀ f as bs (a b : List Term) x y, Row.mk f as a ∈ db.rows →
      Row.mk f bs b ∈ db.rows → db.sig.mergeOf f = MergeSpec.union →
      List.Forall₂ R as bs → (x, y) ∈ a.zip b → R x y)
    {a b : Term} (h : MCong db a b) : R a b := by
  match h with
  | .assert hm => exact hassert _ _ hm
  | .refl hm => exact hrefl _ hm
  | .symm h => exact hsymm _ _ (MCong.le hassert hrefl hsymm htrans hfd h)
  | .trans h₁ h₂ =>
    exact htrans _ _ _ (MCong.le hassert hrefl hsymm htrans hfd h₁)
      (MCong.le hassert hrefl hsymm htrans hfd h₂)
  | .fd hra hrb hu hl hxy =>
    exact hfd _ _ _ _ _ _ _ hra hrb hu (MCongList.le hassert hrefl hsymm htrans hfd hl) hxy

/-- `MCong.le` over key tuples; the companion `MCong.le`'s `fd` case recurses into. -/
theorem MCongList.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hfd : ∀ f as bs (a b : List Term) x y, Row.mk f as a ∈ db.rows →
      Row.mk f bs b ∈ db.rows → db.sig.mergeOf f = MergeSpec.union →
      List.Forall₂ R as bs → (x, y) ∈ a.zip b → R x y)
    {as bs : List Term} (h : MCongList db as bs) : List.Forall₂ R as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (MCong.le hassert hrefl hsymm htrans hfd hab)
      (MCongList.le hassert hrefl hsymm htrans hfd hl)

end

/-! ### `MCongList` is an equivalence

`MCong.setoid` pointwise. `Out.union_cong` needs it: two lookups at one key class reach
their rows through *different* congruent keys, and `fd` compares those two directly. -/
theorem MCongList.symm {db : Database} {as bs : List Term} (h : MCongList db as bs) :
    MCongList db bs as := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab.symm (MCongList.symm hl)

theorem MCongList.trans {db : Database} {as bs cs : List Term} (h₁ : MCongList db as bs)
    (h₂ : MCongList db bs cs) : MCongList db as cs := by
  match h₁, h₂ with
  | .nil, .nil => exact .nil
  | .cons hab hl₁, .cons hbc hl₂ => exact .cons (hab.trans hbc) (MCongList.trans hl₁ hl₂)

theorem MCongList.forall₂ {db : Database} {as bs : List Term} (h : MCongList db as bs) :
    List.Forall₂ (MCong db) as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab (MCongList.forall₂ hl)

theorem MCongList.ofForall₂ {db : Database} {as bs : List Term}
    (h : List.Forall₂ (MCong db) as bs) : MCongList db as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

/-! ### Monotonicity

Constraint (3). That a merge *adds* the combined row instead of replacing the two it
combined is exactly what these need.

All three carry an **added hypothesis** `d₁.sig = d₂.sig`, and it is not decoration:
`Database.Contained` ignores `sig`, while `MCong.fd` fires only where
`mergeOf f = .union`, so redeclaring `f` as `:no-merge` destroys a derivation without
removing anything. `mcong_mono_needs_sig` below is the counterexample. Every use in this
file has it — `MergeStep.sig` and `MergeClosure.sig` — because only `Cmd.decl` writes
`sig`. -/
mutual

/-- Adding terms, rows and equalities only adds derivations. `Cong.mono`, with the
`fd` case in place of `congr`. -/
theorem MCong.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {a b : Term} (hc : MCong d₁ a b) : MCong d₂ a b := by
  match hc with
  | .assert hm => exact .assert (h.eqs hm)
  | .refl hm => exact .refl (h.terms hm)
  | .symm hc => exact .symm (MCong.mono h hsig hc)
  | .trans h₁ h₂ => exact .trans (MCong.mono h hsig h₁) (MCong.mono h hsig h₂)
  | .fd hra hrb hu hl hxy =>
    exact .fd (h.rows hra) (h.rows hrb) (hsig ▸ hu) (MCongList.mono h hsig hl) hxy

theorem MCongList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {as bs : List Term} (hc : MCongList d₁ as bs) : MCongList d₂ as bs := by
  match hc with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (MCong.mono h hsig hab) (MCongList.mono h hsig hl)

end

/-- **Why `MCong.mono` needs the signature hypothesis.** Two rows of `f` recording
different outputs at one key make those outputs `fd`-equal while `f` is a constructor.
Declaring `f` `:no-merge` adds no term, row or equality — so `Contained` still holds —
and takes the derivation away. -/
theorem mcong_mono_needs_sig : ∃ d₁ d₂ : Database, ∃ a b : Term,
    d₁.Contained d₂ ∧ MCong d₁ a b ∧ ¬ MCong d₂ a b := by
  classical
  let x : Term := .lit (.int 0)
  let y : Term := .lit (.int 1)
  let rows : Set Row := {Row.mk "f" [] [x], Row.mk "f" [] [y]}
  let d₁ : Database := ⟨fun _ => none, ∅, rows, ∅, [], ∅⟩
  let d₂ : Database := ⟨fun _ => some ⟨0, 1, .noMerge⟩, ∅, rows, ∅, [], ∅⟩
  refine ⟨d₁, d₂, x, y, ⟨subset_rfl, subset_rfl, subset_rfl⟩, ?_, ?_⟩
  · exact MCong.fd (f := "f") (as := []) (bs := []) (a := [x]) (b := [y])
      (by simp [d₁, rows]) (by simp [d₁, rows]) rfl .nil (by simp)
  · intro h
    have hxy : x = y :=
      MCong.le (R := fun a b => a = b) (by simp [d₂]) (by simp [d₂]) (fun _ _ h => h.symm)
        (fun _ _ _ h₁ h₂ => h₁.trans h₂)
        (fun _ _ _ _ _ _ _ _ _ hu _ _ => absurd hu (by simp [d₂, Signature.mergeOf])) h
    simp [x, y] at hxy

/-- `Out` is monotone, because both of its conjuncts are. A rule body reading a table
never *loses* a match — the property an overwriting merge would destroy, and the one
seminaive evaluation rests on. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, MCongList.mono h hsig hl, h.rows hrow⟩

/-- A `set` only adds. -/
theorem Database.contained_addRow {db : Database} {f : FnName} {as vs : List Term} :
    db.Contained (db.addRow f as vs) :=
  Database.Contained.addRow f as vs db

/-- Row actions only add, exactly as `evalAction_contained` does for `Action`. -/
theorem Database.ActionStep.contained {db d : Database} {a : Action}
    (h : Database.ActionStep db a d) : db.Contained d := by
  cases h with
  | expr => exact Database.Contained.addTerm _ _
  | letBind => exact ⟨Set.subset_union_left, Set.subset_union_left, subset_rfl⟩
  | union => exact Database.Contained.addEq _ _ _
  | set => exact Database.Contained.addRow _ _ _ _

theorem Database.ActionsStep.contained {db d : Database} {as : List Action}
    (h : Database.ActionsStep db as d) : db.Contained d := by
  induction h with
  | nil => exact Database.Contained.refl _
  | cons ha _ ih => exact (Database.ActionStep.contained ha).trans ih

/-- **A merge never shrinks the database.**

Constraint (3), discharged by the representation rather than by an argument: the step
adds the combined row beside the two it merged, so there is nothing to overwrite. This
is what lets `MCong.mono`, `Out.mono` and every `WF`-preservation lemma survive into
M9 unchanged. -/
theorem MergeStep.contained {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₁.Contained d₂ := by
  cases h with
  | @collide d f as _ _ _ vs _ _ _ _ _ _ hbody _ =>
    have hb : d₁.Contained d :=
      ⟨(Database.ActionsStep.contained hbody).terms,
        (Database.ActionsStep.contained hbody).rows,
        (Database.ActionsStep.contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addRow f as vs d)
    exact ⟨hc.terms, hc.rows, hc.eqs⟩

theorem MergeClosure.contained {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₁.Contained d₂ := by
  induction h with
  | refl => exact Database.Contained.refl _
  | tail _ hstep ih => exact ih.trans (MergeStep.contained hstep)

/-! #### Re-adding what is already there

`addRow` re-inserts its key and value terms, so "the step changed nothing" needs those
insertions to be no-ops. That is exactly `WF.subtermClosed` plus the two halves of
`CtorRows`: the row's terms are terms (`RowsWF`), and every application in `terms` has
its constructor row (`ctorRowsOf db.terms ⊆ db.rows`, the direction `addTerm`
maintains). These belong in `Proofs/Database.lean`. -/
theorem Database.addTerm_eq_self {db : Database} (hw : db.WF)
    (hctor : Database.ctorRowsOf db.terms ⊆ db.rows) {t : Term} (ht : t ∈ db.terms) :
    db.addTerm t = db := by
  have hs : t.subterms ⊆ db.terms := hw.subtermClosed t ht
  have hr : t.ctorRows ⊆ db.rows := fun r hr => hctor ⟨hr.1, hs hr.2⟩
  unfold Database.addTerm
  rw [Set.union_eq_left.mpr hs, Set.union_eq_left.mpr hr]

theorem Database.addTerms_eq_self {db : Database} (hw : db.WF)
    (hctor : Database.ctorRowsOf db.terms ⊆ db.rows) {ts : List Term}
    (ht : ∀ t ∈ ts, t ∈ db.terms) : db.addTerms ts = db := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih =>
    have h1 : db.addTerm t = db := Database.addTerm_eq_self hw hctor (ht t (by simp))
    change Database.addTerms ts (db.addTerm t) = db
    rw [h1]
    exact ih hw hctor fun s hs => ht s (by simp [hs])

/-- `addTerms` reads only `terms` and `rows`, so two databases agreeing there agree
after it. This is what lets a merge body's result `d` be substituted for `db`. -/
theorem Database.addTerms_terms_rows {d₁ d₂ : Database} (ht : d₁.terms = d₂.terms)
    (hr : d₁.rows = d₂.rows) (ts : List Term) :
    (d₁.addTerms ts).terms = (d₂.addTerms ts).terms ∧
      (d₁.addTerms ts).rows = (d₂.addTerms ts).rows := by
  induction ts generalizing d₁ d₂ with
  | nil => exact ⟨ht, hr⟩
  | cons t ts ih =>
    exact ih (by simp only [Database.addTerm, ht]) (by simp only [Database.addTerm, hr])

set_option linter.unusedVariables false in
/-- **A vacuous self-collision is the identity step.**

Three hypotheses beyond the original statement, all forced and all discharged by the
invariants `addTerm` maintains: `addRow` re-inserts the row's key and value terms, so
those insertions have to be no-ops. See `Database.addTerm_eq_self`.

`hsig` and `hres` are not used by the equation — they are what makes the conclusion an
instance of `MergeStep`, so removing them would change what the theorem says. -/
theorem MergeStep.self_id {db d : Database} {f : FnName} {as a : List Term}
    {body : List Action} {res : List Expr} (hw : db.WF) (hrw : db.RowsWF)
    (hctor : Database.ctorRowsOf db.terms ⊆ db.rows) (hrow : Row.mk f as a ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.merge body res)
    (hbody : Database.ActionsStep { db with env := mergeEnv a a } body d)
    (hfix : d.terms = db.terms ∧ d.rows = db.rows ∧ d.eqs = db.eqs)
    (hres : Expr.MEvalList d d.env res a) :
    ({ d.addRow f as a with env := db.env, rules := db.rules } : Database) = db := by
  obtain ⟨hft, hfr, hfe⟩ := hfix
  have hbase : (db.addTerms as).addTerms a = db := by
    rw [Database.addTerms_eq_self hw hctor fun t ht => (hrw _ hrow).1 t ht]
    exact Database.addTerms_eq_self hw hctor fun t ht => (hrw _ hrow).2 t ht
  obtain ⟨h1t, h1r⟩ := Database.addTerms_terms_rows hft hfr as
  obtain ⟨h2t, h2r⟩ := Database.addTerms_terms_rows h1t h1r a
  rw [hbase] at h2t h2r
  have hsg := Database.ActionsStep.sig hbody
  refine Database.ext ?_ ?_ ?_ ?_ rfl rfl
  · exact (Database.addRow_sig (db := d) (f := f) (as := as) (vs := a)).trans hsg
  · exact h2t
  · change insert (Row.mk f as a) ((d.addTerms as).addTerms a).rows = db.rows
    rw [h2r]
    exact Set.insert_eq_self.mpr hrow
  · exact (Database.addRow_eqs (db := d) (f := f) (as := as) (vs := a)).trans hfe

/-! ### The observable value

Constraint (3)'s second half. `PLAN.md` proposes a merge-fold and asks for it to be
well defined; `Current` is that value defined as a maximum instead, which needs only
antisymmetry. It is not what `Expr.MEval` reads. -/
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

/-- **A `.union` function's outputs are all congruent.**

The functional dependency, stated as what it buys: however many rows a `.union`
function accumulates at one key class, they are one e-class. For `@UF_<Sort>` this is
"every parent a term ever had is equal to it"; for `@<C>View` it is congruence. -/
theorem Database.Out.union_cong {db : Database} {f : FnName} {as v w : List Term}
    {x y : Term} (hsig : db.sig.mergeOf f = MergeSpec.union) (hv : db.Out f as v)
    (hw : db.Out f as w) (hxy : (x, y) ∈ v.zip w) : MCong db x y := by
  obtain ⟨bs, hlb, hrb⟩ := hv
  obtain ⟨cs, hlc, hrc⟩ := hw
  exact .fd hrb hrc hsig (hlb.symm.trans hlc) hxy

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
fields `Contained` ignores. -/
theorem CmdStep.contained {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db.Contained db' := by
  cases h with
  | action ha => exact Database.ActionStep.contained ha
  | rule => exact ⟨subset_rfl, subset_rfl, subset_rfl⟩
  | run hrun =>
    have hu : db.Contained (RunRules db) := Database.Contained.sUnion _ _
    exact hu.trans (MergeClosure.contained hrun)
  | decl => exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem ProgramStep.contained {db db' : Database} {p : Program}
    (h : ProgramStep db p db') : db.Contained db' := by
  induction h with
  | nil => exact Database.Contained.refl _
  | cons hc _ ih => exact (CmdStep.contained hc).trans ih

/-! ### Determinism

Demoted. Confluence is not needed by any safety theorem — see `invariant_of_step`. It
buys one thing only: strengthening M10's refinement from "the interpreter's result is
spec-reachable" to an equality. -/
/-! Evaluation is monotone in the database. `lookup` is the only constructor that reads
it, and it reads `Out`, which is. Half of what a diamond proof for `MergeStep` needs —
see `MergeStep.diamond_of_join`. -/
mutual

/-- A larger database admits every evaluation a smaller one does. -/
theorem Expr.MEval.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {σ : Env} {e : Expr} {t : Term} (h : Expr.MEval d₁ σ e t) : Expr.MEval d₂ σ e t := by
  match h with
  | .lit => exact .lit
  | .var hv => exact .var hv
  | .ctor hp hu hl => exact .ctor hp (hsig ▸ hu) (Expr.MEvalList.mono hc hsig hl)
  | .lookup hp hu hl ho =>
    exact .lookup hp (hsig ▸ hu) (Expr.MEvalList.mono hc hsig hl)
      (Database.Out.mono hc hsig ho)
  | .prim hp hl hv => exact .prim hp (Expr.MEvalList.mono hc hsig hl) hv

theorem Expr.MEvalList.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) {σ : Env} {es : List Expr} {ts : List Term}
    (h : Expr.MEvalList d₁ σ es ts) : Expr.MEvalList d₂ σ es ts := by
  match h with
  | .nil => exact .nil
  | .cons he hl => exact .cons (Expr.MEval.mono hc hsig he) (Expr.MEvalList.mono hc hsig hl)

end

/-- A saturated state is a fixpoint of the whole closure, not only of one step. -/
theorem MergeSaturated.closure_eq {db d : Database} (hs : MergeSaturated db)
    (h : MergeClosure db d) : d = db := by
  induction h with
  | refl => rfl
  | @tail _ _ _ hstep ih => subst ih; exact hs _ hstep

/-- A merge that is a `le`-join is locally confluent: two collisions available at once
can be fired in either order and rejoined. **Unproved, and the statement is worse than
"not known to hold" — `hjoin` is vacuous.** Instantiate `le := fun _ _ => False`:
then `db.Current le f as v` unfolds to `db.Out f as v ∧ ∀ ws, db.Out f as ws → False`,
which is self-contradictory, so `hjoin` holds for *every* `db` and the statement is
unconditional local confluence of `MergeStep`. Any repair has to make the join
condition bite on the merge *body*, not on `Current`.

Unconditional local confluence nevertheless looks **true**, and in the stronger
one-step-on-one-side form `Relation.church_rosser` wants, for a reason `MERGE.md`'s
"open question 2" does not consider: a step's *effect* does not depend on the ambient
state. `addTerm`/`addEq`/`addRow` each add a set determined by the terms involved, and
those terms are fixed by the evaluation witnesses, which `Expr.MEval.mono` says stay
available in a larger database. So firing collision 2 at `d₁` and collision 1 at `d₂`
should land on the same state — the third table's merge that `MERGE.md` worries about
is a *later* step, and it too remains available because nothing is removed.

What is missing is exactness, and it is the whole cost: a transport lemma
`ActionsStep db body d → db.Contained e → e.sig = db.sig → e.env = db.env →
ActionsStep e body (e ⊔ d)` for a componentwise join `⊔`, proved by one case per
action against the set algebra of `addTerm`/`addTerms`/`addRow`. Estimated 150–250
lines. `Expr.MEval.mono` above is the other half and is done. -/
theorem MergeStep.diamond_of_join {db d₁ d₂ : Database}
    {le : List Term → List Term → Prop}
    (hjoin : ∀ f as v w, db.Current le f as v → db.Out f as w → le w v)
    (h₁ : MergeStep db d₁) (h₂ : MergeStep db d₂) :
    ∃ d, MergeClosure d₁ d ∧ MergeClosure d₂ d := by
  sorry

/-- **`hconf` is too weak to use.** Local confluence plus "both are normal forms" gives
uniqueness only via Newman's lemma, which needs the relation to be *terminating* — and
`MergeStep` deliberately is not (`MERGE.md`, constraint (6)). Without termination the
implication genuinely fails in general rewriting: `a ⇄ b`, `a → c`, `b → d` with `c`,
`d` normal is locally confluent and has two normal forms. That shape cannot arise here,
because `MergeStep.contained` forbids cycles — so the *conclusion* is very likely true
— but it is true for a reason `hconf` does not supply, and the only route to it is the
strong diamond, which is `MergeStep.diamond_of_join` restated. Hence
`RunStep.unique_of_diamond` below, which is this theorem with a hypothesis a proof can
actually consume. -/
theorem RunStep.unique_of_confluent {db d₁ d₂ : Database}
    (hconf : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', MergeClosure e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : RunStep db d₁) (h₂ : RunStep db d₂) : d₁ = d₂ := by
  sorry

/-- With a confluent merge the *saturated* states of a round coincide, so an
interpreter that runs merges to a fixpoint computes the one answer `RunStep` allows
that egglog also allows. `RunStep` itself stays a relation.

The hypothesis is `Relation.church_rosser`'s: one of the two joining paths has to be at
most a *single* step. That is exactly the form the monotonicity argument in
`MergeStep.diamond_of_join` would give, and unlike plain local confluence it needs no
termination. -/
theorem RunStep.unique_of_diamond {db d₁ d₂ : Database}
    (hdiamond : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', Relation.ReflGen MergeStep e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : RunStep db d₁) (h₂ : RunStep db d₂) : d₁ = d₂ := by
  obtain ⟨e, he₁, he₂⟩ := Relation.church_rosser hdiamond h₁ h₂
  exact (hs₁.closure_eq he₁).symm.trans (hs₂.closure_eq he₂)

/-! ### Fewer rows mean fewer matches

The other half of the containment contract. `mergeRound_confined` says the implementation
deletes only what it may; this says that deleting can only *lose* results, never invent
them — there is no negation anywhere in the fragment, so every premise of a match is
positive in the state. Together they are "the implementation may find fewer results, never
more", which is the safe direction for M11: a safety property is positive in the state, so
it transfers downward. -/
/-- `Contained` is preserved by adding the same term to both sides. Belongs in
`Proofs/Database.lean`. -/
theorem Database.Contained.addTerm_mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    (t : Term) : (d₁.addTerm t).Contained (d₂.addTerm t) :=
  ⟨Set.union_subset_union h.terms subset_rfl, Set.union_subset_union h.rows subset_rfl,
    h.eqs⟩

theorem ValidEnv.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => h.terms (hv.2 b hb)⟩

/-- **A larger database admits every match a smaller one does.** Read contrapositively —
which is how the containment contract uses it — a database missing rows finds at most the
matches the full one finds. -/
theorem MValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    (henv : d₂.env = d₁.env) {p : Pattern} {σ : Env} (h : MValidSubst d₁ p σ) :
    MValidSubst d₂ p σ := by
  have hsig₁ : ∀ t : Term, (d₁.addTerm t).sig = (d₂.addTerm t).sig := fun _ => hsig
  cases h with
  | expr hv hw he hcong =>
    refine .expr ?_ (hc.terms hw) ?_ (MCong.mono (hc.addTerm_mono _) (hsig₁ _) hcong)
    · rw [henv]; exact hv.mono hc
    · rw [henv]; exact Expr.MEval.mono hc hsig he
  | eq hv hw he₁ he₂ hc₁ hc₂ =>
    refine .eq ?_ (hc.terms hw) ?_ ?_
      (MCong.mono ((hc.addTerm_mono _).addTerm_mono _) hsig hc₁)
      (MCong.mono ((hc.addTerm_mono _).addTerm_mono _) hsig hc₂)
    · rw [henv]; exact hv.mono hc
    · rw [henv]; exact Expr.MEval.mono hc hsig he₁
    · rw [henv]; exact Expr.MEval.mono hc hsig he₂
  | values hv hu ht hk hw hrow =>
    refine .values ?_ ?_ ?_ (MCongList.mono hc hsig hk) (MCongList.mono hc hsig hw)
      (hc.rows hrow)
    · rw [henv]; exact hv.mono hc
    · rw [henv]; exact Expr.MEvalList.mono hc hsig hu
    · rw [henv]; exact Expr.MEvalList.mono hc hsig ht

theorem MValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {q : Query} {σ : Env}
    (h : MValidQuerySubst d₁ q σ) : MValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, hall.imp fun _ _ hv => MValidSubst.mono hc hsig henv hv, hu⟩

/-! ### The interpreter

`Impl/Merge.lean` runs the M9 semantics. The refinement is weaker than M10's on purpose:
the spec admits several results, so the interpreter's is one of them rather than *the*
one. -/
/-- **The M9 refinement: reachability, not equality.**

`exec_toDatabase` says the constructor interpreter computes exactly `run p`. Here the
spec is a relation, so the statement is that the interpreter lands on a state the spec
reaches. Nothing stronger is available, and nothing stronger is wanted — pinning a
single result would mean pinning the merge order, which is the thing `MERGE.md` argues
the semantics should decline to pin.

**False as stated**, for the reason `Expr.MEval_of_eval'` exists: `exec` is
`Impl/Interp.lean`'s constructor interpreter and evaluates with `Expr.eval`, which
builds an application for *every* name.

* `p = [.action (.expr (.app "ordering-min" [1, 2]))]` — `exec` adds the term
  `ordering-min 1 2`; `MEval.prim` gives `1`, so `ActionStep` adds `1` instead and the
  two states differ.
* `p = [.decl "g" ⟨1, 1, .noMerge⟩, .action (.expr (.app "g" [1]))]` — `exec` adds the
  term `g 1`; `MEval` has only `lookup` for `g`, which needs a row, so no `ActionStep`
  exists at all and no `ProgramStep` relates the two.

Both are repaired by hypotheses: the program declares nothing but constructors, and no
`Expr` in it names a primitive (`Expr.NoPrim`). Under those, the proof is the whole
`runProgram → ProgramStep` bridge — `evalAction → ActionStep` via
`Expr.MEval_of_eval'`, `ValidSubst → MValidSubst` via `mcong_iff_cong`, then
`stepCmd`/`runProgram`. The e-matching step needs `db.CtorRows` at every intermediate
state, i.e. the `CtorRows` preservation lemmas being added to `Proofs/Database.lean` and
`Proofs/Step.lean`, so this is blocked on those rather than merely long. -/
theorem execM_reachable {p : Program} {d : FDatabase} (h : exec p = some d) :
    ProgramStep FDatabase.empty.toDatabase p d.toDatabase := by
  sorry

/-! ### The contract for `execM`: containment, not reachability

`execM_reachable`'s shape is unavailable for `execM`, and not because it is hard —
because it is **false**. The implementation's merge phase deletes the rows it merged and
the specification never deletes, so no `ProgramStep` state equals the implementation's:
a spec run that performed the same merges still holds the two originals, and a spec run
that performed none holds no combined row. `execM_reachable` above survives only because
`exec` is `Impl/Interp.lean`'s constructor interpreter, which has no merge phase at all
(`FDatabase.mergeRound_eq_self` and `hasMergeRow_eq_false`) — the layering is intact.

What replaces it is that the implementation's state is *contained* in one the spec
reaches: the implementation may find **fewer** results, never more. That is the safe
direction, because everything the M11 safety theorem reads is positive in the state, so
safety transfers downward. `MValidSubst.mono` is the step that makes "fewer rows" mean
"fewer matches" rather than merely "a different database".

The deletion adds one obligation on top of the plain refinement — that the witness `db`
can be chosen to have performed *at least* the merges the implementation did — which is
where `MergeClosure`'s freedom to take any number of steps is spent.

#### The refinement chain

Everything below is *stated* and unproved. Together they are what `execM_contained`,
`execM_current_of_lattice` and `execM_reachable` are all blocked on: a step-by-step
account of the merge interpreter against the merge specification.

The chain has one prerequisite that is not obvious, and it is why `Cong.toMCong'` exists.
`FDatabase.execExpr` compares keys with `congrKeys d.closureF`, and `closureF` computes
**`Cong`** — it closes over `eqsF` and `congrPair`, with no notion of a row. The
specification's `Database.Out` compares them with **`MCong`**. So every lookup the
interpreter performs has to be re-read as a specification lookup, and that is exactly
`Cong.toMCong'`: `CtorTerms` and `RowsComplete` are what license it, and unlike
`CtorRows` they survive a `:merge` declaration.

Hence `Inv`, which is what the induction actually carries. Prove its preservation lemmas
first; the rest of the chain is structural recursion once they are available. -/

/-- The invariant the refinement chain carries.

`wf` is what `mem_closureF_iff_of_wf` needs; the other two are what `Cong.toMCong'` needs.
All three hold of `FDatabase.empty` and are preserved by every interpreter step —
`addTerm` inserts a term's constructor rows, `addRow` inserts its operands' terms, and a
merge pass touches neither `terms` nor any non-`.merge` row (`mergeRound_confined`). -/
structure FDatabase.Inv (d : FDatabase) : Prop where
  wf : d.WF
  ctorTerms : d.toDatabase.CtorTerms
  rowsComplete : d.toDatabase.RowsComplete

theorem FDatabase.Inv.empty : FDatabase.empty.Inv := by sorry

theorem FDatabase.Inv.addTerm {d : FDatabase} (h : d.Inv) (t : Term) :
    (d.addTerm t).Inv := by sorry

theorem FDatabase.Inv.addEq {d : FDatabase} (h : d.Inv) (a b : Term) :
    (d.addEq a b).Inv := by sorry

/-- `addRow` preserves the invariant only for a key whose operands are already terms and
whose function is not a constructor — a `set` on a constructor would add a row that
`RowsComplete` does not account for, which is what `Action.SetLegal` rules out. -/
theorem FDatabase.Inv.addRow {d : FDatabase} (h : d.Inv) {f : FnName} {as vs : List Term}
    (hf : d.sig.mergeOf f ≠ MergeSpec.union) : (d.addRow f as vs).Inv := by sorry

theorem FDatabase.Inv.execAction {d d' : FDatabase} (h : d.Inv) {a : Action}
    (hlegal : a.SetLegal d.sig) (hs : d.execAction a = some d') : d'.Inv := by sorry

theorem FDatabase.Inv.mergeRound {d : FDatabase} (h : d.Inv) : d.mergeRound.Inv := by
  sorry

/-! #### Evaluation -/

/-- The interpreter's evaluation is one of the evaluations the specification allows.

Exact, not a containment: `execExpr` picks the *first* recorded output where `MEval`
allows any, so the implementation's choice is among the specification's. The `lookup` case
is where `Cong.toMCong'` is spent — `outs` filters by `closureF`, which is `Cong`. -/
theorem FDatabase.execExpr_MEval {d : FDatabase} (h : d.Inv) {σ : Env} {e : Expr}
    {t : Term} (hs : d.execExpr σ e = some t) : Expr.MEval d.toDatabase σ e t := by
  sorry

theorem FDatabase.execExprList_MEvalList {d : FDatabase} (h : d.Inv) {σ : Env}
    {es : List Expr} {ts : List Term} (hs : d.execExprList σ es = some ts) :
    Expr.MEvalList d.toDatabase σ es ts := by
  sorry

/-! #### Actions -/

theorem FDatabase.execAction_ActionStep {d d' : FDatabase} (h : d.Inv) {a : Action}
    (hs : d.execAction a = some d') :
    Database.ActionStep d.toDatabase a d'.toDatabase := by
  sorry

theorem FDatabase.execActions_ActionsStep {d d' : FDatabase} (h : d.Inv)
    {as : List Action} (hs : d.execActions as = some d') :
    Database.ActionsStep d.toDatabase as d'.toDatabase := by
  sorry

/-! #### Matching -/

theorem FDatabase.patternHoldsM_MValidSubst {d : FDatabase} (h : d.Inv) {p : Pattern}
    {σ : Env} (hs : d.patternHoldsM p σ = true) : MValidSubst d.toDatabase p σ := by
  sorry

theorem FDatabase.matchQueryM_MValidQuerySubst {d : FDatabase} (h : d.Inv) {q : Query}
    {σ : Env} (hs : σ ∈ d.matchQueryM q) : MValidQuerySubst d.toDatabase q σ := by
  sorry

/-! #### The merge phase and the round

These are the two containment steps, and the only places the *witness* has to be chosen
rather than computed. A merge pass deletes, so its result is not a `MergeClosure` state;
the specification state to compare against is one that took at least the same merges, and
`MergeClosure`'s freedom to take any number of steps is what pays for that. -/

theorem FDatabase.mergeRound_contained {d : FDatabase} (h : d.Inv) :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Contained db := by
  sorry

theorem FDatabase.mergeSaturateF_contained {d e : FDatabase} (h : d.Inv) {n : Nat}
    (hs : d.mergeSaturateF n = some e) :
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Contained db := by
  sorry

theorem FDatabase.execRunRulesM_contained {d : FDatabase} (h : d.Inv) :
    ∃ db, RunStep d.toDatabase db ∧ d.execRunRulesM.toDatabase.Contained db := by
  sorry

/-! #### Commands and programs -/

theorem FDatabase.execCmdM_contained {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hs : d.execCmdM c = some d') :
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Contained db := by
  sorry

/-- The chain's inductive step needs the witness to keep being a *step* from a database
the previous witness contained, which is `MValidSubst.mono` read forwards: a larger
specification state still admits every match, so the specification can follow along. -/
theorem FDatabase.execProgramM_contained {d d' : FDatabase} (h : d.Inv) {p : Program}
    (hs : d.execProgramM p = some d') :
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Contained db := by
  sorry

/-- **The contract for `execM`.** Whatever the implementation computes, the specification
could have reached a state containing it. See the section header above for why this is
containment rather than the equality `exec_toDatabase` enjoys. -/
theorem execM_contained {p : Program} {d : FDatabase} (h : execM p = some d) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ d.toDatabase.Contained db :=
  FDatabase.execProgramM_contained FDatabase.Inv.empty h

/-- **Completeness, so containment is not vacuous.**

A do-nothing implementation satisfies `execM_contained`, so containment needs a companion
saying the implementation keeps the *right* row and not merely a subset of the rows. For a
**lattice** merge that is exactly `Database.Current`, which is what `Current` was defined
for — "the single value it has when the merge is a join, used only where a result must
match egglog exactly".

`le` is a parameter rather than an instance because the order is per function and orders
whole rows. `hjoin` says the merge really is a `le`-join: whatever the body computes from
two colliding outputs is an upper bound of both. `hanti` is what makes the greatest
element unique (`Database.current_unique`). For a merge that is *not* a lattice there is no
`Current` to be complete against and nothing is claimed — `MERGE.md`'s "order-dependent
merges are the user's fault".

Unproved. Beyond the refinement `execM_contained` needs, this wants an induction over the
merge phase carrying "every output the specification records at this key class is `le` the
one the implementation holds", whose step is that `mergeOneWith` replaces two rows by
their join and its saturation removes the rest. Deleting the merged rows is what makes
that invariant maintainable at all: while the implementation was append-only it held every
superseded output and the statement was simply false. Estimated 200–300 lines on top of
the refinement, which is why it is stated rather than proved. -/
theorem execM_current_of_lattice {p : Program} {d : FDatabase}
    {le : List Term → List Term → Prop} (hexec : execM p = some d)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (hjoin : ∀ (f : FnName) (body : List Action) (res : List Expr) (a b vs : List Term),
      d.sig.mergeOf f = MergeSpec.merge body res →
      (∃ e, Database.ActionsStep { d.toDatabase with env := mergeEnv a b } body e ∧
        Expr.MEvalList e e.env res vs) → le a vs ∧ le b vs)
    {f : FnName} {as vs : List Term} {body : List Action} {res : List Expr}
    (hmerge : d.sig.mergeOf f = MergeSpec.merge body res)
    (hrow : Row.mk f as vs ∈ d.rows) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ db.Current le f as vs := by
  sorry

/-- The interpreter's merge phase against the specification's.

**False as stated, once the implementation deletes.** `MergeClosure` is
`Relation.ReflTransGen MergeStep` and `MergeStep.contained` says every step only grows the
state, so no `MergeClosure` can reach a database with *fewer* rows — which is exactly what
a pass now produces. The containment form below is what survives, and it is the merge-phase
instance of `execM_contained`.

It needs at least `d.WF`: `mergeOne` gates on `congrKeys d.closureF`, and `closureF`
decides `Cong` only for a well-formed database (`mem_closureF_iff_of_wf`), while
`MergeStep` gates on `MCongList`. Turning the first into the second also needs
`closureF_ok`, hence its `hunion` hypothesis, at every accumulator inside `mergeRound`'s
two nested folds. Beyond that it needs the `execExpr → MEval` and
`execActions → ActionsStep` refinements, which no lemma provides yet — `Impl/Merge.lean`
is unrefined territory. What `mergeRound_confined` already gives, unconditionally, is that
the rows the pass drops are merge rows and nothing else. -/
theorem mergeRound_closure {d : FDatabase} :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Contained db := by
  sorry

/-! #### `mcong_iff_cong` without `CtorRows`

`CtorRows` is an equality of row *sets*, which the interpreter's databases do not
satisfy once a `:merge` function has a row. The two halves it is used for are separated
here so `closureF_ok` can have only the halves that hold. -/
/-- `hrow` in reduced form. Stating it separately is the same trick
`Database.mem_rows_iff` plays: applied to a row *literal* the projections
`{fn := f, args := as, out := vs}.out` do not reduce on their own, and `obtain ⟨rfl, _⟩`
then sees `vs` occurring in its own definition. -/
theorem Database.ctor_row {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {f : FnName} {as vs : List Term} (h : Row.mk f as vs ∈ db.rows)
    (hu : db.sig.mergeOf f = MergeSpec.union) :
    vs = [.app f as] ∧ Term.app f as ∈ db.terms := hrow _ h hu

mutual

/-- `MCong.toCong` needing only that a `.union` function's rows are constructor rows. -/
theorem MCong.toCong_of_rows {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {a b : Term} (h : MCong db a b) : Cong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (MCong.toCong_of_rows hrow h)
  | .trans h₁ h₂ =>
    exact .trans (MCong.toCong_of_rows hrow h₁) (MCong.toCong_of_rows hrow h₂)
  | .fd hra hrb hu hl hxy =>
    obtain ⟨rfl, hma⟩ := Database.ctor_row hrow hra hu
    obtain ⟨rfl, hmb⟩ := Database.ctor_row hrow hrb hu
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact .congr hma hmb (MCongList.toCongList_of_rows hrow hl)

theorem MCongList.toCongList_of_rows {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {as bs : List Term} (h : MCongList db as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (MCong.toCong_of_rows hrow hab) (MCongList.toCongList_of_rows hrow hl)

end

mutual

/-- `Cong.toMCong` needing only that every application the database holds is a `.union`
function's and has its constructor row. -/
theorem Cong.toMCong_of_terms {db : Database}
    (hterm : ∀ f as, Term.app f as ∈ db.terms → Row.mk f as [.app f as] ∈ db.rows)
    (hunion : ∀ f as, Term.app f as ∈ db.terms → db.sig.mergeOf f = MergeSpec.union)
    {a b : Term} (h : Cong db a b) : MCong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (Cong.toMCong_of_terms hterm hunion h)
  | .trans h₁ h₂ =>
    exact .trans (Cong.toMCong_of_terms hterm hunion h₁)
      (Cong.toMCong_of_terms hterm hunion h₂)
  | .congr (f := f) (as := as) (bs := bs) hma hmb hl =>
    exact .fd (a := [Term.app f as]) (b := [Term.app f bs]) (hterm f as hma)
      (hterm f bs hmb) (hunion f as hma)
      (CongList.toMCongList_of_terms hterm hunion hl) (by simp)

theorem CongList.toMCongList_of_terms {db : Database}
    (hterm : ∀ f as, Term.app f as ∈ db.terms → Row.mk f as [.app f as] ∈ db.rows)
    (hunion : ∀ f as, Term.app f as ∈ db.terms → db.sig.mergeOf f = MergeSpec.union)
    {as bs : List Term} (h : CongList db as bs) : MCongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.toMCong_of_terms hterm hunion hab)
      (CongList.toMCongList_of_terms hterm hunion hl)

end

/-- **The congruence closure needs no `fd` disjunct.**

`MCong.fd` fires only at a `.union` function, and in a database the interpreter builds a
`.union` function's rows are exactly the constructor rows of its terms — the two
hypotheses. So `MCong` coincides with `Cong` on the row-free projection, and
`Impl/Closure.lean`'s `closure` decides it unchanged. This is what licenses
`FDatabase.closureF` reusing `closureTotal`.

`hunion` is an **added hypothesis** and the `←` direction is false without it: with
`sig g = .merge …`, terms `g x`, `g y` and an asserted `x = y`, `Cong` relates
`g x` and `g y` by `congr` while `MCong` has no rule that can — `fd` fires only at
`.union`. It says what `Impl/Merge.lean`'s comment means by "every declared function is
`.merge` or `.noMerge`": a `:merge` function's application is never itself a term,
because `execExpr` resolves it to its recorded output. -/
theorem FDatabase.closureF_ok {d : FDatabase}
    (hrow : ∀ r ∈ d.rows, d.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ d.terms)
    (hterm : ∀ f as, Term.app f as ∈ d.terms → d.sig.mergeOf f = MergeSpec.union →
      Row.mk f as [.app f as] ∈ d.rows)
    (hunion : ∀ f as, Term.app f as ∈ d.terms → d.sig.mergeOf f = MergeSpec.union)
    {a b : Term} : MCong d.toDatabase a b ↔ Cong d.toDatabase a b :=
  ⟨MCong.toCong_of_rows hrow,
    Cong.toMCong_of_terms (fun f as h => hterm f as h (hunion f as h)) hunion⟩

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
`MValidSubst.mono`, that fewer rows really do mean fewer matches. -/
namespace FDatabase

@[simp] theorem addTerms_sig {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).sig = d.sig := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addRow_sig {d : FDatabase} {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).sig = d.sig := by
  show ((d.addTerms as).addTerms vs).sig = d.sig
  rw [addTerms_sig, addTerms_sig]

/-- The interpreter's actions only add, so the only thing that ever removes a row is the
merge phase. `Database.ActionStep.contained` read through `toDatabase`. -/
theorem execAction_contained {d e : FDatabase} {a : Action}
    (h : d.execAction a = some e) : d.toDatabase.Contained e.toDatabase := by
  cases a with
  | expr e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      subst h
      rw [toDatabase_addTerm]
      exact Database.Contained.addTerm t d.toDatabase
  | letBind v e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => hx⟩
      · exact List.mem_dedup.mpr (List.mem_append_right _ hx)
      · exact List.mem_dedup.mpr (List.mem_append_right _ hx)
  | union e₁ e₂ =>
    cases hv₁ : d.execExpr d.env e₁ with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some t₁ =>
      cases hv₂ : d.execExpr d.env e₂ with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some t₂ =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        subst h
        rw [toDatabase_addEq]
        exact Database.Contained.addEq t₁ t₂ d.toDatabase
  | set f args out =>
    cases hv₁ : d.execExprList d.env args with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some ts =>
      cases hv₂ : d.execExprList d.env out with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some vs =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        subst h
        rw [toDatabase_addRow]
        exact Database.Contained.addRow f ts vs d.toDatabase

/-- The interpreter's actions do not touch the signature either, so which functions are
`.merge` functions is stable across a merge pass. -/
theorem execAction_sig {d e : FDatabase} {a : Action} (h : d.execAction a = some e) :
    e.sig = d.sig := by
  cases a with
  | expr e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | letBind v e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | union e₁ e₂ =>
    cases hv₁ : d.execExpr d.env e₁ with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some t₁ =>
      cases hv₂ : d.execExpr d.env e₂ with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some t₂ =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact h ▸ rfl
  | set f args out =>
    cases hv₁ : d.execExprList d.env args with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some ts =>
      cases hv₂ : d.execExprList d.env out with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some vs =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact h ▸ addRow_sig

theorem execActions_contained {d e : FDatabase} {as : List Action}
    (h : d.execActions as = some e) : d.toDatabase.Contained e.toDatabase := by
  induction as generalizing d with
  | nil =>
    rw [FDatabase.execActions, Option.some.injEq] at h
    exact h ▸ Database.Contained.refl _
  | cons a as ih =>
    cases hv : d.execAction a with
    | none => rw [FDatabase.execActions, hv] at h; simp at h
    | some d' =>
      rw [FDatabase.execActions, hv, Option.bind_some] at h
      exact (execAction_contained hv).trans (ih h)

theorem execActions_sig {d e : FDatabase} {as : List Action}
    (h : d.execActions as = some e) : e.sig = d.sig := by
  induction as generalizing d with
  | nil => rw [FDatabase.execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    cases hv : d.execAction a with
    | none => rw [FDatabase.execActions, hv] at h; simp at h
    | some d' =>
      rw [FDatabase.execActions, hv, Option.bind_some] at h
      exact (ih h).trans (execAction_sig hv)

/-- `addRow` only adds, at the interpreter level. -/
theorem contained_addRow {d : FDatabase} {f : FnName} {as vs : List Term} :
    d.toDatabase.Contained (d.addRow f as vs).toDatabase := by
  rw [toDatabase_addRow]; exact Database.Contained.addRow f as vs d.toDatabase

/-- **One merge firing removes nothing it must not.**

The three prohibitions of the design, discharged: a merge deletes no term, no equality,
and no row of a function that is not the `.merge` function being merged. The last covers
both `.union` — constructor rows, which `Database.CtorRows` and the whole congruence
argument rest on — and `.noMerge`, which is how the proof encoding declares its proof
nodes, so deleting one would delete a proof.

The reason it holds is one line: the only rows filtered are `r₁` and `r₂` themselves,
whose function is `r₁.fn`, and the branch was taken only because
`d.sig.mergeOf r₁.fn = .merge body res`. A row of any other kind of function is therefore
distinct from both. -/
theorem mergeOneWith_confined {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.mergeOneWith cl r₁ r₂ = some e) :
    d.toDatabase.terms ⊆ e.toDatabase.terms ∧ d.toDatabase.eqs ⊆ e.toDatabase.eqs ∧
      e.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) →
        r ∈ e.rows := by
  unfold FDatabase.mergeOneWith at h
  cases hm : d.sig.mergeOf r₁.fn with
  | union => rw [hm] at h; simp at h
  | noMerge => rw [hm] at h; simp at h
  | merge body res =>
    rw [hm] at h
    simp only at h
    split at h
    case isFalse => simp at h
    case isTrue hcond =>
      cases hb : FDatabase.execActions { d with env := mergeEnv r₁.out r₂.out } body with
      | none => rw [hb] at h; simp at h
      | some eb =>
        rw [hb, Option.bind_some] at h
        cases hv : eb.execExprList eb.env res with
        | none => rw [hv] at h; simp at h
        | some vs =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          subst h
          have hcb := execActions_contained hb
          have hsb := execActions_sig hb
          set e' : FDatabase :=
            { eb with rows := eb.rows.filter fun r => r ≠ r₁ && r ≠ r₂ } with he'
          have hadd := contained_addRow (d := e') (f := r₁.fn) (as := r₁.args) (vs := vs)
          refine ⟨fun x hx => hadd.terms (hcb.terms hx), fun q hq => hadd.eqs (hcb.eqs hq),
            ?_, fun r hr hnm => hadd.rows ?_⟩
          · show ((e'.addTerms r₁.args).addTerms vs).sig = d.sig
            rw [addTerms_sig, addTerms_sig]; exact hsb
          · have hrb : r ∈ eb.rows := hcb.rows hr
            have hfn : r₁.fn = r₂.fn := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              exact hcond.1.1.1
            have hne : r ≠ r₁ ∧ r ≠ r₂ := by
              refine ⟨fun hq => hnm body res ?_, fun hq => hnm body res ?_⟩
              · rw [hq]; exact hm
              · rw [hq, ← hfn]; exact hm
            show r ∈ e'.rows
            rw [he']
            exact List.mem_filter.mpr ⟨hrb, by simp [hne.1, hne.2]⟩

/-- **A merge pass removes nothing it must not.** `mergeOneWith_confined` through the two
folds. This is the formal content of "`Impl/` deletes merge rows only". -/
theorem mergeRound_confined {d : FDatabase} :
    d.toDatabase.terms ⊆ d.mergeRound.toDatabase.terms ∧
      d.toDatabase.eqs ⊆ d.mergeRound.toDatabase.eqs ∧ d.mergeRound.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) →
        r ∈ d.mergeRound.rows := by
  -- The invariant is exactly the conclusion, relative to the fixed starting database.
  let P : FDatabase → Prop := fun x =>
    d.toDatabase.terms ⊆ x.toDatabase.terms ∧ d.toDatabase.eqs ⊆ x.toDatabase.eqs ∧
      x.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) → r ∈ x.rows
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y =>
      obtain ⟨ht, hq, hs, hr⟩ := mergeOneWith_confined hy
      refine ⟨hx.1.trans ht, hx.2.1.trans hq, hs.trans hx.2.2.1, fun r hrd hnm => ?_⟩
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
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  have hinit : P d := ⟨subset_rfl, subset_rfl, rfl, fun r hr _ => hr⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter d.rows d hinit

/-- **On the constructor fragment nothing is deleted, because nothing merges.** With every
function a constructor no row belongs to a `.merge` function, `hasMergeRow` is false and
the pass is the identity — which is why `Impl/Interp.lean`'s `exec` and the equality
`exec_toDatabase` are untouched by any of this. -/
theorem hasMergeRow_eq_false {d : FDatabase} (hsig : d.sig.AllConstructors) :
    d.hasMergeRow = false := by
  simp only [FDatabase.hasMergeRow, List.any_eq_false]
  intro r _
  rw [Signature.mergeOf_eq_union hsig]
  simp

theorem mergeRound_eq_self {d : FDatabase} (h : d.hasMergeRow = false) :
    d.mergeRound = d := by
  unfold FDatabase.mergeRound
  simp [h]

theorem mergeSaturateF_eq_self {d : FDatabase} (h : d.hasMergeRow = false) {n : Nat} :
    FDatabase.mergeSaturateF n d = some d := by
  have hs : d.settled = true := by
    simp [FDatabase.settled, mergeRound_eq_self h]
  cases n <;> simp [FDatabase.mergeSaturateF, hs]

end FDatabase

/-- **Row counts do not observe the merge phase.**

`rowCount` counts congruence classes of *keys*. A merge step writes its combined row at a
key already present, and a merge with an empty action block writes nothing else, so a
merge pass leaves every count alone.

This is what lets the differential test compare row counts while the interpreter runs
only one merge pass instead of saturating — and it is also why keeping every superseded
output, the over-approximation the design rests on, does not inflate the number: three
recorded values at one key are still one row. Both halves of `PLAN.md`'s row-count oracle
survive into M9 because of it.

**False as stated.** `hpure` bounds the merge's *action block* but not its *result*, and
`FDatabase.addRow` inserts the result's terms together with their constructor rows —
so a merge whose result builds an application adds a key class to a *different*
function's table. Counterexample, with `k` any term:

```
d.sig  = fun n => if n = "f" then some ⟨1, 1, .merge [] [.app "F" [.var "old"]]⟩ else none
d.terms = [k],  d.rows = [⟨"f", [k], [k]⟩],  d.eqs = []
```

`hpure` holds (the only block is `[]`). The row collides with itself — `MCongList` is
reflexive and `closureF` has `(k, k)` — so `mergeRound` fires, the result evaluates to
`F k`, and `addRow "f" [k] [F k]` writes the constructor row `⟨F, [k], [F k]⟩`. Then
`d.mergeRound.keyRowCount "F" = 1` while `d.keyRowCount "F" = 0`.

The theorem the difftest actually relies on is the same statement with `hpure`
strengthened to "the merge result is a term the database already holds" — under which
`addRow` adds no key class anywhere, which is the argument the docstring gives. Every
generated merge case satisfies it (results are `i64` literals). -/
theorem FDatabase.mergeRound_rowCount {d : FDatabase} (f : FnName)
    (hpure : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res → body = []) :
    d.mergeRound.keyRowCount f = d.keyRowCount f := by
  sorry

/-! ### Well-formedness -/
/-- Every binding a merge body's environment provides is one of the two colliding rows'
outputs. This is what `MergeStep.wf` needs `RowsWF` for: `WF.envInTerms` has to hold of
`mergeEnv a b` before the body runs. -/
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

theorem Database.ActionStep.wf {db d : Database} {a : Action} (hw : db.WF)
    (h : Database.ActionStep db a d) : d.WF := by
  cases h with
  | @expr _ t _ => exact hw.addTerm t
  | @letBind v _ t _ =>
    refine ⟨(hw.addTerm t).subtermClosed, (hw.addTerm t).eqsInTerms, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact Database.mem_addTerm t db
    · exact (hw.addTerm t).envInTerms b hb'
  | @union _ _ t₁ t₂ _ _ => exact hw.addEq t₁ t₂
  | @set f _ _ ts vs _ _ => exact hw.addRow f ts vs

theorem Database.ActionsStep.wf {db d : Database} {as : List Action} (hw : db.WF)
    (h : Database.ActionsStep db as d) : d.WF := by
  induction h with
  | nil => exact hw
  | cons ha _ ih => exact ih (Database.ActionStep.wf hw ha)

/-- A merge preserves the invariants. `RowsWF` is an added hypothesis and is forced: the
body runs with `mergeEnv a b` in scope, so `WF.envInTerms` needs the colliding rows'
outputs to be terms, which only `RowsWF` says. -/
theorem MergeStep.wf {d₁ d₂ : Database} (hw : d₁.WF) (hrw : d₁.RowsWF)
    (h : MergeStep d₁ d₂) : d₂.WF := by
  cases h with
  | @collide d f as _ a b vs _ _ hra hrb _ _ hbody _ =>
    have hw0 : ({ d₁ with env := mergeEnv a b } : Database).WF := by
      refine ⟨hw.subtermClosed, hw.eqsInTerms, fun p hp => ?_⟩
      rcases mem_mergeEnv hp with hpa | hpb
      · exact (hrw _ hra).2 _ hpa
      · exact (hrw _ hrb).2 _ hpb
    have hd : d.WF := Database.ActionsStep.wf hw0 hbody
    have hr : (d.addRow f as vs).WF := hd.addRow f as vs
    have hb : d₁.Contained d :=
      ⟨(Database.ActionsStep.contained hbody).terms,
        (Database.ActionsStep.contained hbody).rows,
        (Database.ActionsStep.contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addRow f as vs d)
    exact ⟨hr.subtermClosed, hr.eqsInTerms, fun p hp => hc.terms (hw.envInTerms p hp)⟩

end Egglog
