import EgglogSemantics.Spec.Encode
import EgglogSemantics.Spec.Step

/-!
# The proof-encoding theorems

M11. `PLAN.md`'s three theorems over `Spec/Encode.lean`'s `encode`, all `sorry`. The
statements are the deliverable: what M11 is worth turns on getting them right, and a
wrong statement proved is worth less than a right one stated.

## The asymmetry between the two sides

The source `P` is in the constructor fragment, so `Database.CtorRows` and
`Signature.AllConstructors` hold of the state it runs to and `mcong_iff_cong` says the
functional dependency there *is* congruence. Source-side equality is therefore written
`Cong`.

Neither holds of the target. `encode` declares `@UF` and every `@fView` with a `:merge`,
so `AllConstructors` is false (`encode_not_allConstructors`), and their rows are not
constructor rows, so `CtorRows` is false and `mcong_iff_cong` does not apply. What takes
its place is the opposite fact: the encoded program has no `.union` function and asserts
no equalities, so `MCong` on the target collapses to syntactic equality
(`encode_mcong_eq`) — congruence there is *entirely simulated* by `@UF` and the views'
`:merge`. So no theorem below writes `Cong tgt` or `MCong tgt`; the target side speaks
only of `ViewRepr`, `UFLeader` and rows.

The second asymmetry is `Rebuilt`. Soundness — every recorded equality is real — is an
invariant and holds at every reachable state, so it needs no saturation hypothesis at
all. Completeness needs one: until the rebuild has re-keyed the view rows to their
children's leaders, a collision that congruence would find has not happened yet.

## What is not here

The proof checker. `CHECKER.md` scopes it at 150–250 lines of definitions and it is
separate work, so `Checks` below is an opaque stand-in. And the encoding itself is
proofs-off, so `encode_proof_rows_check` is vacuous as it stands. That is now an
*encoder* gap rather than a language one: `Action.set` takes a `List Expr` and
`Pattern.values` reads a column other than the first, so the two-column row shape these
statements quantify over is expressible — `encode` simply does not emit it yet.
-/

namespace Egglog
variable {P : Program} {src tgt : Database} {a b : Term}

/-! ### `CongOn` against `Cong`

`encode_sound` concludes `CongOn`, which is defined on any pair of terms; the simulation
theorem states `Cong`, which is not. This is what converts. -/
/-- On terms the database holds, building them again changes nothing. -/
theorem congOn_iff_cong {db : Database} (hwf : db.WF) (hrows : db.CtorRows)
    (ha : a ∈ db.terms) (hb : b ∈ db.terms) : CongOn db a b ↔ Cong db a b := sorry

/-! ### The target is not the constructor fragment

Three statements of one fact, and the reason the theorems below are not symmetric. -/
/-- `encode` declares `@UF` with a `:merge`, so the target signature has a
non-constructor. `mcong_iff_cong` is therefore unavailable on the target, and with it
every M2–M8 theorem that transports through it. -/
theorem encode_not_allConstructors (htgt : ProgramStep Database.empty (encode P) tgt) :
    ¬ tgt.sig.AllConstructors := sorry

/-- The encoded program asserts no equalities: `encode` emits no `union` action, which
is the whole point of the transformation ("the job of the term encoding is to remove all
calls to union"). Every equality it records is a `@UF` row. -/
theorem encode_eqs_empty (htgt : ProgramStep Database.empty (encode P) tgt) :
    tgt.eqs = ∅ := sorry

/-- **Congruence in the target is entirely simulated.** `MCong` there is syntactic
equality: `eqs` is empty by `encode_eqs_empty`, and the only `.union` functions are the
source constructor names, whose rows are exactly the constructor rows their own terms
induce, so `fd` only ever re-derives reflexivity.

This is what makes table lookups in the target read keys syntactically, as egglog's do,
and it is the formal content of `MERGE.md`'s "in the target, congruence is entirely
simulated". -/
theorem encode_mcong_eq (htgt : ProgramStep Database.empty (encode P) tgt) {x y : Term}
    (h : MCong tgt x y) : x = y := sorry

/-! ### Theorem (2), soundness

Every equality the encoded database records is one the source derives. An invariant over
the step relation, so no saturation and no confluence hypothesis: it holds at every
reachable state, and a partially rebuilt or diverging run satisfies it throughout
(`MERGE.md`, "Why the reader over-approximates"). -/
/-- Rows are true. A `@UF` row proves its key equal to its parent; a view row proves its
e-class equal to the application it is keyed on.

Stated with `CongOn` rather than `Cong` because the rebuild re-keys view rows to their
children's leaders, so the target holds rows about applications the source never built —
`@AddView [1,1] ↦ Add[1,2]` after `(Add 1 2)` and `(union 1 2)`, where `Add 1 1` is not
in `src.terms` and `Cong src` cannot mention it. The equality is still real; `CongOn` is
the reading under which it is. -/
theorem encode_rows_sound (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (hsig : src.sig.AllConstructors)
    (hrows : src.CtorRows) (htgt : ProgramStep Database.empty (encode P) tgt) :
    (∀ k p, Row.mk ufName [k] [p] ∈ tgt.rows → CongOn src k p) ∧
      (∀ f es e, Row.mk (viewName f) es [e] ∈ tgt.rows → CongOn src (.app f es) e) := sorry

/-- A union-find leader is equal to what it leads. The transitive closure of the first
half of `encode_rows_sound`, and the form the simulation theorem consumes. -/
theorem encode_leader_sound (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (hsig : src.sig.AllConstructors)
    (hrows : src.CtorRows) (htgt : ProgramStep Database.empty (encode P) tgt)
    {t l : Term} (h : UFLeader tgt t l) : CongOn src t l := sorry

/-! ### Theorem (3), simulation

Split into its two halves, because they need different hypotheses — which is the point
of stating them separately. -/
/-- **Soundness half.** Two source terms whose view reads land on a common leader are
`Cong`-equal in the source.

No `Rebuilt`: soundness is an invariant. No membership hypothesis either, because the
conclusion is `CongOn`; `encode_simulation` adds both to state it as `Cong`. -/
theorem encode_sound (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (hsig : src.sig.AllConstructors)
    (hrows : src.CtorRows) (htgt : ProgramStep Database.empty (encode P) tgt)
    (h : SameClass tgt a b) : CongOn src a b := sorry

/-- Every source term has a view reading. The encoding builds and interns every term the
source builds, so the right-hand side of the simulation theorem is never vacuously
false. -/
theorem encode_repr_total (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src)
    (htgt : ProgramStep Database.empty (encode P) tgt) (ha : a ∈ src.terms) :
    ∃ e, ViewRepr tgt a e := sorry

/-- **Completeness half.** The encoding loses no equality.

`Rebuilt` is what this needs and soundness does not. The encoding resolves congruence
through a view collision, and a collision only happens once the rebuild rules have moved
both rows' keys to their children's leaders; before that the two congruent applications
still sit at distinct keys. `Rebuilt` is `proof_encoding.md`'s
`(saturate (seq (run @rebuilding_cleanup) (saturate (run @parent)) (run @rebuilding)))`
as a predicate on the state, because `Cmd.run` carries no ruleset.

Any `P` can be brought into range by appending `(run)`s to *both* sides — the extra
rounds fire the encoded source rules too, so appending them to the target alone would
break the soundness half. -/
theorem encode_complete (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (hsig : src.sig.AllConstructors)
    (hrows : src.CtorRows) (htgt : ProgramStep Database.empty (encode P) tgt)
    (hreb : Rebuilt P tgt) (ha : a ∈ src.terms) (hb : b ∈ src.terms)
    (h : Cong src a b) : SameClass tgt a b := sorry

/-- **The simulation theorem** (`PLAN.md` M11 (3)).

`Cong (run P) a b` iff `a` and `b` have the same `@UF` leader in `run (encode P)`, where
"the same `@UF` leader" is `SameClass`: read each term out of the views, subterm by
subterm, and follow `@UF` to a representative. Reading through the views rather than
naming an id directly is not an artifact — it is exactly what `check` compiles to, and
it is the correspondence between a source term and a target e-class.

The hypotheses, and why each is here:

* `hdom` — `encode`'s domain, `PLAN.md`'s fragment.
* `hsig`, `hrows` — the source is in the constructor fragment, so `mcong_iff_cong`
  applies there and `Cong` is the right relation to state. They follow from `hdom` along
  `hsrc` by the `CtorRows` preservation lemma; they are hypotheses here so the statement
  can be read without it.
* `hwf` — `Database.WF`, to know `a` and `b` are subterm-closed, which is what makes
  `CongOn src a b` and `Cong src a b` the same on terms the source holds.
* `hreb` — completeness only; see `encode_complete`.
* `ha`, `hb` — `Cong` is restricted to `db.terms` at `refl` and `congr`, so it is only
  the intended relation on terms the source holds.

There is deliberately **no** `tgt.CtorRows` and no `tgt.sig.AllConstructors`: both are
false, and the target side of the statement is written to not want them. -/
theorem encode_simulation (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (hsig : src.sig.AllConstructors)
    (hrows : src.CtorRows) (hwf : src.WF)
    (htgt : ProgramStep Database.empty (encode P) tgt) (hreb : Rebuilt P tgt)
    (ha : a ∈ src.terms) (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass tgt a b := sorry

/-- `PLAN.md`'s literal shape, over the M0–M8 functional semantics. `run P` is defined
on the constructor fragment and agrees with `ProgramStep` there, and `hdom` is what
supplies the two fragment hypotheses `encode_simulation` takes explicitly. -/
theorem encode_simulation_run (hdom : P.EncodeDomain) (hsrc : run P = some src)
    (htgt : ProgramStep Database.empty (encode P) tgt) (hreb : Rebuilt P tgt)
    (ha : a ∈ src.terms) (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass tgt a b := sorry

/-! ### Theorem (1), the proofs the encoding writes

`CHECKER.md` scopes the checker and this file deliberately does not build it, so `Checks`
is opaque. What is fixed here is the shape, which is the reviewable part:

* the checker's first argument is the **source** program, not `encode P` — `check_proof`
  takes `&[ResolvedNCommand]` and reads no e-graph table at all (`CHECKER.md`, Q2), so a
  Lean `Checks` is a predicate over syntax `Spec/` already models;
* a proof sits in a row's *proof column*, and what it claims is fixed by the row it sits
  in: a `@UF` row's proof proves `key = parent`, a view row's proves
  `eclass = f(children)`;
* the constructor fragment needs five justifications (`Fiat`, `Rule`, `Trans`, `Sym`,
  `Congr`), each with a `Cong` constructor behind it, which is why `encode_rows_sound`
  is the half of theorem (1) + (2) that is statable today.

**These two statements are currently vacuous**, because `encode` emits one-column rows.
The language no longer stops it: `Action.set` takes a `List Expr` and `Pattern.values` is
egglog's tuple destructure. What is missing is the encoder emitting a proof column and a
`Lit` that can hold `Unit` and a rule name. -/
/-- Stand-in for `ProofStore::check_proof`. `Checks P pf x y` reads "`pf` is a proof the
checker accepts against the source program `P`, concluding `x = y`". -/
opaque Checks : Program → Term → Term → Term → Prop

/-- **Theorem (1).** Every proof the encoding writes is accepted by the checker, and
**theorem (2)**, its conclusion is derivable in the source. -/
theorem encode_proof_rows_check (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (hsig : src.sig.AllConstructors)
    (hrows : src.CtorRows) (htgt : ProgramStep Database.empty (encode P) tgt)
    {k p pf : Term} (hrow : Row.mk ufName [k] [p, pf] ∈ tgt.rows) :
    Checks P pf k p ∧ CongOn src k p := sorry

/-- The view's half of theorem (1) + (2). A view row's proof runs the other way round
from a `@UF` row's: it proves `eclass = f(children)`. -/
theorem encode_proof_view_rows_check (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (hsig : src.sig.AllConstructors)
    (hrows : src.CtorRows) (htgt : ProgramStep Database.empty (encode P) tgt)
    {f : FnName} {es : List Term} {e pf : Term}
    (hrow : Row.mk (viewName f) es [e, pf] ∈ tgt.rows) :
    Checks P pf e (.app f es) ∧ CongOn src e (.app f es) := sorry

end Egglog
