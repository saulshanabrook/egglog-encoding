import EgglogSemantics.Tests.Congruence
import EgglogSemantics.Congruence.Reader
import EgglogSemantics.Provenance.Log
import EgglogSemantics.SourceProof.Simplify
import EgglogSemantics.Resugar.Export
import EgglogSemantics.Tests.Egg
import EgglogSemantics.Tests.Parse
import EgglogSemantics.Tests.Render
import EgglogSemantics.Tests.PaperTex
import EgglogSemantics.Slotted.Tests.Parse
import EgglogSemantics.Slotted.Tests.Bounded

/-!
# Differential tests

Curated and seeded constructor programs. Each invocation writes a `.egg` program and
expected row counts; `semantics/difftest.sh` runs egglog with a per-case timeout, and
`semantics/compiled-difftest.sh` does the same for the compiled programs.

Nullary constructors stand in for literals where Rust requires distinct sorts.
Additional modes run the congruence, provenance, and resugar gates and export certificates.
The hand-written programs under `tests/` join every gate, and `difftest egg` snapshots
their encodings and lifted proofs.
-/

open Egglog

/-- A nullary constructor. -/
private def C (f : FnName) : Expr := .app f []

private def add (a b : Expr) : Expr := .app "Add" [a, b]

/-- The corpus is written in egglog's registration style: a `rule` joins the unnamed
ruleset, `run` and `saturate` fire everything registered so far, and a `global` is a
top-level action. `prog` resolves that into runs over rule lists, as `Program.ofEgg` does
for a `.egg` file. -/
private inductive Src where
  | global (a : Action)
  | rule (r : Rule)
  | run
  | saturate
  /-- A named ruleset holding exactly these rules, saturated. -/
  | saturateRules (rs : List Rule)

private def prog (cs : List Src) (check : Query := []) : Program :=
  let (cmds, _) := cs.foldl (fun (acc : List Schedule × List Rule) c => match c with
    | .global a => (acc.1 ++ [.run [⟨[], [a]⟩]], acc.2)
    | .rule r => (acc.1, acc.2 ++ [r])
    | .run => (acc.1 ++ [.run acc.2], acc.2)
    | .saturate => (acc.1 ++ [.saturate (.run acc.2)], acc.2)
    | .saturateRules rs => (acc.1 ++ [.saturate (.run rs)], acc.2)) ([], [])
  ⟨Schedule.seqAll cmds, check⟩

/-! ### Curated cases -/

private def commuteRule : Rule where
  query := [.expr (add (.var "a") (.var "b"))]
  actions := [.union (add (.var "a") (.var "b")) (add (.var "b") (.var "a"))]

private def swapRule : Rule where
  query := [.expr (add (.var "a") (.var "b"))]
  actions := [.expr (add (.var "b") (.var "a"))]

private def detectRule : Rule where
  query := [.eq (.app "Wrapper" [add (C "One") (C "Two")])
                (.app "Wrapper" [add (C "Two") (C "One")])]
  actions := [.expr (.app "Success" [])]

private def assocRule : Rule where
  query := [.expr (add (add (.var "a") (.var "b")) (.var "c"))]
  actions := [.union (add (add (.var "a") (.var "b")) (.var "c"))
                     (add (.var "a") (add (.var "b") (.var "c")))]


private def wrapAtRule (key : Expr) : Rule where
  query := [.expr (.app "Wrapper" [key])]
  actions := [.expr (C "Hit")]


private def wrapHeadRule : Rule where
  query := [.expr (.app "Wrapper" [.var "x"])]
  actions := [.expr (.app "Hit" [.var "x"])]

/-- The same query with a `union` head, so what a failure to fire costs is an *equality*
between two terms both databases hold rather than an e-node. -/
private def wrapUnionAtRule (key : Expr) : Rule where
  query := [.expr (.app "Wrapper" [key])]
  actions := [.union (.app "Wrapper" [key]) (C "Hit")]


private def addAtRule (key : Expr) : Rule where
  query := [.expr (add (key) (.var "b"))]
  actions := [.expr (.app "Mark" [.var "b"])]


private def nestedAtRule (key : Expr) : Rule where
  query := [.expr (.app "Wrapper" [.app "Wrapper" [key]])]
  actions := [.expr (C "Hit")]

/-! #### Source saturation

The `sat-*` cases require rebuilding after every run inside a source saturation, so later
rounds see equalities asserted by earlier ones. `sat-hit` uses a union to enable a rule;
`sat-hit-late` delays that union by one round. Generated programs also exercise this
behavior through `genCollapseRules`. -/

/-- Round 1's rule: asserts the `union` a later round's rule needs. -/
private def unionOnAaRule : Rule where
  query := [.expr (C "Aa")]
  actions := [.union (C "Zz") (C "Aa")]

/-- The rule that needs it. `(Wrapper (Zz))` is the only `Wrapper` the program builds, so
this matches only through the equality the rule above asserts. -/
private def wrapAaHitRule : Rule where
  query := [.expr (.app "Wrapper" [C "Aa"])]
  actions := [.expr (C "Hit")]

/-- A round of delay: `(Kk)` builds `(Mm)`, and only then is the `union` asserted. -/
private def kkMmRule : Rule where
  query := [.expr (C "Kk")]
  actions := [.expr (C "Mm")]

@[inherit_doc kkMmRule]
private def mmUnionRule : Rule where
  query := [.expr (C "Mm")]
  actions := [.union (C "Zz") (C "Aa")]


private def variableFreshCase : List Src :=
  [.rule (wrapAtRule (.var "x")),
   .global (.expr (C "Zz")),
   .global (.expr (.app "Wrapper" [C "Bb"])),
   .run]


private def variableCase : List Src :=
  [.rule (wrapAtRule (.var "x")),
   .global (.expr (C "Zz")),
   .global (.expr (.app "Wrapper" [C "Aa"])),
   .global (.union (C "Zz") (C "Aa")),
   .run]


private def variableHeadCase : List Src :=
  [.rule wrapHeadRule,
   .global (.expr (C "Zz")),
   .global (.expr (.app "Wrapper" [C "Bb"])),
   .run]

/-- The same with a `union` head, so what a missing firing costs is an **equality** between
two terms both databases hold — the shape `Database.UnionsJoined` is stated in. -/
private def variableEqCase : List Src :=
  [.rule (wrapUnionAtRule (.var "x")),
   .global (.expr (C "Zz")),
   .global (.expr (.app "Wrapper" [C "Aa"])),
   .global (.expr (C "Hit")),
   .global (.union (C "Zz") (C "Aa")),
   .run]

private def curatedRaw : List (String × List Src) :=
  [ ("actions",
      [.global (.expr (add (C "One") (C "Two"))),
       .global (.union (C "One") (C "One")),
       .global (.expr (add (C "Two") (C "Three"))),
       .global (.expr (.app "Wrapper" [add (C "Two") (C "Three")]))]),
    ("swap-1", [.global (.expr (add (C "One") (C "Two"))), .rule swapRule, .run]),
    ("swap-2", [.global (.expr (add (C "One") (C "Two"))), .rule swapRule, .run, .run]),
    ("wrapper-1",
      [.global (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run]),
    ("wrapper-2",
      [.global (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run, .run]),
    ("wrapper-3",
      [.global (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run, .run, .run]),
    ("assoc-1",
      [.global (.expr (add (add (C "One") (C "Two")) (C "Three"))), .rule assocRule, .run]),
    ("assoc-2",
      [.global (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .run, .run]),
    ("both-2",
      [.global (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .rule commuteRule, .run, .run]),
    ("seed-2", [.rule ⟨[], [.expr (add (C "One") (C "Two"))]⟩, .run, .run]),
    -- through congruence, the target has no row to read.
    ("ground-lost",
      [.global (.expr (C "Zz")),
       .global (.expr (.app "Wrapper" [C "Aa"])),
       .global (.union (C "Zz") (C "Aa")),
       .rule (wrapAtRule (C "Zz")), .run]),
    -- The same, with the `union` after a run the rule already sat through.
    ("ground-lost-after",
      [.global (.expr (C "Zz")),
       .global (.expr (.app "Wrapper" [C "Aa"])),
       .rule (wrapAtRule (C "Zz")), .run,
       .global (.union (C "Zz") (C "Aa")), .run]),
    -- The head is a `union` and both its terms are built up front, so what a missing firing
    -- costs is an equality between two terms both sides hold.
    ("ground-lost-eq",
      [.global (.expr (C "Zz")),
       .global (.expr (.app "Wrapper" [C "Aa"])),
       .global (.expr (C "Hit")),
       .global (.union (C "Zz") (C "Aa")),
       .rule (wrapUnionAtRule (C "Zz")), .run]),
    ("ground-lost-add",
      [.global (.expr (C "Zz")),
       .global (.expr (add (C "Aa") (C "Cc"))),
       .global (.union (C "Zz") (C "Aa")),
       .rule (addAtRule (C "Zz")), .run]),
    ("ground-lost-nested",
      [.global (.expr (C "Zz")),
       .global (.expr (.app "Wrapper" [.app "Wrapper" [C "Aa"]])),
       .global (.union (C "Zz") (C "Aa")),
       .rule (nestedAtRule (C "Zz")), .run]),
    -- nullary partner because `Term.blt` compares arity first.
    ("ground-lost-app",
      [.global (.expr (add (C "Zz") (C "Cc"))),
       .global (.expr (.app "Wrapper" [C "Aa"])),
       .global (.union (add (C "Zz") (C "Cc")) (C "Aa")),
       .rule (wrapAtRule (add (C "Zz") (C "Cc"))), .run]),
    -- row is an extra row rather than a moved one, so the original survives.
    ("ground-keyed",
      [.global (.expr (C "Zz")),
       .global (.expr (.app "Wrapper" [C "Zz"])),
       .global (.expr (.app "Wrapper" [C "Aa"])),
       .global (.union (C "Zz") (C "Aa")),
       .rule (wrapAtRule (C "Zz")), .run]),
    -- rebuild's column rules carry rows in.
    ("ground-leader",
      [.global (.expr (C "Aa")),
       .global (.expr (.app "Wrapper" [C "Zz"])),
       .global (.union (C "Zz") (C "Aa")),
       .rule (wrapAtRule (C "Aa")), .run]),
    -- A source `saturate`: the `union` lands in round 1 and the rule that needs it fires in
    -- round 2, so the rebuild has to run *between* the rounds.
    ("sat-hit",
      [.global (.expr (.app "Wrapper" [C "Zz"])),
       .global (.expr (C "Aa")),
       .rule unionOnAaRule, .rule wrapAaHitRule, .saturate]),
    -- The same, with the `union` discovered a round later: `wrapAaHitRule` sits through
    -- rounds it cannot fire in before the equality it needs exists at all.
    ("sat-hit-late",
      [.global (.expr (.app "Wrapper" [C "Zz"])),
       .global (.expr (C "Aa")),
       .global (.expr (C "Kk")),
       .rule kkMmRule, .rule mmUnionRule, .rule wrapAaHitRule, .saturate]),
    -- The congruence has to travel up a `Wrapper` between rounds: `commuteRule` asserts the
    -- equality and `detectRule` reads it one level above. `wrapper-3` is the same program
    -- run three times.
    ("sat-wrapper",
      [.global (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .saturate]),
    -- rule was registered: `ground-lost-after`'s shape on the saturating schedule.
    ("sat-ground",
      [.global (.expr (C "Zz")),
       .global (.expr (.app "Wrapper" [C "Aa"])),
       .rule (wrapAtRule (C "Zz")),
       .global (.union (C "Zz") (C "Aa")), .saturate]),
    -- A `run` and a `saturate` in one program, so the maintenance rules the encoding joins
    -- to the unnamed ruleset fire in a plain round too.
    ("sat-after-run",
      [.global (.expr (add (C "One") (C "Two"))),
       .rule swapRule, .rule commuteRule, .run, .saturate]),
    ("variable-fresh", variableFreshCase),
    ("variable-head", variableHeadCase),
    -- readings of the query match and only the *encoding* can lose the firing.
    ("variable", variableCase),
    -- The same with a `union` head, so what a missing firing costs is an equality between two
    -- terms both databases hold — the shape `Database.UnionsJoined` is stated in.
    ("variable-eq", variableEqCase) ]

private def curated : List (String × Program) := curatedRaw.map fun c => (c.1, prog c.2)

-- The emitted egglog parses back to the same program.
set_option linter.hashCommand false in
#guard (Program.ofEgg (prog
    [.global (.expr (add (C "One") (C "Two"))), .rule swapRule, .run, .run]).render).isOk

/-! ### Random cases

A fixed signature — two nullary constructors, one unary, one binary — keeps every
generated program expressible in egglog, where one name may not be used at two arities.
Depths are small on purpose: a rule whose head builds a deep term grows the term set fast,
and the enumerator is |terms| ^ |vars|. -/

private def step (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- A number below `n`, and the advanced seed.

Read off the **high** bits. Bit `k` of a linear congruential generator with a
power-of-two modulus has period `2^(k+1)`, so `s % n` for a small `n` cycles almost
immediately: with `s % 4` every fourth draw agrees, and the generated cases were all
emitting the same `union` because of it. Discarding the low 16 bits is the usual fix. -/
private def pick (n : Nat) (s : Nat) : Nat × Nat :=
  let s := step s
  (s / 65536 % max n 1, s)

/-- A leaf: a nullary constructor, or one of `vars`. -/
private def genLeaf (vars : List Var) (s : Nat) : Expr × Nat :=
  let (i, s) := pick (2 + vars.length) s
  match i with
  | 0 => (C "A", s)
  | 1 => (C "B", s)
  | k => (.var (vars.getD (k - 2) "a"), s)

/-- A ground expression of depth at most `d`. -/
private def genGround : Nat → Nat → Expr × Nat
  | 0, s => genLeaf [] s
  | d + 1, s =>
    let (i, s) := pick 4 s
    match i with
    | 2 =>
      let (e, s) := genGround d s
      (.app "F" [e], s)
    | 3 =>
      let (e₁, s) := genGround d s
      let (e₂, s) := genGround d s
      (.app "G" [e₁, e₂], s)
    | _ => genLeaf [] s

/-- An expression of depth at most `d` whose leaves may be any of `vars`.

Weighted **towards building** rather than uniformly, at one leaf to two `F` to one `G`.
This is what a rule head is drawn from, so it is what decides whether a round's firings
grow the term set or just permute it: the cases worth having are the ones where a rule
matching everything builds a nested term and the next round matches that. Over the default
60 seeds the weighting takes the spread from 32 distinct row-count profiles to 38. -/
private def genOver (vars : List Var) : Nat → Nat → Expr × Nat
  | 0, s => genLeaf vars s
  | d + 1, s =>
    let (i, s) := pick 4 s
    match i with
    | 1 | 2 =>
      let (e, s) := genOver vars d s
      (.app "F" [e], s)
    | 3 =>
      let (e₁, s) := genOver vars d s
      let (e₂, s) := genOver vars d s
      (.app "G" [e₁, e₂], s)
    | _ => genLeaf vars s

/-- An expression whose top is a constructor application.

The model admits a bare variable as a query fact or as an `expr` action — it matches, or
adds, any term — where egglog's grammar does not. The fragment is therefore not a subset
of egglog's language, and the generator has to stay inside the overlap. -/
private def genApp (vars : List Var) (d : Nat) (s : Nat) : Expr × Nat :=
  -- Weighted away from a nullary top: `(A)` as a query matches at most one term, so a
  -- program full of them exercises almost nothing.
  let (i, s) := pick 6 s
  match i with
  | 0 => genLeaf [] s
  | 1 | 2 =>
    let (e, s) := genOver vars d s
    (.app "F" [e], s)
  | _ =>
    let (e₁, s) := genOver vars d s
    let (e₂, s) := genOver vars d s
    (.app "G" [e₁, e₂], s)

mutual

/-- Replace some subterms with variables. -/
private def abstractExpr (vars : List Var) : Expr → Nat → Expr × Nat
  | .app f args, s =>
    let (i, s) := pick 3 s
    match i, vars with
    | 0, v :: vs =>
      let (j, s) := pick (v :: vs).length s
      (.var ((v :: vs).getD j v), s)
    | _, _ =>
      let (args, s) := abstractArgs vars args s
      (.app f args, s)
  | e, s => (e, s)

private def abstractArgs (vars : List Var) : List Expr → Nat → List Expr × Nat
  | [], s => ([], s)
  | e :: es, s =>
    let (e, s) := abstractExpr vars e s
    let (es, s) := abstractArgs vars es s
    (e :: es, s)

end

/-- A pattern got by abstracting some subterms of `src` into variables, keeping `src`'s
root constructor.

Abstracting a term the program actually builds is what makes the rule fire: a freely
generated pattern of this shape almost never matches anything, which showed up as most
generated programs producing no rows beyond their seeded terms. Keeping the root is what
keeps it a legal egglog fact. -/
private def genPattern (vars : List Var) (src : Expr) (s : Nat) : Expr × Nat :=
  match src with
  | .app f args =>
    let (args, s) := abstractArgs vars args s
    (.app f args, s)
  | e => (e, s)

/-- A rule whose body is abstracted from `src`. The head is built only over variables the
body binds, so every generated program is well-scoped and neither engine rejects it. -/
private def genRule (src : Expr) (s : Nat) : Rule × Nat :=
  let (shape, s) := pick 3 s
  let (p, s) := genPattern ["a", "b"] src s
  match shape with
  | 0 =>
    -- one pattern, head builds a term
    let (a, s) := genApp p.vars 2 s
    (⟨[.expr p], [.expr a]⟩, s)
  | 1 =>
    -- one pattern, head unions two terms; `union` operands may be bare variables
    let (a₁, s) := genOver p.vars 2 s
    let (a₂, s) := genOver p.vars 2 s
    (⟨[.expr p], [.union a₁ a₂]⟩, s)
  | _ =>
    -- an equality body, so matching has to go through congruence
    let (q, s) := genPattern ["a", "b"] src s
    let (a, s) := genApp (p.vars ∪ q.vars) 2 s
    (⟨[.eq p q], [.expr a]⟩, s)

/-- Generate a terminating saturation test from the root's first argument.
The first rule unions a match with `(Sat)`; the second builds `(Hit)` using that equality
in a later round. A single variable bounds enumeration cost. Leaves return `none`. -/
private def genCollapseRules : Expr → Option (List Rule)
  | .app f (_ :: args) =>
    some [⟨[.expr (.app f (.var "a" :: args))], [.union (.var "a") (C "Sat")]⟩,
          ⟨[.expr (.app f (C "Sat" :: args))], [.expr (C "Hit")]⟩]
  | _ => none

private def genProgram (s : Nat) : List Src :=
  let (g₁, s) := genGround 2 s
  let (g₂, s) := genGround 3 s
  let (g₃, s) := genGround 3 s
  let (r₁, s) := genRule g₂ s
  let (r₂, s) := genRule g₃ s
  let (rounds, s) := pick 3 s
  -- **Sometimes a source `saturate`**, drawn after everything else so that the rest of a
  -- seed's program is independent of this choice. `encodeScheduleWith` compiles it structurally,
  -- and nothing else in the corpus but the `sat-*` cases reaches it.
  let (wantSat, s) := pick 2 s
  let sat := match wantSat, genCollapseRules g₂ with
    | 0, some rs => [Src.saturateRules rs]
    | _, _ => []
  -- egglog panics on registering one rule twice. Compare the rendered form, there being no
  -- decidable equality on `Rule`.
  let rules := if r₁.toEgg = r₂.toEgg then [Src.rule r₁] else [Src.rule r₁, Src.rule r₂]
  [.global (.expr g₁), .global (.expr g₂), .global (.expr g₃)] ++ sat ++ rules
    ++ List.replicate (rounds + 1) Src.run

/-! ### The whole corpus

The cases `semantics/difftest.sh` runs, as data rather than as files, so that a harness which
does not go through egglog can reuse them. The random family is drawn at the script's
default `RANDOM_CASES`, and the seed is `k + 1` exactly as `main`'s `seed` mode computes it. -/

/-- The 60 random constructor-fragment cases. -/
private def randomCases : List (String × Program) :=
  (List.range 60).map fun k => (s!"rand-{k}", prog (genProgram (k + 1)))

/-- Every case the difftest runs, in the order the script writes them. -/
private def allCases : List (String × Program) :=
  curated ++ randomCases

set_option linter.hashCommand false in
#guard curated.length = 27
set_option linter.hashCommand false in
#guard allCases.length = 87

/-! Three cases small enough to pin the encoding's behaviour at compile time. None has a
rule, so none runs the enumerator, whose cost is `|terms| ^ |vars|`. -/

/-- One construction and nothing else. -/
private def buildCase : List Src := [.global (.expr (add (C "One") (C "Two")))]

/-- Two applications made congruent by a `union`, and nothing else — the smallest program
whose congruence rule has to fire. -/
private def unionCase : List Src :=
  [.global (.expr (add (C "One") (C "Two"))),
   .global (.expr (add (C "Two") (C "One"))),
   .global (.union (C "One") (C "Two"))]

/-- `unionCase` under a `Wrapper`, so the congruence the `union` creates has to travel
**up** a level. The harness's negative control: it is the same three commands and it does
not agree. -/
private def upCase : List Src :=
  [.global (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
   .global (.expr (.app "Wrapper" [add (C "Two") (C "One")])),
   .global (.union (C "One") (C "Two"))]

/-- `upCase` with unary constructors: congruence must propagate through two levels. -/
private def upThinCase : List Src :=
  [.global (.expr (.app "H" [.app "F" [C "A"]])),
   .global (.expr (.app "H" [.app "F" [C "B"]])),
   .global (.union (C "A") (C "B"))]

/-! Literal probes run only in Lean. egglog's `i64` is a separate primitive sort, whereas
`Term.lit` shares the model's term type with applications. These probes exercise `Repr` on
source literal children and are excluded from the corpus passed to `writeCase`. -/

/-- A literal the encoding also mints (`unitE` is `0`) is absent from this source. -/
private def litCase : List Src := [.global (.expr (add (.lit (.int 1)) (.lit (.int 2))))]

/-- The same, with `0` among the source's own literals. -/
private def litZeroCase : List Src := [.global (.expr (add (.lit (.int 0)) (.lit (.int 1))))]

/-! ### Union-find probes

`Congruence.sameClassF` requires each term to read to exactly one root and the roots to
agree. These probes cover union chains in both directions, differing term depths,
congruence across several levels, representative ordering, unions across source rounds,
and rejection of literal unions. Literal probes are Lean-only; the constructor cases
exercise readings checked by the congruence gate.
-/

/-- `Wrapper` applied `n` times. -/
private def wrap : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => .app "Wrapper" [wrap n e]

/-- A three-link union chain under two wrappers. The initial-fact runs each rebuild;
there is no additional source rule run. `Term.blt` selects `A`, while the unions write
`D → C`, `C → B`, and `B → A`, requiring path compression. -/
private def chainCase : List Src :=
  [.global (.expr (.app "Wrapper" [C "A"])),
   .global (.expr (.app "Wrapper" [C "D"])),
   .global (.union (C "C") (C "D")),
   .global (.union (C "B") (C "C")),
   .global (.union (C "A") (C "B"))]

/-- The same chain in the opposite order, so each `union` lands below the standing
representative and every edge already recorded has to be re-pointed. -/
private def chainDownCase : List Src :=
  [.global (.expr (.app "Wrapper" [C "A"])),
   .global (.expr (.app "Wrapper" [C "D"])),
   .global (.union (C "A") (C "B")),
   .global (.union (C "B") (C "C")),
   .global (.union (C "C") (C "D"))]

/-- Endpoints at different term depths: a leaf `union`ed with a one-level application, both
ways round. A nullary constructor sorts below a unary application in `Term.blt`, so the
leaf is the representative both times and the application is what gains a parent. -/
private def depthCase : List Src :=
  [.global (.expr (wrap 2 (C "A"))),
   .global (.expr (wrap 2 (C "B"))),
   .global (.union (C "A") (.app "Wrapper" [C "B"])),
   .global (.union (C "B") (.app "Wrapper" [C "A"]))]

/-- Congruence propagates through three levels above a unioned leaf, creating union-find
edges in successive rebuild rounds. -/
private def towerCase : List Src :=
  [.global (.expr (wrap 3 (C "A"))),
   .global (.expr (wrap 3 (C "B"))),
   .global (.union (C "A") (C "B"))]

/-- A `union` whose representative is the *deeper* term: `Term.blt` compares argument
count first, so `(Wrapper Z)` sorts below `(Add A B)` and `ordering-min` puts the
representative one level down. The second `union` then moves its own child. -/
private def orderCase : List Src :=
  [.global (.expr (.app "Wrapper" [C "Z"])),
   .global (.expr (add (C "A") (C "B"))),
   .global (.union (.app "Wrapper" [C "Z"]) (add (C "A") (C "B"))),
   .global (.union (C "Z") (C "A"))]

/-- `(Wrapper (Add a b)) = (Wrapper (One))` off a commuted `Add`: the premise holds only
after `commuteRule` has fired, so this `union`'s `@UF` edge lands a round later, on a
union-find the previous round's rebuild already compressed. -/
private def liftRule : Rule where
  query := [.eq (add (.var "a") (.var "b")) (add (.var "b") (.var "a"))]
  actions := [.union (.app "Wrapper" [add (.var "a") (.var "b")])
                     (.app "Wrapper" [C "One"])]

/-- `liftRule` over a wrapped `Add`, run twice. -/
private def roundCase : List Src :=
  [.global (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
   .global (.expr (.app "Wrapper" [C "One"])),
   .rule commuteRule, .rule liftRule, .run, .run]

/-- A literal-union rejection probe: `unionCase` with literal endpoints. `execAction`
rejects the union, so source execution is stuck. -/
private def litUnionCase : List Src :=
  [.global (.expr (add (.lit (.int 1)) (.lit (.int 2)))),
   .global (.expr (add (.lit (.int 2)) (.lit (.int 1)))),
   .global (.union (.lit (.int 1)) (.lit (.int 2)))]

/-- One literal operand is refused too, not just two, which is what keeps every `@UF` key
an application. -/
private def litMixCase : List Src :=
  [.global (.expr (add (.lit (.int 1)) (C "One"))),
   .global (.union (.lit (.int 1)) (add (.lit (.int 1)) (C "One")))]

/-- The probes, reachable from `difftest encode <fuel> <name>` by name. The `-run` variants
append one empty round, which is what makes `encode` emit a `Cmd.saturate rebuildRuleset` and
so the only way to ask whether the rebuild repairs the gap `upCase` shows. They are out of
the guards because running a rebuild is far too slow to sit in a build. -/
private def probeCasesRaw : List (String × List Src) :=
  [("build", buildCase), ("union", unionCase),
   ("up", upCase), ("up-run", upCase ++ [.run]),
   ("up-thin", upThinCase), ("up-thin-run", upThinCase ++ [.run]),
   ("lit", litCase), ("lit-zero", litZeroCase),
   ("chain", chainCase), ("chain-run", chainCase ++ [.run]),
   ("chain-down", chainDownCase), ("depth", depthCase),
   ("tower", towerCase), ("order", orderCase), ("round", roundCase),
   ("lit-union", litUnionCase), ("lit-mix", litMixCase)]

@[inherit_doc probeCasesRaw]
private def probeCases : List (String × Program) := probeCasesRaw.map fun c => (c.1, prog c.2)

namespace Egglog
/-- The source fragment, decided: the programs the congruence and provenance gates run. -/
def Program.encodeDomainB (p : Program) : Bool := decide p.Fragment

/-- The checker's fragment, decided: the programs whose proofs lift to source proofs. -/
def Program.proofDomainB (p : Program) : Bool := decide (SourceProof.Fragment p)

/-! #### Running the compiled program

`Congruence.encode` follows every run by a rebuild saturation, so a compiled program is
outside `Program.NoSaturate` and `exec` is fuel-bounded, answering `none` on exhaustion.
`execAt` takes the fuel as an argument so that the corpus can raise it. -/
/-- `exec` with the saturation fuel supplied by the caller. -/
def execAt (fuel : Nat) (d : FDatabase) (S : Schedule) : Option FDatabase :=
  execSchedule fuel d S

/-- **At `runFuel` it is `exec`**, so raising the fuel is the only thing the parameter does. -/
theorem execAt_runFuel (P : Program) : execAt runFuel FDatabase.empty P.schedule = exec P := rfl

end Egglog

/-! ### The slotted corpus

`difftest slotted-parse <dir>…` reads every `.egg` under the directories with the slotted
parser (`Slotted/Tests/Parse.lean`) and reports the files it accepts, with their check
counts, and the files it skips, with the unsupported form. It fails when nothing is accepted
or when a file under a `paper/` directory is skipped: those port the slotted e-graphs paper's
examples and must stay in the subset. -/

private def runSlottedParse (dirs : List String) : IO UInt32 := do
  let mut files : Array System.FilePath := #[]
  for d in dirs do
    let ps ← System.FilePath.walkDir d
    files := files ++ ps.filter fun p => p.extension == some "egg"
  let sorted := files.qsort fun a b => a.toString < b.toString
  let mut accepted := 0
  let mut cases := 0
  let mut skipped := 0
  let mut paperSkipped := 0
  for f in sorted do
    let src ← IO.FS.readFile f
    match Slotted.parseFile src with
    | .ok cs =>
      accepted := accepted + 1
      cases := cases + cs.length
      IO.println s!"ACCEPT {f}: {cs.length} checks"
    | .error e =>
      skipped := skipped + 1
      if (f.toString.splitOn "/paper/").length > 1 then paperSkipped := paperSkipped + 1
      IO.println s!"SKIP {f}: {e}"
  IO.println s!"slotted-parse: {accepted} of {sorted.size} files accepted, {cases} checks, \
    {skipped} skipped"
  return if accepted > 0 && paperSkipped == 0 then 0 else 1

/-! ### The slotted corpus, evaluated

`difftest slotted-bounded <file>…` parses each file and runs every check with the bounded
evaluator (`Slotted/Tests/Bounded.lean`) over the slot universe of the program's literal
slots plus enough fresh names for action-only slots and α-variants, comparing the outcome
with the one the file asserts, which `slotted-difftest.sh` first confirms against the Rust
reference. A check the evaluator cannot decide within its fuel is reported, not failed. -/

/-- The literal names an expression mentions and its slot identifiers. -/
private partial def exprSlots : Expr → List Slotted.Slot × List Var
  | .app f [] => if Slotted.isSlotName f then ([f], []) else ([], [])
  | .app _ args =>
    args.foldl (fun acc e => let (cs, vs) := exprSlots e; (acc.1 ++ cs, acc.2 ++ vs)) ([], [])
  | .var v => if Slotted.isSlotVar v then ([v], [v]) else ([], [])
  | .min a b => let (c₁, v₁) := exprSlots a; let (c₂, v₂) := exprSlots b; (c₁ ++ c₂, v₁ ++ v₂)
  | .lit _ => ([], [])

private def patternSlots : Pattern → List Slotted.Slot × List Var
  | .expr e => exprSlots e
  | .eq a b | .ne a b => let (c₁, v₁) := exprSlots a; let (c₂, v₂) := exprSlots b; (c₁ ++ c₂, v₁ ++ v₂)

private def actionSlots : Action → List Slotted.Slot × List Var
  | .expr e => exprSlots e
  | .union a b => let (c₁, v₁) := exprSlots a; let (c₂, v₂) := exprSlots b; (c₁ ++ c₂, v₁ ++ v₂)
  | .subsume _ es =>
    es.foldl (fun acc e => let (cs, vs) := exprSlots e; (acc.1 ++ cs, acc.2 ++ vs)) ([], [])

/-- The slot universe: all written names, plus fresh names for action-only slots and
α-variants. Query literals must occur by their actual names in this universe. -/
private def slotUniverse (P : Egglog.Program) : List Slotted.Slot :=
  let ruleSlots := P.rules.map fun r =>
    let qs := r.query.map patternSlots
    let as := r.actions.map actionSlots
    ((qs ++ as).flatMap Prod.fst, ((qs ++ as).flatMap Prod.snd).dedup.length)
  let checkSlots := ((P.check.map patternSlots).flatMap Prod.fst,
    ((P.check.map patternSlots).flatMap Prod.snd).dedup.length)
  let all := checkSlots :: ruleSlots
  let concrete := (all.flatMap Prod.fst).dedup
  let extra := (all.map Prod.snd).foldl max 0 + 2
  concrete ++ ((List.range extra).map fun i => s!"$fresh{i}").filter (· ∉ concrete)

private def runSlottedBounded (files : List String) : IO UInt32 := do
  let mut agree := 0
  let mut disagree := 0
  let mut undecided := 0
  let mut skipped := 0
  for f in files do
    let src ← IO.FS.readFile f
    match Slotted.parseFile src with
    | .error e => skipped := skipped + 1; IO.println s!"SKIP {f}: {e}"
    | .ok cases =>
      for c in cases do
        let S := slotUniverse c.program.plain
        let t0 ← IO.monoMsNow
        let outcome := Slotted.Bounded.observe S c.program 8
        let asserted := c.expected == .ok
        let t1 ← IO.monoMsNow
        match outcome with
        | none =>
          undecided := undecided + 1
          IO.println s!"UNDECIDED {f}#{c.index}: fuel exhausted ({t1 - t0} ms, {S.length} slots)"
        | some b =>
          if b == asserted then
            agree := agree + 1
            IO.println s!"AGREE {f}#{c.index}: {b} ({t1 - t0} ms, {S.length} slots)"
          else
            disagree := disagree + 1
            IO.println s!"DISAGREE {f}#{c.index}: bounded {b}, asserted {asserted} \
              ({t1 - t0} ms, {S.length} slots)"
  IO.println s!"slotted-bounded: {agree} agree, {disagree} disagree, {undecided} undecided, \
    {skipped} files skipped"
  return if disagree == 0 && agree > 0 then 0 else 1

/-! ### Entry point -/


/-- Write a source program for egglog, with `min` spelled `ordering-min`, egglog's minimum
on an eq-sort, its final check asserted with the outcome the interpreter predicts for it in
egglog's check semantics (`FDatabase.holdsWith true`, which sees subsumed rows), and the
row counts the interpreter predicts for it. -/
private def writeCase (dir name : String) (p : Program) : IO Unit := do
  unless p.arityConflicts.isEmpty do
    throw <| IO.userError
      s!"difftest: {name} uses {p.arityConflicts} at more than one arity, which egglog \
         rejects with \"Function already bound\""
  let result := exec p
  let check := result.map fun d => d.holdsWith true p.check
  IO.FS.writeFile s!"{dir}/{name}.egg" ((p.toEgg check).replace "(min " "(ordering-min ")
  IO.FS.writeFile s!"{dir}/{name}.expected" (p.expectedSizesOf result)

/-- Write a compiled program for egglog, with `min` on ids spelled `ordering-min` and the
generated `@` namespace, which egglog reserves, spelled `at_`, and the row counts the
general interpreter predicts for it. -/
private def writeCompiled (dir name : String) (q : Program) : IO Unit := do
  unless q.arityConflicts.isEmpty do
    throw <| IO.userError s!"difftest: compiled {name} uses {q.arityConflicts} at two arities"
  IO.FS.writeFile s!"{dir}/{name}.egg"
    ((q.toEgg.replace "(min " "(ordering-min ").replace "@" "at_")
  IO.FS.writeFile s!"{dir}/{name}.expected" (q.expectedSizes.replace "@" "at_")

/-! ### Egg files

Hand-written programs under `tests/`, in egglog syntax. Each is a corpus case for every
gate, and `difftest egg` snapshots its congruence encoding, its provenance encoding, and
its lifted source proofs next to it. -/

private def eggDir : System.FilePath := "tests"

private def eggSnapshots : List String := ["congruence.egg", "provenance.egg", "proofs.txt"]

/-- The `.egg` programs under `tests/`, by file stem, in name order. -/
private def fileCases : IO (List (String × Program)) := do
  if !(← eggDir.pathExists) then return []
  let entries ← eggDir.readDir
  let stems := entries.filterMap fun e =>
    let name := e.fileName
    if name.endsWith ".egg" && !(eggSnapshots.any fun s => name.endsWith ("." ++ s)) then
      some (String.ofList (name.toList.take (name.length - 4)))
    else none
  (stems.qsort (fun a b => decide (a < b))).toList.mapM fun stem => do
    let src ← IO.FS.readFile (eggDir / s!"{stem}.egg")
    match Program.ofEgg src with
    | .ok p => pure (stem, p)
    | .error e => throw (IO.userError s!"tests/{stem}.egg: {e}")

/-- Run the target with structural equality and the corpus's saturation fuel. -/
private def relationalExecAt (fuel : Nat) (d : FDatabase) (S : Schedule) : Option FDatabase :=
  Relational.execSchedule fuel d S

/-- Every stored equation is reflexive: the target asserted no union. -/
private def eqsReflB (d : FDatabase) : Bool := d.eqs.all fun p => p.1 == p.2

/-- The term list is closed under subterms. -/
private def subtermClosedB (d : FDatabase) : Bool :=
  d.terms.all fun t => t.subtermList.all fun s => d.terms.contains s

/-- `difftest trace <fuel> <case>`: run the instrumented compilation of a case with the
relational runtime, reporting the state's size and the time after every command and every
saturation round. For finding out where an instrumented program spends its time. -/
private def traceInstrumented (fuel : Nat) (p : Program) : IO Unit := do
  IO.eprintln "  compiling"
  let q := Congruence.encode p
  IO.eprintln s!"  compiled: {q.schedule.topLevel.length} commands, {q.rules.length} rules"
  let some inst := Provenance.encode q | IO.println "provenance pass rejected input"
  let rounds (rs : List Rule) (d : FDatabase) : IO (Option FDatabase) := do
    let mut d := d
    for i in [0:fuel] do
      let t0 ← IO.monoMsNow
      let e := Relational.runRules rs d
      let n := e.terms.length
      let t ← IO.monoMsNow
      let same := d.sameData e
      IO.eprintln s!"      round {i}: terms {n} rows {e.rows.length} ({t - t0} ms)"
      if same then return some e
      d := e
    return none
  let mut d := FDatabase.empty
  for c in inst.schedule.topLevel do
    match c with
    | .saturate (.run rs) =>
      IO.eprintln s!"    saturate {rs.length} rules"
      match ← rounds rs d with
      | some d' => d := d'
      | none => IO.println "    fuel exhausted"; return
    | S =>
      let t0 ← IO.monoMsNow
      match Relational.execSchedule fuel d S with
      | none => IO.println "    stuck or fuel exhausted"; return
      | some d' =>
        let n := d'.terms.length
        let t ← IO.monoMsNow
        IO.eprintln s!"    schedule over {S.rules.length} rules -> terms {n} rows {d'.rows.length} ({t - t0} ms)"
        d := d'
  IO.println s!"  data rows {(Provenance.dataRows q d.terms).length}, firings {(Provenance.firings q d.terms).length}, check {Relational.holds d inst.check}"

/-- `difftest paper-proof <file.egg> [--elide]`: the proof of the file's final check in the
paper's notation, simplified for presentation and checked again, on stdout. -/
private def paperProof (src : String) (e : PaperTex.Elision) : IO UInt32 := do
    let text ← IO.FS.readFile src
    match Program.ofEgg text with
    | .error e => IO.eprintln s!"difftest: {src}: {e}"; return 1
    | .ok p =>
      let some pfs := Resugar.prove
          (fun Q => relationalExecAt runFuel FDatabase.empty Q.schedule) p
        | IO.eprintln "difftest: no proof of the check"; return 1
      -- Simplified for presentation, and checked again.
      for pf in pfs do
        let simple := pf.simplify p
        let shown := if SourceProof.check p simple == some pf.claim then simple else pf
        IO.print (PaperTex.proof p shown e)
      return 0

/-- `difftest time <fuel> <case>`: time the stages of the congruence gate, and run the
source schedule pass by pass under the general interpreter, reporting the state's size. -/
private def timeCase (fuel : Nat) (p : Program) : IO Unit := do
  let q := Congruence.encode p
  let stage (label : String) (f : Unit → Option FDatabase) : IO (Option FDatabase) := do
    let t0 ← IO.monoMsNow
    let r := f ()
    let n := r.map (·.terms.length)
    let t ← IO.monoMsNow
    IO.println s!"  {label}: {t - t0} ms, terms {n}"
    pure r
  -- The source, top-level command by command; a saturation pass by pass.
  let mut d := FDatabase.empty
  for S in p.schedule.topLevel do
    match S with
    | .saturate body =>
      IO.println "  source saturate:"
      let mut cur := d
      let mut done := false
      for i in [0:fuel] do
        if done then break
        match ← stage s!"    pass {i}" (fun _ => execSchedule fuel cur body) with
        | none => IO.println "    body stuck"; return
        | some e =>
          if cur.sameData e then done := true
          cur := e
      d := cur
    | S =>
      match ← stage "  source command" (fun _ => execSchedule fuel d S) with
      | none => IO.println "  stuck"; return
      | some e => d := e
  let _ ← stage "  source check" (fun _ => if d.holds p.check then some d else none)
  let tgt ← stage "  target (general)" (fun _ => execSchedule fuel FDatabase.empty q.schedule)
  let plain ← stage "  target (relational)"
    (fun _ => Relational.execSchedule fuel FDatabase.empty q.schedule)
  if let some e := tgt then
    for k in [1:q.check.length + 1] do
      let _ ← stage s!"  target check (general) on {k} atoms: {(q.check.take k).map Pattern.toEgg}"
        (fun _ => if e.holds (q.check.take k) then some e else none)
    let _ ← stage "  readings" (fun _ =>
      let cl := d.closureF
      let readings := d.terms.map fun t => (t, Congruence.idF e t)
      if readings.any (fun (a, ia) => readings.any fun (b, ib) =>
          decide ((a, b) ∈ cl) != (ia.isSome && ia == ib)) then none else some e)
  if let some e := plain then
    let _ ← stage "  target check (relational)"
      (fun _ => if Relational.holds e q.check then some e else none)

/-- Compare the compiled program's reading of every pair of source terms against source
congruence, and its execution with and without equality reasoning. `o` selects the
compiler's optimizations; the reading goes through the union-find either way. -/
private def congruenceCheck (fuel : Nat) (o : Congruence.Options) (p : Program) :
    List String := Id.run do
  let compiled := Congruence.compileWith o p
  let q := compiled.program
  let mut errors : List String := []
  if !q.arityConflicts.isEmpty then errors := errors ++ ["conflicting target arities"]
  -- One origin per compiled rule.
  if compiled.origins.length != q.rules.length then errors := errors ++ ["origins misaligned"]
  match execAt fuel FDatabase.empty p.schedule, execAt fuel FDatabase.empty q.schedule with
  | some src, some tgt =>
    match relationalExecAt fuel FDatabase.empty q.schedule with
    | none => errors := errors ++ ["relational target stuck or exhausted fuel"]
    | some plain =>
      if !plain.sameData tgt then
        errors := errors ++ ["target depends on implicit equality reasoning"]
    if !eqsReflB tgt || !subtermClosedB tgt then
      errors := errors ++ ["target violates reader assumptions"]
    let cl := src.closureF
    let readings := src.terms.map fun t => (t, Congruence.idF tgt t)
    if readings.any (fun (a, ia) => readings.any fun (b, ib) =>
        decide ((a, b) ∈ cl) != (ia.isSome && ia == ib)) then
      errors := errors ++ ["source equality mismatch"]
    -- The final check is the observed behavior; both sides must agree on it.
    if src.holds p.check != tgt.holds q.check then
      errors := errors ++ ["check outcome differs"]
  | none, _ => errors := errors ++ ["source stuck or exhausted fuel"]
  | _, none => errors := errors ++ ["congruence target stuck or exhausted fuel"]
  return errors

/-- Leading encoding options; source subsumption is also detected automatically. -/
private def parseOptions : List String → Congruence.Options × List String
  | "--views=naive" :: rest =>
      let (o, names) := parseOptions rest
      ({ o with views := .naive }, names)
  | "--views=indexed" :: rest =>
      let (o, names) := parseOptions rest
      ({ o with views := .indexed }, names)
  | "--subsumption" :: rest =>
      let (o, names) := parseOptions rest
      ({ o with subsumption := true }, names)
  | "--phased" :: rest =>
      let (o, names) := parseOptions rest
      ({ o with phased := true }, names)
  | rest => ({}, rest)

private def runCongruenceChecks (fuel : Nat) (o : Congruence.Options) (names : List String) :
    IO UInt32 := do
  let files ← fileCases
  let available := allCases ++ files ++ probeCases
  let unknown := names.filter fun name => !(available.any fun c => c.1 == name)
  unless unknown.isEmpty do
    IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
    return 1
  let cases := if names.isEmpty then allCases ++ files else available.filter fun c => names.contains c.1
  let mut tested := 0
  let mut failed := 0
  let mut skipped := 0
  for (name, p₀) in cases do
    let p := p₀
    if !p.encodeDomainB then
      skipped := skipped + 1
      continue
    tested := tested + 1
    let errors := congruenceCheck fuel o p
    unless errors.isEmpty do
      failed := failed + 1
      IO.println s!"FAIL {name}: {String.intercalate "; " errors}"
  IO.println s!"congruence: {tested} tested, {failed} failures, {skipped} outside domain"
  return if failed == 0 && tested > 0 then 0 else 1

/-- Exercise lifting with the origins of an explicitly selected compilation. The public
`Resugar.lift` is also tested below against the default compilation. -/
private def checkedLiftFor (p : Program) (compiled : Congruence.Compiled)
    (pf : SourceProof.Proof) : Option SourceProof.Proof := do
  if !SourceProof.sourceOk p then none else do
    let fact ← Provenance.check compiled.program pf
    let wanted ← Resugar.factClaim p fact
    let result ← Resugar.liftProof p compiled.origins pf
    if SourceProof.check p result == some wanted then some result else none

private def provenanceCheck (fuel : Nat) (p : Program) (liftProofs : Bool)
    (forceSubsumption : Bool := false) : List String := Id.run do
  let compiled := Congruence.compileWith { subsumption := forceSubsumption } p
  let q := compiled.program
  let some encoded := Provenance.encode q | return ["provenance pass rejected input"]
  let some original := relationalExecAt fuel FDatabase.empty q.schedule |
    return ["congruence program stuck or exhausted fuel"]
  let some annotated := relationalExecAt fuel FDatabase.empty encoded.schedule |
    return ["instrumented program stuck or exhausted fuel"]
  let mut errors : List String := []
  if !Provenance.unionFree encoded then errors := errors ++ ["provenance introduced union"]
  -- Without its log, the instrumented state is the original state.
  if (Provenance.eraseLog annotated.terms).toFinset != original.terms.toFinset then
    errors := errors ++ ["states differ without the log"]
  if annotated.subsumed.toFinset != original.subsumed.toFinset then
    errors := errors ++ ["subsumed rows differ after instrumentation"]
  if Relational.holds original q.check != Relational.holds annotated encoded.check then
    errors := errors ++ ["check outcome differs after instrumentation"]
  let proofs := Provenance.rowProofs q annotated.terms
  let bad := proofs.filter fun tp => match tp.2 with
    | none => true
    | some pf => liftProofs &&
        (if forceSubsumption then checkedLiftFor p compiled pf else Resugar.lift p pf).isNone
  if !bad.isEmpty then
    errors := errors ++ [s!"{bad.length}/{proofs.length} rows without a proof"]
  return errors

private def runProvenanceChecks (fuel : Nat) (names : List String)
    (liftProofs : Bool := false) : IO UInt32 := do
  let files ← fileCases
  let available := allCases ++ files ++ probeCases
  let unknown := names.filter fun name => !(available.any fun c => c.1 == name)
  unless unknown.isEmpty do
    IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
    return 1
  let cases := if names.isEmpty then allCases ++ files else available.filter fun c => names.contains c.1
  let mut tested := 0
  let mut failed := 0
  let mut skipped := 0
  let mut nodeTested := 0
  for (name, p₀) in cases do
    let p := p₀
    if !p.encodeDomainB || (liftProofs && !p.proofDomainB) then
      skipped := skipped + 1
      continue
    tested := tested + 1
    let mut errors := provenanceCheck fuel p liftProofs
    -- The checker excludes source subsumption, so explicitly retain nodes on plain
    -- sources to exercise both representations in the lifting gate as well.
    if p.schedule.subsumeFreeB then
      nodeTested := nodeTested + 1
      errors := errors ++ (provenanceCheck fuel p liftProofs true).map ("node encoding: " ++ ·)
    unless errors.isEmpty do
      failed := failed + 1
      IO.println s!"FAIL {name}: {String.intercalate "; " errors}"
  let label := if liftProofs then "resugar" else "provenance"
  IO.println s!"{label}: {tested} tested, {failed} failures, {skipped} outside domain"
  IO.println s!"{label}: {nodeTested} additional node encodings checked"
  return if failed == 0 && tested > 0 then 0 else 1

private def firstDifference (expected actual : String) : String :=
  let es := expected.splitOn "\n"
  let as := actual.splitOn "\n"
  match (List.range (max es.length as.length)).find? fun i => es[i]? != as[i]? with
  | some i =>
    s!"line {i + 1}: expected `{(es[i]?).getD "<end>"}`, got `{(as[i]?).getD "<end>"}`"
  | none => "identical"

/-- Check the parser against the emitter on the whole corpus. -/
private def parseRoundTrip : List String :=
  allCases.filterMap fun c =>
    let src := c.2.toEgg
    match Program.ofEgg src with
    | .ok p => if p.toEgg == src then none else some c.1
    | .error e => some s!"{c.1} ({e})"

/-- Snapshot the encodings and lifted proofs of every program under `tests/`, or rewrite
the snapshots when `update` is set, and run the corpus gates on each. -/
private def runEggChecks (fuel : Nat) (update : Bool) (names : List String) : IO UInt32 := do
  let files ← fileCases
  let unknown := names.filter fun name => !(files.any fun c => c.1 == name)
  unless unknown.isEmpty do
    IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
    return 1
  let selected := if names.isEmpty then files else files.filter fun c => names.contains c.1
  let mut failed := 0
  unless parseRoundTrip.isEmpty do
    failed := failed + 1
    IO.println s!"FAIL parse round trip: {String.intercalate ", " parseRoundTrip}"
  for (name, p) in selected do
    let mut errors : List String := []
    if !p.encodeDomainB then errors := ["outside the correspondence domain"]
    else
      let congruence := Congruence.encode p
      -- A program outside the checker's fragment has encodings but no lifted proofs.
      let snapshots : List (String × Option String) :=
        [("congruence.egg", some congruence.render),
         ("provenance.egg", (Provenance.encode congruence).map Program.render)] ++
        (if p.proofDomainB then
          [("proofs.txt", (Resugar.certificates
            (fun Q => relationalExecAt fuel FDatabase.empty Q.schedule) p).map
            Resugar.renderProofs)]
         else [])
      for (suffix, text) in snapshots do
        let path := eggDir / s!"{name}.{suffix}"
        match text with
        | none => errors := errors ++ [s!"{suffix} not produced"]
        | some text =>
          if update then IO.FS.writeFile path text
          else if !(← path.pathExists) then errors := errors ++ [s!"{suffix} missing"]
          else
            let expected ← IO.FS.readFile path
            if expected != text then
              errors := errors ++ [s!"{suffix} differs, {firstDifference expected text}"]
      errors := errors ++ congruenceCheck fuel {} p ++ provenanceCheck fuel p false ++
        (if p.proofDomainB then (provenanceCheck fuel p true).map ("lifting: " ++ ·) else [])
    unless errors.isEmpty do
      failed := failed + 1
      IO.println s!"FAIL {name}: {String.intercalate "; " errors}"
  IO.println s!"egg: {selected.length} tested, {failed} failures"
  return if failed == 0 && selected.length > 0 then 0 else 1

/-- Write the curated fixtures and every in-domain case's lifted certificates as one JSON
array, for `egglog/tests/lean_certificates.rs`. The fixtures alone go to `path` when
`fixturesOnly` is set. -/
private def exportCertificates (fuel : Nat) (path : String) (names : List String)
    (fixturesOnly : Bool) : IO UInt32 := do
  let some fixtures := Resugar.Export.fixtures () |
    IO.eprintln "difftest: a fixture program does not lift"; return 1
  let mut cases := fixtures
  unless fixturesOnly do
    let files ← fileCases
    let available := allCases ++ files ++ probeCases
    let unknown := names.filter fun name => !(available.any fun c => c.1 == name)
    unless unknown.isEmpty do
      IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
      return 1
    let selected := if names.isEmpty then allCases ++ files else available.filter fun c => names.contains c.1
    for (name, p₀) in selected do
      let p := p₀
      if !p.proofDomainB then continue
      let some cs := Resugar.certificates
          (fun Q => relationalExecAt fuel FDatabase.empty Q.schedule) p |
        IO.eprintln s!"difftest: {name} does not lift"; return 1
      let some json := Resugar.Export.caseJson name p cs |
        IO.eprintln s!"difftest: {name} is outside the source checker's fragment"; return 1
      cases := cases ++ [json]
  let json := Lean.Json.arr cases.toArray
  IO.FS.writeFile path ((if fixturesOnly then json.pretty else json.compress) ++ "\n")
  IO.println s!"wrote {cases.length} cases to {path}"
  return 0

/-- `difftest <dir> curated` writes the curated cases and `difftest <dir> seed <n>` one
random case named `rand-<n>`; `difftest <dir> compiled` writes the compiled programs. The
script reports the random cases' profile distribution — a collapsing distribution is how a
generator that has stopped exercising anything shows up.

`difftest encode-domain` prints how much of the corpus the correspondence domain covers.
`difftest congruence`, `provenance` and `resugar` run the corpus gates at a saturation fuel,
`egg` checks the snapshots under `tests/`, and `export-fixtures` and `export-certificates`
write source certificates for Rust egglog.
These write nothing and never invoke egglog; the comparison is between the model and
itself. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "slotted-parse" :: dirs => runSlottedParse dirs
  | "slotted-bounded" :: files => runSlottedBounded files
  | "resugar" :: fuel :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n => runProvenanceChecks n names true
  | ["export-fixtures", path] => exportCertificates 0 path [] true
  | "export-certificates" :: fuel :: path :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n => exportCertificates n path names false
  | "provenance" :: fuel :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n => runProvenanceChecks n names
  | "egg" :: fuel :: rest =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n =>
      match rest with
      | "update" :: names => runEggChecks n true names
      | names => runEggChecks n false names
  | "congruence" :: fuel :: rest =>
    -- `difftest congruence <fuel> [--views=naive|indexed] [--phased] [--subsumption] [names]`
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n =>
      let (o, names) := parseOptions rest
      runCongruenceChecks n o names
  | ["paper-tex", src] =>
    -- The congruence pass over a source `.egg` file, in the paper's notation, on stdout.
    let text ← IO.FS.readFile src
    match Program.ofEgg text with
    | .error e => IO.eprintln s!"difftest: {src}: {e}"; return 1
    | .ok p =>
      unless decide p.Fragment do
        IO.eprintln s!"difftest: {src} is outside the source fragment"
      IO.print (PaperTex.compiled p)
      return 0
  | ["paper-proof", src] => paperProof src {}
  | ["paper-proof", src, "--elide"] | ["paper-proof", "--elide", src] =>
    paperProof src PaperTex.elideAll
  | ["time", fuel, name] =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n =>
      let files ← fileCases
      match (allCases ++ files ++ probeCases).find? (·.1 == name) with
      | none => IO.eprintln s!"unknown case {name}"; return 1
      | some (_, p) => timeCase n p; return 0
  | ["trace", fuel, name] =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n =>
      let files ← fileCases
      match (allCases ++ files ++ probeCases).find? (·.1 == name) with
      | none => IO.eprintln s!"unknown case {name}"; return 1
      | some (_, p) => traceInstrumented n p; return 0
  | ["encode-domain"] =>
    let inDom := allCases.filter fun c => c.2.encodeDomainB
    IO.println s!"{inDom.length} of {allCases.length} cases are in encode's domain"
    IO.println (String.intercalate " " (inDom.map Prod.fst))
    return 0
  | [dir, "curated"] =>
    IO.FS.createDirAll dir
    let files ← fileCases
    for (name, p) in curated ++ files do writeCase dir name p
    IO.println s!"wrote {curated.length + files.length} curated cases"
    return 0
  | [dir, "seed", n] =>
    match n.toNat? with
    | none => IO.eprintln s!"difftest: bad seed {n}"; return 1
    | some k =>
      IO.FS.createDirAll dir
      writeCase dir s!"rand-{n}" (prog (genProgram (k + 1)))
      return 0
  | dir :: "compiled" :: rest =>
    -- `difftest <dir> compiled [--views=naive|indexed] [--phased] [--subsumption]`
    let (o, extra) := parseOptions rest
    unless extra.isEmpty do
      IO.eprintln s!"difftest: unknown arguments {extra}"
      return 1
    IO.FS.createDirAll dir
    let files ← fileCases
    let mut n := 0
    for (name, p₀) in curated ++ files ++ randomCases do
      let p := p₀
      if !p.encodeDomainB then continue
      writeCompiled dir name (Congruence.encodeWith o p)
      n := n + 1
    IO.println s!"wrote {n} compiled cases"
    return 0
  | _ =>
    IO.eprintln "usage: difftest <dir> curated | seed <n> | compiled"
    IO.eprintln "       difftest encode-domain"
    IO.eprintln "       difftest congruence <fuel> [case…]"
    IO.eprintln "       difftest trace <fuel> <case>"
    IO.eprintln "       difftest provenance <fuel> [case…]"
    IO.eprintln "       difftest resugar <fuel> [case…]"
    IO.eprintln "       difftest egg <fuel> [update] [case…]"
    IO.eprintln "       difftest export-fixtures <path>"
    IO.eprintln "       difftest export-certificates <fuel> <path> [case…]"
    IO.eprintln "       difftest slotted-parse <dir>…"
    IO.eprintln "       difftest slotted-bounded <file>…"
    return 1
