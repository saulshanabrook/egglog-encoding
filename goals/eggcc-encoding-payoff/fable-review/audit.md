## Verdict

The report nearly stands alone. A reader who knows egglog can follow both main chains from source facts to timing with only two or three guesses, the controls tables are genuine explanation, and the Parts32 section now states the logical direction, the operational search direction, and that nothing intermediate is stored. It falls short of a bounded Diataxis explanation in two ways. The opening uses arm names before defining them, and the last third is a study record: test counts, Clippy diagnostics, snapshot tallies, and Mach-O hash notes that duplicate the reference and interrupt the causal account. The core sections still lack the one design-rationale paragraph that tells a reader why both sidecars look the way they do and why Parts32 cannot be done with equality alone.

Terminology is clean. I found no "proof", "mode", or "theorem"; the only drift is one use of "witness-query phase". The compact examples are clear schematic fragments, labeled as such and fenced as text. The rule-shape fragment for the store-forwarding bridge matches the actual `mem-simple` rules.

Verification caveat. The engine files named in the brief do not exist in the working tree, and the two engine checkouts under `/private/tmp/encoding-*` were outside my allowed paths. I checked engine claims against the retained snapshot of `disequality.rs` in the same-mask study and the Parts32 engine delta patch, plus the retained `injectivity.rs` snapshot. Every engine statement in the report matched those sources. I audited the on-disk version that names the `HighKnown` diagnostic markers.

All numeric claims in the two main-case sections check out against the primary JSON and Bril files: 91/55 instructions, 2/0 backward branches, all six Parts32 ratios and intervals, the QR7 Encoding/U0 ratio and interval, the four other QR7 point estimates, 209 to 155 lines, six to five branches, and the exact hot output.

## Gaps, ranked, with replacement prose

**1. Why the sidecars have this shape, and how the two cases differ.** The report never says that both sidecars mark one unary constructor over the opaque word and union it with an unmarked `Pair` of the compared components, nor why that is the only useful place for the mark. It also never states in one place that QR7 consumes the mark through the scheduled cancellation rule while Parts32 consumes the same mark as a forward edge inside the read-only search, and why a negative conclusion forces that choice.

```text
Location: "How derived facts reach generated code", replace the paragraph
beginning "The next two sections follow those stages one at a time."

Both sidecars have the same shape. Each introduces one private unary
constructor over the opaque source word, marks only that constructor, and
unions each application with an unmarked `Pair` of the component terms that
the source's branch predicates compare. The mark records the host's
arithmetic promise that the word is determined by its components. The `Pair`
identity is the representation invariant that ties that abstract key to the
components. Marking `Pair` instead would be sound but useless, because a pair
constructor only recovers component equality from pair equality, and the
guards already supply component equality.

The two cases consume the mark differently. QR7 needs a positive fact, `x=y`,
so it runs the generated cancellation rule in the `injectivity` schedule and
reads the resulting equality. Parts32 starts from a negative fact, `x!=y`, and
needs another negative fact, `high(x)!=high(y)`. No union can produce a
disequality, so Parts32 asks the read-only `known-disequal?` search instead.
That search uses the same mark as a forward edge and ordinary congruence as a
sibling-guarded reverse edge. The reverse edge is what lets the equal low
halves select the high halves as the pair that must differ.

The next two sections follow those stages one at a time. In each case, the
domain-specific code recognizes and exports a narrowly scoped fact; the
injectivity and disequality steps in the middle are generic.
```

**2. Arm names used before definition; PrimitiveOnly never defined.** "Encoding" appears in the first and second paragraphs as if it were a compiler mode. PrimitiveOnly is used in the QR7 controls and timing table but is absent from the arm paragraph. The Off/B1 definition also omits the reason they exist.

```text
Location: opening paragraph, replace the sentence beginning "In an
independent 112-cycle confirmation".

In an independent 112-cycle confirmation, programs built with the sidecar
active, the Encoding arm defined below, use about 44.9% less elapsed time than
programs from the pinned untouched compiler, U0, on the fixed hot workload,
including fresh process startup.

Location: second paragraph, replace the sentence beginning "Across three
constructed workloads".

Across three constructed workloads and two independent prospectively balanced
sessions, the Encoding arm uses about 7.5% to 8.6% less elapsed time than U0.

Location: replace the whole arm-names paragraph.

The arm names recur in the evidence. **U0** is the pinned untouched compiler.
**Off** in QR7 and **B1** in Parts32 are built from the same retargeted engine
dependency as Encoding but never run the sidecar, so comparing Encoding with
them separates the inference from the dependency change. **SeedOnly**
populates the same private graph and seeds, including ordinary e-graph
rebuilding, but skips the scheduled cancellation or read-only query phase, the
Manual closure, and export. **PrimitiveOnly** keeps that same graph and seeds
but compares only primitive fields of marked constructors and runs no
equality-sort inference; `K7` and `Parts32` have no primitive fields, so it
establishes nothing. **Manual** computes the same finite closure directly,
while **Encoding** uses the generic engine.
```

**3. How and when the exported fact enters EggCC's graph.** The report says the host "emits" a relation or union but not that it is written into the egglog program EggCC is building and asserted during initialization, before any optimization ruleset. Without that, the link from exported fact to existing consumer is a guess.

```text
Location: "How derived facts reach generated code", first paragraph, replace
the sentence beginning "In both cases, the Rust recognizer maps".

In both cases, the Rust recognizer maps the successful private result back to
EggCC expressions it had already matched. The sidecar runs while EggCC is still
writing the egglog program for the whole program, so the exported fact is
written into that text beside the program's own terms. QR7 adds one
`Qr7MustAlias` row over the two source address expressions. Parts32 adds one
union between the source `Eq` term and a `false` constant that carries the same
type and branch context. Both are asserted when the program's initialization
rule runs, before any optimization ruleset, so the existing consumers meet them
as ordinary facts.
```

**4. Why untouched EggCC cannot derive either fact.** Both "optimization opportunity" sections assert that the untouched compiler misses the fact but do not say why. The reason is the same in both cases and is central to the explanation.

```text
Location: QR7 "The optimization opportunity", replace the final sentence
beginning "Untouched EggCC does not combine".

Untouched EggCC does not combine the two guarded equalities into `x=y`.
Congruence only carries equal inputs to equal outputs, and no rule in its
rulesets reconstructs a word from its quotient and remainder by seven. The two
address terms therefore sit in different e-classes when the same-address
store-forwarding rule looks for a shared one.

Location: Parts32 "The optimization opportunity", replace the final sentence
beginning "Untouched EggCC retains".

Untouched EggCC retains the high-part calculation, comparison, and branch. Its
branch context records each predicate and the direction taken, but no rule
turns a false word equality and a true low equality into a verdict about the
high halves. That step is arithmetic about the partition, not congruence.
```

**5. Two layers where the brief needs three.** The "Layer" table folds the case-specific sidecar and the bounded consumer into one row, so a reader cannot see which parts are reusable, which are per-case, and which are EggCC-side.

```text
Location: replace the sentence "There are also two kinds of implementation
change:" and the two-row table.

The implementation has three layers, and only the first is reusable:

| Layer | What it is | What it knows |
| --- | --- | --- |
| Reusable engine | `:injective`, the generated cancellation and primitive-panic rules, the `injectivity` schedule, and the read-only `known-disequal?` search with marked-forward and equal-sibling reverse edges | constructor schemas, committed rows, unions, and asserted disequalities; no arithmetic |
| Case-specific sidecar | an exact source recognizer, a fresh private graph with opaque words, the marked constructor and its `Pair` representation invariant, the imported path facts, and the export of one narrow fact | the arithmetic law that justifies the mark, and which source expressions the private terms stand for |
| Bounded EggCC consumer | QR7: the added `Qr7MustAlias` store-forwarding rule in `mem-simple`. Parts32: no added rule; existing constant-predicate consumers act on the exported `Eq=false` union | ordinary EggCC relations, unions, and rewrites |
```

**6. Record material in the tail.** The "Final validation" section and the count-heavy paragraphs in "What the search did not find" and "Supporting actual-host examples" are reference content that the reference already holds. Replace "Final validation" with a pointer and trim the A1 paragraph; I recommend the same trim for the Pack32 paragraph and the Route/Sort bullets.

```text
Location: replace the entire body of "## Final validation".

The validation record for the frozen compilers, the repository test runs, the
r2 cleanup, and the matrix reproduction lives in the
[reference](reference.md#source-identities-and-validation-boundaries) and the
linked r2 summaries. Two points matter for this explanation. The retained
timing samples measure the r1 compiler's native programs, and the r2 cleanup
changed only the QR7 sidecar file without altering its behavior or producing a
new timing claim. No snapshot was accepted and no checked-in source changed.

Location: "What the search did not find", replace the paragraph beginning
"The same-region `NoAlias` lead".

The same-region `NoAlias` lead reached an actual compiler implementation but
exported nothing. After one permitted revision, every positive treatment still
rejected its auxiliary rows conservatively, so emitted and native code stayed
identical and no timing was justified. This exhausts the bounded attempt budget
without refuting the scoped `NoAlias` law or ruling out a different design. The
[A1 attempt report](../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-integration/actual-r0/report.md)
holds the test counts and the failing cases.
```

**7. The baseline-load sentence puzzles the reader.** "LLVM already removes the executed baseline entry's i64 load" is true per the inspection, but the reader needs to know why the baseline still has a loop while the Encoding program does not.

```text
Location: QR7 "How the derived equality changes the program", replace the
paragraph beginning "The exported fact has therefore done something concrete".

The exported fact has therefore done something concrete before lowering: it
has exposed the loop recurrence `sum += count`. In the baseline the loaded
value still depends on whether the two indices coincide, a question the source
leaves open. Later optimization removes the executed entry's i64 load but keeps
a loop and vectorizes it. In the Encoding program the recurrence no longer
touches memory, and the loop collapses to a closed-form sum. The native payoff
is therefore not a newly absent load but the loop that disappears with it.
```

**8. Small wording fixes.** "Crosses the representation unions" suggests an explicit step; the search simply finds `Parts32` rows in the e-class it already reached. The QR7 step-1 justification should say where path facts come from. The NEE opening is denser than an explanation needs.

```text
Location: Parts32 "How the disequality is derived", replace the sentence
beginning "Operationally, the query searches backward".

Operationally, the query searches backward from the high-child goal. It uses
the equal low siblings to move to the two `Pair` results. Because each
representation union placed `Pair(...)` and `Parts32(...)` in one e-class, that
goal already names the two `Parts32` e-classes. The search then finds the
`Parts32` rows in those e-classes and uses the mark to reduce the goal to the
child pair `x`, `y`, where it meets the asserted `x!=y`.

Location: QR7 step 1, "Why it follows" cell.

the two enclosing branches are true; EggCC's context labels record each
predicate and its direction, and the recognizer imports the path facts from
those labels

Location: "The mathematical rules", replace the first paragraph.

Asserted disequalities are stored as ordinary facts: one canonical ordered pair
per assertion, with reads probing both orientations. Disequalities that only
follow structurally are never stored; a read-only search finds them on demand,
as described below. Three logical implications matter here.
```

Two nits without prose. Drop the `(run-schedule (saturate injectivity))` line from the QR7 schematic so it parallels the Parts32 schematic, since the prose already covers the schedule. Consider replacing "representation identities" with "representation invariant" at first use so the term matches the brief.

## Claims in the proposed prose that need human verification

- **Engine behavior** was checked against retained snapshots and the Parts32 engine delta patch, not the two `/private/tmp/encoding-*` checkouts the compilers actually link. Confirm those match.
- **Negative claims about untouched EggCC** in patch 4: no rule reconstructs a word from quotient and remainder by seven, and no rule connects a false word equality plus a true low equality to the high halves. The empirical U0 arms support this, but I did not census the rulesets.
- **Baseline loop characterization** in patch 7: "the loaded value still depends on whether the two indices coincide" is a reading of the source, and "keeps a loop and vectorizes it" follows the inspection fields. Confirm against the retained LLVM IR that this is acceptable without pass attribution.
- **Off and B1 share the retargeted dependency** with Encoding. Verified for QR7 from the patch's Cargo.toml hunks and the reference's treatment table; confirm B1 for Parts32 specifically.
- **"Marking `Pair` would be sound but useless"** is a design-rationale framing the authors should endorse.
- **Initialization timing** in patch 3 was read from the Parts32 candidate's program template and both patches' `lib.rs` hunks; confirm the frozen r1 QR7 build uses the same template.
- **Unverified numbers I left intact:** the four QR7 intervals other than Encoding/U0, the same-mask table, and every test or receipt count in the tail sections were matched only to the reference and sub-reports, not to raw receipts.
