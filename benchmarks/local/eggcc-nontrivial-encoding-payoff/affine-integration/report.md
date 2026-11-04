# Reversible affine keys exercise the combined encoding in EggCC

This constructed EggCC case demonstrates an actual emitted/native-code change with correct tested outputs. It uses injectivity and disequality together over dynamic equality-sort values; fixed constructor fields alone cannot decide the needed dynamic equalities. The encoding removes the target comparison and its `99` result arm from emitted Bril and ARM64 code. Broad host validation still fails, as detailed below. The case does **not** establish a measured runtime speedup or find a pre-existing compiler bug, so it is supporting evidence rather than a standalone completion of the stronger payoff goal.

The evaluated host starts from U0 `a0bbec127f83249074a46af3fd6f6126c90fe0fb`. All 884 files retained in the selected engine checkout match the corresponding Parts32 E1 candidate files; its five changed E1 files also match the frozen Parts32 source manifest. The isolated sources are `/private/tmp/eggcc-affine-candidate` and `/private/tmp/encoding-affine-candidate`; immutable archives, binaries, command receipts, source/emitted programs, LLVM, assembly, and native outputs are retained here. No root source, previous candidate, commit, branch, push, PR, proof, or paper file was changed.

## The source fact

Treat each signed i64 as a bit pattern in the ring `Z/(2^64)`. Define

```text
u(a,b) = a + 2b
v(a,b) = 2a + 3b
F(a,b) = (u(a,b), v(a,b)).
```

The matrix of `F` has determinant `-1`, which is invertible modulo `2^64`. Its explicit inverse is

```text
a = 2v - 3u
b = 2u - v             (all arithmetic modulo 2^64).
```

Therefore `F(a,b)=F(c,d)` implies both `a=c` and `b=d` for every i64 bit pattern, including signed extrema and wrapping results.

The Bril fixture checks four nested predicates:

```text
u(a,b) = u(c,d)
v(a,b) = v(c,d)
c + z != a + w
3z = 3w ? 99 : 7
```

The first two true guards imply `a=c`. The third false guard then implies `z!=w`, because its other Add children are equal. Multiplication by 3 is injective modulo `2^64`, since 3 is odd. Hence `3z!=3w`, so the target's `99` arm is unreachable.

U0 does not combine these guards. Its emitted Bril retains the fourth equality and `const 99`; LLVM simplifies `3z=3w` to `z=w`, but the native function still contains that comparison and the immediate `0x63`. Encoding and Manual omit the target comparison and `99` in both emitted Bril and native code.

## The private graph and generic derivation

The host admits only the exact nested guard chain and follows each branch input back to the same lexical root. It builds a fresh graph for one target. `Linear`, `Pair`, and `Add` are unmarked. `Affine` and `OddMul` are marked injective. The primitive coefficients are retained as constructor fields.

```text
Uab = Linear(a,1,b,2)        Ucd = Linear(c,1,d,2)
Vab = Linear(a,2,b,3)        Vcd = Linear(c,2,d,3)
Kab = Affine(a,b,1,2,2,3)    Kcd = Affine(c,d,1,2,2,3)
Pab = Pair(Uab,Vab)           Pcd = Pair(Ucd,Vcd)

Kab = Pab                     Kcd = Pcd       representation identities
Uab = Ucd                     Vab = Vcd       true source guards
Add(c,z) != Add(a,w)                          false source guard
```

Generic congruence first gives `Pab=Pcd`. The identities give `Kab=Kcd`. Marked-constructor cancellation gives `a=c` and `b=d`. Reverse congruence for the unmarked Adds uses the equal first siblings to derive `z!=w`. Marked forward disequality then gives `OddMul(z,3)!=OddMul(w,3)`. Only that exact final predicate is exported as `Eq=false`; none of the private word equalities enters EggCC's main graph.

Manual computes an independent finite least fixed point over the same rows, primitive fields, identities, and dynamic seeds. It does not recognize the affine theorem or target syntax directly. Its emitted Bril and native entry code are byte-identical to Encoding. This shows that the reusable encoding and a faithful hand-written multi-rule closure have the same result; it does not claim unique logical expressiveness.

Seed-only and Primitive-only are operationally identical null arms in this sidecar: both use the same constructors, annotations, primitive fields, representation identities, and dynamic source seeds as Encoding, then skip e-graph saturation and witness queries. The sidecar also computes a finite Manual closure in every active mode, including these two, but discards its result in both null arms. The Primitive-only label makes the fixed-field sufficiency question explicit. Equal coefficients alone cannot decide whether dynamic `a` equals `c` or whether dynamic `z` differs from `w`, so neither arm exports anything; both match U0 exactly.

## Causal matrix

Every knockout uses the same source and ten fixed input rows. A baseline result means both the emitted Bril and native main function have the exact U0 hashes. An optimized result has the exact Encoding hashes.

| Mode | Last retained fact | Export/application | Final code |
| --- | --- | --- | --- |
| U0 / Off | no private derivation | none | baseline |
| Seed-only / Primitive-only | full private graph, primitive fields, and source seeds; no e-graph saturation or witness queries; Manual result ignored | none | baseline |
| Cancellation off | `Kab=Kcd`; no `a=c` | no target witness | baseline |
| Identity off | `Pab=Pcd`; no bridge to `Kab=Kcd` | no target witness | baseline |
| Reverse off | `a=c`, `b=d`, mixed Adds differ | no `z!=w` | baseline |
| Forward off | `z!=w` | no odd-product witness | baseline |
| Query off | odd-product witness is derivable but deliberately unqueried | no export | baseline |
| Bridge off | exact target witness present | export disabled | baseline |
| Application off | exact target witness and export receipt present | main-graph union disabled | baseline |
| Exact target rescue | target disequality seeded directly; affine marking, odd-product marking, reverse query, and representation identity disabled | exported and applied | optimized |
| Manual / Encoding | complete generic chain | exported and applied | optimized |

The application control is the strongest endpoint check: it retains the internal witness and export decision but suppresses only the union into EggCC's main graph. Its exact return to U0 proves that the exported `Eq=false`, rather than unrelated candidate changes, causes the generated-code difference. The exact rescue shows that the downstream bridge and compiler can consume precisely that witness without relying on the earlier derivation.

The rescue seeds the **final** target disequality. No separate rescue of an intermediate `a=c` or `z!=w` fact was captured, so the stronger intermediate-rescue requirement in the goal remains open.

## Correctness and rejection boundary

The retained matrix contains 185 native executions: 140 across 14 positive/causal arms, 25 across five semantic-negative fixtures, and 20 across the two no-context arms. A separate interpreter pass checks 200 source and emitted-program/input combinations. All outputs match an independent wrapping-i64 oracle. The positive rows include `MIN`, `MAX`, mixed signs, equal-sum exits, key-mismatch exits, and wrapping odd products.

The independent law checker exhaustively verifies the affine inverse for word widths 2 through 8, then checks 4,145 boundary/random i64 pairs. It also records concrete counterexamples for the rejected laws:

- omitting either component equality permits distinct `(a,b)` and `(c,d)`;
- the singular matrix `(a+2b, 2a+4b)` maps `(0,1)` and `(2,0)` to the same key;
- multiplication by 2 maps both `0` and `MIN` to zero;
- taking the target under the equal-Add branch reverses the required source fact;
- running without context support creates no query or export.

Each negative's U0, Off, Seed-only, Manual, and Encoding programs produces `99`, and every emitted/native hash matches its U0 comparator. No negative query is accepted. U0 equals B1 exactly; Manual equals Encoding exactly.

Focused validation passes the 2 new causal tests, all 66 `dag_in_context` library tests, formatting, and all 18 registered engine injectivity/disequality oracle tests. The selected engine's prior full `make check` passed on source whose retained files match this experiment. Fresh U0 release `make test` passes 31 unit, 2,421 file, and 64 DAG tests, with no pending snapshots. Fresh candidate release `make test` passes its 31 unit and 2,421 file tests but exits 2 with 13 pending snapshots, before its DAG release step. Those 13 names and hashes exactly match the earlier frozen Parts32 E1 run; they are not U0 baseline snapshots.

The candidate DAG Clippy check exits 101: two diagnostics at previously recorded U0/Parts32 locations and 17 new `needless_borrow` diagnostics in the affine sidecar. The candidate debug workspace command aborts on stack overflow after recording 12 snapshot failures. The separate U0 debug workspace command also aborts on stack overflow, but after eight different failures with `slice is not sorted` panics in pinned `egg-smol` core-relations. These incomplete debug runs cannot serve as passing full checks or as a complete failure-set comparison. The candidate release snapshot and new Clippy failures remain unwaived; no snapshot was accepted. Exact receipts and U0 comparison are in `validation.json`. Run `python3 inspect.py` for the read-only final audit; the older `inspection.json` predates this validation reconciliation.

## Scope and timing decision

This is a constructed acyclic trigger, not a discovered corpus optimization. The integration is intentionally a source-initialization sidecar with a narrow syntactic admission boundary, not a proposal for general affine analysis in EggCC. It demonstrates that a nonprimitive, two-child injective representation can feed reverse disequality and then another injective constructor in a real compiler path.

No timing samples were collected. The final native difference was established first, as required, but this one-shot six-argument program is dominated by process startup. A defensible timing design would need a new hot workload whose per-iteration tuples preserve the complete guard chain without making the target loop-invariant. That workload and its admission proof were outside this bounded integration, so freezing an acyclic process-timing design would have produced misleading evidence.
