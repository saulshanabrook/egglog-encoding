**Found a redundancy bug, and it's unsound.** `tests/claude/34.egg` (control: `35.egg`) — same program, one slot literal different:

```
(rewrite (App2 "f" (App2 "sub" x x) (App2 "sub" x x)) x)
(let $s (App2 "sub" (Var 0) (Var 0)))   ; (Var 9) in 35
(union $s $z)
(let $w (App2 "f" (App2 "sub" (Var 0) (Var 0)) (App2 "sub" (Var 1) (Var 1))))
```

With `(Var 0)` the rule matches, `x` binds with a renaming truncated to the empty map, and `(Union $w {} (Var 0))` asserts the variable class has no free slots — **every variable in the e-graph collapses into one** (`k($5) = k($6)`). With `(Var 9)` it doesn't fire. slotted-egraphs collapses in neither case.

**Your 4 vs 5 is the same thing.** Not that `0` is special — what matters is whether the unioned invocation coincides with one appearing in `$x`. Union at 0 or 1 → matches; at 3 or 9 → doesn't. It's also *statement-order* dependent: test 5 starts passing if you just add a `(run)` between the `union` and the `let $x`, or let-bind `sub($0,$0)`/`sub($1,$1)` first.

**Evidence.** The stored node is `(App2 "sub" (map-of 0 0) …)` in one case and `(map-of 0 3)` in the other — a redundant slot keeps whatever name it had instead of being renamed to `$0` as Def. 7 requires, so equal things are two rows. And the candidate-symmetry triple satisfying the rule's guard exists only at one intermediate iteration; the saturated e-graph has no row satisfying it. User rules sit in the default ruleset alongside the machinery, so they can match mid-repair. (I tried to confirm that by phase-separating the rulesets and couldn't get a working schedule — treat it as a hypothesis.)

Redundancy repair also leaves junk self-maps on the slotless class: `[3↦0]`, `[3↦1]`, and `[0↦0,1↦1,3↦3,10↦10]` — that `10` is the `(run 10)` count, since `$global_identity` is built from every integer literal in the file. Inert as far as I could tell.

**Where I looked and found nothing**, so you don't re-search it: partial redundancy keeping a live slot, junk self-maps creating a spurious symmetry, leakage to unrelated classes, orbit closure, `f($0,$1)=f($1,$2)`, leaf-class redundancy (`union (Var 0) (Var 7)`), Def. 8 matching with two redundant slots. All sound. The failure is narrowly **cross-occurrence `≡` checks over a redundant slot**.

**Also:** I restored `claude/30.egg` — the eta-expansion / fresh-slot test you called out got swept up in "remove tests that go beyond our scope". And `claude/10.egg` **panics slotted-egraphs** v0.0.36 (`SlotMap::index($f1): index missing!`, `src/group/mod.rs:167`) when the symmetry union comes before the redundancy union; swap them and it's fine, so it's an ordering bug in orbit closure.

Corpus now: 30 pass, 3 fail (`tests/5.egg`, `claude/30.egg`, `claude/34.egg`). `claude/36.egg` is a passing companion showing the canonicalization property directly.
