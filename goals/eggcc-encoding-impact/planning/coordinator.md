# Planning frame

Setup only: the interview and both facts passes are submitted; fourteen accepted facts are authoritative. No goal execution, compiler changes or benchmarks have started.

## Carry-forward boundaries

The preceding study demonstrated load elimination and six avoided explicit pair rows on a small source-derived local-address example. It established neither a stable compiler wall/RSS advantage nor a genuine compiler bug. Generated-program runtime was not measured. These are historical starting facts from the completed report and completion audit, not fresh performance claims.

The follow-on must preserve frozen source, binaries, measurements and receipts under `benchmarks/local/eggcc-encoding-case-study/`. New raw evidence will use `benchmarks/local/eggcc-encoding-impact/`; new source experiments will use separate worktrees or preserved source checkpoints. The primary encoding checkout remains dirty at `fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0` on main. Its unrelated changes are outside scope.

## Decisions to bind into the plan

- Either compiler/analysis speedup or generated-program speedup qualifies, with separate metric labels; a genuine baseline bug also qualifies.
- The new remaining-child rule is `f(a,b) != f(c,d)` and `a = c` imply `b != d`, by congruence. Parent disequality alone gives a disjunction. Injectivity gives the child-difference-to-parent-difference direction.
- Encoding improvements may close a defined reasoning gap even before an EggCC application is known. Such a result is useful, but alone does not establish the impact objective.
- Search exhaustion is a reviewed evidence claim, not a fixed experiment count. Promising unresolved leads require continued work or explicit blocker documentation.
- Research execution may use bounded concurrent circles, with one owner per shared build/benchmark surface. After two no-progress cycles in a domain, reassess the hypothesis and evidence rather than repeating status-only work.
- Do not commit, push, edit the paper, or add proof/Lean support as part of this goal setup.

## Coordinator orientation commands

All were read-only in `/Users/saul/p/egglog-encoding`:

- `git status --short`, `git rev-parse HEAD`, `git branch --show-current`.
- Read `goals/eggcc-encoding-case-study/{facts.md,STATUS.md,plan.md,completion-audit.json}`.
- Read current setup skill, sociocracy skill and `plannotator annotate --help` for the required review gate.

Agent discovery owns concrete source paths and proposed verification entrypoints. Main thread owns the synthesis and final plan gate.
