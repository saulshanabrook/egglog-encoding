# Eggcc encoding case study: accepted facts

- Deliver a research dossier with candidate assessments, reproducible examples, measurements, and figures for a later paper section; drafting or editing the paper is outside this goal.
- Record the eggcc and encoding revisions, dependency pins, configurations, and existing local changes; preserve author work and develop experiments in isolated worktrees.
- Assess constructor/constant-merge checks and pointer/alias analyses, distinguishing active default rules from optional analyses and recording why each candidate is promising or rejected.
- Every injectivity annotation or pointer-nonalias inference used in a result has an explicit semantic justification; arbitrary tuple Concat injectivity and expression disequality alone are not assumed sound.
- Broader compiler or runtime changes are allowed when a promising case needs them; each such change is tied to the case rather than an unrelated redesign.
- Implemented cases include positive and negative checks, baseline-versus-feature comparisons, and available source-versus-optimized execution checks on representative Bril inputs.
- A claimed real eggcc bug includes a minimal reproducer, a sound violated invariant, and evidence of the fault in baseline eggcc; deliberately seeded faults are labeled separately.
- A claimed optimization or analysis replacement demonstrates its effect in an actual eggcc optimization run and validates the resulting program; an encoding-only replay is labeled as such.
- Report repeated runtime and memory measurements per workload with treatment boundaries and variability; distinguish optimizer costs from generated-program performance and retain regressions or neutral results.
- Retain case origins, exact commands, inputs, configurations, raw machine-readable results, and scripts that regenerate the reported figures and tables.
- A documented negative eggcc result is a valid outcome: state the investigated scope and concrete barriers without claiming that no use case could exist.
- If no convincing eggcc case emerges, provide a small clearly labeled illustrative example with correctness checks and measured encoding costs for the paper.
- New proof support and Lean mechanization are outside scope; the evidence states the execution modes and limitations of the encodings actually used.
