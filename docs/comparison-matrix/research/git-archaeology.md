# Git archaeology: the multi-endpoint benchmark harness, and why it became pair-only

All commits/paths refer to `/Users/saul/p/egglog-encoding` (repo `saulshanabrook/egglog-encoding`). Read-only reconstruction via `git show`/`git log` and `gh`.

## TL;DR

- A **full matrix harness existed and worked**: repeated `--target` (N builds), `--backend main,dd`, `--treatments off,term,proofs`, with auto-enumerated cross-target, cross-backend, and within-target-overhead comparison tables, a DuckDB SQL analysis catalog, a `--duckdb-ui` escape hatch, and a `--serve` live scope-editor page.
- It was collapsed to **one candidate-vs-baseline pair** in `8f72ecb5` ("Simplify benchmark reports around pair comparisons", 2026-07-17), merged as part of **PR #21** (2026-07-20). The multi-endpoint DuckDB peak lived only ~2 days, *inside the PR branch*; main went directly from a multi-target monolithic `bench.py` to the pair-only package.
- Motivation (from the PR #21 body, the only written record; commits have no bodies): the matrix was *implicit* — every CLI selection fanned out into dozens of tables that needed "this is not X" disclaimer captions; the DuckDB layer duplicated every schema in SQL and Python for no line-count win (measured: 6,061 → 5,188 lines across four preserved architecture experiments); and the project's decision criterion was a single gate ("proofs < 2x"), which a pair answers directly.
- Ten days later the matrix **crept back at the edges**: the nightly (PR #32) runs the pair CLI once per endpoint into one shared JSONL cache, and the eval-live HTML report's dropdown "can compare any two of them". This is the strongest archaeological signal: the *collection* layer was never the problem and already supports N endpoints; only the *comparison-specification and presentation* layer was amputated.
- The one thing the user wants that **never existed**: an interaction estimate ("did the proofs overhead itself get worse") with a CI. The old system showed proofs/off per target side-by-side for eyeballing, but never computed a ratio of ratios.

## Timeline

| Date (2026) | Ref | What |
|---|---|---|
| 07-07 | PR [#5](https://github.com/saulshanabrook/egglog-encoding/pull/5) "Add benchmarking and readme" | Monolithic root `bench.py`. Single target, `--treatments` matrix, per-file wall-time matrix (File x off/term/proofs), overhead-ratio matrix (term/off, proofs/off, proofs/term), suite summary with gate ratio + geomean. |
| 07-09 | PR [#11](https://github.com/saulshanabrook/egglog-encoding/pull/11) "Improve benchmark report clarity" | Multi-target reports reorganized "so that important/decision making criteria is at the bottom and highlighted". Adds "vs baseline" comparison tables and the disclaimer-caption style. |
| 07-13 | PR [#4](https://github.com/saulshanabrook/egglog-encoding/pull/4) "Differential Dataflow Backend" | Adds the `dd` backend and `--backend` list dimension. |
| 07-14/15 | PRs [#13](https://github.com/saulshanabrook/egglog-encoding/pull/13), [#14](https://github.com/saulshanabrook/egglog-encoding/pull/14), [#16](https://github.com/saulshanabrook/egglog-encoding/pull/16) | Proof-overhead work; 6-workload default suite; isolated worktrees for git-ref targets. |
| 07-15 | `1ad92984` | (PR #21 branch) `bench.py` monolith → `benchmarking/` package; per-ruleset phase timings; DuckDB reporting refactor. |
| 07-16 | `47962d74`, `d9310bb2` | (PR #21 branch) **Peak flexibility**: renderer-neutral shared SQL catalog; `--serve` cache-only live reports; `--duckdb-ui`; `--phase-timings`/`--detailed-timing`. |
| 07-17 | `8f72ecb5` | **"Simplify benchmark reports around pair comparisons"** — deletes `benchmark_config.py`, `reports/summary.py` (1,146 lines), `reports/timing.py`; adds `reports/comparison.py`; pair-only CLI. |
| 07-17 | `eb921aa8`, `c8cd17bc`, `934ce8d3` | Three preserved architecture experiments (persistent DuckDB, Pydantic, stdlib JSONL). |
| 07-17 | `5f965bbd` | "Replace DuckDB benchmark reports with pure Python" — DuckDB dependency removed entirely; SciPy Fieller in Python. |
| 07-17 | `898733d3`, `d0646cb6`, `2e25b152`, `0d4b3eaf`, `e496c282` | Polish, hardening (blocking `wait4` vs 50 ms polling bias), runner simplification, review fixes. |
| 07-20 | merge `1cc0e8a1`, PR [#21](https://github.com/saulshanabrook/egglog-encoding/pull/21) | All of the above lands on main as one PR. |
| 07-23 | PR [#27](https://github.com/saulshanabrook/egglog-encoding/pull/27) | `proof-extraction` treatment added (pair world). |
| 07-27 | PR [#32](https://github.com/saulshanabrook/egglog-encoding/pull/32) "Add nightly benchmark webpage"; commit `379ec57f` | **Matrix re-emerges**: run `bench.py` once per endpoint (main: off/term/proofs/proof-extraction; dd: term/proofs) on both branch and `@origin/main`, all into one cache; eval-live dropdown compares any two endpoints. |
| 07-22..29 | `544d63d8`, `7092b68c` etc. (branch) | `causal-receipts`/`causal-proofs` treatments — the treatment dimension keeps growing. |

Note on provenance: PR #21's description carries an explicit "AI disclosure: This pull request description was written by AI." It is nonetheless the only written motivation record — commit messages in this era are subject-line-only. The human review (oflatt) did not request the pair-only change; his review asked to use "eval-live's filterable tables instead of the static tables" and quibbled terminology ("I usually call this a 'treatment' and a backend is (flowlog/native/duckdb)... I usually call a Treatment an encoder").

## 1. What the old system could express

### 1.1 CLI surface (exact, from `git show 8f72ecb5^:benchmarking/benchmark_config.py`)

```
./bench.py [FILE ...]
  --fact-directory PATH        # fact dir for explicitly selected files
  --target SRC                 # action="append": ., /path, @git-ref, #pr, label=source, or label=
  --report PATH                # append-only JSONL cache (default .reports.jsonl); "-" rejected
  --format {rich,markdown}
  --rounds N                   # default 6; rows required per target/file/backend/treatment
  --timeout-sec N              # default 120
  --backend LIST               # comma-separated; default "main"; BACKEND_SPECS = {main, dd}
  --treatments LIST            # comma-separated; default "off,term,proofs"
  --force-run
  --phase-timings              # compact engine-timing breakdown per selected result
  --detailed-timing            # implies --phase-timings; every recorded ruleset
  --duckdb-ui                  # open DuckDB local UI on the transient in-memory catalog
  --serve                      # loopback live report page (eval-live), cache-only rescoping
  --serve-port PORT            # requires --serve; --serve and --duckdb-ui mutually exclusive
```

Key semantics (old README, `git show 8f72ecb5^:README.md`):

- **Multi-target list**: "Use one `--target` per build … The first target is the comparison baseline." Examples in the docs: `./bench.py --target @origin/main --target .`, `--target main=@origin/main --target mine=.`, `--target before=@abc123 --target after=@HEAD`, `--target old=/tmp/egglog-old --target new=/tmp/egglog-new`, `--target prev-run=` (label-only lookup reusing the newest cached identity with that label).
- Target grammar: `.` = checkout, `/path` = other checkout, `@ref` = git ref built in an isolated worktree, `'#33'` = PR head fetched from origin, `label=SOURCE` names it, `label=` resolves from cache. Duplicate binary SHA-256s rejected.
- **Report scope = CLI selection**: "Positional files together with `--target`, `--backend`, and `--treatments` define the initially selected benchmark results. CLI display options do not change that subset: every enabled report view covers every CLI-selected result."
- Backend capability masking: `BACKEND_SPECS = {"main": ("off","term","proofs"), "dd": ("term","proofs")}` — cells are the product of backends x treatments filtered per backend, in canonical backend-then-treatment order (`backend_treatment_cells` in old `models.py`).
- Cache identity per observation: `EstimateKey(binary_sha256, file_sha256, treatment, timeout_sec, backend, fact_directory_sha256)` — unchanged in spirit today.

So the user's desired collection `{old, new} x {off, proofs}` was exactly `./bench.py --target old=@A --target new=@B --treatments off,proofs`.

### 1.2 Which comparisons it auto-enumerated

`_comparison_requests` (old `reports/summary.py`) generated, per metric (wall_sec, max_rss_bytes):

1. **Cross-target, same cell**: target 0 (baseline) vs every other target, for every (backend, treatment) cell — the user's `new-off/old-off` and `new-proofs/old-proofs`.
2. **Within-target treatment overhead**, per backend, from a fixed adjacency list (`ratio_specs`): `term/off`, `proofs/off`, `proofs/term` — the user's `proofs/off within each commit`.
3. **Within-target cross-backend, same treatment**: `backends[0]` vs each other backend over shared treatments.

It did **not** generate ratio-of-ratios (interaction), arbitrary cell-vs-cell pairs (e.g., `dd/proofs` vs `main/off`), or cross-file contrasts. The comparison set was hard-coded structure, not user-specifiable — there was no way to *ask* for a particular contrast or suppress unwanted ones.

### 1.3 Report shape (actual output)

Section order (old catalog): `Targets` tree → `Comparisons` → `Target Diagnostics` → optional timing sections → `Benchmark Summary`.

Single-target sketch (verbatim from PR #5/#11 bodies):

```
                    24e60ee38329: per-file wall time
  File                                   off                  term                 proofs
  math-microbenchmark.egg                [0.4029s, 0.4482s]   [6.1558s, 6.6026s]   [14.6287s, 17.5879s]
  ...
                    24e60ee38329: overhead ratios
  File                                   term/off             proofs/off           proofs/term
  math-microbenchmark.egg                [14.077x, 15.992x]   [33.938x, 41.989x]   [2.280x, 2.777x]
  ...
Within-target treatment ratios. These are not target-vs-baseline wall-time change.
                    24e60ee38329: proof overhead summary
  Metric                    Ratio                Change               Worst file             Worst ratio          Result
  wall proofs/off           [17.733x, 19.601x]   [1673.3%, 1860.1%]   math-microbenchmark…   [33.938x, 41.989x]   <2x not established
  wall proofs/off geomean   3.544x               254.4%               -                      -                    descriptive
```

Two-target sketch (PR #11, `--target . --target '#6' --treatments proofs`):

```
                    Per-file wall-time change vs 24e60ee38329: #6
  File                                    Treatment   Time ratio         Wall-time change   Result
  math-microbenchmark.egg                 proofs      [0.491x, 0.610x]   [-50.9%, -39.0%]   faster
  rw-analysis.egg                         proofs      [0.941x, 1.102x]   [-5.9%, 10.2%]     unclear
Ratio is target / baseline. Values below 1x are faster; above 1x are slower. …
                    Wall-time summary vs 24e60ee38329
  Target   Treatment   Wall-time change   Geomean   Worst file        Worst ratio        Result
  #6       proofs      [-50.8%, -38.9%]   0.746x    rw-analysis.egg   [0.941x, 1.102x]   faster
```

Note the epidemic of defensive captions: "These are not target-vs-baseline ratios.", "This is not backend-vs-main performance.", "Within-target proof overhead. This is separate from target-vs-baseline wall-time change." A matrix report where every table must disavow being a different table is a presentation-language smell.

### 1.4 Statistics (old `reports/sql/analysis.sql`, 1,009 lines of DuckDB)

> **Verification correction:** 1,009 is the diffstat churn of `analysis.sql`
> in `8f72ecb5` (440+/569− over 812→683), not a file length. The file's
> actual peak was 812 lines at `8f72ecb5^`; all three SQL files together
> (analysis + presentation + schema) totaled 1,135 lines.

- Per-cell: mean with t-based 95% CI (`t_critical = stats.t.ppf(0.975, rounds-1)` computed in Python, passed into SQL).
- Per-file ratio of means: **Fieller interval**, verbatim SQL: `fieller_a = baseline_mean^2 - t²·baseline_var_mean`, `fieller_d = candidate_mean^2 - t²·candidate_var_mean`, `radicand = (baseline_mean·candidate_mean)² - fieller_a·fieller_d`; bounds `= baseline_mean·candidate_mean/fieller_a ∓ sqrt(radicand)/fieller_a`; `fieller_a <= 0 OR radicand < 0` → "Fieller interval undefined". (Same formula survives today in Python: `benchmarking/reports/analysis.py` lines 283–291.)
- Suite ratio: ratio of per-file *sums* with a Fieller CI over the summed variances (the "gate" number), plus an equal-file **geometric mean** of per-file ratios — explicitly "a separate descriptive aggregate without an interval" (comment at analysis.sql:389).
- Result classification per comparison: faster/slower/unclear (CI straddles 1), `<2x not established` for the proof gate; RSS variants "less/more".
- No multiple-comparison correction anywhere; a default run produced 2 targets x 6 files x up to 5 cells x 2 metrics ≈ dozens of intervals classified independently.

### 1.5 The two interactive surfaces

- **`--duckdb-ui`**: opened DuckDB's official local UI on the same transient in-memory database with a typed report scope installed; "eight `presentation_*` views/table macros are available for interactive SQL": `presentation_targets`, `_files`, `_cells`, `_cell_estimates`, `_file_ratios`, `_comparison_rollups`, `_compact_timings`, `_ruleset_timings` (`reports/sql/presentation.sql`). This was the "arbitrary query" escape hatch for many-endpoint questions.
- **`--serve`**: loopback eval-live page rendering the same renderer-neutral catalog as the terminal; per-table SQL-style WHERE filters via AlaSQL (display-only); a **scope editor** "deliberately bounded by the invocation": choose a non-empty subset of the already-resolved targets/files/backends/treatments, pick which target is baseline, adjust rounds/timeout; each Apply did one complete cache-only recomputation in a fresh transient DuckDB catalog; never built or ran anything.

### 1.6 Renderer-neutral catalog (kept!)

`reports/catalog.py` — `ReportCatalog → ReportSection → ReportTable/ReportMessage → ReportRow → ReportCell(raw, display, tone)` with stable JSON-array IDs (`report_id(*parts)`), alignment/collapse policies, and tones (`positive/negative/warning/error/muted`). This abstraction survived the purge and still backs Rich, Markdown, and the interactive HTML today. It is the natural rendering target for any future matrix view.

## 2. Why it was simplified — the recorded motivation

All quotes from the PR #21 body (https://github.com/saulshanabrook/egglog-encoding/pull/21):

1. **Implicit matrix → explicit question.** "Replace implicit target/backend/treatment matrices with one explicit candidate-versus-baseline comparison; a non-main candidate backend compares against `main` by default." And under *Compatibility and migration*: "This intentionally changes the benchmark CLI from a multi-way matrix to one pair: repeated `--target` becomes `--target` plus `--compare-target`; `--treatments` becomes singular `--treatment` plus `--compare-treatment`; candidate and baseline backends use `--backend` and `--compare-backend`."
2. **The DuckDB layer cost more than it earned.** The *Architecture experiments* table measured four implementations of the same behavior over `benchmarking/**/*.{py,sql}`:
   - JSONL scanned through transient DuckDB SQL (`8f72ecb5` checkpoint): 6,061 lines — "Relational queries worked, but required duplicated SQL/Python schemas, adapters, macros, and catalog lifecycle."
   - Persistent `.duckdb` cache (`eb921aa8`): 6,057 — "Direct writes did not materially reduce code and added bootstrap, locking, versioning, and a less inspectable cache."
   - Pydantic over JSONL (`c8cd17bc`): 5,190 — "Runtime validation added four locked packages while saving no meaningful code for a trusted disposable cache."
   - Standard-library JSONL (`934ce8d3`): 5,188 — "**Selected:** one TypedDict schema, direct append/index/select operations, no database lifecycle, and data that embeds directly in HTML."
3. **Feature retirement was explicit.** "Earlier revisions exposed `--phase-timings`, `--detailed-timing`, `--serve`, and `--duckdb-ui`. They are not part of the final interface: `--detail` replaces the timing flags, `--open` replaces the server, and the DuckDB UI was removed with DuckDB."
4. **Presentation was redesigned around one decision.** Cumulative `--detail summary|files|phases|rulesets`; "Rich puts the most specific requested diagnostics first and the decision summary last, since the bottom is what remains visible after a CLI run." The repo's stated success target (README, both eras): "proof mode is less than 2x slower than the non-proof baseline; and that claim is supported by benchmark reports with confidence intervals, not just point estimates."
5. **Attribution discipline.** Today's README: "If a command changes more than one of target, backend, and treatment, the report warns that the ratio is a joint endpoint change and does not attribute the effect to one cause." The pair model made confounded comparisons *visible* instead of burying them in a matrix.
6. What it was **not**: not driven by reviewer pushback (only bot comments plus oflatt's approval), not driven by stats concerns *explicitly* (no written mention of multiplicity), and not a loss of collection capability (the JSONL cache remained endpoint-keyed and append-only).

Pain-point inventory, inferred and ranked by evidence strength:

| Pain | Evidence | Caused by flexibility itself? |
|---|---|---|
| Duplicated schema/lifecycle (SQL+Python mirrors, macros, scope install, transient catalog) | Measured line counts; schema.sql "Python mirror: …" comments | No — caused by the DuckDB implementation choice |
| Report sprawl + misreading risk (disclaimer captions on every table) | Caption text throughout `summary.py`; PR #11's stated goal | Yes — auto-enumeration of every structural comparison |
| One decision gate vs many numbers | README success target; `--detail` redesign | Yes — matrix output diluted the gate |
| Two competing interactive stacks (`--serve` server vs `--duckdb-ui`) | Mutual-exclusion error in argparse; both retired for `--open` | Partly — each was a workaround for "the terminal can't show the matrix" |
| Fragile stats at scale (Fieller-undefined cells, "unclear" proliferation, no correction) | analysis.sql issue plumbing; result-class machinery | Yes — more cells ⇒ more undefined/borderline intervals |

## 3. The matrix crept back: nightly + eval-live (the existing precedent)

PR #32 (merged 2026-07-27) and commit `379ec57f` rebuilt many-endpoint comparison *on top of* the pair CLI without new CLI surface:

- "`scripts/nightly_bench.py` runs the public `bench.py` once per available backend/treatment endpoint (main: `off`, `term`, `proofs`, `proof-extraction`; dd: `term`, `proofs`) on both the current checkout and `@origin/main`, accumulating every endpoint in one report cache. eval-live builds its dropdown from every cached endpoint, so the page can compare any two of them."
- "Targets are labelled `branch=.` and `main=@origin/main` … Endpoints with identical binaries collapse to one option."
- Best-effort population: a failed endpoint "drops one dropdown option instead of failing the nightly."

And today's `--open` snapshot (`benchmarking/reports/interactive_runtime.py`) "discovers selector choices from every row in the loaded JSONL" — i.e., the interactive page is already an any-pair-from-the-cache browser; only *one pair at a time* is renderable, and no derived contrast (ratio-of-ratios) exists.

## 4. Lost capabilities vs what the user now wants

| User's want | Old system (pre-8f72ecb5) | Today (pair-only) |
|---|---|---|
| Collect `{old,new} x {off,proofs}` in one command | Yes: `--target old=@A --target new=@B --treatments off,proofs` | No: 4 endpoints ⇒ up to 4 invocations (cache dedupes; nightly script pattern) |
| `new-off/old-off`, `new-proofs/old-proofs` | Yes: cross-target same-cell tables with Fieller CIs | One per invocation |
| `proofs/off` within each commit | Yes: per-target "overhead ratios" table (term/off, proofs/off, proofs/term) | One per invocation |
| Interaction: `(new-proofs/new-off)/(old-proofs/old-off)` with CI | **Never existed** — only side-by-side eyeballing of per-target overhead tables | Never existed |
| One display of the whole grid | Yes: per-file cell matrix (File x cells per target) + comparison tables; `--duckdb-ui` for ad-hoc SQL | No; interactive HTML shows one pair at a time |
| Named contrasts / suppress unwanted comparisons | No — enumeration was hard-coded | N/A |
| New measures multiplying comparisons (egg-equivalence) | Metrics were a closed enum (`wall_sec`, `max_rss_bytes`) with per-metric table builders | Same closure, in Python |

## Implications for this harness

Opinionated takeaways from the record:

1. **Do not re-derive "flexible = DuckDB".** The experiment table is unusually good evidence: the relational engine cost ~900 lines of mirrored schema/lifecycle versus stdlib JSONL *for the same behavior*, plus a dependency and a second UI. The JSONL cache + typed rows + renderer-neutral `ReportCatalog` all survived and are sufficient substrate for a matrix. If ad-hoc SQL is ever wanted again, `duckdb -c "SELECT ... FROM read_json('.reports.jsonl')"` works externally without any harness code ([DuckDB JSON reading](https://duckdb.org/docs/stable/data/json/loading_json)).
2. **The failure mode to avoid is auto-enumeration, not the matrix.** Every disclaimer caption in the old report marks a table the tool volunteered but nobody asked for. The fix the repo already groped toward (explicit `--compare-*` naming of the baseline) generalizes: a **contrast list** the user states, e.g. `--cell old=@A,off --cell old=@A,proofs --cell new=.,off --cell new=.,proofs --contrast new,proofs / old,proofs --contrast '(new,proofs / new,off) / (old,proofs / old,off)'`. Collection scope = union of cells mentioned; report = exactly the requested contrasts, each a small pair-style table. This keeps PR #21's real win (each table answers one asked question) while restoring N endpoints.
3. **Model contrasts in log space; that's the missing conceptual language.** Every ratio and ratio-of-ratios over strictly-positive means is a ±1-weighted linear combination of log cell means (a *contrast* in the factorial-design sense — see Jain, *The Art of Computer Systems Performance Analysis*, Wiley 1991, 2^k factorial designs, https://www.cse.wustl.edu/~jain/books/perfbook.htm; and Kalibera & Jones, "Rigorous Benchmarking in Reasonable Time", ISMM 2013, https://doi.org/10.1145/2464157.2464160, for ratio CIs in benchmarking). The interaction gets a t-CI from summed per-cell log-variances — uniform machinery where Fieller composition is awkward (Fieller, "Some Problems in Interval Estimation", JRSS B 16(2), 1954, https://www.jstor.org/stable/2984043; keep the existing Fieller path for raw pair ratios where it's already validated). A contrast grammar is to comparisons what Vega-Lite is to charts: a small algebra (cells, weights, aggregation across files) rather than a menu of table types (Satyanarayan, Moritz, Wongsuphasawat, Heer, "Vega-Lite: A Grammar of Interactive Graphics", IEEE TVCG 2017, https://idl.cs.washington.edu/papers/vega-lite/).
4. **Reuse the nightly's population pattern as the official multi-cell collector.** `379ec57f` proved endpoints accumulate cleanly in one cache with binary-collapse dedupe. A `--cell`-list front end is a loop over the existing single-endpoint collection, not new machinery. Keep append-only JSONL identity keys exactly as-is.
5. **Presentation: grid of cells + list of contrasts, in the existing catalog.** One `File x cell` estimate matrix (the old "per-file wall time" table was genuinely good and needed no disclaimer), then one table per *requested* contrast with CI and result class, decision summary last (PR #21's ordering insight). The interactive `--open` page already discovers all cached endpoints; extend its selector from "pick 2 endpoints" to "pick/compose a contrast" instead of building a static everything-page. Prior art for CLI-level multi-way comparison display is thin — [hyperfine](https://github.com/sharkdp/hyperfine) does N commands with relative-speed ranking and `--parameter-list` scans but no factorial contrasts; [airspeed velocity's `asv compare`](https://asv.readthedocs.io/en/stable/using.html#comparing-the-benchmarking-results) is strictly two revisions; Google Benchmark's [`compare.py`](https://github.com/google/benchmark/blob/main/docs/tools.md) is two runs with a U-test — so a small contrast language would be genuinely novel and worth keeping tiny.
6. **Guard the stats as the matrix grows.** The old report's "unclear" sprawl and undefined-Fieller cells were a flexibility tax. With an explicit contrast list, the list length is known: apply Holm–Bonferroni across the *requested* contrasts (not every cell), and keep the suite gate (ratio of sums) separate from the descriptive geomean as the old SQL carefully did.
7. **If nothing is built**: the current system plus the nightly pattern already covers the user's four simple ratios (four cached-pair invocations over one cache); only the interaction estimate and single-view display are truly missing. The cheapest real step is a report-only command that reads the existing cache and prints requested contrasts — no collection changes at all.
