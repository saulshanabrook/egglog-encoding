# Code map: `benchmarking/` on branch `relations-encoding` (pair-only benchmark harness)

Scope: `/Users/saul/p/egglog-encoding/benchmarking/` — `benchmark.py`, `models.py`, `targets.py`, `workloads.py`, `collection.py`, `processes.py`, `profile.py`, and `reports/` (`store.py`, `analysis.py`, `catalog.py`, `presentation.py`, `render.py`, `interactive.py`, `interactive_runtime.py`, `interactive.js`, `interactive.css`). There is **no `reports/sql/` directory**. Entry point is the repo-root shim `/Users/saul/p/egglog-encoding/bench.py` (`uv run`; `profile` subcommand dispatches to `benchmarking/profile.py`, everything else to `benchmarking/benchmark.py`).

---

## 1. End-to-end data flow

### 1a. CLI (`benchmark.py:53-140`, `main` at 217-288)

Exact flags: positional `files…`, `--fact-directory`, `--target` (candidate; `.` | `/path` | `@git-ref` | `#pr` | `label=source` | cache-only `label=`), `--backend {main,dd}`, `--treatment {off,term,proofs,causal-receipts,causal-proofs}` (default **proofs**), `--compare-target` (default = candidate target), `--compare-backend` (default main), `--compare-treatment` (default **off**), `--detail {summary,files,phases,rulesets}`, `--report` (append-only JSONL, default `.reports.jsonl`), `--format {rich,markdown}`, `--rounds` (default 6), `--timeout-sec` (default 120), `--force-run`, `--open` (write + open interactive HTML).

So the implicit default comparison is *same target, main/off (baseline) vs main/proofs (candidate)* — the pair is baked into the flag grammar itself (`--X` = candidate, `--compare-X` = baseline).

### 1b. Endpoint requests → target materialization/build

- `endpoint_requests` (`benchmark.py:161-178`) returns exactly `(baseline, candidate)` `EndpointRequest(target, backend, treatment)`; rejects equality.
- `models.py:36-64`: `BACKEND_SPECS` — `main` supports all 5 treatments, no flags; `dd` supports only `term`/`proofs`, adds `--backend dd` flag and `dd-backend` cargo feature. `validate_backend_treatment` runs in every `EndpointRequest`/`BenchmarkEndpoint` `__post_init__`.
- `resolve_targets` (`collection.py:152-212`) — **already N-ary** (takes `request_groups: tuple[(TargetRequest, tuple[EndpointRequest,...]), ...]`). Per request: cache-only `label=` lookup via `ReportStore.find_label_pointer` (reuse without any build if `label_has_enough_rows`, `collection.py:262-285`); otherwise materialize:
  - `@ref` → `git worktree add --detach` under `<repo>/.bench-worktrees/<label>` (reusing any clean worktree already at that sha) — `targets.py:135-159`;
  - `#N` → `git fetch origin +refs/pull/N/head:refs/remotes/origin/pr/N` then worktree — `targets.py:162-179`;
  - path → its git root.
- Build once per canonical checkout with the **union** of cargo features needed by all backends touching that checkout (`collection.py:191-203`): `cargo build --release -p egglog-experimental [--features dd-backend]` (`targets.py:220-246`); result hashed → `binary_sha256` (`sha256:<hex>` of the executable bytes).
- Workloads (`workloads.py:39-83`): explicit files or the 5-file `DEFAULT_WORKLOADS` suite (math-microbenchmark, eggcc-2mm-pass1, pointer-analysis-small + fact dir, hardboiled_conv1d_32, luminal-llama). Each `FileSpec` carries `sha256` of the file and `fact_directory_sha256` (deterministic dir hash). Validation: unique `(sha256, fact_dir_sha256)` identities; no top-level `(prove …)` command (real tokenizer, `workloads.py:86-142`).

### 1c. Collection plan → JSONL cache

- `ComparisonSpec` (`models.py:160-179`): `baseline`, `candidate`, `files`, `rounds`, `timeout_sec`; requires distinct `cache_identity = (binary_sha256, backend, treatment)`.
- `build_collection_plan` (`collection.py:107-149`) — **already N-ary over endpoints**: for each file × endpoint builds a `CacheKey`, asks the store for latest statuses, `missing = rounds − cached` (or `rounds` under `--force-run`).
- Preflight (`collection.py:318-345`): fresh targets must answer `--help` containing the literal `--timing-summary`.
- `collect_rows` (`collection.py:442-536`): round-robin across runs (round 1 of every cell before round 2 — good interleaving hygiene). Each observation: `run_process` (`collection.py:288-315`) executes

  ```
  <binary> --timing-summary <tmp>/timing-summary.json --mode no-messages -j 1 \
      [--fact-directory D] [--backend dd] [--term-encoding|--proofs|--causal-receipts|--causal-slice --proofs] file.egg
  ```

  (`targets.py:284-300`, treatment flags at `targets.py:27-34`). Wall time via `time.perf_counter` around `os.wait4` (no polling overhead; `processes.py:119-146`), peak RSS from `rusage.ru_maxrss` (Darwin bytes / Linux KiB, `processes.py:164-169`), timeout kills the whole process group. Workload hashes re-verified after every run (`workloads.py:145-159`).

**Exact `CacheKey` fields** (`store.py:79-106`) — the *only* identity used to select reusable rows:

| field | note |
|---|---|
| `binary_sha256` | hash of built executable (subsumes git sha, dirtiness, cargo features, toolchain) |
| `file_sha256` | workload content hash |
| `treatment` | `off\|term\|proofs\|causal-receipts\|causal-proofs` |
| `timeout_sec` | int; different timeout ⇒ different cache universe |
| `backend` | default `"main"` |
| `fact_directory_sha256` | `""` when none |

`rounds` is **not** in the key — it is a *selection depth*: `latest_records(key, rounds)` returns the newest ≤ rounds rows ordered by `(started_at, row_index)` (`store.py:195-214`).

**Exact JSONL row schema** — `ReportRecord` (`store.py:51-76`), one JSON object per line, `report_schema_version: 1`:
`started_at` (UTC ISO, second granularity), `status` (`success|timed-out|failure`), `target_label`, `target_source`, `target_path`, `target_git_ref`, `target_git_sha`, `target_is_dirty`, `binary_sha256`, `file_path`, `file_sha256`, `fact_directory_path`, `fact_directory_sha256`, `backend`, `treatment`, `timeout_sec`, `wall_sec`, `max_rss_bytes`, `error_exit_code`, `error_signal`, `error_message`, `timing_summary` (nullable; **required** when status=success). `timing_summary` (`schema_version: 2`) = `{rulesets: [{name, search_ns, apply_ns, unattributed_ns, merge_ns, rebuild_ns}]}`. Store validates every line on load and rejects the whole file on any schema mismatch (`store.py:132-147`, `273-290`).

### 1d. Analysis (`reports/analysis.py`)

`analyze_pair` (174-198) selects observations per `(endpoint_order ∈ {0,1}, file_order)` via `latest_records`, flags issues (missing rows / failure / timeout selected), then:

- **Per-cell estimate** (`_sample_estimate`, 558-573): mean = `statistics.fmean`; `var_mean = sample variance / n`; 95% CI = mean ± `t.ppf(0.975, rounds−1) · sqrt(var_mean)`.
- **Ratio** (`_ratio_estimate`, 262-294): point = `candidate_mean / baseline_mean`; **Fieller CI**: `a = m_b² − t²v_b`, `d = m_c² − t²v_c`, `radicand = (m_b·m_c)² − a·d`, center `m_b·m_c/a`, half-width `sqrt(radicand)/a`; degenerates to `point_only` when `a ≤ 0` or radicand < 0, or n < 2. `ResultClass`: `lower` (ci_high < 1), `higher` (ci_low > 1), `unclear` (CI spans 1), `point_only`, `invalid`.
- **Suite summary** (309-370): sums per-file wall means and sums `var_mean`s (independence assumption), Fieller on the sums; plus lowest/highest-ratio file tails for wall and RSS.
- **Phases** (373-467): six phases — `search, apply, unattributed ("Execution overhead"), merge, rebuild` summed across rulesets per observation, plus `outside = wall·1e9 − recorded_total` (can be negative → `!` marker). Per-phase mean/CI per endpoint, share of endpoint wall, signed delta ns, and `Δ contribution = phase_delta / wall_delta`.
- **Rulesets** (490-555): per-ruleset totals with **zero-padding** for observations where a ruleset never fired (526-537), top-10 by |total Δ| per file, per-phase deltas.

### 1e. Presentation → render

- `presentation.py:build_report_catalog` (77-97) → renderer-neutral `ReportCatalog` (`catalog.py`): sections `selection`, `summary`, `files`, `phases`, `rulesets`; each a tree of `ReportTable(columns, rows of ReportCell(raw, display, tone))` / `ReportMessage`. Stable ids via `report_id(*parts)` = JSON array string. Notable: the "joint comparison" warning (`presentation.py:137-152`) fires when >1 of {binary, backend, treatment} differ — the harness *knows* about confounded contrasts and warns rather than model them.
- `render.py`: Rich (sections re-ordered `rulesets, phases, files, selection, summary` so terminals end on the verdict; 120-col warning) and Markdown (canonical order). Both are dumb catalog serializers — zero statistics, zero pair knowledge.
- Interactive HTML (`interactive.py`): one self-contained file next to the JSONL (`.reports.html`), embedding (base64) the **entire JSONL**, the initial all-sections catalog payload, the sources of 8 Python modules, and a bootstrap that loads Pyodide 314.0.2 + SciPy from jsDelivr. `interactive_runtime.py:_cache_universe` (306-355) enumerates from *all rows* the distinct endpoints (binary×backend×treatment), files, timeouts, and max cached rounds; the JS form (`interactive.js:39-134`) offers baseline/candidate dropdowns + swap, file checkboxes, timeout dropdown, rounds number input, and recomputes catalogs **cache-only** in the browser via the identical Python analysis stack.

### 1f. `profile.py` (briefly)

Separate single-endpoint path: Samply CPU profiles, own cache at `.profiles/v3/<binary-hash>/<file-hash>/<facts>/<backend>-<treatment>-<mode>.json.gz`, `profiling` cargo profile (so a *different* binary hash universe from benchmark rows), duration-calibrated iteration count, macOS-only CPU summary. No JSONL interaction. No pair concept at all.

---

## 2. Exhaustive pair-only assumptions (file:line)

Types/fields hardcoding baseline+candidate:

- `models.py:160-179` — `ComparisonSpec.baseline` / `.candidate` (162-165); pair-distinctness invariant (178-179).
- `analysis.py:91-97` — `SummaryView` carries exactly one `ratio`.
- `analysis.py:100-107` — `FileComparisonView.baseline/.candidate/.ratio`.
- `analysis.py:110-118` — `PhaseComparisonView.baseline/.candidate/delta/wall_delta_contribution`.
- `analysis.py:121-129` — `RulesetComparisonView.baseline/.candidate/.delta`.
- `analysis.py:132-138` — `PairReportViewData` (name + shape).
- `analysis.py:165-171` — `_RankedRuleset.baseline/.candidate`.
- `interactive_runtime.py:30-38` — `_ScopeRequest.baseline_endpoint_id/candidate_endpoint_id`.
- `interactive_runtime.py:41-49` — `InteractiveScope` same two fields.

Functions hardcoding 2-endpoint structure:

- `benchmark.py:53-140` — CLI grammar itself: `--X` (candidate) vs `--compare-X` (baseline); docstrings 1, 54 declare "pair-only".
- `benchmark.py:161-178` — `endpoint_requests` returns exactly 2; equality check 176-177.
- `benchmark.py:181-190` — `group_endpoint_requests(baseline, candidate)` positional pair.
- `benchmark.py:193-214` — `collection_plans` iterates `(comparison.baseline, comparison.candidate)` (201).
- `benchmark.py:245-259` — `ComparisonSpec(baseline=…, candidate=…)` construction.
- `analysis.py:174-198` — `analyze_pair` API.
- `analysis.py:201-210` — `_selected_observations` enumerates `(baseline, candidate)` → `endpoint_order ∈ {0,1}` (206); every downstream dict is keyed `(endpoint_order, file_order[, metric|phase])`.
- `analysis.py:240-259` — `_file_comparisons` indexes `(0, …)` / `(1, …)` (248-249).
- `analysis.py:262-294` — `_ratio_estimate` is inherently binary (candidate/baseline + Fieller).
- `analysis.py:309-370` — `_summary_rows` indexes 0/1 (315-316).
- `analysis.py:373-423` — `_phase_comparisons` indexes 0/1 (394-395, 404-405).
- `analysis.py:490-523` — `_ruleset_comparisons` `endpoint_order in (0, 1)` (500), indexes 0/1 (503-504).
- `analysis.py:544-555` — `_ruleset_phase_deltas` indexes 1/0 (551-552).
- `presentation.py:54-65` — captions hardcode "candidate / baseline", "candidate − baseline" wording.
- `presentation.py:104-152` — `_selection_section`: role loop over exactly `("baseline", …), ("candidate", …)` (126); joint-change warning compares exactly the two endpoints across exactly 3 axes (137-141).
- `presentation.py:183` — summary title "`candidate` vs `baseline`".
- `presentation.py:284, 296-297` — files tables: `baseline`/`candidate` columns.
- `presentation.py:325-326, 338-339` — phase tables: two endpoint columns + delta.
- `presentation.py:383-398` — ruleset tables: baseline/candidate totals + deltas.
- `interactive_runtime.py:120-134` — `initial_payload` reorders choices around `(comparison.baseline, comparison.candidate)` (124).
- `interactive_runtime.py:163-171` — `_comparison` builds a 2-endpoint `ComparisonSpec`.
- `interactive_runtime.py:173-211` — `_parse_scope` validates the two ids; equality rejection (195-196).
- `interactive_runtime.py:237-238, 256-265` — payload/scope serialization of the two ids.
- `interactive.js:49-63` — exactly two `<select>`s ("Baseline", "Candidate") + Swap button; `:118-119` — request carries the two ids.
- `catalog.py:1` — docstring only ("pair reports"); the model itself is generic.

**No pair assumptions in:** `store.py` (rows are per-observation; `CacheKey` is per-endpoint), `collection.py` core (`build_collection_plan`/`resolve_targets`/`label_has_enough_rows`/`collect_rows` all take N endpoints — only their *callers* pass 2), `processes.py`, `targets.py`, `workloads.py`, `render.py`, `catalog.py` (structurally), `profile.py` (single-endpoint), `models.py` apart from `ComparisonSpec`.

---

## 3. What is already general

**The cache is fully per-endpoint-cell.** A row records one `(binary, backend, treatment, file, facts, timeout)` observation with no reference to any comparison, role, or partner endpoint. Therefore **an N-cell matrix can be assembled today from cached rows of many past pair runs with zero re-collection**, exactly as the interactive report already proves: `_cache_universe` (`interactive_runtime.py:306-355`) reconstructs every endpoint/file/timeout choice from the raw JSONL, and any pair among them can be recomputed browser-side. The missing piece is only *analysis/presentation over >2 cells at once*, not data.

**What makes two rows the same cell (poolable):** identical `CacheKey` 6-tuple. **What makes two cells comparable in a report:** nothing structural — analysis only needs each cell's own selection; ratios require baseline mean > 0. Practical comparability caveats:

- `timeout_sec` is in the key: rows collected at 120 s and 180 s are *different cells* even for the same binary/file — a real friction for matrix assembly across historical runs (the interactive UI exposes a single timeout selector for this reason, `interactive.js:80-91`).
- `rounds` does **not** partition the cache; any depth ≤ cached count is selectable per cell (`store.latest_records`), and the interactive form caps at the max across cells.
- `binary_sha256` is the target identity, which is stricter than git sha: the same commit rebuilt with a different **cargo feature union** (e.g., a run that also touched the `dd` backend adds `--features dd-backend` to *every* endpoint sharing the checkout — `collection.py:195-203`, `models.py:51-54`), a different toolchain, or a dirty tree yields a new hash and thus incomparable-by-key cells. Nothing in the row records the feature set, so such splits look like unexplained cache misses.
- Statuses: selection takes the latest N rows *regardless of status*; failures/timeouts poison the cell (`analysis.py:213-221` → `invalid` ratio) rather than being skipped.
- Cross-cell time skew is accepted silently: cells may come from runs weeks apart on different machine load; only `started_at` is recorded (no host/load metadata).

**Also already general:** the whole collection pipeline is N-endpoint (§2 end); the catalog/render layers are comparison-agnostic table serializers; `_sample_estimate` is a per-cell primitive and `_ratio_estimate` is a reusable 2-cell contrast primitive.

---

## 4. Full menu of recorded measures usable as comparison measures

Per observation (JSONL row):

1. `wall_sec` — end-to-end child wall time (perf_counter around wait4).
2. `max_rss_bytes` — rusage peak RSS.
3. `status` (+ `error_exit_code`/`error_signal`/`error_message`) — usable as a success-rate/robustness measure; today only a validity gate.
4. `timing_summary.rulesets[]` — per-ruleset `search_ns`, `apply_ns`, `unattributed_ns`, `merge_ns`, `rebuild_ns`; aggregable to: per-phase suite totals, per-ruleset totals, `outside = wall − Σ recorded`, phase share of wall, ruleset count.
5. `started_at` — ordering only.

Dimensions (potential matrix axes) recorded per row: target (`git_sha`/`git_ref`/`label`/`is_dirty`/`binary_sha256`), `backend`, `treatment`, workload (`file_sha256` + `fact_directory_sha256`), `timeout_sec`.

Comparison measures computed today: wall ratio + Fieller CI, RSS ratio + Fieller CI, suite wall ratio (summed means/variances), per-phase signed delta (ns) and Δ-contribution share, per-ruleset total/phase signed deltas. Not yet measures but recorded: failure/timeout counts. Not recorded at all: iterations/e-graph sizes, host/load metadata, and the anticipated egg-equivalence data (would enter as new fields in `timing_summary` or as sibling nullable row fields, gated by the two schema-version constants in `store.py:26-30`).

---

## 5. Blast radius: pair → N-cell matrix + contrast specs

**Fundamental redesign (4 files):**

- `models.py` — replace/supplement `ComparisonSpec` with a cell-set model (`cells: tuple[BenchmarkEndpoint, ...]` × files × rounds × timeout) plus a `ContrastSpec` (numerator cell selector, denominator cell selector, measure, scale) where an interaction is a contrast of contrasts. ~60 lines but it is the identity spine every other module imports.
- `benchmark.py` — CLI grammar: today's `--X`/`--compare-X` cannot express a grid. Needs either repeated `--endpoint target=…,backend=…,treatment=…` or cross-product flags (`--targets old,new --treatments off,proofs`) plus `--contrast` selectors. Parsing, `endpoint_requests`, `collection_plans` rewire (though `collection_plans`' body already loops over endpoints generically).
- `reports/analysis.py` — the real work. `_selected_observations`/`_metric_estimates` generalize trivially (key by cell index instead of `{0,1}`), and `_sample_estimate`/`_ratio_estimate` survive as primitives; but every `*View` NamedTuple, `_summary_rows`, `_phase_comparisons`, `_ruleset_comparisons` bakes in two roles. New need: contrast evaluation over arbitrary cell pairs and **ratio-of-ratios** for the "did proofs overhead get worse" interaction — Fieller does not compose, so interactions want log-scale contrasts (Δlog with summed `var_mean/mean²` via the delta method, or bootstrap) rather than nested Fieller.
- `reports/presentation.py` — sections re-keyed from role-columns to matrix/faceted tables (cells as columns or rows, contrasts as their own table). Captions/titles all reworded. The joint-change warning (137-152) generalizes nicely into per-contrast "this contrast varies k axes" metadata.

**Mechanical only (3-4 files):**

- `reports/interactive_runtime.py` — scope shape gains a cell list + contrast list; `_cache_universe`, payload plumbing, and validation patterns all carry over. The universe discovery is *already* the matrix enumerator.
- `reports/interactive.js` (+ `.css`) — replace two dropdowns with N cell selectors / axis-role pickers; form/submit/render loop unchanged.
- `benchmark.py::main` wiring; `reports/__init__.py`/docstrings.

**Untouched (7+ files):**

- `reports/store.py` (row schema and `CacheKey` need no change — the strongest asset), `collection.py` (already N-endpoint; only callers change), `processes.py`, `targets.py`, `workloads.py`, `reports/render.py`, `reports/catalog.py` (its generic table/cell/tone model renders any matrix), `profile.py`, `samply_analysis.py`.

**Where the interactive HTML already handles multiple dimensions:** the selector universe spans every endpoint (target×backend×treatment), file, timeout, and rounds present in the whole JSONL (`interactive_runtime.py:306-355`, `interactive.js:24-102`); retargeting is cache-only and instant. It is a matrix *browser* constrained to one pair at a time — which makes it the cheapest venue to prototype N-cell views: no collection, no CLI changes, same embedded Python.

---

## Implications for this harness

Everything below follows from the code; the two external references are: Fieller's theorem (ratio-of-means CI used at `analysis.py:262-294`; https://en.wikipedia.org/wiki/Fieller%27s_theorem) and Vega-Lite as the design analogy for a small declarative spec compiled to views ("Vega-Lite: A Grammar of Interactive Graphics", A. Satyanarayan, D. Moritz, K. Wongsuphasawat, J. Heer, IEEE TVCG (Proc. InfoVis) 2017; https://ieeexplore.ieee.org/document/7539624; docs https://vega.github.io/vega-lite/). The broader literature survey is a sibling deliverable.

1. **The matrix is an analysis/presentation feature, not a collection feature.** The JSONL is already a tidy per-cell fact table; `collection.py` already plans N endpoints; the interactive runtime already enumerates the full cache universe. Do not touch `store.py` — its `CacheKey` is exactly the cell identity a matrix needs. A first increment can be *cache-only*: a `report`/`matrix` mode (or the interactive HTML) that assembles cells from existing rows and refuses to collect.
2. **Model contrasts as a tiny algebra, not more flags.** The natural spec is Vega-Lite-shaped: dimensions `{target, backend, treatment, file}` bound to roles `{fixed, axis, contrast}`; a contrast = ordered pair of cell selectors + measure + scale (`ratio | diff | log-ratio`); an interaction = contrast whose operands are contrasts. `ComparisonSpec` becomes the degenerate one-contrast case, which keeps the existing CLI as sugar.
3. **Switch chained contrasts to the log scale.** Fieller (`_ratio_estimate`) is fine for a single ratio but does not compose into ratios-of-ratios. For the "(new-proofs/new-off)/(old-proofs/old-off)" interaction use `Δlog = (log m₁₁ − log m₁₀) − (log m₀₁ − log m₀₀)` with variance `Σ var_meanᵢ/mᵢ²` (delta method) and a t CI, exponentiated back; keep Fieller for leaf ratios if continuity with today's numbers matters. All inputs (`mean`, `var_mean`, `sample_count` per cell) already exist in `_MetricEstimate`.
4. **Two comparability traps to fix before matrices amplify them:** (a) record the cargo feature set (or normalize it) in each row — feature-union builds currently split `binary_sha256` for the same commit invisibly (`collection.py:195-203`); (b) decide a policy for `timeout_sec` mismatches across historical runs (either relax it out of the display key with a warning, or surface it as an axis), since it silently fragments otherwise-identical cells.
5. **Presentation cost is the real budget line.** `catalog.py`/`render.py` will render any table, but pair wording is woven through every `presentation.py` section (§2). Plan the generalization as: per-cell estimate tables (cells × measures) + per-contrast tables (contrast × file × measure), and derive today's five sections as the 2-cell special case — otherwise you maintain two presentation stacks.
6. **Prototype in the interactive HTML first.** It already ships the whole cache and the whole Python stack to the browser; adding an N-cell/contrast form there validates the spec language and the statistics with zero CLI/back-compat risk, then the CLI grammar can be designed against a proven model.
7. **New measures slot in cleanly.** Egg-equivalence data should enter as versioned additions to `timing_summary` (bump `TIMING_SUMMARY_SCHEMA_VERSION`) or nullable row fields; the metric menu in `analysis.py` (`_METRICS`, `MetricName`) is the only registry to extend — one more reason to make "measure" a first-class axis of the contrast spec now.
