.PHONY: \
	check nits test python-check python-nits rust-check rust-nits \
	proof-tests benchmark-smoke nightly nightly-local nightly-uv nightly-rustup \
	update-snapshots format \
	python-lock python-format-check python-lint python-typecheck python-test \
	rust-format-check rust-clippy rust-doc-links rust-test

BENCHMARK_SMOKE_REPORT ?= /tmp/egglog-encoding-bench-smoke.jsonl
REPRODUCE_ARGS ?=
RUST_TEST_ARGS ?=

# No Ubuntu release packages uv, so `make nightly` installs a pinned copy into
# the checkout when uv is missing from PATH. uv then downloads its own CPython,
# so the runner needs neither uv nor Python 3.12.
UV_VERSION ?= 0.11.30
UV_BOOTSTRAP_DIR ?= $(CURDIR)/.uv/$(UV_VERSION)
NIGHTLY_UV = $(shell command -v uv || echo $(UV_BOOTSTRAP_DIR)/uv)

# Ubuntu's cargo predates rust-toolchain.toml's pin, so the nightly needs
# rustup's shims; scripts/nightly_bench.py puts them first on PATH.
CARGO_HOME_DIR ?= $(HOME)/.cargo

# Full validation is hygiene followed by tests.
check: nits test

# Nits are intentionally test-free.
nits: python-nits rust-nits

test: python-test rust-test

python-check: python-nits python-test

python-nits: python-lock python-format-check python-lint python-typecheck

python-lock:
	uv lock --check

python-format-check:
	uv run --locked ruff format --check .

python-lint:
	uv run --locked ruff check .

python-typecheck:
	uv run --locked mypy .

python-test:
	uv run --locked pytest -q

rust-check: rust-nits rust-test

rust-nits: rust-format-check rust-clippy rust-doc-links

rust-format-check:
	cargo fmt --all -- --check

rust-test:
	cargo test --workspace -- $(RUST_TEST_ARGS)

rust-clippy:
	cargo clippy --workspace --all-targets -- -D warnings

# Clippy does not resolve doc links, and plain `cargo doc` skips the private
# items most of this codebase documents, so a rename leaves stale links behind
# unless rustdoc is run over them too.
rust-doc-links:
	RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --document-private-items --workspace

# This is a name-filtered subset of rust-test, useful for proof iteration.
proof-tests:
	cargo test --workspace --test files 'proofs/'

# Smoke the runner on small files, not the full local benchmark suite.
benchmark-smoke:
	rm -f -- "$(BENCHMARK_SMOKE_REPORT)"
	uv run --locked ./bench.py \
		egglog-experimental/tests/math-microbenchmark-rational.egg \
		egglog-experimental/tests/disequality/congruence.egg --rounds 1 \
		--report "$(BENCHMARK_SMOKE_REPORT)" --format markdown > /dev/null
	uv run --locked python -c \
		'from pathlib import Path; import sys; from benchmarking.reports.store import ReportStore; assert ReportStore(Path(sys.argv[1])).row_count > 0' \
		"$(BENCHMARK_SMOKE_REPORT)"

# Publish nightly/output/ for the egraphs-good nightly service
# (nightly.cs.washington.edu), which runs this target and serves that directory.
nightly: nightly-uv nightly-rustup
	CARGO_HOME="$(CARGO_HOME_DIR)" $(NIGHTLY_UV) run --locked python scripts/nightly_bench.py

nightly-uv:
	@command -v uv >/dev/null || test -x "$(UV_BOOTSTRAP_DIR)/uv" || \
		curl -LsSf https://astral.sh/uv/$(UV_VERSION)/install.sh \
			| env UV_INSTALL_DIR="$(UV_BOOTSTRAP_DIR)" UV_NO_MODIFY_PATH=1 sh

nightly-rustup:
	@test -x "$(CARGO_HOME_DIR)/bin/rustup" || \
		curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
			| env CARGO_HOME="$(CARGO_HOME_DIR)" sh -s -- \
				-y --no-modify-path --default-toolchain none

# The nightly host's run at one round, for trying it locally. nightly/output/ is
# git-ignored, so this writes it just as the host does.
nightly-local: nightly-uv nightly-rustup
	CARGO_HOME="$(CARGO_HOME_DIR)" $(NIGHTLY_UV) run --locked python scripts/nightly_bench.py --rounds 1

update-snapshots:
	uv run --locked pytest -q --snapshot-update --snapshot-details

format:
	uv run --locked ruff format .
	cargo fmt --all

# Same committed input, six implementations, no proof recording or extraction.
PARAMETER_FILE := benchmarks/disequality/parameter-analysis.egg
PARAMETER_ROUNDS ?= 10
PARAMETER_TIMEOUT_SEC ?= 300
PARAMETER_ARGS = $(PARAMETER_FILE) --target figures=. --rounds $(PARAMETER_ROUNDS) --timeout-sec $(PARAMETER_TIMEOUT_SEC)

.PHONY: parameter-test parameter-bench figures-parameter figures-parameter-test
parameter-test:
	uv run --locked pytest -q benchmarks/disequality/native/test_original.py

parameter-bench:
	./bench.py $(PARAMETER_ARGS) \
		--treatment off --compare-treatment off --disequality-encoding ee --compare-disequality-encoding nee
	./bench.py $(PARAMETER_ARGS) \
		--treatment egg-de --compare-treatment egg-nee
	./bench.py $(PARAMETER_ARGS) \
		--treatment egg-ee --compare-treatment egg-oee

figures-parameter: parameter-bench
	$(MAKE) figures/parameter-analysis.svg figures/parameter-analysis.png
	@printf '%s\n' "$(abspath figures/parameter-analysis.svg)" "$(abspath figures/parameter-analysis.png)"

.DELETE_ON_ERROR:
NPX ?= npx --yes
VEGA = $(NPX) --package=vega@6.4.0 --package=vega-lite@6.4.3 --package=vega-cli@6.4.0 --package=canvas@3.2.3

figures/parameter-analysis.svg: figures/parameter-analysis.vl.json .reports-grouped.json Makefile
	cd figures && $(VEGA) vl2svg $(notdir $<) $(notdir $@)

figures/parameter-analysis.png: figures/parameter-analysis.vl.json .reports-grouped.json Makefile
	cd figures && $(VEGA) vl2png $(notdir $<) $(notdir $@) -s 3

figures-parameter-test:
	cd figures && $(VEGA) node --test parameter.test.mjs

# Source generation and correctness diagnostics are separate from timing.
.PHONY: reproduce-benchmarks validate-benchmarks expanded-bench-recording expanded-bench
reproduce-benchmarks validate-benchmarks: export EGGLOG_BENCH_MEMORY_GUARD = 1
reproduce-benchmarks:
	uv run --locked python -m scripts.suite_reproduction $(REPRODUCE_ARGS)

validate-benchmarks:
	uv run --locked python -m scripts.validate_benchmarks --suite expanded --timeout-sec $(EXPANDED_TIMEOUT_SEC)

EXPANDED_ROUNDS ?= 10
EXPANDED_TIMEOUT_SEC ?= 300
EXPANDED_ARGS = --target figures=. --rounds $(EXPANDED_ROUNDS) --timeout-sec $(EXPANDED_TIMEOUT_SEC)

expanded-bench-recording expanded-bench: export EGGLOG_BENCH_MEMORY_GUARD = 1
# Keep collectors serial under make -j; the extraction comparison reuses off rows.
expanded-bench-recording:
	./bench.py --suite expanded $(EXPANDED_ARGS) \
		--treatment proofs --compare-treatment off

expanded-bench: expanded-bench-recording
	./bench.py --suite expanded $(EXPANDED_ARGS) \
		--treatment proof-extraction --compare-treatment off
	./bench.py --suite math-11 $(EXPANDED_ARGS) \
		--treatment egg-proof-extraction --compare-treatment egg

EXPANDED_SPECS := figures/expanded/math-cutoff-11.vl.json figures/expanded/proof-overhead-cdf.vl.json
EXPANDED_IMAGES := $(EXPANDED_SPECS:.vl.json=.svg) $(EXPANDED_SPECS:.vl.json=.png)
.PHONY: figures figures-all figures-all-cached figures-bench figures-data figures-expanded figures-expanded-data figures-expanded-cached figures-expanded-archive figures-expanded-test figure-inventory
figures: figures-all
figures-all: figures-expanded
figures-all-cached: figures-expanded-cached
figures-bench: expanded-bench
figures-data: figures-expanded-data
figures-expanded-data: expanded-bench
	$(MAKE) figure-inventory

# A recursive Make sees the final write-if-changed metadata and snapshot mtimes.
figures-expanded: figures-expanded-data
figures-expanded-cached: figure-inventory
figures-expanded figures-expanded-cached:
	$(MAKE) $(EXPANDED_IMAGES)
	@printf '%s\n' $(foreach image,$(EXPANDED_IMAGES),"$(abspath $(image))")

FIGURE_ARCHIVE ?= figures/expanded/paper-evidence.zip
figures-expanded-archive: figures-expanded-cached
	uv run --locked python -m benchmarking.archive --output "$(FIGURE_ARCHIVE)"

figure-inventory:
	uv run --locked python -m benchmarking.figure_inventory --timeout-sec $(EXPANDED_TIMEOUT_SEC)

figures/expanded/%.svg: figures/expanded/%.vl.json .reports-grouped.json benchmarks/local/figure-inventory.json Makefile
	cd figures/expanded && $(VEGA) vl2svg $(notdir $<) $(notdir $@)

figures/expanded/%.png: figures/expanded/%.vl.json .reports-grouped.json benchmarks/local/figure-inventory.json Makefile
	cd figures/expanded && $(VEGA) vl2png $(notdir $<) $(notdir $@) -s 3

figures-expanded-test:
	cd figures && $(VEGA) node --test expanded.test.mjs
