# Validation recipes live in scripts/check.py; these names remain public aliases.
CHECK_TARGETS := \
	check nits test python-check python-nits rust-check rust-nits proof-tests slotted-test math-parity \
	lean-check lean-difftest lean-compiled-difftest lean-congruence-test lean-provenance-test \
	lean-resugar-test \
	lean-certificate-test lean-update-fixtures lean-egg-test lean-update-egg-snapshots \
	paper paper-check paper-extract update-snapshots format \
	python-lock python-format-check python-lint python-typecheck python-test \
	rust-format-check rust-clippy rust-doc-links rust-test
.PHONY: $(CHECK_TARGETS) slotted-eval benchmark-smoke nightly nightly-local nightly-uv nightly-rustup
.DEFAULT_GOAL := check

# Make command-line overrides reach the script without shell interpolation.
# RUST_TEST_ARGS is empty by default; constrained hosts can set --test-threads=1.
export RUST_TEST_ARGS LEAN_BIN_DIR LEAN_CERTIFICATES

$(CHECK_TARGETS):
	python3 -m scripts.check $@

BENCHMARK_SMOKE_REPORT ?= /tmp/egglog-encoding-bench-smoke.jsonl

# No Ubuntu release packages uv, so `make nightly` installs a pinned copy into
# the checkout when uv is missing from PATH. uv then downloads its own CPython,
# so the runner needs neither uv nor Python 3.12.
UV_VERSION ?= 0.11.30
UV_BOOTSTRAP_DIR ?= $(CURDIR)/.uv/$(UV_VERSION)
NIGHTLY_UV = $(shell command -v uv || echo $(UV_BOOTSTRAP_DIR)/uv)

# Ubuntu's cargo predates rust-toolchain.toml's pin, so the nightly needs
# rustup's shims; scripts/nightly_bench.py puts them first on PATH.
CARGO_HOME_DIR ?= $(HOME)/.cargo

# The paper's case studies -- the S4.1 array goal and the S4.2 SDQL workloads -- on the
# encoding and on the reference through both of its matchers, at the artifact's budgets.
# Release builds of both binaries, since these are the numbers a graph is drawn from.
slotted-eval:
	uv run --locked python slotted/eval.py

# Use a disposable report path, keeping the default report cache untouched.
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

# Paper figures share one cached collection plan and the standalone Vega toolkit.
NPX ?= npx --yes
VEGA = $(NPX) --package=vega@6.4.0 --package=vega-lite@6.4.3 --package=vega-cli@6.4.0 --package=canvas@3.2.3

.PHONY: figures figures-all figures-expanded figures-parameter figures-test figures-expanded-test figures-parameter-test
figures figures-all:
	./bench.py figures

figures-expanded:
	./bench.py figures math-runtime math-memory corpus-runtime-cdf corpus-memory-cdf

figures-parameter:
	./bench.py figures disequality-runtime

figures-test figures-expanded-test figures-parameter-test:
	cd figures && $(VEGA) node --test eval.test.mjs

.PHONY: parameter-test reproduce-benchmarks validate-benchmarks
parameter-test:
	uv run --locked pytest -q benchmarks/disequality/native/test_original.py

REPRODUCE_ARGS ?=
reproduce-benchmarks:
	uv run --locked python -m benchmarks.reproduction.suite_reproduction $(REPRODUCE_ARGS)

validate-benchmarks:
	uv run --locked python -m benchmarks.reproduction.validate_benchmarks
