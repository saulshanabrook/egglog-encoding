.PHONY: \
	check nits test python-check python-nits rust-check rust-nits \
	proof-tests benchmark-smoke figures figures-bench figures-data nightly nightly-local nightly-uv nightly-rustup \
	reproduce-benchmarks \
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

# Source optimization and standalone replay only; never timed observations.
reproduce-benchmarks:
	uv run --locked python scripts/suite_acquisition.py reproduce $(REPRODUCE_ARGS)

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

# Use a disposable report path, keeping the default report cache untouched.
benchmark-smoke:
	rm -f -- "$(BENCHMARK_SMOKE_REPORT)"
	uv run --locked ./bench.py --rounds 1 \
		--report "$(BENCHMARK_SMOKE_REPORT)" --format markdown > /dev/null
	uv run --locked python -c \
		'from pathlib import Path; import sys; from benchmarking.reports.store import ReportStore; assert ReportStore(Path(sys.argv[1])).row_count > 0' \
		"$(BENCHMARK_SMOKE_REPORT)"

# Always let the runner rebuild and reuse the default cache. One recipe keeps
# the collectors sequential even under make -j; both Math Egglog conditions are shared.
figures-bench:
	./bench.py --target figures=. \
		--treatment proofs --compare-treatment off \
		--rounds 30 --timeout-sec 120
	./bench.py --target figures=. \
		--treatment proof-extraction --compare-treatment off \
		--rounds 30 --timeout-sec 120
	./bench.py egglog-experimental/tests/math-microbenchmark-rational.egg \
		--target figures=. \
		--treatment proof-extraction --compare-treatment egg-proof-extraction \
		--rounds 30 --timeout-sec 120
	./bench.py egglog-experimental/tests/math-microbenchmark-rational.egg \
		--target figures=. \
		--treatment off --compare-treatment egg \
		--rounds 30 --timeout-sec 120

figures-data: figures-bench
	uv run --locked python -m figures.prepare

figures: figures-data
	$(MAKE) -C figures

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

# Opt-in expansion never inherits the default ten-workload selection.
EXPANDED_TIMEOUT_SEC ?= 300
.PHONY: expanded-pilot expanded-bench expanded-coverage figures-expanded-data figures-expanded
expanded-pilot expanded-bench expanded-coverage figures-expanded-data figures-expanded: export EGGLOG_BENCH_MEMORY_GUARD = 1
expanded-pilot:
	./bench.py --suite expanded --baseline-window --baseline-only --target figures=. \
		--treatment proof-extraction --compare-treatment off --rounds 30 --timeout-sec $(EXPANDED_TIMEOUT_SEC)

# Keep all collectors in one recipe so make -j cannot overlap measurements.
# Math charts cover all eleven cutoffs, independently of the overhead cohort.
# Classified Math failures remain visible; safety and command errors halt Make.
expanded-bench: expanded-pilot
	./bench.py --suite expanded --baseline-window --target figures=. \
		--treatment proofs --compare-treatment off --rounds 30 --timeout-sec $(EXPANDED_TIMEOUT_SEC)
	./bench.py --suite expanded --baseline-window --target figures=. \
		--treatment proof-extraction --compare-treatment off --rounds 30 --timeout-sec $(EXPANDED_TIMEOUT_SEC)
	uv run --locked python -m benchmarking.pilot --suite math-growth --build \
		--allow-classified-failures --timeout-sec $(EXPANDED_TIMEOUT_SEC)
	./bench.py --suite math-growth --target figures=. \
		--treatment proof-extraction --compare-treatment off --rounds 30 --timeout-sec $(EXPANDED_TIMEOUT_SEC)
	./bench.py --suite math-growth --target figures=. \
		--treatment egg-proof-extraction --compare-treatment egg --rounds 30 --timeout-sec $(EXPANDED_TIMEOUT_SEC)

expanded-coverage:
	uv run --locked python -m benchmarking.pilot --suite expanded --coverage-only \
		--report .reports.jsonl --coverage-output benchmarks/local/coverage.json --timeout-sec $(EXPANDED_TIMEOUT_SEC)

figures-expanded-data: expanded-bench
	uv run --locked python -m figures.prepare_expanded --timeout-sec $(EXPANDED_TIMEOUT_SEC)
	$(MAKE) expanded-coverage

figures-expanded: figures-expanded-data
	$(MAKE) -C figures expanded
