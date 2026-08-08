.PHONY: \
	check nits test python-check python-nits rust-check rust-nits \
	proof-tests benchmark-smoke nightly nightly-local nightly-uv nightly-rustup \
	lean-check lean-difftest \
	update-snapshots format \
	python-lock python-format-check python-lint python-typecheck python-test \
	rust-format-check rust-clippy rust-doc-links rust-test

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

# elan installs here by default and is not on PATH in a non-login shell.
LEAN_BIN_DIR ?= $(HOME)/.elan/bin

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
	cargo test --workspace
	cargo test -p egglog-experimental --features dd-backend --test timing_summary_cli

rust-clippy:
	cargo clippy --workspace --all-targets -- -D warnings
	cargo clippy -p egglog-experimental --features dd-backend --all-targets -- -D warnings

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
		--report "$(BENCHMARK_SMOKE_REPORT)" --format markdown \
		egglog/tests/integer_math.egg > /dev/null
	uv run --locked python -c \
		'from pathlib import Path; import sys; from benchmarking.reports.store import ReportStore; assert ReportStore(Path(sys.argv[1])).row_count > 0' \
		"$(BENCHMARK_SMOKE_REPORT)"

# Benchmark each endpoint in nightly_bench.py's ENDPOINTS on this checkout and on
# main, then copy eval-live's interactive report to nightly/output/. The
# egraphs-good nightly service (nightly.cs.washington.edu) runs this target and
# serves that directory, matching `report=` in the nightly configuration.
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

# The Lean formalization in semantics/. Kept out of `check` so the Rust and Python
# suites do not depend on a Lean toolchain; `elan` and a Mathlib cache are needed,
# see semantics/README.md. `lake build` only warns on a `sorry`, so the sources are
# grepped for one as well.
lean-check:
	cd semantics && PATH="$(LEAN_BIN_DIR):$$PATH" lake build
	! grep -rnw --include='*.lean' sorry semantics/EgglogSemantics

# Differentially test the Lean semantics against egglog: for each generated program, the
# Lean interpreter's per-constructor row counts against egglog's `(print-size)`. Needs a
# release egglog binary (`cargo build --release -p egglog`) or EGGLOG_BIN.
lean-difftest:
	./scripts/difftest.sh

update-snapshots:
	uv run --locked pytest -q --snapshot-update --snapshot-details

format:
	uv run --locked ruff format .
	cargo fmt --all
