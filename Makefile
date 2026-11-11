# Complete validation, hygiene and the external nightly entrypoint.

.DEFAULT_GOAL := check

.PHONY: check nits test-python test-rust test-figures nightly

export CARGO_PROFILE_DEV_DEBUG ?= 0
export CARGO_PROFILE_TEST_DEBUG ?= 0
export CARGO_INCREMENTAL ?= 0
export RUST_TEST_ARGS

UV_VERSION ?= 0.11.30
UV_BOOTSTRAP_DIR ?= $(CURDIR)/.uv/$(UV_VERSION)
NIGHTLY_UV = $(shell command -v uv || echo $(UV_BOOTSTRAP_DIR)/uv)
CARGO_HOME_DIR ?= $(HOME)/.cargo
NPX ?= npx --yes
VEGA = $(NPX) --package=vega@6.4.0 --package=vega-lite@6.4.3 --package=vega-cli@6.4.0 --package=canvas@3.2.3

check: nits test-python test-rust test-figures

test-python:
	uv run --locked pytest -q

test-rust:
	cargo build --locked --release --manifest-path benchmarks/disequality/native/Cargo.toml --target-dir benchmarks/local/parameter-native/target --bins
	cargo test --locked --manifest-path benchmarks/disequality/native/Cargo.toml --target-dir benchmarks/local/parameter-native/target --features proof-driver --bin egg-nee-proofs
	cargo test --locked --workspace --exclude paper-tests -- $(RUST_TEST_ARGS)
	RUST_TEST_THREADS=$${RUST_TEST_THREADS:-2} cargo test --locked -p paper-tests -- $(RUST_TEST_ARGS)

test-figures:
	cd figures && $(VEGA) node --test eval.test.mjs

nits:
	uv lock --check
	uv run --locked ruff format --check .
	uv run --locked ruff check .
	uv run --locked mypy .
	cargo fmt --all -- --check
	cargo clippy --locked --workspace --all-targets -- -D warnings
	cargo clippy --locked --manifest-path benchmarks/disequality/native/Cargo.toml --target-dir benchmarks/local/parameter-native/target --features proof-driver --bin egg-nee-proofs -- -D warnings
	RUSTDOCFLAGS="-D warnings" cargo doc --locked --no-deps --document-private-items --workspace

# Keep the existing external nightly contract and its bootstrap behavior.
nightly:
	@command -v uv >/dev/null || test -x "$(UV_BOOTSTRAP_DIR)/uv" || \
		curl -LsSf https://astral.sh/uv/$(UV_VERSION)/install.sh \
			| env UV_INSTALL_DIR="$(UV_BOOTSTRAP_DIR)" UV_NO_MODIFY_PATH=1 sh
	@test -x "$(CARGO_HOME_DIR)/bin/rustup" || \
		curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
			| env CARGO_HOME="$(CARGO_HOME_DIR)" sh -s -- \
				-y --no-modify-path --default-toolchain none
	CARGO_HOME="$(CARGO_HOME_DIR)" $(NIGHTLY_UV) run --locked python -m benchmarking.nightly
