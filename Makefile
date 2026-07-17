.PHONY: \
	check nits test python-check python-nits rust-check rust-nits \
	proof-tests benchmark-smoke update-snapshots format \
	python-lock python-format-check python-lint python-typecheck python-test \
	rust-format-check rust-clippy rust-test

BENCHMARK_SMOKE_REPORT ?= /tmp/egglog-encoding-bench-smoke.jsonl

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

rust-nits: rust-format-check rust-clippy

rust-format-check:
	cargo fmt --all -- --check

rust-test:
	cargo test --workspace
	cargo test -p egglog-experimental --features dd-backend --test timing_summary_cli

rust-clippy:
	cargo clippy --workspace --all-targets -- -D warnings
	cargo clippy -p egglog-experimental --features dd-backend --all-targets -- -D warnings

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

update-snapshots:
	uv run --locked pytest -q --snapshot-update --snapshot-details

format:
	uv run --locked ruff format .
	cargo fmt --all
