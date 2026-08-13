.PHONY: \
	check rust-test euf-test propel-jvm propel-native propel-smoke \
	snapshots update-snapshots propel-parity import-check

ROOT := $(abspath ../..)
PROPEL_DIR := $(ROOT)/benchmarks/disequality/inductive-prover/propel
PROPEL_BINARY ?= $(PROPEL_DIR)/.native/target/scala-3.4.2/propel
PROPEL_INPUT := $(ROOT)/benchmarks/disequality/inductive-prover/benchmarks/propel
PROPEL_TIMEOUT ?= 10
PROPEL_JOBS ?= 8
SBT ?= sbt

check: rust-test euf-test propel-jvm propel-native propel-smoke snapshots

rust-test:
	cd "$(ROOT)" && cargo test -p egglog-experimental disequality --lib
	cd "$(ROOT)" && cargo test -p egglog-disequality-backend

euf-test:
	cd "$(ROOT)" && cargo test --manifest-path benchmarks/disequality/euf-solver/Cargo.toml

propel-jvm:
	cd "$(PROPEL_DIR)" && $(SBT) 'propelJVM/compile'

propel-native:
	cd "$(PROPEL_DIR)" && $(SBT) 'propelNative/Compile/nativeLink'

propel-smoke: propel-native
	@set -e; for variant in de ee nee egglog-ee egglog-oee egglog-nee egglog-de; do \
		"$(PROPEL_BINARY)" \
			-f "$(PROPEL_INPUT)/gset_comm.propel" \
			--variant "$$variant" | grep -q 'Check successful'; \
	done

snapshots: propel-native
	cd "$(ROOT)" && cargo build --manifest-path benchmarks/disequality/euf-solver/Cargo.toml
	cd "$(ROOT)" && cargo build -p egglog-experimental
	cd "$(ROOT)" && uv run --locked python \
		benchmarks/disequality/scripts/generate_snapshots.py \
		--propel-binary "$(PROPEL_BINARY)" \
		--check

update-snapshots: propel-native
	cd "$(ROOT)" && cargo build --manifest-path benchmarks/disequality/euf-solver/Cargo.toml
	cd "$(ROOT)" && cargo build -p egglog-experimental
	cd "$(ROOT)" && uv run --locked python \
		benchmarks/disequality/scripts/generate_snapshots.py \
		--propel-binary "$(PROPEL_BINARY)" \
		--force

propel-parity: propel-native
	cd "$(ROOT)" && uv run --locked python \
		benchmarks/disequality/scripts/validate_propel.py \
		--binary "$(PROPEL_BINARY)" \
		--input "$(PROPEL_INPUT)" \
		--variants de egglog-ee egglog-oee egglog-nee egglog-de \
		--timeout "$(PROPEL_TIMEOUT)" \
		--jobs "$(PROPEL_JOBS)" \
		--allow-timeouts \
		--output benchmarks/disequality/reports/propel-parity.json

import-check:
	@test -n "$(ARCHIVE)" || (echo 'set ARCHIVE=/path/to/die-graph.zip' >&2; exit 2)
	cd "$(ROOT)" && uv run --locked python \
		benchmarks/disequality/scripts/verify_import.py \
		--archive "$(ARCHIVE)" \
		--check
