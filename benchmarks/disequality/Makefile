.PHONY: \
	check rust-test euf-test propel-jvm propel-native propel-smoke \
	snapshots update-snapshots replay-snapshots propel-parity import-check

ROOT := $(abspath ../..)
PROPEL_DIR := $(ROOT)/benchmarks/disequality/inductive-prover/propel
PROPEL_BINARY ?= $(PROPEL_DIR)/.native/target/scala-3.4.2/propel
PROPEL_INPUT := $(ROOT)/benchmarks/disequality/inductive-prover/benchmarks/propel
PROPEL_TIMEOUT ?= 10
PROPEL_JOBS ?= 8
PROPEL_TERM_LANGUAGE ?= vec
PROPEL_PARITY_OUTPUT ?= benchmarks/disequality/reports/propel-parity.json
PROPEL_DIRECT_SMOKE_INPUTS := gset_comm.propel tip_list_append_assoc.propel
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
	@for variant in de ee nee egglog-ee egglog-oee egglog-nee egglog-de; do \
		output="$$("$(PROPEL_BINARY)" \
			-f "$(PROPEL_INPUT)/gset_comm.propel" \
			--variant "$$variant" 2>&1)"; status=$$?; \
		printf '%s\n' "$$output"; \
		test $$status -eq 0 || exit $$status; \
		printf '%s\n' "$$output" | grep -Eq 'Check successful\.$$' || exit 1; \
	done
	@for input in $(PROPEL_DIRECT_SMOKE_INPUTS); do \
		for variant in egglog-ee egglog-oee egglog-nee egglog-de; do \
			output="$$("$(PROPEL_BINARY)" \
				-f "$(PROPEL_INPUT)/$$input" \
				--variant "$$variant" \
				--term-language direct 2>&1)"; status=$$?; \
			printf '%s\n' "$$output"; \
			test $$status -eq 0 || exit $$status; \
			printf '%s\n' "$$output" | grep -Eq 'Check successful\.$$' || exit 1; \
		done; \
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

replay-snapshots:
	cd "$(ROOT)" && cargo build -p egglog-experimental
	cd "$(ROOT)" && uv run --locked python \
		benchmarks/disequality/scripts/generate_snapshots.py \
		--replay

propel-parity: propel-native
	cd "$(ROOT)" && uv run --locked python \
		benchmarks/disequality/scripts/validate_propel.py \
		--binary "$(PROPEL_BINARY)" \
		--input "$(PROPEL_INPUT)" \
		--variants de egglog-ee egglog-oee egglog-nee egglog-de \
		--timeout "$(PROPEL_TIMEOUT)" \
		--jobs "$(PROPEL_JOBS)" \
		--term-language "$(PROPEL_TERM_LANGUAGE)" \
		--allow-timeouts \
		--output "$(PROPEL_PARITY_OUTPUT)"

import-check:
	@test -n "$(ARCHIVE)" || (echo 'set ARCHIVE=/path/to/die-graph.zip' >&2; exit 2)
	cd "$(ROOT)" && uv run --locked python \
		benchmarks/disequality/scripts/verify_import.py \
		--archive "$(ARCHIVE)" \
		--check
