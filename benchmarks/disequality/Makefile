.PHONY: \
	check rust-test euf-test propel-jvm propel-native propel-smoke \
	snapshots update-snapshots replay-snapshots propel-parity import-check \
	artifact-archive prepare-parameter-facts prepare-parameter-native \
	parameter-analysis prepare-euf-input generate-euf-capture replay-generated-euf

ROOT := $(abspath ../..)
PROPEL_DIR := $(ROOT)/benchmarks/disequality/inductive-prover/propel
PROPEL_BINARY ?= $(PROPEL_DIR)/.native/target/scala-3.4.2/propel
PROPEL_INPUT := $(ROOT)/benchmarks/disequality/inductive-prover/benchmarks/propel
PROPEL_TIMEOUT ?= 10
PROPEL_JOBS ?= 8
PROPEL_TERM_LANGUAGE ?= vec
PROPEL_PARITY_OUTPUT ?= /tmp/egglog-disequality-propel-parity.json
PROPEL_DIRECT_SMOKE_INPUTS := gset_comm.propel tip_list_append_assoc.propel
SBT ?= sbt

ARCHIVE_CACHE ?= $(HOME)/.cache/egglog-encoding/disequality/die-graph.zip
GENERATED := $(ROOT)/target/disequality
PARAMETER_FACTS := $(GENERATED)/parameter-analysis/facts
PARAMETER_NATIVE := $(GENERATED)/parameter-analysis/native
PARAMETER_RESULTS ?= /tmp/egglog-disequality-parameter-analysis.csv
PARAMETER_TRIALS ?= 5
EUF_INPUT := $(GENERATED)/euf/uf.614981.smt2
EUF_CAPTURE_DIR := $(GENERATED)/euf/capture
EUF_BINARY := $(ROOT)/benchmarks/disequality/euf-solver/target/release/euf-solver
EGGLOG_BINARY := $(ROOT)/target/release/egglog-experimental
CORE_EGGLOG_BINARY := $(ROOT)/target/release/egglog

check: rust-test euf-test propel-jvm propel-native propel-smoke snapshots

rust-test:
	cd "$(ROOT)" && cargo test -p egglog-experimental disequality --lib
	cd "$(ROOT)" && cargo test -p egglog-experimental --bin egglog-experimental
	cd "$(ROOT)" && cargo test -p egglog --test container_rebuild custom_set_output_key_collapse_normal_mode
	cd "$(ROOT)" && cargo test -p egglog-disequality-backend

euf-test:
	cd "$(ROOT)" && cargo test --manifest-path benchmarks/disequality/euf-solver/Cargo.toml

propel-jvm:
	cd "$(PROPEL_DIR)" && $(SBT) 'propelJVM/test'

propel-native:
	cd "$(PROPEL_DIR)" && $(SBT) 'propelNative/Compile/nativeLink'

propel-smoke: propel-native
	@for variant in de ee nee egglog-ee egglog-oee egglog-nee egglog-de; do \
		output="$$($(PROPEL_BINARY) -f "$(PROPEL_INPUT)/gset_comm.propel" --variant "$$variant" 2>&1)"; status=$$?; \
		printf '%s\n' "$$output"; \
		test $$status -eq 0 || exit $$status; \
		printf '%s\n' "$$output" | grep -Eq 'Check successful\.$$' || exit 1; \
	done
	@for input in $(PROPEL_DIRECT_SMOKE_INPUTS); do \
		for variant in egglog-ee egglog-oee egglog-nee egglog-de; do \
			output="$$($(PROPEL_BINARY) -f "$(PROPEL_INPUT)/$$input" --variant "$$variant" --term-language direct 2>&1)"; status=$$?; \
			printf '%s\n' "$$output"; \
			test $$status -eq 0 || exit $$status; \
			printf '%s\n' "$$output" | grep -Eq 'Check successful\.$$' || exit 1; \
		done; \
	done

snapshots: propel-native
	cd "$(ROOT)" && cargo build --manifest-path benchmarks/disequality/euf-solver/Cargo.toml
	cd "$(ROOT)" && cargo build -p egglog-experimental -p egglog
	cd "$(ROOT)" && uv run --locked python benchmarks/disequality/scripts/generate_snapshots.py \
		--propel-binary "$(PROPEL_BINARY)" --check

update-snapshots: propel-native
	cd "$(ROOT)" && cargo build --manifest-path benchmarks/disequality/euf-solver/Cargo.toml
	cd "$(ROOT)" && cargo build -p egglog-experimental -p egglog
	cd "$(ROOT)" && uv run --locked python benchmarks/disequality/scripts/generate_snapshots.py \
		--propel-binary "$(PROPEL_BINARY)" --force

replay-snapshots:
	cd "$(ROOT)" && cargo build -p egglog-experimental -p egglog
	cd "$(ROOT)" && uv run --locked python benchmarks/disequality/scripts/generate_snapshots.py --replay

propel-parity: propel-native
	cd "$(ROOT)" && uv run --locked python benchmarks/disequality/scripts/validate_propel.py \
		--binary "$(PROPEL_BINARY)" \
		--input "$(PROPEL_INPUT)" \
		--variants de egglog-ee egglog-oee egglog-nee egglog-de \
		--timeout "$(PROPEL_TIMEOUT)" \
		--jobs "$(PROPEL_JOBS)" \
		--term-language "$(PROPEL_TERM_LANGUAGE)" \
		--allow-timeouts \
		--output "$(PROPEL_PARITY_OUTPUT)"

artifact-archive:
	cd "$(ROOT)" && uv run --locked python scripts/paper_benchmarks/prepare_parameter_analysis.py \
		--download --archive-cache "$(ARCHIVE_CACHE)" --archive-only

prepare-parameter-facts:
	cd "$(ROOT)" && uv run --locked python scripts/paper_benchmarks/prepare_parameter_analysis.py \
		--download --archive-cache "$(ARCHIVE_CACHE)" --ratio 0.5 \
		--output "$(PARAMETER_FACTS)" --force

prepare-parameter-native:
	cd "$(ROOT)" && uv run --locked python scripts/paper_benchmarks/prepare_parameter_analysis.py \
		--download --archive-cache "$(ARCHIVE_CACHE)" \
		--extract-native "$(PARAMETER_NATIVE)" \
		--disegg-path "$(ROOT)/benchmarks/disequality/disegg" --force
	cargo build --release --manifest-path "$(PARAMETER_NATIVE)/ee/Cargo.toml"
	cargo build --release --manifest-path "$(PARAMETER_NATIVE)/de/Cargo.toml"

parameter-analysis: prepare-parameter-facts prepare-parameter-native
	cd "$(ROOT)" && cargo build --release -p egglog-experimental
	cd "$(ROOT)" && uv run --locked python egglog-experimental/benchmarks/disequality/run_parameter_analysis.py \
		--egglog "$(EGGLOG_BINARY)" \
		--program egglog-experimental/tests/disequality/parameter-analysis.egg \
		--facts "$(PARAMETER_FACTS)" \
		--native-ee "$(PARAMETER_NATIVE)/ee/target/release/parameter_analysis_ee" \
		--native-de "$(PARAMETER_NATIVE)/de/target/release/parameter_analysis_de" \
		--native-input "$(PARAMETER_NATIVE)/exprs.in" \
		--trials "$(PARAMETER_TRIALS)" \
		--output "$(PARAMETER_RESULTS)"

prepare-euf-input:
	cd "$(ROOT)" && uv run --locked python scripts/paper_benchmarks/prepare_parameter_analysis.py \
		--download --archive-cache "$(ARCHIVE_CACHE)" --extract-euf "$(EUF_INPUT)" --force

generate-euf-capture: prepare-euf-input
	cd "$(ROOT)" && cargo build --release --manifest-path benchmarks/disequality/euf-solver/Cargo.toml
	rm -rf "$(EUF_CAPTURE_DIR)"
	mkdir -p "$(EUF_CAPTURE_DIR)"
	"$(EUF_BINARY)" "$(EUF_INPUT)" --backend egglog-de --term-language direct \
		--emit-source-dir "$(EUF_CAPTURE_DIR)" --emit-model 0

replay-generated-euf: generate-euf-capture
	cd "$(ROOT)" && cargo build --release -p egglog-experimental -p egglog
	@for encoding in ee oee nee de; do \
		"$(EGGLOG_BINARY)" --disequality-encoding "$$encoding" \
			"$(EUF_CAPTURE_DIR)/egglog-de-model-0000.egg" || exit $$?; \
	done
	"$(CORE_EGGLOG_BINARY)" "$(EUF_CAPTURE_DIR)/egglog-de-model-0000.desugared.egg"

import-check:
	cd "$(ROOT)" && uv run --locked python benchmarks/disequality/scripts/verify_import.py \
		--archive "$(ARCHIVE_CACHE)" --check
