# Semantics/proof development is independent of paper experiment validation.
.DEFAULT_GOAL := lean-check
.PHONY: lean-check lean-build lean-holes difftest lean-slotted-parse lean-slotted-difftest lean-slotted-compile lean-slotted-egg-test lean-difftest lean-compiled-difftest lean-congruence-test lean-provenance-test lean-resugar-test lean-certificate-test lean-update-fixtures lean-egg-test lean-update-egg-snapshots paper paper-check paper-extract paper-sync

LEAN_BIN_DIR ?= $(HOME)/.elan/bin
LEAN_CERTIFICATES ?= /tmp/egglog-lean-certificates.json
LEAN_BIN := $(abspath $(if $(filter /%,$(LEAN_BIN_DIR)),$(LEAN_BIN_DIR),../$(LEAN_BIN_DIR)))
export PATH := $(LEAN_BIN):$(PATH)
CERTIFICATES := $(abspath $(if $(filter /%,$(LEAN_CERTIFICATES)),$(LEAN_CERTIFICATES),../$(LEAN_CERTIFICATES)))
LAKE ?= $(LEAN_BIN)/lake
# The checkout of the paper that paper-sync writes into.
PAPER_DIR ?= $(abspath ../../extended-egglog-paper)

PAPER_MODULES := \
  ExtlogTheorems \
  EgglogSemantics.Spec.Syntax \
  EgglogSemantics.Spec.Term \
  EgglogSemantics.Spec.Database \
  EgglogSemantics.Spec.Congruence \
  EgglogSemantics.Spec.Eval \
  EgglogSemantics.Spec.Match \
  EgglogSemantics.Spec.Step \
  EgglogSemantics.Spec.Divergence \
  EgglogSemantics.Spec.Behavior \
  EgglogSemantics.Spec.Order \
  EgglogSemantics.Source.Domain \
  EgglogSemantics.Source.WellFormed \
  EgglogSemantics.Proofs.OrderFinite \
  EgglogSemantics.Congruence.Encode \
  EgglogSemantics.SourceProof.Format \
  EgglogSemantics.SourceProof.Checker \
  EgglogSemantics.Provenance.Encode \
  EgglogSemantics.Provenance.Log \
  EgglogSemantics.Resugar.Claim \
  EgglogSemantics.Resugar.Query \
  EgglogSemantics.Resugar.Lift \
  EgglogSemantics.Slotted.Spec.Binders \
  EgglogSemantics.Slotted.Spec.Slots \
  EgglogSemantics.Slotted.Spec.Congruence \
  EgglogSemantics.Slotted.Spec.Match \
  EgglogSemantics.Slotted.Spec.Step \
  EgglogSemantics.Slotted.Target.Prim \
  EgglogSemantics.Slotted.Encode.Maintenance \
  EgglogSemantics.Slotted.Encode.Query

lean-check: lean-build lean-holes lean-congruence-test lean-provenance-test lean-resugar-test lean-egg-test lean-certificate-test lean-slotted-parse lean-slotted-egg-test

lean-build:
	$(LAKE) build

lean-holes:
	@find EgglogSemantics -name '*.lean' -print0 | xargs -0 awk '/(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$$)/ && !/`sorry`/ { print FILENAME ":" FNR ":" $$0; holes = 1 } END { exit holes }'

difftest:
	$(LAKE) build difftest

lean-congruence-test lean-provenance-test lean-resugar-test lean-egg-test: difftest
	.lake/build/bin/difftest $(patsubst lean-%-test,%,$@) 64

lean-certificate-test: difftest
	mkdir -p "$(dir $(CERTIFICATES))"
	.lake/build/bin/difftest export-fixtures "$(CERTIFICATES)"
	cmp "$(CERTIFICATES)" ../egglog/tests/lean-certificates.json
	.lake/build/bin/difftest export-certificates 64 "$(CERTIFICATES)"
	cd .. && EGGLOG_LEAN_CERTIFICATES="$(CERTIFICATES)" cargo test -p egglog --test lean_certificates -- $(RUST_TEST_ARGS)

lean-update-fixtures: difftest
	.lake/build/bin/difftest export-fixtures ../egglog/tests/lean-certificates.json

lean-update-egg-snapshots: difftest
	.lake/build/bin/difftest egg 64 update
	.lake/build/bin/difftest slotted-egg update

# The slotted corpus files the slotted parser accepts, with their check counts.
lean-slotted-parse: difftest
	.lake/build/bin/difftest slotted-parse ../egglog-experimental/tests/slotted

# The hand-written slotted programs: their compiled snapshots and outcomes.
lean-slotted-egg-test: difftest
	.lake/build/bin/difftest slotted-egg

# The paper's slotted corpus files, in the Rust reference and the bounded evaluator.
lean-slotted-difftest:
	./slotted-difftest.sh

# Every slotted corpus file the parser accepts, compiled by the slotted pass and run by the
# target interpreter, against the outcomes the Rust reference confirms.
lean-slotted-compile:
	./slotted-compile.sh

lean-difftest:
	./difftest.sh

lean-compiled-difftest:
	./compiled-difftest.sh

paper: paper-check

# The local paper is set to the ACM text width, so an overfull box there is one in the paper.
paper-check: paper-extract
	latexmk -pdf -Werror -halt-on-error -interaction=nonstopmode -outdir=../paper/build ../paper/semantics.tex
	@! grep -n '^Overfull' ../paper/build/semantics.log || { echo "paper-check: overfull boxes in ../paper/build/semantics.log"; exit 1; }

# Write the semantics blocks and the worked examples into $(PAPER_DIR)/generated.
paper-sync: paper-extract
	python3 paper_sync.py --no-extract --paper-dir "$(PAPER_DIR)"

paper-extract:
	$(LAKE) build ExtlogTheorems $(addsuffix :blueprint,$(PAPER_MODULES))
	$(LAKE) env .lake/packages/LeanArchitect/.lake/build/bin/extract_blueprint index ExtlogTheorems "$$(printf '%s\n' $(PAPER_MODULES) | paste -sd, -)"
