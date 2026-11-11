.PHONY: all build run graph check
.DELETE_ON_ERROR:

ITERATIONS ?= 13
ROUNDS ?= 3
MEMORY_GIB ?= 7
TIMEOUT ?= 120
VIZ_BIN ?= node_modules/.bin
PLOTS := $(patsubst %.vl.json,%,$(wildcard *.vl.json))

all: run

build:
	python3 run.py build --timeout 900 --memory-gib $(MEMORY_GIB)

# Render retained results even when a workload hits a resource limit.
# Use literal make here: $(MAKE) would execute this entire shell under make -n.
run: build
	@python3 run.py --iterations $(ITERATIONS) --rounds $(ROUNDS) \
		--memory-gib $(MEMORY_GIB) --timeout $(TIMEOUT); result=$$?; \
		make graph && exit $$result

graph: $(addsuffix .svg,$(PLOTS)) $(addsuffix .png,$(PLOTS))

node_modules/.installed: package.json package-lock.json
	npm ci --no-audit --no-fund
	touch $@

%.svg: %.vl.json results.json package-lock.json node_modules/.installed
	$(VIZ_BIN)/vl2svg $< $@

%.png: %.vl.json results.json package-lock.json node_modules/.installed
	$(VIZ_BIN)/vl2png $< $@ -s 3

check:
	python3 -m unittest -v test_run.py
	cargo fmt --check
