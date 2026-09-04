# Blueprint pipeline: PDF + web (dependency graph) + verification that every
# \lean{...} declaration cited in the blueprint exists in the compiled project.
BP_VENV := $(HOME)/.venvs/leanblueprint

.PHONY: build blueprint blueprint-pdf blueprint-web checkdecls

build:
	lake build

checkdecls: build
	python3 blueprint/checkdecls.py

blueprint-pdf:
	mkdir -p blueprint/print
	cd blueprint/src && tectonic --outdir ../print print.tex

blueprint-web:
	cd blueprint/src && $(BP_VENV)/bin/plastex -c plastex.cfg web.tex

blueprint: checkdecls blueprint-pdf blueprint-web
	@echo "Blueprint complete: pdf in blueprint/print/, web + dep graph in blueprint/web/"
