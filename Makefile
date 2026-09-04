# Blueprint pipeline: PDF + web (dependency graph) + verification that every
# \lean{...} declaration cited in the blueprint exists in the compiled project.
BP_VENV := $(HOME)/.venvs/leanblueprint

.PHONY: build blueprint blueprint-pdf blueprint-web blueprint-graph blueprint-serve checkdecls

build:
	lake build

checkdecls: build
	python3 blueprint/checkdecls.py

blueprint-pdf:
	mkdir -p blueprint/print
	cd blueprint/src && tectonic --outdir ../print print.tex

blueprint-web:
	cd blueprint/src && $(BP_VENV)/bin/plastex -c plastex.cfg web.tex

# The web pages draw the dependency graph with a WebAssembly Graphviz, which a
# browser refuses to load from a file:// URL.  Either serve the directory...
blueprint-serve: blueprint-web
	@echo "Open http://localhost:8000/dep_graph_document.html (Ctrl-C to stop)"
	cd blueprint/web && python3 -m http.server 8000

# ...or render the same graph with the local `dot` to a standalone SVG that
# opens straight from the filesystem.
blueprint-graph: blueprint-web
	python3 blueprint/render_graph.py

blueprint: checkdecls blueprint-pdf blueprint-web blueprint-graph
	@echo "Blueprint complete: pdf in blueprint/print/, web in blueprint/web/,"
	@echo "standalone graph at blueprint/web/dep_graph.svg."
	@echo "For the interactive graph run: make blueprint-serve"
