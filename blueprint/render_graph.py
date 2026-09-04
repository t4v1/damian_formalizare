#!/usr/bin/env python3
"""Render the dependency graph to a standalone SVG.

The blueprint's own dep_graph_document.html draws the graph in the browser with
a WebAssembly build of Graphviz.  That works when the pages are served over
HTTP, but not when opened as file:// URLs: the browser treats each local file as
an opaque origin and blocks the fetch of graphvizlib.wasm, so the canvas stays
blank.  This script runs the same graph through the local `dot` binary instead,
producing blueprint/web/dep_graph.svg, which opens fine from the filesystem.
"""
import re
import subprocess
import sys
from pathlib import Path

web = Path(__file__).resolve().parent / "web"
src = web / "dep_graph_document.html"
if not src.exists():
    sys.exit(f"{src} not found — run `make blueprint-web` first.")

html = src.read_text(encoding="utf-8")
m = re.search(r"\.renderDot\(`(.*?)`\)", html, re.S)
if not m:
    sys.exit("No graph data found in dep_graph_document.html.")

out = web / "dep_graph.svg"
res = subprocess.run(["dot", "-Tsvg"], input=m.group(1), capture_output=True, text=True)
if res.returncode != 0:
    sys.exit(f"dot failed: {res.stderr.strip()}")
out.write_text(res.stdout, encoding="utf-8")

nodes = len(re.findall(r'class="node"', res.stdout))
edges = len(re.findall(r'class="edge"', res.stdout))
print(f"Wrote {out} — {nodes} nodes, {edges} edges.")
