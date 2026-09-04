#!/usr/bin/env python3
"""One-time compatibility patch for plastexdepgraph 0.0.5 + plasTeX 3.1:
restores identity hashing on theorem-node classes before the dependency
graph builds its node set.  Run once after (re)installing the
~/.venvs/leanblueprint virtualenv; idempotent."""
from pathlib import Path

target = (Path.home() / ".venvs/leanblueprint/lib/python3.11/site-packages/"
          "plastexdepgraph/Packages/depgraph.py")
s = target.read_text()
marker = "# Compatibility fix (plasTeX 3.1)"
if marker in s:
    print("already patched")
else:
    old = """        graph = DepGraph()
        graph.document = document
        graph.nodes = set(nodes)"""
    new = """        graph = DepGraph()
        graph.document = document
        # Compatibility fix (plasTeX 3.1): restore identity hashing on node
        # classes that lost __hash__ (a class in their MRO defines __eq__).
        for _n in nodes:
            if type(_n).__hash__ is None:
                type(_n).__hash__ = lambda self: id(self)
        graph.nodes = set(nodes)"""
    assert old in s, "pattern not found; plastexdepgraph version changed?"
    target.write_text(s.replace(old, new))
    print("patched", target)
