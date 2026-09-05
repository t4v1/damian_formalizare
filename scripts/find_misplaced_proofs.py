#!/usr/bin/env python3
"""Find results that are assumed in one file but proved somewhere else.

Because the chapters were written in parallel, a result is sometimes proved in a
chapter that *imports* the one where it is assumed.  The import order forbids
citing it back, but the proof can be moved.  Those are free wins.

Parses every declaration, splits into assumed (proof contains `sorry`) and
proved, then scores each assumed one against every proved one on
  * an exact or near-exact name match, and
  * Jaccard overlap of the tokens of the statement.
"""
import re, sys
from pathlib import Path

DECL = re.compile(r'^(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.\'₀-₉]*)', re.M)

def parse(path):
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    starts = []
    for m in DECL.finditer(text):
        ln = text[:m.start()].count("\n")
        starts.append((ln, m.group(2)))
    out = []
    for i, (ln, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(lines)
        body = "".join(lines[ln:end])
        # signature = up to the first ':=' at the end of the statement
        sig = body.split(":= by")[0].split(":=")[0]
        out.append({
            "file": path.name, "name": name, "sig": sig,
            "assumed": re.search(r'\bsorry\b', body) is not None,
        })
    return out

def toks(s):
    s = re.sub(r'/--.*?-/', ' ', s, flags=re.S)          # drop docstrings
    s = re.sub(r'\{[^}]*\}|\([^)]*:[^)]*\)|\[[^\]]*\]', ' ', s)  # drop binders
    return set(re.findall(r'[A-Za-z_][A-Za-z0-9_.\'₀-₉]{2,}', s))

files = sorted(Path("MorseFloer").rglob("*.lean"))
decls = [d for f in files for d in parse(f)]
assumed = [d for d in decls if d["assumed"]]
proved  = [d for d in decls if not d["assumed"]]
print(f"parsed {len(decls)} declarations: {len(assumed)} assumed, {len(proved)} proved\n")

hits = []
for a in assumed:
    ta = toks(a["sig"])
    if len(ta) < 4:
        continue
    for p in proved:
        if p["file"] == a["file"] and p["name"] == a["name"]:
            continue
        score = 0.0
        if p["name"] == a["name"]:
            score += 1.0                                  # same name, different file
        tp = toks(p["sig"])
        if tp:
            j = len(ta & tp) / len(ta | tp)
            score += j
        if score >= 0.62:
            hits.append((score, a, p))

hits.sort(key=lambda h: -h[0])
seen = set()
for score, a, p in hits:
    key = (a["file"], a["name"])
    if key in seen:
        continue
    seen.add(key)
    flag = "NAME MATCH" if p["name"] == a["name"] else f"overlap {score:.2f}"
    print(f"[{flag}]")
    print(f"  assumed : {a['file']:12s} {a['name']}")
    print(f"  proved  : {p['file']:12s} {p['name']}\n")
if not hits:
    print("no candidates found")
