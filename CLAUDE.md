# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

There is no code yet. The repository holds the source text for a formalization project
(directory name: `damian_formalizare`) based on the book

> M. Audin & M. Damian, *Théorie de Morse et homologie de Floer* (French edition).

The book is split into three PDFs under `parts/`, produced with iLovePDF and carrying no
embedded metadata, bookmarks, or table of contents:

| File | Pages | Content |
|---|---|---|
| `parts/partI.pdf` | 103 | Part I: Morse theory (chapters 1–4), printed pages 3–105 |
| `parts/partII.pdf` | 417 | Part II: Floer homology (chapters 5–16), printed pages ~109–527 |
| `parts/biblio.pdf` | 5 | Bibliography |

Until a formalization target (Lean/Mathlib, Isabelle, etc.) and its build tooling are
added, there are no build, lint, or test commands. Add them here once they exist.

## Reading the PDFs

`pdftoppm`/`pdftotext` (poppler) are not installed, so the built-in Read tool cannot
render PDF pages. Use PyMuPDF from the Anaconda Python instead:

```bash
python3 - <<'EOF'
import pymupdf
d = pymupdf.open("parts/partII.pdf")
print(d[22].get_text())   # 0-indexed: pdf page 23 = start of chapter 6
EOF
```

`pypdf` is also available but PyMuPDF's text extraction handles the math typography
better. Text extraction of displayed equations is lossy (cases braces, sub/superscripts,
some symbols come out garbled); when a statement matters, render the page to PNG with
`page.get_pixmap(dpi=150).save("out.png")` and view the image.

## Chapter map (PDF page numbers, 1-indexed)

Chapter-opening pages carry no printed page number, so search by chapter title rather
than by printed number. Printed page ≈ PDF page + 2 in Part I, and ≈ PDF page + 108
in Part II (drifting to +110 by the end because some pages were dropped in the split).

**partI.pdf**
- p1 Introduction de la première partie
- p5 Ch. 1 Fonctions de Morse
- p19 Ch. 2 Pseudo-gradients
- p49 Ch. 3 Le complexe des points critiques
- p73 Ch. 4 Homologie de Morse, applications (exercises to p103)

**partII.pdf**
- p1 Introduction de la deuxième partie (proof strategy for the Arnold conjecture)
- p3 Ch. 5 Ce qu'il faut savoir en géométrie symplectique
- p23 Ch. 6 La conjecture d'Arnold et l'équation de Floer
- p61 Ch. 7 Géométrie du groupe symplectique, indice de Maslov
- p91 Ch. 8 Linéarisation et transversalité
- p167 Ch. 9 Homologie de Floer : étude des espaces de trajectoires
- p217 Ch. 10 De Floer à Morse
- p239 Ch. 11 Homologie de Floer : invariance
- p305 Ch. 12 La régularité elliptique de l'opérateur de Floer
- p325 Ch. 13 Les lemmes sur la dérivée seconde de l'opérateur de Floer
- p377 Ch. 14 Un peu de géométrie différentielle (background appendix)
- p395 Ch. 15 Un peu de topologie algébrique (background appendix)
- p401 Ch. 16 Un peu d'analyse (Ascoli, Sobolev spaces; background appendix)

Theorem/definition numbering in the book is `chapter.section.item` (e.g. Théorème 2.1.7,
Proposition 4.4.3, Théorème 6.5.4); the text cross-references by these numbers and by
printed page, so keep the offsets above in mind when following a reference.
