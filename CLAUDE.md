# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

A Lean 4 formalization of both parts of

> M. Audin & M. Damian, *Théorie de Morse et homologie de Floer* (French edition)

— Part I, Morse theory (chapters 1–4), and Part II, Floer homology and the
Arnold conjecture (chapters 5–16).

The approach is **blueprint-first, chapter by chapter**. Every definition and
theorem of the book gets a faithful Lean statement; proofs are supplied wherever
today's Mathlib allows and left as `sorry` otherwise. A result the current
Mathlib cannot even *state* (it needs, say, the `Cᵏ` topology on `C^∞(V;ℝ)`)
gets a blueprint node with no Lean declaration rather than a fictitious
statement. Keeping that distinction honest is the point of the project.

The book's PDFs are in `parts/` and are **gitignored** (copyrighted). Never
commit them and never reproduce the book's text: statements in this repo are
paraphrases and the Lean docstrings are original.

## Commands

```sh
lake build                          # build everything
make blueprint                      # checkdecls + PDF + web + standalone graph SVG
make blueprint-serve                # serve the web blueprint (needed for the live graph)
lake build MorseFloer.Part1.Ch1     # build one chapter
lake env lean MorseFloer/Part1/Ch1.lean   # type-check one file, no build lock
```

- Toolchain `leanprover/lean4:v4.33.1`, pinned in `lean-toolchain`.
- Mathlib is a **git dependency pinned to tag `v4.33.1`**, already fetched with
  its prebuilt cache in `.lake/packages/mathlib`. Do not run `lake update` — it
  would re-resolve and force a multi-hour rebuild.
- A cold build of one chapter file takes **3–6 minutes** (importing Mathlib
  dominates). Budget for that: get a file as close to correct as possible before
  building, rather than iterating one error at a time.
- Several `lake build` runs contend for the build lock. To work on files in
  parallel use `lake env lean <file>`, which takes no lock.
- New chapter files must be imported from `MorseFloer.lean`.
- To find exact Mathlib names, grep `.lake/packages/mathlib/Mathlib/` before
  guessing.

### Viewing the dependency graph

`blueprint/web/dep_graph_document.html` draws the graph in the browser with a
WebAssembly build of Graphviz. Opening it as a `file://` URL shows a blank
canvas: the browser gives each local file its own opaque origin and blocks the
fetch of `js/graphvizlib.wasm`. Nothing is wrong with the blueprint. Either run
`make blueprint-serve` and open the page over HTTP, or use
`blueprint/web/dep_graph.svg`, which `make blueprint-graph` renders with the
local `dot` and which opens straight from the filesystem.


## Architecture

`MorseFloer/Basic.lean` is the shared foundation and the one file every chapter
depends on. It exists because the book's second-order notions (Hessian,
nondegeneracy, index) are *defined in a chart* and only then shown to be
chart-independent at a critical point; the file follows that route exactly:

- `sndFDeriv f x` — the second differential as a continuous bilinear map.
- `sndFDeriv_comp` — the transformation rule `d²(f∘φ) = d²f(dφ·,dφ·) + df(d²φ)`,
  and `sndFDeriv_comp_of_critical`, the tensorial form at a critical point. This
  pair is what makes `hessian` on a manifold legitimate; everything second-order
  in the book routes through it.
- `hessian I f x` — the Hessian of `f : M → ℝ`, read in the preferred extended
  chart at `x`; `IsCriticalPoint`, `IsNondegenerate`, `IsMorseFunction`.
- `index` / `morseIndex` — the Morse index, defined as `sigNeg` of the Hessian
  quadratic form. Mathlib's `QuadraticMap.Equivalent.sigNeg_eq` (Sylvester's law
  of inertia) is what makes the index well defined, so do not reinvent it.

Chapter files live in `MorseFloer/Part1/ChN.lean` and `MorseFloer/Part2/ChN.lean`,
one per book chapter, each opening with a module docstring that states which
results are proved and which are assumed. A long self-contained proof may live in
a helper file beside the chapter (`Part1/Brouwer.lean`, `Part1/MorseLemma.lean`,
`Part1/DistSqMorse.lean`), importing only `Basic` or Mathlib; the chapter then
restates the book's theorem as a one-line term. This keeps chapter builds short
and lets several proofs be developed in parallel. Most chapter content is stated in the
**local model** (a normed space, `IsCriticalPt f x : fderiv ℝ f x = 0`) because
that is where the book's proofs actually live; the manifold-level definitions
sit in `Basic.lean`.

## Chapter status

`lake build` is green; every `sorry` below is a deliberate, documented
assumption. Blueprint nodes carry the status, and `python3 blueprint/checkdecls.py`
verifies every cited declaration still exists.

| File | Book chapter | `sorry` | Notes |
|---|---|---|---|
| `MorseFloer/Basic.lean` | foundations | 0 | second differentials, Hessian, index |
| `Part1/Brouwer.lean` | helper for 2.3.3 / §4.8.b | 0 | Brouwer in every dimension, analytically (Milnor–Rogers) |
| `Part1/MorseLemma.lean` | helper for 1.3.1 | 0 | the Morse lemma in every finite dimension |
| `Part1/DistSqMorse.lean` | helper for 1.2.1 | 0 | normal-bundle argument in charts + equidimensional Sard |
| `Part1/BorsukUlam.lean` | helper for 4.8.3 | 0 | Borsuk–Ulam in every dimension, by Tucker's lemma (no algebraic topology) |
| `Part1/ManifoldFlow.lean` | helper for 2.1.9 | 0 | the flow of a `C¹` field on a compact manifold, jointly continuous |
| `Part1/Reeb.lean` | helper for 2.1.9 | 0 | Reeb's theorem, by a gradient-like flow and the Morse lemma at the minimum |
| `Part1/OneManifold.lean` | helper for 2.3.2 | 0 | compact connected 1-manifolds are circles (Gale) |
| `Part1/Ch1.lean` | 1 Morse functions | 0 | Morse lemma and Prop 1.2.1, restated from the two helpers above |
| `Part1/Ch2.lean` | 2 Pseudo-gradients | 0 | Reeb (2.1.9), the classification of 1-manifolds (2.3.2), Prop 2.1.6 and Brouwer, restated from the helpers above |
| `Part1/Ch3.lean` | 3 The Morse complex | 0 | ∂∘∂ = 0 proved from an explicit hypothesis |
| `Part1/Ch4.lean` | 4 Morse homology | 0 | Künneth, integral duality, disjoint unions, Brouwer and Borsuk–Ulam all proved |
| `Part2/Calibrated.lean` | helper for 5.5.4 | 0 | calibrated complex structures form a contractible space (Cayley transform) |
| `Part2/Ch5.lean` | 5 Symplectic geometry | 1 | Darboux only (needs differentiable dependence of ODE flows on initial data) |
| `Part2/Ch6.lean` | 6 Arnold conjecture, Floer equation | 12 | critical points of the action = periodic orbits; the first variation |
| `Part2/Ch7.lean` | 7 Maslov, Conley–Zehnder | 13 | index axiomatised; dimension two in full |
| `Part2/Ch8.lean` | 8 Linearisation, transversality | 3 | the Fredholm index bookkeeping |
| `Part2/Ch9.lean` | 9 Spaces of trajectories | 0 | the Floer complex, ∂∘∂ = 0 |
| `Part2/Ch10.lean` | 10 From Floer to Morse | 4 | the two complexes compared |
| `Part2/Ch11.lean` | 11 Invariance | 0 | the full invariance chain, up to isomorphism |
| `Part2/Ch12.lean` | 12 Elliptic regularity | 1 | Cauchy–Riemann regularity, the bootstrapping recursion |
| `Part2/Ch13.lean` | 13 Second derivative | 0 | Lemmas 13.4.1 and 13.5.1 in full |
| `Part2/Ch14.lean` | 14 Differential geometry | 1 | Morse–Sard for `dim E > dim F` only; the other two regimes proved |
| `Part2/Ch15.lean` | 15 Algebraic topology | 0 | long exact sequence; Künneth over a field (alias of Ch4's `betti_prod`) |
| `Part2/Ch16.lean` | 16 Analysis | 1 | the Fredholm index for operators; additivity and local constancy proved (see the Fredholm note below) |

**All sixteen chapters of the book are now formalized.**

Chapters 9 and 11 carry the two results that, together, prove the Arnold
conjecture: Chapter 9 builds the Floer complex and proves its differential
squares to zero, and Chapter 11 proves Floer homology does not depend on the
pair `(H, J)`. Chapter 10 supplies the other half, that for a small
time-independent Hamiltonian the Floer complex *is* the Morse complex.

### Two design devices worth keeping

**Geometric input enters as a hypothesis, never as a fake theorem.** Chapter 3
takes the trajectory counts as an abstract function plus a `BrokenPairs`
hypothesis, and proves ∂∘∂ = 0 from it. Chapters 8 and 10 do the same for the
Floer data. This is what lets the algebra be proved outright while the analysis
Mathlib cannot express stays visibly assumed.

**Where asserting a book theorem of arbitrary abstract data would be *false*, it
is stated as a predicate the data may satisfy, not as a `sorry`ed theorem.**
Chapter 8's `IsFredholmOfCZIndex` and Chapter 10's `IsFredholmOfIndex` are the
examples. A `sorry`ed false statement would be worse than no statement.

### Cross-chapter proofs

Two results are proved in a later chapter than the one that states them, because
the import order runs the other way:

Both have now been resolved the same way — by moving the proof up to the chapter
that states the result, leaving an alias behind so no name changes:

- Künneth's algebraic half, proved in Chapter 15, moved into `Part1/Ch4.lean` as
  `brokenPairs_prod`; `Chapter15.tensor_brokenPairs` is an alias for it. The
  Künneth formula itself is now proved in Chapter 4 (`betti_prod`), and
  `Chapter15.betti_tensor` and `Chapter15.numCrit_prodIndex` are aliases too.
- Proposition 5.6.4, proved in Chapter 7, moved into `Part2/Ch5.lean` as
  `det_charpoly_symmetric`, together with the four-lemma chain it rests on;
  Chapter 7 keeps aliases and its own general-field version.

**The search for more of these has been run and came back empty.**
`scripts/find_misplaced_proofs.py` parses every declaration in `MorseFloer/`,
splits them into assumed and proved, and scores each assumed one against every
proved one on both an exact name match and token overlap of the statement. Over
556 declarations it surfaced only two candidates, both false positives: the
Morse lemma against its own one-dimensional case, which is strictly weaker, and
the no-retraction theorem against a Borsuk–Ulam corollary, which merely shares
vocabulary. So the two transplants above were the only ones, and there is no
point hunting by hand.

Re-run the script after adding chapters or after a batch of parallel work —
that is when the pattern arises. (Last run after the Part I push: 684
declarations, no candidates.)

### Contributing Sobolev spaces upstream

The single gap that blocks the most is `W^{k,p}` on a domain. A worked plan for
closing it as a Mathlib contribution — what already exists upstream, why the
cylinder `ℝ × S¹` does not fit the designs in flight, and which PR to write
first — is at https://claude.ai/code/artifact/6128ff05-9235-473b-beb9-9f0a2614767a

Its conclusion in one line: **Morrey's inequality (the `p > n` Sobolev
embedding) is absent from Mathlib**, is self-contained enough to state for
compactly supported `C¹` functions without settling the space design, and is
exactly the input Chapter 13 assumes repeatedly.

### The gaps that matter most

Four missing Mathlib pieces account for nearly every assumption and for every
result recorded in the blueprint with no Lean statement at all:

1. **Morse–Sard above the diagonal.** Narrowed, as of the Sard work in Chapter
   14. Sard now splits into three dimension regimes, of which two are *proved*:
   the image is null outright when `dim E < dim F`, and the equidimensional case
   is Mathlib's Jacobian lemma after transport. Only `dim E > dim F` remains
   assumed, as `Chapter14.sard_of_lt_finrank`, stated at the sharp threshold
   `k ≥ dim E - dim F + 1`. It is complete and `sorry`-free in Kudryashov's
   external `SardMoreira` project; transplanting it, not reproving it, is the
   route. Proposition 1.2.1 needs only the *equidimensional* case, and is now
   proved (`Part1/DistSqMorse.lean`) by running the normal-bundle argument in
   charts, so it needs no normal bundle either.
2. **Submanifolds** as a type carrying its own smooth structure, with tubular
   neighbourhoods and transversality. Without it there is no space of
   trajectories, so all of §3.2 and the Smale condition are unstatable, and
   Chapter 3 has to take the broken-trajectory count as a hypothesis.
3. **Differential forms on manifolds, and Sobolev spaces.** The first blocks
   symplectic manifolds (only the linear theory is reachable in Chapter 5); the
   second blocks the elliptic regularity of Chapters 12 and 13.
4. **Excision or Mayer–Vietoris for singular homology.** Mathlib has singular
   homology as a functor with homotopy invariance and `H₀`, but cannot compute
   `H_{n-1}(Sⁿ⁻¹)` or the mod 2 homology of `Pⁿ(ℝ)`. It no longer blocks
   Brouwer, which has an analytic proof (Milnor–Rogers, in `Part1/Brouwer.lean`,
   from the change of variables formula and partitions of unity), nor
   Borsuk–Ulam, which `Part1/BorsukUlam.lean` proves combinatorially from
   Tucker's lemma on the barycentric subdivision of the cube. Neither route uses
   algebraic topology, so `π₁(S¹) ≅ ℤ` and degree theory are still absent, and
   nothing in Part I now waits on them. Two names are traps when grepping:
   Mathlib's
   `IsAntichain.sperner` is Sperner's *theorem* on antichains, not the
   simplicial lemma, and its `MayerVietoris` files are for sheaf cohomology,
   not singular homology.

Chapter 2 no longer assumes anything. Reeb's theorem avoids the gluing of
disks: `Part1/ManifoldFlow.lean` builds the flow of a vector field on a compact
manifold, continuous in the initial point (Mathlib stops at integral curves),
and `Part1/Reeb.lean` sends each point along it to a level set that the Morse
lemma identifies with `Sⁿ⁻¹`. The classification of 1-manifolds is Gale's
purely topological argument.


## What Mathlib does and does not have

Checked against this pinned checkout, and worth knowing before planning a proof:

- **Has**: manifolds (`IsManifold`, `mfderiv`, `extChartAt`, `writtenInExtChartAt`),
  immersions/submersions/embeddings (in namespace `Manifold`), integral curves,
  the inverse function theorem, symmetry of the second derivative
  (`ContDiffAt.isSymmSndFDerivAt`), quadratic-form signature and Sylvester's law
  (`sigPos`/`sigNeg`, at *root* namespace, not `QuadraticMap.`), Fredholm
  operators — `IsFredholm`, `FredholmPackage` and quasi-inverses in
  `Analysis/Normed/Operator/Fredholm/Basic.lean`, plus the *algebraic* index
  `LinearMap.index` (`dim ker − dim coker`, with the injective, surjective and
  finite-dimensional cases) in `Algebra/Module/LinearMap/Index.lean` — and
  `Matrix.SymplecticGroup`, Hofer's lemma (`Analysis/Hofer.lean`, the metric
  lemma behind bubbling arguments), Sobolev-adjacent analysis, homological
  algebra and homology of complexes. Note that upstream *master* has since
  moved past the pin here: it has `IsFredholm.index_comp` (additivity) and
  `Fredholm/Open.lean` (local constancy of the index on Fredholm operators),
  and it takes the index of an operator to be `LinearMap.index` of its
  underlying linear map rather than a separate definition. The pinned
  checkout has none of this, so Chapter 16's proofs stand on their own — but
  the `contrib/` Fredholm package is largely superseded upstream and must be
  compared against master before any PR.
- **Also has, and this was wrong in earlier notes**: distributions. Bundled
  test functions `𝓓^{n}(Ω, F)` on an open `Ω` with the LF topology, the space
  `𝓓'^{n}(Ω, F)`, and the distributional directional derivative
  (`Analysis/Distribution/TestFunction.lean`, `Distribution.lean`). Also
  Bessel-potential Sobolev spaces `H^{s,p}` of *tempered* distributions defined
  through the Fourier transform (`Analysis/Distribution/Sobolev.lean`), the
  Gagliardo–Nirenberg–Sobolev inequality for compactly supported `C¹` functions
  (`Analysis/FunctionalSpaces/SobolevInequality.lean`), harmonic functions with
  the mean value property and analyticity, and the Cauchy–Riemann criterion
  `differentiableAt_complex_iff_differentiableAt_real`. The nearest thing to
  a `Cᵏ` topology is `ContDiffMapSupportedIn n K` with its LF topology
  (`Analysis/Distribution/ContDiffMapSupportedIn.lean`): compactly supported
  `Cⁿ` maps on a *normed space*, not on a manifold, so it does not reach the
  vector fields of Chapter 2 directly.
- **Does not have**: Morse theory of any kind, Morse–Sard above the diagonal
  (the other two regimes are now proved in Chapter 14) or Sard for manifolds,
  the Hessian on a manifold, tubular neighbourhoods, the `Cᵏ` topology on
  `C^∞(V;ℝ)`, symplectic manifolds (only the linear symplectic group), Floer
  homology, and — the one that blocks Part II hardest — `W^{k,p}(V)` or
  `W^{k,p}_loc(U)` **on a domain**, with their norms. The Bessel spaces above
  are global on all of `ℝⁿ` and admit no restriction to a relatively compact
  `V`, and the GNS inequality is stated only for `p < finrank ℝ E`. There is no
  Sobolev embedding into `L^∞`, no Poincaré, no Rellich.

## Lean gotchas that cost real time here

These are specific to this Mathlib version and were each hit during the build:

- **Instance search fails on nested operator spaces** such as
  `E →L[ℝ] E →L[ℝ] ℝ` or `(E →L[ℝ] ℝ) →L[ℝ] E` — `NormSMulClass`,
  `IntervalIntegrable`, even `norm_nonneg` — because this project builds at the
  default `maxSynthPendingDepth` of 1. `set_option maxSynthPendingDepth 3`
  (Mathlib's own setting) fixes it file-locally; `Part1/MorseLemma.lean` uses
  it. It can also trigger `whnf` timeouts elsewhere, so scope it to the
  sections that need it.
- **Junk values make careless statements false.** An unconstrained `X : E → E`
  is not a vector field in the book's sense (Prop 2.1.6 was false until
  `Continuous X` and `FiniteDimensional` were added), and `mfderiv` is `0` where
  `f` is not differentiable, so `IsMorseFunction` alone does not make `f`
  smooth (Reeb now carries a `ContMDiff` hypothesis). Check the hypotheses of a
  `sorry`ed statement for these before spending effort on its proof.

- **`simpa ... using h` fails across instance diamonds.** Composing Mathlib
  calculus lemmas produces terms whose `ℝ` `AddCommGroup`/`Module` instances go
  through `RCLike`, while a freshly stated goal uses `Real.instAddCommGroup`.
  These are defeq but not syntactically equal, so `simpa`'s final match fails
  while `exact` succeeds. Prefer stating a lemma in exactly the form the
  composition produces and closing with `exact`.
- **`rw [f_eq]` where `f_eq : deriv f = fun t => …` does not beta-reduce**, so
  the next `rw` cannot find its pattern. Use `simp only [f_eq]` instead.
- **`ContDiffAt.differentiableAt` takes `n ≠ 0`**, not `1 ≤ n`. Same for
  several `ContDiff` lemmas that look like they should take an inequality.
- **`simp only [mul_eq_zero]` will split a numeral product** such as `2 * π = 0`
  into `2 = 0 ∨ π = 0`, changing the shape of the hypothesis you meant to
  discharge. Use `rcases mul_eq_zero.mp h` on the specific hypothesis instead.
- **`absurd h hn` already has the goal's type**; do not append `.elim`.
- **Field notation needs a syntactic head constant.** `key.fderiv_eq` fails when
  `key : ∀ᶠ y in 𝓝 x, g y = h y` because that is `Filter.Eventually`, not
  `Filter.EventuallyEq`; state the hypothesis with `=ᶠ[𝓝 x]`. Likewise a `have`
  whose type is still a metavariable cannot take a projection — write
  `HasFDerivAt.fderiv hcomp` rather than `hcomp.fderiv`.
- `Matrix` notation is **scoped**: `*ᵥ`, `ᵥ*` and `ᵀ` need `open scoped Matrix`,
  while `dotProduct` and friends sit at the root namespace.
- `LinearMap.IsAlt.neg` is shadowed by a `BilinForm.IsAlt.neg` that means
  something else; derive skew-symmetry from `self_eq_zero (v + w)` instead.
- **`Continuous.comp` against a large goal function is where defeq blows up.**
  Building a sectional continuity statement directly from small pieces, instead
  of composing a big joint statement with `fun t => (σ, t)`, turned a
  million-heartbeat `isDefEq` timeout into an instant check. If you find
  yourself raising `maxHeartbeats`, split the declaration instead.
- `ContDiff.differentiable` takes `n ≠ 0`, like `ContDiffAt.differentiableAt`.
- **Tangent spaces leak into types.** A definition like
  `dF (f : M → ℝ) (x : M) : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x` cannot infer
  `E`, and at `dF f x (v x)` Lean unifies it with `TangentSpace 𝓘(ℝ, E) x`, then
  fails on `NormedAddCommGroup (TangentSpace …)`. Make `E` explicit
  (`variable (E) in`). Likewise a `HasFDerivAt` obtained from
  `hasMFDerivAt_iff_hasFDerivAt` has tangent-space types, and `.hasDerivAt` on
  it fails with `ContinuousSMul ℝ ℝ`; restate it first with the model-space
  types (`have h3 : HasFDerivAt … := h2`, which holds by defeq).
- The unused-section-variable linter reports in rounds: after adding
  `omit [X] in`, a rebuild can flag `[Y]` on the same theorem, or `[X]` on the
  theorems that use it. Rebuild until clean.
- `le_or_lt` does not exist in this Mathlib; it is `le_or_gt`. And `push_neg` is
  deprecated in favour of `push Not` — it emits a warning, which breaks the
  project's warning-clean build.
- `Manifold.IsSmoothEmbedding` is in namespace `Manifold`; `open scoped Manifold`
  does not bring it into scope.
- `ω` in `ContDiff ℝ ω f` needs `open scoped ContDiff`. Without it the file still
  parses and elaborates — `ω` resolves to a *different* element of `WithTop ℕ∞` —
  and then `le_top` will not close `1 ≤ ω`, with a confusing error naming `ω` on
  one side and `⊤` on the other. With the scope open, `OrderTop.le_top _` and
  `WithTop.top_ne_zero` are the two coercions you want; bare `le_top` fails to
  unify.

## Reading the book's PDFs

Poppler is not installed, so the Read tool cannot render PDF pages. Use PyMuPDF
from the Anaconda Python:

```sh
python3 -c "import pymupdf; d=pymupdf.open('parts/partII.pdf'); print(d[22].get_text())"
```

Extraction of displayed equations is lossy (cases braces, sub/superscripts and
some symbols come out garbled). When a statement matters, render the page with
`page.get_pixmap(dpi=150).save('out.png')` and view the image.

### Chapter map (PDF page numbers, 1-indexed)

Chapter-opening pages carry no printed page number, so search by chapter title.
Printed page ≈ PDF page + 2 in Part I, and ≈ PDF page + 108 in Part II (drifting
to +110 by the end).

**partI.pdf** — p1 introduction; p5 Ch. 1 Fonctions de Morse; p19 Ch. 2
Pseudo-gradients; p49 Ch. 3 Le complexe des points critiques; p73 Ch. 4
Homologie de Morse, applications.

**partII.pdf** — p1 introduction; p3 Ch. 5 Géométrie symplectique; p23 Ch. 6 La
conjecture d'Arnold et l'équation de Floer; p61 Ch. 7 Groupe symplectique,
indice de Maslov; p91 Ch. 8 Linéarisation et transversalité; p167 Ch. 9 Espaces
de trajectoires; p217 Ch. 10 De Floer à Morse; p239 Ch. 11 Invariance; p305
Ch. 12 Régularité elliptique; p325 Ch. 13 Dérivée seconde de l'opérateur de
Floer; p377 Ch. 14 Géométrie différentielle; p395 Ch. 15 Topologie algébrique;
p401 Ch. 16 Analyse.

Theorem numbering is `chapter.section.item` (Théorème 2.1.7, Proposition 4.4.3);
cross-references use those numbers and printed pages.

## Related work by the same author

`~/projects/damian` holds solutions to the book's 71 exercises — LaTeX write-ups
plus a Lean project (`exercises/`) with a leanblueprint dependency graph. That
project pins Lean v4.29.0-rc2 against a *path* dependency on `~/projects/mathlib4`,
so its Lean files are not directly portable here, but its blueprint tooling
(`checkdecls.py`, `patch_depgraph.py`, the plasTeX config) was copied into
`blueprint/` and its conventions still apply.

## Git conventions

Commit messages here carry the `Co-Authored-By` trailer. Note the sibling
`~/projects/damian` repo asks for **no** trailer; that preference is specific to
that repo.
