# contrib/ — drafts aimed at Mathlib, not part of the MorseFloer library

Files here mirror their intended Mathlib paths so they can be moved over
unchanged. They are **not** imported from `MorseFloer.lean` and are not built by
`lake build`, so they do not enter the project's `sorry` audit. Check one with:

```sh
lake env lean contrib/Mathlib/Analysis/FunctionalSpaces/MorreyInequality.lean
```

## LinearAlgebra/Prod.lean

Two isomorphisms about products of submodules that Mathlib does not have:
`Submodule.prodEquiv` (`↥(p × q) ≃ₗ ↥p × ↥q`) and `Submodule.quotientProdEquiv`
(`(M × N) ⧸ (p × q) ≃ₗ (M ⧸ p) × (N ⧸ q)`). Together they split a rank
computation on `f.prodMap g` into one on each factor.

**State.** Complete, no `sorry`. The first belongs in
`Mathlib/LinearAlgebra/Prod.lean` beside `Submodule.prod`; the second needs
`Mathlib.LinearAlgebra.Isomorphisms`, so it may prefer to live there. Once they
are upstream, `fredholmIndex (u.prodMap v) = fredholmIndex u + fredholmIndex v`
becomes a short follow-up to the Fredholm index file below.

## Analysis/Normed/Operator/Fredholm/Index.lean

The **index of a Fredholm operator**, which Mathlib does not have at all: it has
`ContinuousLinearMap.IsFredholm`, Fredholm decompositions and quasi-inverses,
but no index. The file defines `ContinuousLinearMap.fredholmIndex u` as
`dim (ker u) - dim (coker u)` and proves the two stability theorems that make it
useful: additivity under composition (`fredholmIndex_comp`) and local constancy
(`fredholmIndex_locally_constant`), together with the finite-rank case of
invariance under compact perturbations
(`isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange`), the value in
finite dimensions, the value read off a `FredholmPackage`, and the surjective,
injective and bijective special cases.

It opens with three lemmas of pure linear algebra, in `namespace LinearMap`.
The first, `LinearMap.finrank_ker_sub_finrank_coker_comp`, is the engine of
additivity: `dim (ker ·) - dim (coker ·)` is additive under composition of bare
linear maps. The usual proof needs the six-term exact sequence and an
alternating-sum count; this one avoids it, deriving the identity from four
applications of rank-nullity to four explicitly constructed maps. It could be
split out into `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` if a
reviewer prefers, but it ships here because the index additivity is what it is
for. (This absorbs the former `LinearAlgebra/FiniteDimensional/CompIndex.lean`
draft, which is gone: a separate draft file cannot be imported by another one,
and the two belong in a single PR.)

**State.** Complete, no `sorry`; imports are
`Mathlib.Analysis.Normed.Operator.Fredholm.Basic` and
`Mathlib.Analysis.Normed.Operator.NormedSpace`. Belongs beside
`Mathlib/Analysis/Normed/Operator/Fredholm/Basic.lean`, as `Fredholm/Index.lean`.

Two results are deliberately left out, and the module docstring says so:
invariance of the index under a *compact* perturbation, which needs
Riesz-Schauder in a form Mathlib's Riesz theory does not provide, and the index
of a direct sum, which needs the two isomorphisms of `LinearAlgebra/Prod.lean`
above and so waits on that PR.

## MorreyInequality.lean

Morrey's inequality — the Sobolev embedding `W^{1,p} ↪ L^∞` for `p > n`, and the
Hölder estimate behind it.

**Why this one first.** Mathlib's `Analysis/FunctionalSpaces/SobolevInequality.lean`
proves the Gagliardo–Nirenberg–Sobolev inequality under the hypothesis
`p < finrank ℝ E`. The supercritical case is absent; the name Morrey appears in
Mathlib only as an attribution inside the Rademacher proof. Closing that
asymmetry is a self-contained contribution that does not wait on the unsettled
design of Sobolev spaces themselves, because — like the GNS file — it is stated
for compactly supported `C¹` functions and needs no Sobolev space to exist.

It is also the exact input `MorseFloer/Part2/Ch13.lean` assumes repeatedly: the
constant `K` in `‖g‖_∞ ≤ K‖g‖_{W^{1,p}}`, on a two-dimensional domain where
`p > 2` means `p > n`.

**State.** Two of the four results are proved, two remain.

`lintegral_ball_rpow_neg_lt_top` — integrability of the Riesz kernel on a ball,
and the only place the hypothesis `n < p` is used — is proved outright:
`#print axioms` shows it depends on nothing but `propext`, `Classical.choice`
and `Quot.sound`.

`eLpNorm_top_le_eLpNorm_fderiv` has a complete proof, but a *conditional* one: it
is derived from the Hölder estimate, which is still assumed, so `#print axioms`
reports `sorryAx`. It becomes unconditional the moment that estimate lands.

What remains is the Riesz potential estimate and the Hölder estimate that follows
from it. Neither is blocked by anything missing from Mathlib — every ingredient
exists — only by size: the potential estimate needs a `lintegral` polar-coordinate
formula derived from `measurePreserving_homeomorphUnitSphereProd`, since Mathlib
states only the Bochner and integrability corollaries and both are for radial
integrands.

Proved: `lintegral_ball_rpow_neg_lt_top`, the integrability of the Riesz kernel
`y ↦ ‖y - x‖ ^ (-a)` on a ball for `a < n` — this is where supercriticality is
consumed, and it is the only place it is used; and
`eLpNorm_top_le_eLpNorm_fderiv`, which derives the bound on the essential
supremum from the Hölder estimate by walking out of the support along a ray to
find a point at distance `Metric.diam s` at which the function vanishes.

Still `sorry`: `lintegral_ball_enorm_sub_le_lintegral_riesz`, the Riesz
potential estimate, and `enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`,
the Hölder estimate itself.

Two notes that correct earlier ones:

- Mathlib **does** have a generalized polar-coordinates change of variables,
  `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`: `Measure.toSphere`,
  `measurePreserving_homeomorphUnitSphereProd`, and the radial corollaries
  `integrableOn_fun_norm_addHaar` and `integral_fun_norm_addHaar`. Together with
  `integrableOn_ball_of_norm_le_rpow` in
  `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean` this is what makes the
  first proof short.
- Two of the drafted constants were not homogeneous of the right degree in `μ`,
  which made the statements they appear in false for a Haar measure scaled down
  by a small factor. They are corrected: the Riesz potential estimate now carries
  `rieszPotentialConst E r = r ^ n / n`, which does not involve `μ` at all, and
  `morreyConst` now carries `2 ^ (n + 1) / n * … * (μ (ball 0 1)).toNNReal⁻¹`
  in place of `2 * … * (μ (ball 0 1)).toNNReal`.

The full rationale, including what Mathlib already has and why the cylinder
`ℝ × S¹` does not fit the Sobolev designs currently in flight, is at
https://claude.ai/code/artifact/6128ff05-9235-473b-beb9-9f0a2614767a
