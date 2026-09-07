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

**State.** One `sorry` remains, on the Hölder estimate
`enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`. Everything else is
proved, and `#print axioms` was used to separate the unconditional results from
the one whose proof is complete but whose dependency is not.

Unconditional — `#print axioms` shows nothing but `propext`, `Classical.choice`
and `Quot.sound`:

- `lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi` — polar coordinates for
  a Lebesgue integral against an additive Haar measure, for a general
  non-negative measurable integrand. Mathlib has
  `Measure.measurePreserving_homeomorphUnitSphereProd` but exposes only its
  radial corollaries, so this is the missing general `lintegral` form. It belongs
  upstream in `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` on its own
  merits, whether or not Morrey ever lands.
- `setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo` — the same, localised
  to a ball, with the radial integral over `Ioo 0 R`.
- `enorm_sub_le_lintegral_Ioc_enorm_fderiv` — the fundamental theorem of calculus
  along a ray, stated without assuming the target space complete: the Bochner
  integral behind it is taken in `UniformSpace.Completion F`.
- `lintegral_ball_rpow_neg_lt_top` — integrability of the Riesz kernel on a ball,
  and the only place the hypothesis `n < p` is used.
- `lintegral_ball_enorm_sub_le_lintegral_riesz` — the Riesz potential estimate:
  the mean oscillation of a `C¹` function on a ball is at most `r ^ n / n` times
  the Riesz potential of its derivative. Both sides are read in polar coordinates
  about the centre, where the radial density `ρ ^ (n - 1)` cancels the Riesz
  kernel exactly and what is left on each ray is the fundamental theorem of
  calculus.

`eLpNorm_top_le_eLpNorm_fderiv` has a complete proof, but a *conditional* one: it
is derived from the Hölder estimate, which is still assumed, so `#print axioms`
reports `sorryAx`. It becomes unconditional the moment that estimate lands. The
proof walks out of the support along a ray to find a point at distance
`Metric.diam s` at which the function vanishes.

What remains is the Hölder estimate itself, and its docstring says exactly what
is left: Hölder's inequality against the Riesz kernel — which additionally wants
a quantitative form of `lintegral_ball_rpow_neg_lt_top`, giving the value of the
integral and not merely its finiteness — followed by the comparison of the
averages over `ball x ‖x - z‖` and `ball z ‖x - z‖` with the average over their
intersection, which contains a ball of half the radius about the midpoint.

Two notes that correct earlier ones:

- Mathlib **does** have a generalized polar-coordinates change of variables,
  `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`: `Measure.toSphere`,
  `measurePreserving_homeomorphUnitSphereProd`, and the radial corollaries
  `integrableOn_fun_norm_addHaar` and `integral_fun_norm_addHaar`. Together with
  `integrableOn_ball_of_norm_le_rpow` in
  `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean` this is what makes the
  Riesz-kernel proof short; the general `lintegral` form recorded in this file is
  what the potential estimate needs.
- Two of the drafted constants were not homogeneous of the right degree in `μ`,
  which made the statements they appear in false for a Haar measure scaled down
  by a small factor. They are corrected: the Riesz potential estimate now carries
  `rieszPotentialConst E r = r ^ n / n`, which does not involve `μ` at all —
  both sides of that estimate are homogeneous of degree one in `μ`, and the
  completed proof does give exactly `r ^ n / n` — and `morreyConst` now carries
  `2 ^ (n + 1) / n * … * (μ (ball 0 1)).toNNReal⁻¹` in place of
  `2 * … * (μ (ball 0 1)).toNNReal`, which makes it homogeneous of degree
  `-1 / p` and so cancels the degree `1 / p` of `eLpNorm · p μ`.

The full rationale, including what Mathlib already has and why the cylinder
`ℝ × S¹` does not fit the Sobolev designs currently in flight, is at
https://claude.ai/code/artifact/6128ff05-9235-473b-beb9-9f0a2614767a
