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

## MorreyInequality.lean — **ready to submit** (verified on Mathlib master `a218e50`, 2026-09-17)

Morrey's inequality — the Sobolev embedding `W^{1,p} ↪ L^∞` for `p > n`, and the
Hölder estimate behind it. Submitted as **two PRs**; the descriptions, labels and
checklists are in `PR-1-polar-lintegral.md` and `PR-2-morrey.md`.

- **PR 1** adds the two polar-coordinate `lintegral` lemmas to
  `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
  (`HaarToSphere.lean.patch` here is that diff).
- **PR 2** adds `Mathlib/Analysis/FunctionalSpaces/MorreyInequality.lean` (the file
  here is the master-ready version: `module` header, `public import`s,
  `@[expose] public section`, plain `def`s for the constants, no unused
  hypotheses), the import line in `Mathlib.lean`, and the two bibliography entries
  `evans2010` and `liebLoss2001` in `docs/references.bib` (`references.bib.patch`).
- `pr-polar-morrey.patch` is the whole diff against master, both PRs together.

**Where the work lives.** `~/projects/mathlib4-master` is a shallow clone of Mathlib
master at `a218e50` (toolchain `v4.35.0-rc2`, build cache fetched), on the branch
`halmaghi/lintegral-toSphere` with the changes **uncommitted** in the working tree.
To split into the two PRs: commit `HaarToSphere.lean` alone on that branch, then
`git checkout -b halmaghi/morrey-inequality` and commit the rest. Mathlib runs CI on
branches of the main repository; ask on Zulip (`#mathlib4`) for write access first,
or push to a fork with `gh repo fork leanprover-community/mathlib4 --remote`.

**Verification done on master** (all clean): `lake build` of both modules,
`lake exe runLinter` on both modules, `lake exe lint-style`, `lake exe mk_all --check`.
No line exceeds 100 characters; the pin-compiled draft had no warnings.

**Differences from the pinned checkout** that a reader of this project should know:
`eLpNorm_eq_lintegral_rpow_enorm_toReal` and `eLpNorm_exponent_top` take an extra
`AEStronglyMeasurable f μ` argument on master. The file here therefore does **not**
compile against this project's pin; that is expected, the project does not import it.

**What it contains, in order** (the polar-coordinates lemmas now live in
`HaarToSphere.lean`):

- `lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi` and
  `setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo` (PR 1): polar coordinates for a
  Lebesgue integral against an additive Haar measure, general non-negative measurable
  integrand, whole space and ball.
- `setLIntegral_ball_rpow_neg`: the exact value of the Riesz kernel integral
  `∫⁻ y in ball x r, ‖y - x‖ ^ (-a)` for `a < n`, namely
  `n / (n - a) * μ (ball 0 1) * r ^ (n - a)`; `lintegral_ball_rpow_neg_lt_top` its
  finiteness. This is where supercriticality is consumed, and the only place.
- `enorm_sub_le_lintegral_Ioc_enorm_fderiv`: the fundamental theorem of calculus along a
  ray, without assuming the target space complete (Bochner integral in
  `UniformSpace.Completion F`).
- `lintegral_ball_enorm_sub_le_lintegral_riesz`: the Riesz potential estimate.
- `enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`: the Hölder estimate, with an
  explicit constant homogeneous of degree `-1/p` in `μ`.
- `eLpNorm_top_le_eLpNorm_fderiv`: the essential-supremum bound for a function supported
  in a bounded set.

The full rationale, including what Mathlib already has and why the cylinder
`ℝ × S¹` does not fit the Sobolev designs currently in flight, is at
https://claude.ai/code/artifact/6128ff05-9235-473b-beb9-9f0a2614767a
