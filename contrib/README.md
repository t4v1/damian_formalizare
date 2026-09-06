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

**State.** Statements and constants are final and type-check. The four proofs
carry `sorry`; each docstring names the ingredient it needs. The two that carry
real work are the Riesz-kernel integrability on a ball (where supercriticality
is consumed, and where Mathlib's lack of a polar-coordinates change of variables
bites) and the Riesz potential estimate.

The full rationale, including what Mathlib already has and why the cylinder
`ℝ × S¹` does not fit the Sobolev designs currently in flight, is at
https://claude.ai/code/artifact/6128ff05-9235-473b-beb9-9f0a2614767a
