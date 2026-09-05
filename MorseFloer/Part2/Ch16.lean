import MorseFloer.Basic

/-!
# Chapter 16: A little analysis

Formalization of Chapter 16 of Audin–Damian, *Théorie de Morse et homologie de
Floer* — the appendix collecting the functional analysis that Part II runs on.
Its sections:

* **§16.1** Ascoli's theorem.
* **§16.2** Fredholm theory: operators with an index, the basic stability
  properties, and Fredholm maps.
* **§16.3** distributions and weak solutions.
* **§16.4** Sobolev spaces on `ℝⁿ`, the Poincaré inequality and the Rellich
  compactness theorem.

## What Mathlib provides, and the one thing it does not

* **Ascoli** (Theorem 16.1.1) is in Mathlib, in the `ArzelaAscoli` namespace —
  see `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`.  Nothing to restate.
* **Fredholm operators** exist as `ContinuousLinearMap.IsFredholm`, with the
  equivalent characterisations of §16.2.a (`isFredholm_tfae`), quasi-inverses,
  and the closed complemented kernel and range.
* **But Mathlib has no Fredholm index.**  Since the index is exactly what
  Chapter 8 computes for the linearised Floer operator, and what makes the
  moduli spaces of Chapters 8 and 9 have the dimensions the theory needs, the
  index is defined here.

## What is proved here

`fredholmIndex` and the fact that in finite dimensions it depends only on the
two spaces, `dim E − dim F`, which is the sanity check that the definition is
the right one.  The stability theorems of §16.2.b (invariance under small and
under compact perturbations, additivity under composition) are stated and
assumed: they are true and standard, but proving them needs a serious chunk of
operator theory that is not yet in Mathlib.

Sections 16.3 and 16.4 are recorded in the blueprint without Lean statements.
Mathlib *does* have distributions — test functions `𝓓^{n}(Ω, F)` on an open
`Ω`, the space `𝓓'^{n}(Ω, F)` and the distributional derivative — and it has
Bessel-potential Sobolev spaces of tempered distributions on all of `ℝⁿ`, defined
through the Fourier transform.  What it does not have is `W^{k,p}(U)` on a
domain with its norm, so the extension
(16.4.1), trace, Poincaré (16.4.3), Sobolev embedding (16.4.4) and Rellich
(16.4.6) theorems have nothing to be stated about.  This is the gap that makes
Chapters 12 and 13 — elliptic regularity for the Floer operator — inaccessible.
-/

open scoped ContDiff
open ContinuousLinearMap Filter Topology

namespace MorseFloer
namespace Chapter16

/-! ## §16.2 Fredholm theory -/

section Fredholm

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The index of an operator** (§16.2.a): `dim ker u − dim coker u`.

Mathlib has `ContinuousLinearMap.IsFredholm` but no index, so it is defined
here.  Following the book, the index is an integer, and the definition is
written for any continuous linear map; it carries its intended meaning exactly
when `u` is Fredholm, so that both dimensions are finite. -/
noncomputable def fredholmIndex (u : E →L[𝕜] F) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) : ℤ)
    - (Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) : ℤ)

/-- **In finite dimensions the index depends only on the two spaces**:
`ind u = dim E − dim F`, whatever `u` is.

This is rank–nullity together with the dimension of a quotient, and it is the
check that `fredholmIndex` is the right notion: the index is insensitive to the
operator, which is why it is a deformation invariant in general (Theorem
16.2.9) and why it can be computed by degeneration in Chapter 8. -/
theorem fredholmIndex_of_finiteDimensional [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (u : E →L[𝕜] F) :
    fredholmIndex u = (Module.finrank 𝕜 E : ℤ) - (Module.finrank 𝕜 F : ℤ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) (V := E) (V₂ := F) (u : E →ₗ[𝕜] F)
  have h2 := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (u : E →ₗ[𝕜] F))
  rw [fredholmIndex]
  omega

/-- **Theorem 16.2.9 (invariance of the index under small perturbations).**
Fredholm operators form an open set and the index is locally constant on it.

*Assumed.*  This is the reason the index of the linearised Floer operator can be
computed at a convenient point of the space of data and then transported. -/
theorem fredholmIndex_locally_constant [CompleteSpace E] [CompleteSpace F]
    {u : E →L[𝕜] F} (_hu : ContinuousLinearMap.IsFredholm u) :
    ∀ᶠ v in 𝓝 u, ContinuousLinearMap.IsFredholm v ∧ fredholmIndex v = fredholmIndex u := by
  sorry

/-- **Theorem 16.2.10 (additivity of the index).**  The composite of two
Fredholm operators is Fredholm, with index the sum of the indices.

*Assumed.* -/
theorem fredholmIndex_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G}
    (_hu : ContinuousLinearMap.IsFredholm u) (_hv : ContinuousLinearMap.IsFredholm v) :
    ContinuousLinearMap.IsFredholm (v.comp u)
      ∧ fredholmIndex (v.comp u) = fredholmIndex v + fredholmIndex u := by
  sorry

/-- **Proposition 16.2.7 (compact perturbations).**  Adding a compact operator
changes neither the Fredholm property nor the index.

*Assumed.*  Chapter 8 uses this to pass from the linearised Floer operator to
its constant-coefficient model, whose index is computable. -/
theorem fredholmIndex_add_compact [CompleteSpace E] [CompleteSpace F]
    {u : E →L[𝕜] F} {k : E →L[𝕜] F}
    (_hu : ContinuousLinearMap.IsFredholm u) (_hk : IsCompactOperator k) :
    ContinuousLinearMap.IsFredholm (u + k) ∧ fredholmIndex (u + k) = fredholmIndex u := by
  sorry

end Fredholm

end Chapter16
end MorseFloer
