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

`fredholmIndex`, and the fact that in finite dimensions it depends only on the
two spaces, `dim E − dim F`, which is the sanity check that the definition is
the right one.

All **three stability theorems of §16.2.b are proved**:

* **Theorem 16.2.10**, `fredholmIndex_comp`: the composite of two Fredholm
  operators is Fredholm with index the sum.  The Fredholm half is Mathlib's
  composition of quasi-inverses; the index half is
  `finrank_ker_sub_finrank_coker_comp`, a self-contained piece of linear algebra
  replacing the usual six-term exact sequence by four rank–nullity counts.
* **Theorem 16.2.9**, `fredholmIndex_locally_constant`: Fredholm operators form
  an open set and the index is locally constant.  Openness is
  `exists_isQuasiInverse_add_of_norm_lt`, the Neumann-series correction of a
  quasi-inverse; the index is then pinned down by
  `fredholmIndex_add_eq_zero_of_isQuasiInverse` — quasi-inverses have opposite
  indices — together with `fredholmIndex_eq_zero_of_one_add`, which says a
  finite-rank perturbation of the identity has index `0`.

* **Proposition 16.2.7**, `fredholmIndex_add_compact`: a compact perturbation
  changes neither the Fredholm property nor the index.  The finite-rank case is
  `isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange`; the general case
  rests on **Riesz–Schauder**, `isFredholm_one_add_of_isCompactOperator` and
  `fredholmIndex_one_add_of_isCompactOperator`, proved in the section of that
  name from Mathlib's Fredholm alternative by a counting argument — no
  ascent–descent chains and no adjoint.  It is stated over `ℝ`, the only place
  the field enters being the Hahn–Banach complement of the finite-dimensional
  kernel.

Two auxiliary results are worth knowing about on their own:

* `fredholmIndex_eq_of_fredholmPackage` reads the index off a Mathlib
  `FredholmPackage`: for a decomposition `E = E₁ ⊕ E₀`, `F = F₁ ⊕ F₀` in which
  `u` is an isomorphism `E₁ ≃ F₁` and zero on `E₀`, the index is
  `dim E₀ − dim F₀`.
* `fredholmIndex_eq_zero_of_one_add`: `ind (1 + N) = 0` whenever `N` has
  finite-dimensional range.
* `isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange`: the finite-rank
  case of Proposition 16.2.7.

All of §16.2.b needs `𝕜` to be complete, because every entry point into
Mathlib's Fredholm API assumes it: over an incomplete field a finite-dimensional
subspace of a normed space need not be complemented, and `IsFredholm` demands a
complemented kernel.  The hypothesis costs nothing here, since Part II works
over `ℝ`.

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

open scoped LinearMap.FiniteRangeSetoid

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

/-- **An invertible operator has index zero**: its kernel and its cokernel both
vanish. -/
theorem fredholmIndex_eq_zero_of_bijective {u : E →L[𝕜] F} (hu : Function.Bijective u) :
    fredholmIndex u = 0 := by
  have hr : LinearMap.range (u : E →ₗ[𝕜] F) = ⊤ := LinearMap.range_eq_top.mpr hu.2
  have hk : LinearMap.ker (u : E →ₗ[𝕜] F) = ⊥ := LinearMap.ker_eq_bot.mpr hu.1
  have h2 : Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) = 0 := by
    have : Subsingleton (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) :=
      Submodule.Quotient.subsingleton_iff.mpr hr
    exact Module.finrank_zero_of_subsingleton
  have h1 : Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) = 0 := by
    rw [hk]; simp
  rw [fredholmIndex, h1, h2]
  omega

/-! ### The index of a Fredholm package -/

/-- **The index read off a Fredholm package.**

A `ContinuousLinearMap.FredholmPackage` for `u` is a pair of topological
decompositions `E = E₁ ⊕ E₀` and `F = F₁ ⊕ F₀`, with `E₀` and `F₀` finite
dimensional, in which `u` kills `E₀` and restricts to an isomorphism
`E₁ ≃L F₁`.  In such a decomposition the index is visible on the nose:
`ker u = E₀` and `range u = F₁`, so the cokernel is `F₀`, and

  `ind u = dim E₀ − dim F₀`.

This is the bridge between the definition of `fredholmIndex`, which is about
a kernel and a quotient, and the decompositions that a proof of a stability
theorem of §16.2.b may prefer to manipulate.  Get a package for a Fredholm
operator from `ContinuousLinearMap.IsFredholm.nonempty_fredholmPackage`
(which additionally needs `𝕜` to be complete), or build one by hand when the
decomposition is known. -/
theorem fredholmIndex_eq_of_fredholmPackage {u : E →L[𝕜] F}
    (pkg : ContinuousLinearMap.FredholmPackage u) :
    fredholmIndex u
      = (Module.finrank 𝕜 pkg.decDom.X₀ : ℤ) - (Module.finrank 𝕜 pkg.decCodom.X₀ : ℤ) := by
  have hker : Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F))
      = Module.finrank 𝕜 pkg.decDom.X₀ :=
    (LinearEquiv.ofEq _ _ pkg.ker_eq).finrank_eq
  have hcoker : Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F))
      = Module.finrank 𝕜 pkg.decCodom.X₀ :=
    ((Submodule.quotEquivOfEq _ _ pkg.range_eq).trans
      (Submodule.quotientEquivOfIsCompl _ _ pkg.decCodom.isTopCompl.isCompl)).finrank_eq
  rw [fredholmIndex, hker, hcoker]

/-! ### Additivity of the index under composition -/

/-- **The index identity for a composite, as pure linear algebra.**

For linear maps `a : X → Y` and `b : Y → Z` whose relevant kernels and cokernels
are finite dimensional,

  `dim ker (b ∘ a) − dim coker (b ∘ a) = (dim ker b − dim coker b) + (dim ker a − dim coker a)`.

This is the content of Theorem 16.2.10, stripped of all topology.  The proof is
four applications of rank–nullity, to the four maps

* `a` restricted to `ker (b ∘ a)`, whose image is `ker b ⊓ range a`
  and whose kernel is `ker a`;
* the projection `Y → Y ⧸ range a` restricted to `ker b`, whose image is
  `S := (ker b + range a)/range a` and whose kernel is `ker b ⊓ range a`;
* the map `Y ⧸ range a → Z ⧸ range (b ∘ a)` induced by `b`, whose image is
  `T := (range b + range (b ∘ a))/range (b ∘ a)` and whose kernel is `S`;
* the projection `Z ⧸ range (b ∘ a) → Z ⧸ range b`, which is onto with kernel `T`.

Writing the four identities down and eliminating `dim (ker b ⊓ range a)`,
`dim S` and `dim T` gives the result. -/
theorem finrank_ker_sub_finrank_coker_comp {X Y Z : Type*}
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y] [AddCommGroup Z] [Module 𝕜 Z]
    (a : X →ₗ[𝕜] Y) (b : Y →ₗ[𝕜] Z)
    [FiniteDimensional 𝕜 (LinearMap.ker (b ∘ₗ a))] [FiniteDimensional 𝕜 (LinearMap.ker b)]
    [FiniteDimensional 𝕜 (Y ⧸ LinearMap.range a)]
    [FiniteDimensional 𝕜 (Z ⧸ LinearMap.range (b ∘ₗ a))] :
    (Module.finrank 𝕜 (LinearMap.ker (b ∘ₗ a)) : ℤ)
        - (Module.finrank 𝕜 (Z ⧸ LinearMap.range (b ∘ₗ a)) : ℤ)
      = ((Module.finrank 𝕜 (LinearMap.ker b) : ℤ)
          - (Module.finrank 𝕜 (Z ⧸ LinearMap.range b) : ℤ))
        + ((Module.finrank 𝕜 (LinearMap.ker a) : ℤ)
          - (Module.finrank 𝕜 (Y ⧸ LinearMap.range a) : ℤ)) := by
  -- `ker a ≤ ker (b ∘ a)`
  have hle : LinearMap.ker a ≤ LinearMap.ker (b ∘ₗ a) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    rw [hx, map_zero]
  -- (1) `dim ker (b ∘ a) = dim (ker b ⊓ range a) + dim ker a`
  have h1 : Module.finrank 𝕜 (LinearMap.ker (b ∘ₗ a))
      = Module.finrank 𝕜 ↥(LinearMap.ker b ⊓ LinearMap.range a)
        + Module.finrank 𝕜 (LinearMap.ker a) := by
    have hrf : LinearMap.range (a ∘ₗ (LinearMap.ker (b ∘ₗ a)).subtype)
        = LinearMap.ker b ⊓ LinearMap.range a := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      ext y
      simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range,
        LinearMap.comp_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x, rfl⟩
      · rintro ⟨hy, x, rfl⟩
        exact ⟨x, hy, rfl⟩
    have hkf : LinearMap.ker (a ∘ₗ (LinearMap.ker (b ∘ₗ a)).subtype)
        = Submodule.comap (LinearMap.ker (b ∘ₗ a)).subtype (LinearMap.ker a) :=
      LinearMap.ker_comp _ _
    have hr := LinearMap.finrank_range_add_finrank_ker
      (a ∘ₗ (LinearMap.ker (b ∘ₗ a)).subtype)
    rw [hrf, hkf, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hr
    omega
  -- (2) `dim ker b = dim S + dim (ker b ⊓ range a)`
  have h2 : Module.finrank 𝕜 (LinearMap.ker b)
      = Module.finrank 𝕜 ↥(Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b))
        + Module.finrank 𝕜 ↥(LinearMap.ker b ⊓ LinearMap.range a) := by
    have hrg : LinearMap.range ((LinearMap.range a).mkQ ∘ₗ (LinearMap.ker b).subtype)
        = Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hkg : LinearMap.ker ((LinearMap.range a).mkQ ∘ₗ (LinearMap.ker b).subtype)
        = Submodule.comap (LinearMap.ker b).subtype
            (LinearMap.ker b ⊓ LinearMap.range a) := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf,
        Submodule.comap_subtype_self, top_inf_eq]
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range a).mkQ ∘ₗ (LinearMap.ker b).subtype)
    rw [hrg, hkg, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at hr
    omega
  -- (3) `dim (Y ⧸ range a) = dim T + dim S`
  have hle3 : LinearMap.range a
      ≤ LinearMap.ker ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  have h3 : Module.finrank 𝕜 (Y ⧸ LinearMap.range a)
      = Module.finrank 𝕜 ↥(Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ (LinearMap.range b))
        + Module.finrank 𝕜 ↥(Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b)) := by
    have hker3 : LinearMap.ker ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b)
        = LinearMap.ker b ⊔ LinearMap.range a := by
      refine le_antisymm (fun y hy => ?_) ?_
      · simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hy
        obtain ⟨x, hx⟩ := hy
        have hmem : y - a x ∈ LinearMap.ker b := by
          simp only [LinearMap.mem_ker, map_sub, hx, sub_self]
        have hy' : y = (y - a x) + a x := by abel
        rw [hy']
        exact Submodule.add_mem_sup hmem ⟨x, rfl⟩
      · rw [sup_le_iff]
        refine ⟨fun y hy => ?_, hle3⟩
        simp only [LinearMap.mem_ker] at hy
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, hy, map_zero]
    have hrg : LinearMap.range ((LinearMap.range a).liftQ
          ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) hle3)
        = Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ (LinearMap.range b) := by
      rw [Submodule.range_liftQ]
      exact LinearMap.range_comp b _
    have hkg : LinearMap.ker ((LinearMap.range a).liftQ
          ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) hle3)
        = Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b) := by
      rw [Submodule.ker_liftQ, hker3, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range a).liftQ ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) hle3)
    rw [hrg, hkg] at hr
    omega
  -- (4) `dim (Z ⧸ range (b ∘ a)) = dim (Z ⧸ range b) + dim T`
  have hle4 : LinearMap.range (b ∘ₗ a) ≤ LinearMap.ker (LinearMap.range b).mkQ := by
    rw [Submodule.ker_mkQ]
    exact LinearMap.range_comp_le_range a b
  have h4 : Module.finrank 𝕜 (Z ⧸ LinearMap.range (b ∘ₗ a))
      = Module.finrank 𝕜 (Z ⧸ LinearMap.range b)
        + Module.finrank 𝕜 ↥(Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ
            (LinearMap.range b)) := by
    have hrg : LinearMap.range ((LinearMap.range (b ∘ₗ a)).liftQ (LinearMap.range b).mkQ hle4)
        = ⊤ := by
      rw [Submodule.range_liftQ, Submodule.range_mkQ]
    have hkg : LinearMap.ker ((LinearMap.range (b ∘ₗ a)).liftQ (LinearMap.range b).mkQ hle4)
        = Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ (LinearMap.range b) := by
      rw [Submodule.ker_liftQ, Submodule.ker_mkQ]
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range (b ∘ₗ a)).liftQ (LinearMap.range b).mkQ hle4)
    rw [hrg, hkg, Submodule.topEquiv.finrank_eq] at hr
    omega
  omega

/-! ### A finite-rank perturbation of the identity -/

/-- **`1 + n` has as much kernel as cokernel**, when `n` has finite-dimensional
range.  Pure linear algebra: with `W := range n`, one checks that `W` is
`(1 + n)`-invariant, that `ker (1 + n) ≤ W`, that `range (1 + n) + W` is
everything, and that `(1 + n) W = W ⊓ range (1 + n)`.  Rank–nullity applied to
`(1 + n)|_W` and to the projection `W → X ⧸ range (1 + n)` then gives the two
identities

  `dim W = dim (W ⊓ range (1 + n)) + dim ker (1 + n)`,
  `dim W = dim (X ⧸ range (1 + n)) + dim (W ⊓ range (1 + n))`,

whose difference is the claim. -/
theorem finrank_ker_eq_finrank_coker_one_add {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    (n : X →ₗ[𝕜] X) [FiniteDimensional 𝕜 ↥(LinearMap.range n)] :
    Module.finrank 𝕜 (LinearMap.ker (LinearMap.id + n))
      = Module.finrank 𝕜 (X ⧸ LinearMap.range (LinearMap.id + n)) := by
  have hkerW : LinearMap.ker (LinearMap.id + n) ≤ LinearMap.range n := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at hx
    have hnx : n x = -x := eq_neg_of_add_eq_zero_right hx
    exact ⟨-x, by rw [map_neg, hnx, neg_neg]⟩
  have hsup : LinearMap.range (LinearMap.id + n) ⊔ LinearMap.range n = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = (LinearMap.id + n : X →ₗ[𝕜] X) x + n (-x) := by
      simp only [LinearMap.add_apply, LinearMap.id_apply, map_neg]
      abel
    rw [hx]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨-x, rfl⟩
  have hmap : Submodule.map (LinearMap.id + n) (LinearMap.range n)
      = LinearMap.range n ⊓ LinearMap.range (LinearMap.id + n) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨Submodule.add_mem _ hy ⟨y, rfl⟩, ⟨y, rfl⟩⟩
    · rintro _ ⟨hzW, x, rfl⟩
      have hx : x ∈ LinearMap.range n := by
        have hxe : x = (LinearMap.id + n : X →ₗ[𝕜] X) x - n x := by
          simp only [LinearMap.add_apply, LinearMap.id_apply]
          abel
        rw [hxe]
        exact Submodule.sub_mem _ hzW ⟨x, rfl⟩
      exact ⟨x, hx, rfl⟩
  have h1 : Module.finrank 𝕜 ↥(LinearMap.range n)
      = Module.finrank 𝕜 ↥(LinearMap.range n ⊓ LinearMap.range (LinearMap.id + n))
        + Module.finrank 𝕜 (LinearMap.ker (LinearMap.id + n)) := by
    have hrf : LinearMap.range ((LinearMap.id + n) ∘ₗ (LinearMap.range n).subtype)
        = LinearMap.range n ⊓ LinearMap.range (LinearMap.id + n) := by
      rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
    have hkf : LinearMap.ker ((LinearMap.id + n) ∘ₗ (LinearMap.range n).subtype)
        = Submodule.comap (LinearMap.range n).subtype (LinearMap.ker (LinearMap.id + n)) :=
      LinearMap.ker_comp _ _
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.id + n) ∘ₗ (LinearMap.range n).subtype)
    rw [hrf, hkf, (Submodule.comapSubtypeEquivOfLe hkerW).finrank_eq] at hr
    omega
  have h2 : Module.finrank 𝕜 ↥(LinearMap.range n)
      = Module.finrank 𝕜 (X ⧸ LinearMap.range (LinearMap.id + n))
        + Module.finrank 𝕜 ↥(LinearMap.range n ⊓ LinearMap.range (LinearMap.id + n)) := by
    have hrg : LinearMap.range ((LinearMap.range (LinearMap.id + n)).mkQ
        ∘ₗ (LinearMap.range n).subtype) = ⊤ := by
      rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_mkQ_eq_top]
      exact hsup
    have hkg : LinearMap.ker ((LinearMap.range (LinearMap.id + n)).mkQ
          ∘ₗ (LinearMap.range n).subtype)
        = Submodule.comap (LinearMap.range n).subtype
            (LinearMap.range n ⊓ LinearMap.range (LinearMap.id + n)) := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf,
        Submodule.comap_subtype_self, top_inf_eq]
    have hr := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range (LinearMap.id + n)).mkQ ∘ₗ (LinearMap.range n).subtype)
    rw [hrg, hkg, Submodule.topEquiv.finrank_eq,
      (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at hr
    omega
  omega

/-- **A finite-rank perturbation of the identity has index zero.**

This is the case of Proposition 16.2.7 that the proof of Theorem 16.2.9 needs,
and the only case that is elementary: for `N` merely compact the statement is
Riesz theory. -/
theorem fredholmIndex_eq_zero_of_one_add {N : E →L[𝕜] E}
    (hN : ((N : E →ₗ[𝕜] E)).HasNoetherianRange) : fredholmIndex (1 + N) = 0 := by
  have : IsNoetherian 𝕜 ↥(LinearMap.range (N : E →ₗ[𝕜] E)) := hN
  have h : ((1 + N : E →L[𝕜] E) : E →ₗ[𝕜] E) = LinearMap.id + (N : E →ₗ[𝕜] E) := rfl
  rw [fredholmIndex, h, finrank_ker_eq_finrank_coker_one_add (N : E →ₗ[𝕜] E)]
  omega

/-! ### Stability of the Fredholm property under small perturbations -/

/-- A left quasi-inverse and a right quasi-inverse of the same map are quasi-inverses
of it, and of each other.

Recall that `≈` here is equality modulo linear maps with noetherian (over a field:
finite-dimensional) range.  The proof is the usual one-line argument
`p ≈ p(mq) = (pm)q ≈ q`. -/
theorem isQuasiInverse_of_left_of_right {X Y : Type*} [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y] {m : X →ₗ[𝕜] Y} {p q : Y →ₗ[𝕜] X}
    (hp : p ∘ₗ m ≈ LinearMap.id) (hq : m ∘ₗ q ≈ LinearMap.id) :
    LinearMap.IsQuasiInverse p m := by
  have hpq : p ≈ q :=
    calc p = p ∘ₗ LinearMap.id := (LinearMap.comp_id p).symm
      _ ≈ p ∘ₗ (m ∘ₗ q) := Setoid.symm (LinearMap.FiniteRangeSetoid.equiv_comp_left hq)
      _ = (p ∘ₗ m) ∘ₗ q := rfl
      _ ≈ LinearMap.id ∘ₗ q := LinearMap.FiniteRangeSetoid.equiv_comp_right hp
      _ = q := LinearMap.id_comp q
  exact ⟨hp, Setoid.trans (LinearMap.FiniteRangeSetoid.equiv_comp_left hpq) hq⟩

/-- If `a ∘L b` is the identity plus an operator with noetherian range, then `a ∘ b`
is the identity modulo such operators — that is, `a` is a left quasi-inverse of `b`. -/
theorem equiv_id_of_comp_eq_one_add {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {a : Y →L[𝕜] X} {b : X →L[𝕜] Y} {k : X →L[𝕜] X}
    (hk : ((k : X →ₗ[𝕜] X)).HasNoetherianRange) (hab : a ∘L b = 1 + k) :
    ((a : Y →ₗ[𝕜] X) ∘ₗ (b : X →ₗ[𝕜] Y)) ≈ LinearMap.id := by
  have h2 : ((a : Y →ₗ[𝕜] X) ∘ₗ (b : X →ₗ[𝕜] Y)) = LinearMap.id + (k : X →ₗ[𝕜] X) :=
    congrArg (fun f : X →L[𝕜] X => (f : X →ₗ[𝕜] X)) hab
  have h3 : LinearMap.id + (k : X →ₗ[𝕜] X) - LinearMap.id = (k : X →ₗ[𝕜] X) := by abel
  rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange, h2, h3]
  exact hk

/-- Two-sided inverses are quasi-inverses. -/
theorem isQuasiInverse_of_comp_eq_one {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {p : X →L[𝕜] Y} {q : Y →L[𝕜] X}
    (h1 : q ∘L p = 1) (h2 : p ∘L q = 1) : q.IsQuasiInverse p := by
  have hzero : ((0 : X →L[𝕜] X) : X →ₗ[𝕜] X).HasNoetherianRange :=
    LinearMap.HasNoetherianRange.zero
  have hzero' : ((0 : Y →L[𝕜] Y) : Y →ₗ[𝕜] Y).HasNoetherianRange :=
    LinearMap.HasNoetherianRange.zero
  exact ⟨equiv_id_of_comp_eq_one_add hzero (by rw [h1, add_zero]),
    equiv_id_of_comp_eq_one_add hzero' (by rw [h2, add_zero])⟩

/-- **Small perturbations keep a quasi-inverse** — the analytic core of Theorem 16.2.9.

If `v` is a quasi-inverse of `u` and `‖v‖ ‖δ‖ < 1`, then `u + δ` again admits a
quasi-inverse, and one of a very specific shape: `p ∘L v`, where `p` is the
inverse of `1 + vδ`.  That shape is what makes the *index* locally constant and
not just the Fredholm property, since `p` is invertible and so does not change
the index.

The naive argument does not work: from `v u = 1 + K` with `K` of finite range one
only gets `v (u + δ) = 1 + K + vδ`, and `vδ` has no reason to have finite range.
The fix is the Neumann series.  Since `‖vδ‖ < 1`, the operator `1 + vδ` is
invertible, and

  `(1 + vδ)⁻¹ v (u + δ) = 1 + (1 + vδ)⁻¹ K`,

whose error term still has finite range; so `(1 + vδ)⁻¹ v` is a *left*
quasi-inverse of `u + δ`.  Symmetrically `1 + δv` is invertible on `F` and
`v (1 + δv)⁻¹` is a right quasi-inverse.  A left and a right quasi-inverse of the
same map agree modulo finite range (`isQuasiInverse_of_left_of_right`), so either
one is a genuine quasi-inverse. -/
theorem exists_isQuasiInverse_add_of_norm_lt [CompleteSpace E] [CompleteSpace F]
    {u : E →L[𝕜] F} {v : F →L[𝕜] E} (h : v.IsQuasiInverse u)
    {δ : E →L[𝕜] F} (hδ : ‖v‖ * ‖δ‖ < 1) :
    ∃ p : E →L[𝕜] E, (1 + v ∘L δ) ∘L p = 1 ∧ p ∘L (1 + v ∘L δ) = 1
      ∧ LinearMap.IsQuasiInverse ((p ∘L v : F →L[𝕜] E) : F →ₗ[𝕜] E)
        ((u + δ : E →L[𝕜] F) : E →ₗ[𝕜] F) := by
  obtain ⟨hL, hR⟩ := h
  -- the two Neumann series
  have hs : ‖(-(v ∘L δ) : E →L[𝕜] E)‖ < 1 := by
    rw [norm_neg]
    exact lt_of_le_of_lt (v.opNorm_comp_le δ) hδ
  have ht : ‖(-(δ ∘L v) : F →L[𝕜] F)‖ < 1 := by
    rw [norm_neg]
    refine lt_of_le_of_lt (δ.opNorm_comp_le v) ?_
    rwa [mul_comm]
  obtain ⟨p, hpl, hpr⟩ : ∃ p : E →L[𝕜] E,
      (1 + v ∘L δ) ∘L p = 1 ∧ p ∘L (1 + v ∘L δ) = 1 := by
    have hval : ((Units.oneSub (-(v ∘L δ)) hs : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) = 1 + v ∘L δ := by
      rw [Units.val_oneSub, sub_neg_eq_add]
    refine ⟨((Units.oneSub (-(v ∘L δ)) hs : (E →L[𝕜] E)ˣ)⁻¹ : (E →L[𝕜] E)ˣ), ?_, ?_⟩
    · rw [← hval]
      exact (Units.oneSub (-(v ∘L δ)) hs).mul_inv
    · rw [← hval]
      exact (Units.oneSub (-(v ∘L δ)) hs).inv_mul
  obtain ⟨r, hr⟩ : ∃ r : F →L[𝕜] F, (1 + δ ∘L v) ∘L r = 1 := by
    have hval : ((Units.oneSub (-(δ ∘L v)) ht : (F →L[𝕜] F)ˣ) : F →L[𝕜] F) = 1 + δ ∘L v := by
      rw [Units.val_oneSub, sub_neg_eq_add]
    refine ⟨((Units.oneSub (-(δ ∘L v)) ht : (F →L[𝕜] F)ˣ)⁻¹ : (F →L[𝕜] F)ˣ), ?_⟩
    rw [← hval]
    exact (Units.oneSub (-(δ ∘L v)) ht).mul_inv
  -- the two finite-range error terms
  have hA : ((v ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E).HasNoetherianRange := by
    have h0 : ((v ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E)
        = (v : F →ₗ[𝕜] E) ∘ₗ (u : E →ₗ[𝕜] F) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hL
  have hB : ((u ∘L v - 1 : F →L[𝕜] F) : F →ₗ[𝕜] F).HasNoetherianRange := by
    have h0 : ((u ∘L v - 1 : F →L[𝕜] F) : F →ₗ[𝕜] F)
        = (u : E →ₗ[𝕜] F) ∘ₗ (v : F →ₗ[𝕜] E) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hR
  -- the corrected quasi-inverses, on the left and on the right
  have hc : v ∘L (u + δ) = (v ∘L u - 1) + (1 + v ∘L δ) := by
    rw [ContinuousLinearMap.comp_add]; abel
  have hd : (u + δ) ∘L v = (u ∘L v - 1) + (1 + δ ∘L v) := by
    rw [ContinuousLinearMap.add_comp]; abel
  have hleft : ((p ∘L v : F →L[𝕜] E) : F →ₗ[𝕜] E) ∘ₗ ((u + δ : E →L[𝕜] F) : E →ₗ[𝕜] F)
      ≈ LinearMap.id := by
    refine equiv_id_of_comp_eq_one_add (k := p ∘L (v ∘L u - 1)) ?_ ?_
    · have h0 : ((p ∘L (v ∘L u - 1) : E →L[𝕜] E) : E →ₗ[𝕜] E)
          = (p : E →ₗ[𝕜] E) ∘ₗ ((v ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E) := rfl
      rw [h0]
      exact hA.comp_left _
    · calc (p ∘L v) ∘L (u + δ) = p ∘L (v ∘L (u + δ)) := ContinuousLinearMap.comp_assoc _ _ _
        _ = p ∘L ((v ∘L u - 1) + (1 + v ∘L δ)) := by rw [hc]
        _ = p ∘L (v ∘L u - 1) + p ∘L (1 + v ∘L δ) := ContinuousLinearMap.comp_add _ _ _
        _ = p ∘L (v ∘L u - 1) + 1 := by rw [hpr]
        _ = 1 + p ∘L (v ∘L u - 1) := add_comm _ _
  have hright : ((u + δ : E →L[𝕜] F) : E →ₗ[𝕜] F) ∘ₗ ((v ∘L r : F →L[𝕜] E) : F →ₗ[𝕜] E)
      ≈ LinearMap.id := by
    refine equiv_id_of_comp_eq_one_add (k := (u ∘L v - 1) ∘L r) ?_ ?_
    · have h0 : (((u ∘L v - 1) ∘L r : F →L[𝕜] F) : F →ₗ[𝕜] F)
          = ((u ∘L v - 1 : F →L[𝕜] F) : F →ₗ[𝕜] F) ∘ₗ (r : F →ₗ[𝕜] F) := rfl
      rw [h0]
      exact hB.comp_right _
    · calc (u + δ) ∘L (v ∘L r) = ((u + δ) ∘L v) ∘L r :=
            (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = ((u ∘L v - 1) + (1 + δ ∘L v)) ∘L r := by rw [hd]
        _ = (u ∘L v - 1) ∘L r + (1 + δ ∘L v) ∘L r := ContinuousLinearMap.add_comp _ _ _
        _ = (u ∘L v - 1) ∘L r + 1 := by rw [hr]
        _ = 1 + (u ∘L v - 1) ∘L r := add_comm _ _
  exact ⟨p, hpl, hpr, isQuasiInverse_of_left_of_right hleft hright⟩

/-- **Fredholm operators form an open set** — the first half of Theorem 16.2.9.

This is `exists_isQuasiInverse_add_of_norm_lt` together with Mathlib's
`ContinuousLinearMap.IsFredholm.of_isQuasiInverse`.  The latter is what forces the
hypothesis that `𝕜` is complete: over an incomplete field, Mathlib cannot
produce the complemented kernel that its definition of `IsFredholm` requires. -/
theorem eventually_isFredholm [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
    {u : E →L[𝕜] F} (hu : ContinuousLinearMap.IsFredholm u) :
    ∀ᶠ w in 𝓝 u, ContinuousLinearMap.IsFredholm w := by
  obtain ⟨v, hv⟩ := hu.exists_isQuasiInverse
  have hcont : Continuous fun w : E →L[𝕜] F => ‖v‖ * ‖w - u‖ := by fun_prop
  have htend : Filter.Tendsto (fun w : E →L[𝕜] F => ‖v‖ * ‖w - u‖) (𝓝 u) (𝓝 0) :=
    hcont.tendsto' u 0 (by simp)
  filter_upwards [htend.eventually_lt_const one_pos] with w hw
  obtain ⟨p, -, -, hqi⟩ := exists_isQuasiInverse_add_of_norm_lt hv hw
  have hwu : u + (w - u) = w := by abel
  rw [hwu] at hqi
  exact ContinuousLinearMap.IsFredholm.of_isQuasiInverse hqi

/-! ### The three stability theorems of §16.2.b -/

/-- **Theorem 16.2.10 (additivity of the index).**  The composite of two
Fredholm operators is Fredholm, with index the sum of the indices.

The Fredholm half is Mathlib's `LinearMap.IsQuasiInverse.comp`: quasi-inverses
compose in the opposite order.  The index half is
`finrank_ker_sub_finrank_coker_comp`, the four rank–nullity counts that replace
the usual six-term exact sequence.

`[CompleteSpace 𝕜]` is needed because Mathlib's Fredholm API — here
`IsFredholm.exists_isQuasiInverse` and `IsFredholm.of_isQuasiInverse` — assumes
it throughout: a finite-dimensional subspace of a normed space is complemented
only over a complete field.  It costs nothing in practice, since Part II works
over `ℝ`. -/
theorem fredholmIndex_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G}
    (hu : ContinuousLinearMap.IsFredholm u) (hv : ContinuousLinearMap.IsFredholm v) :
    ContinuousLinearMap.IsFredholm (v.comp u)
      ∧ fredholmIndex (v.comp u) = fredholmIndex v + fredholmIndex u := by
  obtain ⟨pu, hpu⟩ := hu.exists_isQuasiInverse
  obtain ⟨pv, hpv⟩ := hv.exists_isQuasiInverse
  have hqi : (pu ∘L pv).IsQuasiInverse (v.comp u) := hpu.comp hpv
  have hvu : ContinuousLinearMap.IsFredholm (v.comp u) :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hqi
  refine ⟨hvu, ?_⟩
  have : FiniteDimensional 𝕜 (LinearMap.ker ((v : F →ₗ[𝕜] G) ∘ₗ (u : E →ₗ[𝕜] F))) :=
    hvu.finite_ker
  have : FiniteDimensional 𝕜 (LinearMap.ker (v : F →ₗ[𝕜] G)) := hv.finite_ker
  have : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) := hu.finite_coker
  have : FiniteDimensional 𝕜 (G ⧸ LinearMap.range ((v : F →ₗ[𝕜] G) ∘ₗ (u : E →ₗ[𝕜] F))) :=
    hvu.finite_coker
  simp only [fredholmIndex]
  exact finrank_ker_sub_finrank_coker_comp (u : E →ₗ[𝕜] F) (v : F →ₗ[𝕜] G)

/-- **Quasi-inverses have opposite indices.**  If `q` is a quasi-inverse of `u`
then `q ∘ u` is the identity plus a finite-rank operator, so it has index `0`;
additivity then forces `ind q = − ind u`.

This is the step that turns the openness of the Fredholm property into the local
constancy of the index. -/
theorem fredholmIndex_add_eq_zero_of_isQuasiInverse [CompleteSpace 𝕜] [CompleteSpace E]
    [CompleteSpace F] {u : E →L[𝕜] F} {q : F →L[𝕜] E} (h : q.IsQuasiInverse u)
    (hq : ContinuousLinearMap.IsFredholm q) (hu : ContinuousLinearMap.IsFredholm u) :
    fredholmIndex q + fredholmIndex u = 0 := by
  have hN : ((q.comp u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E).HasNoetherianRange := by
    have h0 : ((q.comp u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E)
        = (q : F →ₗ[𝕜] E) ∘ₗ (u : E →ₗ[𝕜] F) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp h.1
  have hone : q.comp u = 1 + (q.comp u - 1) := by abel
  rw [← (fredholmIndex_comp hu hq).2, hone, fredholmIndex_eq_zero_of_one_add hN]

/-- **Theorem 16.2.9 (invariance of the index under small perturbations).**
Fredholm operators form an open set and the index is locally constant on it.

This is the reason the index of the linearised Floer operator can be computed at
a convenient point of the space of data and then transported.

The proof.  Let `q` be a quasi-inverse of `u`.  For `w` with `‖q‖ ‖w − u‖ < 1`,
`exists_isQuasiInverse_add_of_norm_lt` produces the quasi-inverse `p ∘ q` of `w`,
where `p` is the inverse of `1 + q(w − u)` given by the Neumann series; in
particular `w` is Fredholm.  Now apply `fredholmIndex_add_eq_zero_of_isQuasiInverse`
twice, to `(q, u)` and to `(p ∘ q, w)`, and note that `ind (p ∘ q) = ind q`
because `p` is invertible.  The two relations `ind q + ind u = 0` and
`ind q + ind w = 0` give `ind w = ind u`. -/
theorem fredholmIndex_locally_constant [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
    {u : E →L[𝕜] F} (hu : ContinuousLinearMap.IsFredholm u) :
    ∀ᶠ v in 𝓝 u, ContinuousLinearMap.IsFredholm v ∧ fredholmIndex v = fredholmIndex u := by
  obtain ⟨qu, hqu⟩ := hu.exists_isQuasiInverse
  have hquF : ContinuousLinearMap.IsFredholm qu :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hqu.symm
  have hsum : fredholmIndex qu + fredholmIndex u = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hqu hquF hu
  have hcont : Continuous fun w : E →L[𝕜] F => ‖qu‖ * ‖w - u‖ := by fun_prop
  have htend : Filter.Tendsto (fun w : E →L[𝕜] F => ‖qu‖ * ‖w - u‖) (𝓝 u) (𝓝 0) :=
    hcont.tendsto' u 0 (by simp)
  filter_upwards [htend.eventually_lt_const one_pos] with w hw
  obtain ⟨p, hpl, hpr, hqi⟩ := exists_isQuasiInverse_add_of_norm_lt hqu hw
  have hwu : u + (w - u) = w := by abel
  rw [hwu] at hqi
  have hwF : ContinuousLinearMap.IsFredholm w :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hqi
  have hpquF : ContinuousLinearMap.IsFredholm (p ∘L qu) :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hqi.symm
  have hpF : ContinuousLinearMap.IsFredholm p :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse (isQuasiInverse_of_comp_eq_one hpl hpr)
  have hpbij : Function.Bijective p :=
    Function.bijective_iff_has_inverse.mpr
      ⟨(1 + qu ∘L (w - u) : E →L[𝕜] E), fun y => DFunLike.congr_fun hpl y,
        fun y => DFunLike.congr_fun hpr y⟩
  have hsum2 : fredholmIndex (p ∘L qu) + fredholmIndex w = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hqi hpquF hwF
  have hpqu : fredholmIndex (p ∘L qu) = fredholmIndex qu := by
    rw [(fredholmIndex_comp hquF hpF).2, fredholmIndex_eq_zero_of_bijective hpbij, zero_add]
  exact ⟨hwF, by omega⟩

/-- **The finite-rank case of Proposition 16.2.7.**  Adding an operator with
finite-dimensional range changes neither the Fredholm property nor the index.

A quasi-inverse `q` of `u` is again a quasi-inverse of `u + k`, because
`q(u + k) − 1 = (qu − 1) + qk` and `(u + k)q − 1 = (uq − 1) + kq` both still have
finite-dimensional range; `fredholmIndex_add_eq_zero_of_isQuasiInverse` then
computes both indices as `−ind q`. -/
theorem isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange [CompleteSpace 𝕜]
    [CompleteSpace E] [CompleteSpace F] {u k : E →L[𝕜] F}
    (hu : ContinuousLinearMap.IsFredholm u)
    (hk : ((k : E →ₗ[𝕜] F)).HasNoetherianRange) :
    ContinuousLinearMap.IsFredholm (u + k) ∧ fredholmIndex (u + k) = fredholmIndex u := by
  obtain ⟨q, hq⟩ := hu.exists_isQuasiInverse
  have hqF : ContinuousLinearMap.IsFredholm q :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hq.symm
  have hA : ((q ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E).HasNoetherianRange := by
    have h0 : ((q ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E)
        = (q : F →ₗ[𝕜] E) ∘ₗ (u : E →ₗ[𝕜] F) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hq.1
  have hB : ((u ∘L q - 1 : F →L[𝕜] F) : F →ₗ[𝕜] F).HasNoetherianRange := by
    have h0 : ((u ∘L q - 1 : F →L[𝕜] F) : F →ₗ[𝕜] F)
        = (u : E →ₗ[𝕜] F) ∘ₗ (q : F →ₗ[𝕜] E) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hq.2
  have hleft : ((q : F →L[𝕜] E) : F →ₗ[𝕜] E) ∘ₗ ((u + k : E →L[𝕜] F) : E →ₗ[𝕜] F)
      ≈ LinearMap.id := by
    refine equiv_id_of_comp_eq_one_add (k := (q ∘L u - 1) + q ∘L k) ?_ ?_
    · have h0 : (((q ∘L u - 1) + q ∘L k : E →L[𝕜] E) : E →ₗ[𝕜] E)
          = ((q ∘L u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E)
            + (q : F →ₗ[𝕜] E) ∘ₗ (k : E →ₗ[𝕜] F) := rfl
      rw [h0]
      exact hA.add (hk.comp_left _)
    · rw [ContinuousLinearMap.comp_add]
      abel
  have hright : ((u + k : E →L[𝕜] F) : E →ₗ[𝕜] F) ∘ₗ ((q : F →L[𝕜] E) : F →ₗ[𝕜] E)
      ≈ LinearMap.id := by
    refine equiv_id_of_comp_eq_one_add (k := (u ∘L q - 1) + k ∘L q) ?_ ?_
    · have h0 : (((u ∘L q - 1) + k ∘L q : F →L[𝕜] F) : F →ₗ[𝕜] F)
          = ((u ∘L q - 1 : F →L[𝕜] F) : F →ₗ[𝕜] F)
            + (k : E →ₗ[𝕜] F) ∘ₗ (q : F →ₗ[𝕜] E) := rfl
      rw [h0]
      exact hB.add (hk.comp_right _)
    · rw [ContinuousLinearMap.add_comp]
      abel
  have hqi : LinearMap.IsQuasiInverse ((q : F →L[𝕜] E) : F →ₗ[𝕜] E)
      ((u + k : E →L[𝕜] F) : E →ₗ[𝕜] F) := isQuasiInverse_of_left_of_right hleft hright
  have hukF : ContinuousLinearMap.IsFredholm (u + k) :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hqi
  have h1 : fredholmIndex q + fredholmIndex (u + k) = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hqi hqF hukF
  have h2 : fredholmIndex q + fredholmIndex u = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hq hqF hu
  exact ⟨hukF, by omega⟩

end Fredholm

/-! ### Riesz–Schauder: compact perturbations of the identity

Proposition 16.2.7 needs one fact beyond the finite-rank case proved above:
for a compact operator `c` on a Banach space, `1 + c` is Fredholm of index
zero.  This is Riesz–Schauder theory, and it is proved here from Mathlib's
Fredholm alternative (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`)
by a counting argument that avoids both the ascent–descent chains of Riesz and
the adjoint.  Write `T = 1 + c`, `N = ker T`, `R = range T`.

* `N` is finite-dimensional: `c` restricts to `−Id` on `N`, so the identity of
  `N` is a compact operator.
* `N` has a closed complement `M` (Hahn–Banach), and `T` is bounded below on
  `M`: otherwise unit vectors `x_n ∈ M` with `T x_n → 0` would have, after
  extracting a convergent subsequence of `c x_n`, a limit `x ∈ M` of norm one
  with `T x = 0`.  Hence `R = T(M)` is closed.
* `R` has finite codimension.  If not, there is a linear `h : N → E` injective
  modulo `R`; the finite-rank correction `S = T + h ∘ P_N`, with `P_N` the
  projection onto `N` along `M`, is injective, so by the Fredholm alternative it
  is surjective — but its range is `R + h(N)`, which would make `E ⧸ R` a
  quotient of the finite-dimensional `N`.
* The index vanishes because `t ↦ ind(1 + t c)` is locally constant on the
  connected `[0, 1]` and equals `0` at `t = 0` (Theorem 16.2.9).

The scalars are the reals: the only place the field enters is the Hahn–Banach
complement of the finite-dimensional kernel, which Mathlib provides for
polynormable spaces, and Part II works over `ℝ` throughout. -/

section RieszSchauder

open scoped LinearMap.FiniteRangeSetoid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An operator with finite-dimensional range is compact: it factors through a
finite-dimensional, hence locally compact, space. -/
theorem isCompactOperator_of_hasNoetherianRange {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E →L[ℝ] F} (hf : (f : E →ₗ[ℝ] F).HasNoetherianRange) :
    IsCompactOperator f := by
  have : IsNoetherian ℝ (LinearMap.range (f : E →ₗ[ℝ] F)) := hf
  have h1 : IsCompactOperator (f.codRestrict (LinearMap.range (f : E →ₗ[ℝ] F))
      (fun x => LinearMap.mem_range_self _ x)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have h2 := h1.clm_comp (LinearMap.range (f : E →ₗ[ℝ] F)).subtypeL
  exact h2

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- The kernel of `1 + c` is finite-dimensional for `c` compact: on it, `c` is
`−Id`, so the identity of the kernel is a compact operator. -/
theorem finiteDimensional_ker_one_add_of_isCompactOperator {c : E →L[ℝ] E}
    (hc : IsCompactOperator c) :
    FiniteDimensional ℝ (LinearMap.ker ((1 + c : E →L[ℝ] E) : E →ₗ[ℝ] E)) := by
  set N := LinearMap.ker ((1 + c : E →L[ℝ] E) : E →ₗ[ℝ] E) with hN
  have hker : ∀ v ∈ N, v + c v = 0 := fun v hv => by
    have h := LinearMap.mem_ker.mp hv
    change v + c v = 0 at h
    exact h
  have hmem : ∀ v ∈ N, (c : E →ₗ[ℝ] E) v ∈ N := by
    intro v hv
    have h : (c : E →ₗ[ℝ] E) v = -v := by
      rw [ContinuousLinearMap.coe_coe]
      exact eq_neg_of_add_eq_zero_right (hker v hv)
    rw [h]
    exact N.neg_mem hv
  have hcl : IsClosed (N : Set E) := (1 + c).isClosed_ker
  have hres : IsCompactOperator ((c : E →ₗ[ℝ] E).restrict hmem) :=
    IsCompactOperator.restrict (f := (c : E →ₗ[ℝ] E)) hc hmem hcl
  have hid : IsCompactOperator (id : N → N) := by
    have h := hres.neg
    have heq : (-⇑((c : E →ₗ[ℝ] E).restrict hmem)) = (id : N → N) := by
      funext v
      apply Subtype.ext
      simp only [Pi.neg_apply, LinearMap.restrict_apply, Submodule.coe_neg,
        ContinuousLinearMap.coe_coe, id_eq]
      exact neg_eq_of_add_eq_zero_left (hker v v.2)
    rw [heq] at h
    exact h
  exact FiniteDimensional.of_isCompactOperator_id hid

omit [CompleteSpace E] in
/-- The kernel of `1 + c` has a closed complement. -/
theorem exists_isTopCompl_ker_one_add_of_isCompactOperator {c : E →L[ℝ] E}
    (hc : IsCompactOperator c) :
    ∃ M : Submodule ℝ E, Submodule.IsTopCompl (LinearMap.ker ((1 + c : E →L[ℝ] E) : E →ₗ[ℝ] E)) M := by
  have := finiteDimensional_ker_one_add_of_isCompactOperator hc
  exact (Submodule.ClosedComplemented.of_finiteDimensional _).exists_isTopCompl

omit [CompleteSpace E] in
/-- `1 + c` is bounded below on a closed complement of its kernel. -/
theorem exists_norm_le_of_isTopCompl_ker_one_add {c : E →L[ℝ] E} (hc : IsCompactOperator c)
    {M : Submodule ℝ E}
    (hM : Submodule.IsTopCompl (LinearMap.ker ((1 + c : E →L[ℝ] E) : E →ₗ[ℝ] E)) M) :
    ∃ K : NNReal, ∀ x ∈ M, ‖x‖ ≤ K * ‖(1 + c) x‖ := by
  set T : E →L[ℝ] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[ℝ] E) with hN
  have hMc : IsClosed (M : Set E) := hM.isClosed'
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ x ∈ M, ((n : ℝ) + 1) * ‖T x‖ < ‖x‖ := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨((n + 1 : ℕ) : NNReal), fun x hx => ?_⟩
    by_contra hlt
    apply hn
    refine ⟨x, hx, ?_⟩
    rw [not_le, NNReal.coe_natCast, Nat.cast_add_one] at hlt
    exact hlt
  choose x hxM hx using hseq
  have hx0 : ∀ n, x n ≠ 0 := fun n h => by
    have := hx n
    rw [h, norm_zero] at this
    have : (0:ℝ) ≤ ((n : ℝ) + 1) * ‖T 0‖ := by positivity
    linarith
  set y : ℕ → E := fun n => ‖x n‖⁻¹ • x n with hy
  have hy1 : ∀ n, ‖y n‖ = 1 := fun n => norm_smul_inv_norm (hx0 n)
  have hyM : ∀ n, y n ∈ M := fun n => M.smul_mem _ (hxM n)
  have hTy : ∀ n, ‖T (y n)‖ ≤ 1 / ((n : ℝ) + 1) := fun n => by
    have hpos : 0 < ‖x n‖ := norm_pos_iff.mpr (hx0 n)
    have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hy, map_smul, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_le_iff₀ hpos, mul_one_div, le_div_iff₀ hn1]
    linarith [hx n]
  have hT0 : Tendsto (fun n => T (y n)) atTop (𝓝 0) :=
    squeeze_zero_norm hTy tendsto_one_div_add_atTop_nhds_zero_nat
  have hK : IsCompact (closure (c '' Metric.closedBall 0 1)) :=
    hc.isCompact_closure_image_closedBall 1
  have hmem : ∀ n, c (y n) ∈ closure (c '' Metric.closedBall 0 1) := fun n =>
    subset_closure (Set.mem_image_of_mem c (mem_closedBall_zero_iff.mpr (hy1 n).le))
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝 (0 - a)) := by
    have h := (hT0.comp hφ.tendsto_atTop).sub hlim
    refine h.congr fun n => ?_
    change y (φ n) + c (y (φ n)) - c (y (φ n)) = y (φ n)
    exact add_sub_cancel_right _ _
  have haM : 0 - a ∈ M := hMc.mem_of_tendsto hyφ (Filter.Eventually.of_forall fun n => hyM (φ n))
  have hanorm : ‖0 - a‖ = 1 := by
    have h1 : Tendsto (fun n => ‖y (φ n)‖) atTop (𝓝 ‖0 - a‖) := hyφ.norm
    have h2 : Tendsto (fun n => ‖y (φ n)‖) atTop (𝓝 1) := by
      simp only [hy1]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have haN : 0 - a ∈ N := by
    have h1 : Tendsto (fun n => T (y (φ n))) atTop (𝓝 (T (0 - a))) :=
      (T.continuous.tendsto _).comp hyφ
    have h2 : Tendsto (fun n => T (y (φ n))) atTop (𝓝 0) := hT0.comp hφ.tendsto_atTop
    exact LinearMap.mem_ker.mpr (tendsto_nhds_unique h1 h2)
  have hzero : 0 - a = 0 := Submodule.disjoint_def.mp hM.isCompl.disjoint _ haN haM
  rw [hzero, norm_zero] at hanorm
  exact zero_ne_one hanorm

/-- The range of `1 + c` is closed: it is the image of a closed complement of
the kernel, on which `1 + c` is bounded below. -/
theorem isClosed_range_one_add_of_isCompactOperator {c : E →L[ℝ] E}
    (hc : IsCompactOperator c) :
    IsClosed ((LinearMap.range ((1 + c : E →L[ℝ] E) : E →ₗ[ℝ] E) : Submodule ℝ E) : Set E) := by
  obtain ⟨M, hM⟩ := exists_isTopCompl_ker_one_add_of_isCompactOperator hc
  obtain ⟨K, hK⟩ := exists_norm_le_of_isTopCompl_ker_one_add hc hM
  set T : E →L[ℝ] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[ℝ] E) with hN
  have hMc : IsClosed (M : Set E) := hM.isClosed'
  have : CompleteSpace M := hMc.completeSpace_coe
  have hanti : AntilipschitzWith K (T ∘L M.subtypeL) :=
    (T ∘L M.subtypeL).antilipschitz_of_bound fun x => hK x x.2
  have hcl : IsClosed (Set.range (T ∘L M.subtypeL)) :=
    hanti.isClosed_range (T ∘L M.subtypeL).uniformContinuous
  have heq : ((LinearMap.range (T : E →ₗ[ℝ] E) : Submodule ℝ E) : Set E)
      = Set.range (T ∘L M.subtypeL) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hw : w ∈ N ⊔ M := by rw [hM.isCompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨n, hn, m, hm, rfl⟩ := Submodule.mem_sup.mp hw
      refine ⟨⟨m, hm⟩, ?_⟩
      have hTn : T n = 0 := LinearMap.mem_ker.mp hn
      change T m = T (n + m)
      rw [map_add, hTn, zero_add]
    · rintro ⟨⟨m, hm⟩, rfl⟩
      exact ⟨m, rfl⟩
  rw [heq]
  exact hcl

/-- The cokernel of `1 + c` is finite-dimensional.  This is where the Fredholm
alternative enters: an injective finite-rank correction of `1 + c` would be
surjective, so its range `R + h(N)` would be all of `E`, making `E ⧸ R` a
quotient of the finite-dimensional kernel `N`; such a correction exists as soon
as `E ⧸ R` is infinite-dimensional. -/
theorem finiteDimensional_coker_one_add_of_isCompactOperator {c : E →L[ℝ] E}
    (hc : IsCompactOperator c) :
    FiniteDimensional ℝ (E ⧸ LinearMap.range ((1 + c : E →L[ℝ] E) : E →ₗ[ℝ] E)) := by
  set T : E →L[ℝ] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[ℝ] E) with hN
  set R := LinearMap.range (T : E →ₗ[ℝ] E) with hR
  have hNfin : FiniteDimensional ℝ N := finiteDimensional_ker_one_add_of_isCompactOperator hc
  obtain ⟨M, hM⟩ := exists_isTopCompl_ker_one_add_of_isCompactOperator hc
  have hdecomp : ∀ w : E, ∃ n ∈ N, ∃ m ∈ M, n + m = w := fun w => by
    have hw : w ∈ N ⊔ M := by rw [hM.isCompl.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp hw
  by_contra hinf
  -- an injective map `N → E ⧸ R`, lifted to `E`
  obtain ⟨h, hh⟩ : ∃ h : N →ₗ[ℝ] E, Function.Injective (R.mkQ ∘ₗ h) := by
    have hrank : (Module.finrank ℝ N : Cardinal) ≤ Module.rank ℝ (E ⧸ R) := by
      have h1 : ¬ Module.rank ℝ (E ⧸ R) < Cardinal.aleph0 := fun h =>
        hinf (Module.rank_lt_aleph0_iff.mp h)
      exact Cardinal.natCast_lt_aleph0.le.trans (not_lt.mp h1)
    obtain ⟨s, hs, hsli⟩ := le_rank_iff_exists_linearIndependent_finset.mp hrank
    have hcard : Cardinal.mk {x // x ∈ (↑s : Set (E ⧸ R))} = s.card := Cardinal.mk_coe_finset
    obtain ⟨j, hj⟩ := Module.Free.exists_linearMap_injective_of_linearIndependent_of_rank_le
      (M := N) hsli (le_of_eq (by rw [hcard, hs, Module.finrank_eq_rank]))
    obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective R.mkQ R.range_mkQ
    refine ⟨g ∘ₗ j, ?_⟩
    rw [← LinearMap.comp_assoc, hg, LinearMap.id_comp]
    exact hj
  -- the projection onto `N` along `M`, and the corrected operator `S = T + h ∘ P`
  set P : E →L[ℝ] N := N.projectionOntoL M hM with hP
  set hL : N →L[ℝ] E := LinearMap.toContinuousLinearMap h with hhL
  set S : E →L[ℝ] E := T + hL ∘L P with hS
  have hPn : ∀ n (hn : n ∈ N), P n = ⟨n, hn⟩ := fun n hn =>
    N.projectionOntoL_apply_left hM ⟨n, hn⟩
  have hPm : ∀ m ∈ M, P m = 0 := fun m hm => N.projectionOntoL_apply_right hM ⟨m, hm⟩
  have hSapply : ∀ n (hn : n ∈ N), ∀ m ∈ M, S (n + m) = T m + h ⟨n, hn⟩ := by
    intro n hn m hm
    have hTn : T n = 0 := LinearMap.mem_ker.mp hn
    change T (n + m) + hL (P (n + m)) = T m + h ⟨n, hn⟩
    rw [map_add, map_add, hPn n hn, hPm m hm, add_zero, hTn, zero_add]
    rfl
  have hmkQ_T : ∀ m, R.mkQ (T m) = 0 := fun m =>
    (Submodule.Quotient.mk_eq_zero R).mpr (LinearMap.mem_range_self (T : E →ₗ[ℝ] E) m)
  -- `S` is injective
  have hSinj : Function.Injective S := by
    refine (injective_iff_map_eq_zero S).mpr fun w hw => ?_
    obtain ⟨n, hn, m, hm, rfl⟩ := hdecomp w
    rw [hSapply n hn m hm] at hw
    have h1 : (R.mkQ ∘ₗ h) ⟨n, hn⟩ = 0 := by
      have := congrArg R.mkQ hw
      rw [map_add, hmkQ_T, zero_add, map_zero] at this
      exact this
    have hn0 : (⟨n, hn⟩ : N) = 0 := hh (by rw [h1, map_zero])
    have hn0' : n = 0 := congrArg Subtype.val hn0
    rw [hn0, map_zero, add_zero] at hw
    have hmN : m ∈ N := LinearMap.mem_ker.mpr hw
    have hm0 : m = 0 := Submodule.disjoint_def.mp hM.isCompl.disjoint _ hmN hm
    rw [hn0', hm0, add_zero]
  -- `S = 1 + c''` with `c''` compact
  have hc'' : IsCompactOperator (c + hL ∘L P : E →L[ℝ] E) := by
    have hPc : IsCompactOperator P := isCompactOperator_of_locallyCompactSpace_dom P
    exact hc.add (hPc.clm_comp hL)
  have hSeq : S = 1 + (c + hL ∘L P) := by rw [hS, hT, add_assoc]
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (T := -(c + hL ∘L P)) (μ := 1)
      hc''.neg one_ne_zero with heig | hres
  · exfalso
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have h1 : -((c + hL ∘L P) v) = v := by
      have := hv.apply_eq_smul
      rwa [one_smul] at this
    have h2 : S v = 0 := by
      have h1' : (c + hL ∘L P) v = -v := neg_eq_iff_eq_neg.mp h1
      rw [hSeq]
      change v + (c + hL ∘L P) v = 0
      rw [h1', add_neg_cancel]
    exact hv.2 (hSinj (by rw [h2, map_zero]))
  · rw [spectrum.mem_resolventSet_iff, map_one, sub_neg_eq_add, ← hSeq] at hres
    obtain ⟨w, hw⟩ := hres.exists_right_inv
    have hsurj : Function.Surjective S := fun z => ⟨w z, by
      have := ContinuousLinearMap.ext_iff.mp hw z
      change S (w z) = z at this
      exact this⟩
    have hsurj' : Function.Surjective (R.mkQ ∘ₗ h) := by
      intro q
      obtain ⟨z, rfl⟩ := R.mkQ_surjective q
      obtain ⟨w', rfl⟩ := hsurj z
      obtain ⟨n, hn, m, hm, rfl⟩ := hdecomp w'
      refine ⟨⟨n, hn⟩, ?_⟩
      rw [hSapply n hn m hm, map_add, hmkQ_T, zero_add]
      rfl
    exact hinf (Module.Finite.of_surjective (R.mkQ ∘ₗ h) hsurj')

/-- **Riesz–Schauder.**  For a compact operator `c` on a Banach space, `1 + c`
is Fredholm. -/
theorem isFredholm_one_add_of_isCompactOperator {c : E →L[ℝ] E} (hc : IsCompactOperator c) :
    ContinuousLinearMap.IsFredholm (1 + c) := by
  set T : E →L[ℝ] E := 1 + c with hT
  set N := LinearMap.ker (T : E →ₗ[ℝ] E) with hN
  set R := LinearMap.range (T : E →ₗ[ℝ] E) with hR
  have hNfin : FiniteDimensional ℝ N := finiteDimensional_ker_one_add_of_isCompactOperator hc
  have hRcofg : R.CoFG := finiteDimensional_coker_one_add_of_isCompactOperator hc
  obtain ⟨M, hM⟩ := exists_isTopCompl_ker_one_add_of_isCompactOperator hc
  have hMc : IsClosed (M : Set E) := hM.isClosed'
  have hRc : IsClosed (R : Set E) := isClosed_range_one_add_of_isCompactOperator hc
  have hMcofg : M.CoFG :=
    Module.Finite.equiv (Submodule.quotientEquivOfIsCompl M N hM.isCompl.symm).symm
  have hmaps : Set.MapsTo T M R := fun w _ => LinearMap.mem_range_self (T : E →ₗ[ℝ] E) w
  have : CompleteSpace M := hMc.completeSpace_coe
  have hdecomp : ∀ w : E, ∃ n ∈ N, ∃ m ∈ M, n + m = w := fun w => by
    have hw : w ∈ N ⊔ M := by rw [hM.isCompl.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp hw
  have hinj : (T.restrict hmaps).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h1 : T (x : E) = T (y : E) := congrArg Subtype.val hxy
    have h2 : (x : E) - y ∈ N := LinearMap.mem_ker.mpr (by
      change T ((x : E) - y) = 0
      rw [map_sub, h1, sub_self])
    have h3 : (x : E) - y ∈ M := M.sub_mem x.2 y.2
    exact Subtype.ext (sub_eq_zero.mp (Submodule.disjoint_def.mp hM.isCompl.disjoint _ h2 h3))
  have hsurj : (T.restrict hmaps).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨z, w, rfl⟩
    obtain ⟨n, hn, m, hm, rfl⟩ := hdecomp w
    refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
    have hTn : T n = 0 := LinearMap.mem_ker.mp hn
    show T m = T (n + m)
    rw [map_add, hTn, zero_add]
  exact ContinuousLinearMap.IsFredholm.of_isInvertible_restrict hMc hRc hmaps
    ⟨ContinuousLinearEquiv.ofBijective (T.restrict hmaps) hinj hsurj,
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- **Riesz–Schauder**, the index.  `ind (1 + c) = 0` for `c` compact: the
index of `1 + t c` is locally constant in `t` (Theorem 16.2.9), hence constant
on the connected `ℝ`, and it vanishes at `t = 0`. -/
theorem fredholmIndex_one_add_of_isCompactOperator {c : E →L[ℝ] E} (hc : IsCompactOperator c) :
    fredholmIndex (1 + c) = 0 := by
  have hF : ∀ t : ℝ, ContinuousLinearMap.IsFredholm (1 + t • c) := fun t =>
    isFredholm_one_add_of_isCompactOperator (hc.smul t)
  have hpath : Continuous fun t : ℝ => (1 + t • c : E →L[ℝ] E) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hcont : Continuous fun t : ℝ => fredholmIndex (1 + t • c) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev := (hpath.continuousAt (x := t)).eventually (fredholmIndex_locally_constant (hF t))
    rw [ContinuousAt, nhds_discrete ℤ, Filter.tendsto_pure]
    exact hev.mono fun s hs => hs.2
  have h01 : fredholmIndex (1 + (0:ℝ) • c) = fredholmIndex (1 + (1:ℝ) • c) :=
    PreconnectedSpace.constant inferInstance hcont
  rw [zero_smul, add_zero, one_smul] at h01
  rw [← h01]
  exact fredholmIndex_eq_zero_of_bijective ⟨fun x y h => h, fun y => ⟨y, rfl⟩⟩

/-- **Proposition 16.2.7 (compact perturbations).**  Adding a compact operator
changes neither the Fredholm property nor the index.

Chapter 8 uses this to pass from the linearised Floer operator to its
constant-coefficient model, whose index is computable.

The proof is the finite-rank argument of
`isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange` with Riesz–Schauder
in place of the finite-rank lemma: for a quasi-inverse `q` of `u`,
`q(u + k) = 1 + [(qu − 1) + qk]` and `(u + k)q = 1 + [(uq − 1) + kq]` are
compact perturbations of the identity, hence Fredholm of index `0`
(`isFredholm_one_add_of_isCompactOperator`,
`fredholmIndex_one_add_of_isCompactOperator`).  Their quasi-inverses `p₁`, `p₂`
give the left quasi-inverse `p₁ q` and the right quasi-inverse `q p₂` of
`u + k`, so `u + k` is Fredholm, and additivity
(`ind q + ind (u + k) = ind (q(u + k)) = 0 = ind q + ind u`) gives the index.

Stated over `ℝ`, where Part II works: see the section header for where the
field enters. -/
theorem fredholmIndex_add_compact {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {u : E →L[ℝ] F} {k : E →L[ℝ] F}
    (hu : ContinuousLinearMap.IsFredholm u) (hk : IsCompactOperator k) :
    ContinuousLinearMap.IsFredholm (u + k) ∧ fredholmIndex (u + k) = fredholmIndex u := by
  obtain ⟨q, hq⟩ := hu.exists_isQuasiInverse
  have hqF : ContinuousLinearMap.IsFredholm q :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hq.symm
  have hA : ((q ∘L u - 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).HasNoetherianRange := by
    have h0 : ((q ∘L u - 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = (q : F →ₗ[ℝ] E) ∘ₗ (u : E →ₗ[ℝ] F) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hq.1
  have hB : ((u ∘L q - 1 : F →L[ℝ] F) : F →ₗ[ℝ] F).HasNoetherianRange := by
    have h0 : ((u ∘L q - 1 : F →L[ℝ] F) : F →ₗ[ℝ] F)
        = (u : E →ₗ[ℝ] F) ∘ₗ (q : F →ₗ[ℝ] E) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hq.2
  have hc₁ : IsCompactOperator ((q ∘L u - 1) + q ∘L k : E →L[ℝ] E) :=
    (isCompactOperator_of_hasNoetherianRange hA).add (hk.clm_comp q)
  have hc₂ : IsCompactOperator ((u ∘L q - 1) + k ∘L q : F →L[ℝ] F) :=
    (isCompactOperator_of_hasNoetherianRange hB).add (hk.comp_clm q)
  have e₁ : q ∘L (u + k) = 1 + ((q ∘L u - 1) + q ∘L k) := by
    rw [ContinuousLinearMap.comp_add]; abel
  have e₂ : (u + k) ∘L q = 1 + ((u ∘L q - 1) + k ∘L q) := by
    rw [ContinuousLinearMap.add_comp]; abel
  have hqaF : ContinuousLinearMap.IsFredholm (q ∘L (u + k)) := by
    rw [e₁]; exact isFredholm_one_add_of_isCompactOperator hc₁
  have haqF : ContinuousLinearMap.IsFredholm ((u + k) ∘L q) := by
    rw [e₂]; exact isFredholm_one_add_of_isCompactOperator hc₂
  have hqa0 : fredholmIndex (q ∘L (u + k)) = 0 := by
    rw [e₁]; exact fredholmIndex_one_add_of_isCompactOperator hc₁
  obtain ⟨p₁, hp₁⟩ := hqaF.exists_isQuasiInverse
  obtain ⟨p₂, hp₂⟩ := haqF.exists_isQuasiInverse
  have hleft : (((p₁ ∘L q) : F →L[ℝ] E) : F →ₗ[ℝ] E) ∘ₗ ((u + k : E →L[ℝ] F) : E →ₗ[ℝ] F)
      ≈ LinearMap.id := hp₁.1
  have hright : ((u + k : E →L[ℝ] F) : E →ₗ[ℝ] F) ∘ₗ (((q ∘L p₂) : F →L[ℝ] E) : F →ₗ[ℝ] E)
      ≈ LinearMap.id := hp₂.2
  have hqi := isQuasiInverse_of_left_of_right hleft hright
  have haF : ContinuousLinearMap.IsFredholm (u + k) :=
    ContinuousLinearMap.IsFredholm.of_isQuasiInverse hqi
  have h2 := (fredholmIndex_comp haF hqF).2
  have h3 := fredholmIndex_add_eq_zero_of_isQuasiInverse hq hqF hu
  exact ⟨haF, by omega⟩

end RieszSchauder

end Chapter16
end MorseFloer
