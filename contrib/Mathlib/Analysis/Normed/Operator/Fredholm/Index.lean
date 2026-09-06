/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The index of a Fredholm operator

Mathlib knows what a Fredholm operator is (`ContinuousLinearMap.IsFredholm`), and has Fredholm
decompositions and quasi-inverses, but it has no notion of *index*.  This file defines the index
of a continuous linear map and proves the two basic stability properties of the index of a
Fredholm operator: additivity under composition, and local constancy.

This file is meant to sit beside `Mathlib/Analysis/Normed/Operator/Fredholm/Basic.lean`, as
`Mathlib/Analysis/Normed/Operator/Fredholm/Index.lean`.

## Main definitions

* `ContinuousLinearMap.fredholmIndex u`: the integer `dim (ker u) - dim (coker u)`.

## Main results

* `ContinuousLinearMap.fredholmIndex_of_finiteDimensional`: between finite-dimensional spaces the
  index is `dim E - dim F`, whatever the operator is.
* `ContinuousLinearMap.fredholmIndex_eq_of_fredholmPackage`: the index read off a
  `ContinuousLinearMap.FredholmPackage`, as `dim E₀ - dim F₀`.
* `ContinuousLinearMap.fredholmIndex_comp`: the composition of two Fredholm operators is Fredholm,
  with index the sum of the indices.
* `ContinuousLinearMap.fredholmIndex_locally_constant`: the Fredholm operators form an open set, on
  which the index is locally constant.
* `ContinuousLinearMap.isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange`: adding an
  operator with finite-dimensional range changes neither the Fredholm property nor the index.
* `LinearMap.finrank_ker_sub_finrank_coker_comp`: the purely algebraic identity behind additivity,
  that `dim (ker ·) - dim (coker ·)` is additive under composition of linear maps.

## Design notes

The index is defined for an arbitrary continuous linear map, as the difference of two `finrank`s,
each of which is `0` when the space in question is infinite dimensional.  It therefore carries its
intended meaning exactly when the map is Fredholm, and only then; this is the same convention that
makes `Module.finrank` itself total.  The gain is that the index needs no hypothesis to be written
down, so `IsFredholm` enters only where it is genuinely used.

Additivity is proved through four applications of rank–nullity rather than through the six-term
exact sequence
`0 → ker a → ker (b ∘ a) → ker b → coker a → coker (b ∘ a) → coker b → 0`.
The four maps used are listed in the docstring of `LinearMap.finrank_ker_sub_finrank_coker_comp`.
The exact sequence is the more memorable argument, but turning it into an alternating-sum identity
needs exactness at six places and an induction on the length of the sequence, whereas the four
rank–nullity counts need nothing beyond `LinearMap.finrank_range_add_finrank_ker`,
`Submodule.liftQ` and `Submodule.comapSubtypeEquivOfLe`.

The first section of the file is pure linear algebra over a division ring, with no topology, and
lives in `namespace LinearMap`; if a reviewer prefers, `finrank_ker_sub_finrank_coker_comp` and
`finrank_ker_eq_finrank_coker_one_add` can be split out into
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`, beside
`LinearMap.finrank_range_add_finrank_ker`, and `isQuasiInverse_of_left_of_right` into
`Mathlib.Algebra.Module.LinearMap.FiniteRange`, beside `LinearMap.IsQuasiInverse.comp`.

The stability theorems assume `𝕜` complete, because every entry point into the existing Fredholm
API does: over an incomplete field a finite-dimensional subspace of a normed space need not be
complemented, and `IsFredholm` demands a complemented kernel.  The definition of the index and its
elementary computations need no such hypothesis.

Two natural results are left for follow-up work.

* **Compact perturbations.** That `u + k` is Fredholm of the same index as `u` for `k` compact is
  not proved here.  The finite-rank case *is*, as
  `ContinuousLinearMap.isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange`: if `q` is a
  quasi-inverse of `u` then `q (u + k) = 1 + (q u - 1) + q k`, and when `k` has finite rank so does
  the whole error term.  For `k` merely compact this breaks down, since `q k` need not be a limit
  of finite-rank operators in a general Banach space; what is needed instead is Riesz–Schauder,
  that `1 + c` is Fredholm of index `0` for `c` compact, which Mathlib's Riesz theory does not
  currently provide in that form.
* **The index of a direct sum**, `fredholmIndex (u.prodMap v) = fredholmIndex u + fredholmIndex v`.
  Its proof needs the two isomorphisms `↥(p.prod q) ≃ₗ ↥p × ↥q` and
  `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`, which Mathlib does not have; they belong in
  `Mathlib.LinearAlgebra.Prod`, not here, so this is deferred to a follow-up.
-/

open Filter Topology
open scoped LinearMap.FiniteRangeSetoid

namespace LinearMap

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-- **The index identity for a composite, as pure linear algebra.**  For linear maps
`a : V → V₂` and `b : V₂ → V₃` whose relevant kernels and cokernels are finite dimensional,

`dim ker (b ∘ a) - dim coker (b ∘ a) = (dim ker b - dim coker b) + (dim ker a - dim coker a)`.

For continuous linear maps between Banach spaces this is the additivity of the Fredholm index,
`ContinuousLinearMap.fredholmIndex_comp`, but nothing here is topological.

The proof is four applications of rank–nullity, to the four maps

* `a` restricted to `ker (b ∘ a)`, whose image is `ker b ⊓ range a` and whose kernel is `ker a`;
* the projection `V₂ → V₂ ⧸ range a` restricted to `ker b`, whose image is
  `S := (ker b + range a) / range a` and whose kernel is `ker b ⊓ range a`;
* the map `V₂ ⧸ range a → V₃ ⧸ range (b ∘ a)` induced by `b`, whose image is
  `T := (range b + range (b ∘ a)) / range (b ∘ a)` and whose kernel is `S`;
* the projection `V₃ ⧸ range (b ∘ a) → V₃ ⧸ range b`, which is onto with kernel `T`.

Writing the four identities down and eliminating `dim (ker b ⊓ range a)`, `dim S` and `dim T`
gives the result. -/
theorem finrank_ker_sub_finrank_coker_comp {V V₂ V₃ : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (a : V →ₗ[K] V₂) (b : V₂ →ₗ[K] V₃)
    [FiniteDimensional K (LinearMap.ker (b ∘ₗ a))] [FiniteDimensional K (LinearMap.ker b)]
    [FiniteDimensional K (V₂ ⧸ LinearMap.range a)]
    [FiniteDimensional K (V₃ ⧸ LinearMap.range (b ∘ₗ a))] :
    (Module.finrank K (LinearMap.ker (b ∘ₗ a)) : ℤ)
        - (Module.finrank K (V₃ ⧸ LinearMap.range (b ∘ₗ a)) : ℤ)
      = ((Module.finrank K (LinearMap.ker b) : ℤ)
          - (Module.finrank K (V₃ ⧸ LinearMap.range b) : ℤ))
        + ((Module.finrank K (LinearMap.ker a) : ℤ)
          - (Module.finrank K (V₂ ⧸ LinearMap.range a) : ℤ)) := by
  -- `ker a ≤ ker (b ∘ a)`
  have hle : LinearMap.ker a ≤ LinearMap.ker (b ∘ₗ a) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    rw [hx, map_zero]
  -- (1) `dim ker (b ∘ a) = dim (ker b ⊓ range a) + dim ker a`
  have h1 : Module.finrank K (LinearMap.ker (b ∘ₗ a))
      = Module.finrank K ↥(LinearMap.ker b ⊓ LinearMap.range a)
        + Module.finrank K (LinearMap.ker a) := by
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
  have h2 : Module.finrank K (LinearMap.ker b)
      = Module.finrank K ↥(Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b))
        + Module.finrank K ↥(LinearMap.ker b ⊓ LinearMap.range a) := by
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
  -- (3) `dim (V₂ ⧸ range a) = dim T + dim S`
  have hle3 : LinearMap.range a
      ≤ LinearMap.ker ((LinearMap.range (b ∘ₗ a)).mkQ ∘ₗ b) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  have h3 : Module.finrank K (V₂ ⧸ LinearMap.range a)
      = Module.finrank K ↥(Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ (LinearMap.range b))
        + Module.finrank K ↥(Submodule.map (LinearMap.range a).mkQ (LinearMap.ker b)) := by
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
  -- (4) `dim (V₃ ⧸ range (b ∘ a)) = dim (V₃ ⧸ range b) + dim T`
  have hle4 : LinearMap.range (b ∘ₗ a) ≤ LinearMap.ker (LinearMap.range b).mkQ := by
    rw [Submodule.ker_mkQ]
    exact LinearMap.range_comp_le_range a b
  have h4 : Module.finrank K (V₃ ⧸ LinearMap.range (b ∘ₗ a))
      = Module.finrank K (V₃ ⧸ LinearMap.range b)
        + Module.finrank K ↥(Submodule.map (LinearMap.range (b ∘ₗ a)).mkQ
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

/-- **A finite-rank perturbation of the identity has as much kernel as cokernel.**

With `W := range n`, one checks that `W` is `(1 + n)`-invariant, that `ker (1 + n) ≤ W`, that
`range (1 + n) + W` is everything, and that `(1 + n) W = W ⊓ range (1 + n)`.  Rank–nullity applied
to `(1 + n)|_W` and to the projection `W → V ⧸ range (1 + n)` then gives the two identities

`dim W = dim (W ⊓ range (1 + n)) + dim ker (1 + n)`,
`dim W = dim (V ⧸ range (1 + n)) + dim (W ⊓ range (1 + n))`,

whose difference is the claim.  In the normed setting this is
`ContinuousLinearMap.fredholmIndex_eq_zero_of_one_add`. -/
theorem finrank_ker_eq_finrank_coker_one_add {V : Type*} [AddCommGroup V] [Module K V]
    (n : V →ₗ[K] V) [FiniteDimensional K ↥(LinearMap.range n)] :
    Module.finrank K (LinearMap.ker (LinearMap.id + n))
      = Module.finrank K (V ⧸ LinearMap.range (LinearMap.id + n)) := by
  have hkerW : LinearMap.ker (LinearMap.id + n) ≤ LinearMap.range n := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at hx
    have hnx : n x = -x := eq_neg_of_add_eq_zero_right hx
    exact ⟨-x, by rw [map_neg, hnx, neg_neg]⟩
  have hsup : LinearMap.range (LinearMap.id + n) ⊔ LinearMap.range n = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = (LinearMap.id + n : V →ₗ[K] V) x + n (-x) := by
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
        have hxe : x = (LinearMap.id + n : V →ₗ[K] V) x - n x := by
          simp only [LinearMap.add_apply, LinearMap.id_apply]
          abel
        rw [hxe]
        exact Submodule.sub_mem _ hzW ⟨x, rfl⟩
      exact ⟨x, hx, rfl⟩
  have h1 : Module.finrank K ↥(LinearMap.range n)
      = Module.finrank K ↥(LinearMap.range n ⊓ LinearMap.range (LinearMap.id + n))
        + Module.finrank K (LinearMap.ker (LinearMap.id + n)) := by
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
  have h2 : Module.finrank K ↥(LinearMap.range n)
      = Module.finrank K (V ⧸ LinearMap.range (LinearMap.id + n))
        + Module.finrank K ↥(LinearMap.range n ⊓ LinearMap.range (LinearMap.id + n)) := by
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

end DivisionRing

section CommRing

variable {K : Type*} [CommRing K]

/-- A left quasi-inverse and a right quasi-inverse of the same map are quasi-inverses of it, and
of each other.  Here `≈` is equality modulo linear maps with noetherian (over a field:
finite-dimensional) range, and the proof is the usual `p ≈ p (m q) = (p m) q ≈ q`. -/
theorem isQuasiInverse_of_left_of_right {V V₂ : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup V₂] [Module K V₂] {m : V →ₗ[K] V₂} {p q : V₂ →ₗ[K] V}
    (hp : p ∘ₗ m ≈ LinearMap.id) (hq : m ∘ₗ q ≈ LinearMap.id) :
    LinearMap.IsQuasiInverse p m := by
  have hpq : p ≈ q :=
    calc p = p ∘ₗ LinearMap.id := (LinearMap.comp_id p).symm
      _ ≈ p ∘ₗ (m ∘ₗ q) := Setoid.symm (LinearMap.FiniteRangeSetoid.equiv_comp_left hq)
      _ = (p ∘ₗ m) ∘ₗ q := rfl
      _ ≈ LinearMap.id ∘ₗ q := LinearMap.FiniteRangeSetoid.equiv_comp_right hp
      _ = q := LinearMap.id_comp q
  exact ⟨hp, Setoid.trans (LinearMap.FiniteRangeSetoid.equiv_comp_left hpq) hq⟩

end CommRing

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The index of a continuous linear map**: `dim ker u - dim coker u`, as an integer.

The definition makes sense for any continuous linear map, both dimensions being read as `0` when
the space in question is infinite dimensional; it carries its intended meaning exactly when `u` is
a Fredholm operator, so that both dimensions are genuinely finite. -/
noncomputable def fredholmIndex (u : E →L[𝕜] F) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) : ℤ)
    - (Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) : ℤ)

/-- **In finite dimensions the index depends only on the two spaces**: `ind u = dim E - dim F`,
whatever `u` is.  This is rank–nullity together with the dimension of a quotient, and it is the
first sign that the index is a deformation invariant. -/
theorem fredholmIndex_of_finiteDimensional [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (u : E →L[𝕜] F) :
    fredholmIndex u = (Module.finrank 𝕜 E : ℤ) - (Module.finrank 𝕜 F : ℤ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := 𝕜) (V := E) (V₂ := F) (u : E →ₗ[𝕜] F)
  have h2 := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (u : E →ₗ[𝕜] F))
  rw [fredholmIndex]
  omega

/-- A surjective operator has vanishing cokernel. -/
theorem finrank_coker_eq_zero_of_surjective {u : E →L[𝕜] F} (hu : Function.Surjective u) :
    Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) = 0 := by
  have hr : LinearMap.range (u : E →ₗ[𝕜] F) = ⊤ := LinearMap.range_eq_top.mpr hu
  have : Subsingleton (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) :=
    Submodule.Quotient.subsingleton_iff.mpr hr
  exact Module.finrank_zero_of_subsingleton

/-- **The index of a surjective operator is the dimension of its kernel.**  For a Fredholm operator
this is the form in which the index is usually read off: when `u` is onto, its kernel is
finite dimensional of dimension exactly the index. -/
theorem fredholmIndex_eq_finrank_ker_of_surjective {u : E →L[𝕜] F}
    (hu : Function.Surjective u) :
    fredholmIndex u = (Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) : ℤ) := by
  have h := finrank_coker_eq_zero_of_surjective hu
  simp [fredholmIndex, h]

/-- Dually, an injective operator has index `-dim coker`. -/
theorem fredholmIndex_eq_neg_finrank_coker_of_injective {u : E →L[𝕜] F}
    (hu : Function.Injective u) :
    fredholmIndex u
      = -(Module.finrank 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) : ℤ) := by
  have hk : LinearMap.ker (u : E →ₗ[𝕜] F) = ⊥ := LinearMap.ker_eq_bot.mpr hu
  have h0 : Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) = 0 := by
    rw [hk, finrank_bot]
  simp [fredholmIndex, h0]

/-- **A bijective operator has index zero**: its kernel and its cokernel both vanish. -/
theorem fredholmIndex_eq_zero_of_bijective {u : E →L[𝕜] F} (hu : Function.Bijective u) :
    fredholmIndex u = 0 := by
  have h1 : Module.finrank 𝕜 (LinearMap.ker (u : E →ₗ[𝕜] F)) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hu.1, finrank_bot]
  rw [fredholmIndex, h1, finrank_coker_eq_zero_of_surjective hu.2]
  omega

/-- **The index read off a Fredholm package.**

A `ContinuousLinearMap.FredholmPackage` for `u` is a pair of topological decompositions
`E = E₁ ⊕ E₀` and `F = F₁ ⊕ F₀`, with `E₀` and `F₀` finite dimensional, in which `u` kills `E₀` and
restricts to an isomorphism `E₁ ≃L F₁`.  In such a decomposition `ker u = E₀` and `range u = F₁`,
so the cokernel is `F₀` and the index is `dim E₀ - dim F₀`.

This is the bridge between `fredholmIndex`, which is about a kernel and a quotient, and the
decompositions that are often easier to manipulate.  Obtain a package for a Fredholm operator from
`ContinuousLinearMap.IsFredholm.nonempty_fredholmPackage`, or build one by hand when the
decomposition is known. -/
theorem fredholmIndex_eq_of_fredholmPackage {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
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

/-- **A finite-rank perturbation of the identity has index zero.**  This is the elementary case of
the invariance of the index under compact perturbations, and the case that the local constancy of
the index needs. -/
theorem fredholmIndex_eq_zero_of_one_add {N : E →L[𝕜] E}
    (hN : ((N : E →ₗ[𝕜] E)).HasNoetherianRange) : fredholmIndex (1 + N) = 0 := by
  have : IsNoetherian 𝕜 ↥(LinearMap.range (N : E →ₗ[𝕜] E)) := hN
  have h : ((1 + N : E →L[𝕜] E) : E →ₗ[𝕜] E) = LinearMap.id + (N : E →ₗ[𝕜] E) := rfl
  rw [fredholmIndex, h, LinearMap.finrank_ker_eq_finrank_coker_one_add (N : E →ₗ[𝕜] E)]
  omega

/-- If `a ∘L b` is the identity plus an operator with noetherian range, then `a ∘ b` is the
identity modulo such operators; that is, `a` is a left quasi-inverse of `b`. -/
theorem equiv_id_of_comp_eq_one_add {a : F →L[𝕜] E} {b : E →L[𝕜] F} {k : E →L[𝕜] E}
    (hk : ((k : E →ₗ[𝕜] E)).HasNoetherianRange) (hab : a ∘L b = 1 + k) :
    ((a : F →ₗ[𝕜] E) ∘ₗ (b : E →ₗ[𝕜] F)) ≈ LinearMap.id := by
  have h2 : ((a : F →ₗ[𝕜] E) ∘ₗ (b : E →ₗ[𝕜] F)) = LinearMap.id + (k : E →ₗ[𝕜] E) :=
    congrArg (fun f : E →L[𝕜] E => (f : E →ₗ[𝕜] E)) hab
  have h3 : LinearMap.id + (k : E →ₗ[𝕜] E) - LinearMap.id = (k : E →ₗ[𝕜] E) := by abel
  rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange, h2, h3]
  exact hk

/-- Two-sided inverses are quasi-inverses. -/
theorem isQuasiInverse_of_comp_eq_one {p : E →L[𝕜] F} {q : F →L[𝕜] E}
    (h1 : q ∘L p = 1) (h2 : p ∘L q = 1) : q.IsQuasiInverse p := by
  have hzero : ((0 : E →L[𝕜] E) : E →ₗ[𝕜] E).HasNoetherianRange :=
    LinearMap.HasNoetherianRange.zero
  have hzero' : ((0 : F →L[𝕜] F) : F →ₗ[𝕜] F).HasNoetherianRange :=
    LinearMap.HasNoetherianRange.zero
  exact ⟨equiv_id_of_comp_eq_one_add hzero (by rw [h1, add_zero]),
    equiv_id_of_comp_eq_one_add hzero' (by rw [h2, add_zero])⟩

/-- **Small perturbations keep a quasi-inverse.**

If `v` is a quasi-inverse of `u` and `‖v‖ ‖δ‖ < 1`, then `u + δ` again admits a quasi-inverse, and
one of a very specific shape: `p ∘L v`, where `p` is the inverse of `1 + v δ`.  That shape is what
makes the *index* locally constant, and not merely the Fredholm property, since `p` is invertible
and so contributes nothing to the index.

The naive argument does not work: from `v u = 1 + K` with `K` of finite range one only gets
`v (u + δ) = 1 + K + v δ`, and `v δ` has no reason to have finite range.  The fix is the Neumann
series.  Since `‖v δ‖ < 1`, the operator `1 + v δ` is invertible, and

`(1 + v δ)⁻¹ v (u + δ) = 1 + (1 + v δ)⁻¹ K`,

whose error term still has finite range; so `(1 + v δ)⁻¹ v` is a *left* quasi-inverse of `u + δ`.
Symmetrically `1 + δ v` is invertible on `F` and `v (1 + δ v)⁻¹` is a right quasi-inverse.  A left
and a right quasi-inverse of the same map agree modulo finite range
(`LinearMap.isQuasiInverse_of_left_of_right`), so either one is a genuine quasi-inverse. -/
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
  exact ⟨p, hpl, hpr, LinearMap.isQuasiInverse_of_left_of_right hleft hright⟩

/-- **Fredholm operators form an open set.**

This is `exists_isQuasiInverse_add_of_norm_lt` together with
`ContinuousLinearMap.IsFredholm.of_isQuasiInverse`.  The latter is what forces `𝕜` to be complete:
over an incomplete field one cannot produce the complemented kernel that `IsFredholm` requires. -/
theorem eventually_isFredholm [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
    {u : E →L[𝕜] F} (hu : IsFredholm u) :
    ∀ᶠ w in 𝓝 u, IsFredholm w := by
  obtain ⟨v, hv⟩ := hu.exists_isQuasiInverse
  have hcont : Continuous fun w : E →L[𝕜] F => ‖v‖ * ‖w - u‖ := by fun_prop
  have htend : Filter.Tendsto (fun w : E →L[𝕜] F => ‖v‖ * ‖w - u‖) (𝓝 u) (𝓝 0) :=
    hcont.tendsto' u 0 (by simp)
  filter_upwards [htend.eventually_lt_const one_pos] with w hw
  obtain ⟨p, -, -, hqi⟩ := exists_isQuasiInverse_add_of_norm_lt hv hw
  have hwu : u + (w - u) = w := by abel
  rw [hwu] at hqi
  exact IsFredholm.of_isQuasiInverse hqi

/-- **Additivity of the index.**  The composition of two Fredholm operators is Fredholm, with index
the sum of the indices.

The Fredholm half is `LinearMap.IsQuasiInverse.comp`: quasi-inverses compose in the opposite order.
The index half is `LinearMap.finrank_ker_sub_finrank_coker_comp`, four rank–nullity counts in place
of the six-term exact sequence. -/
theorem fredholmIndex_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G} (hu : IsFredholm u) (hv : IsFredholm v) :
    IsFredholm (v.comp u) ∧ fredholmIndex (v.comp u) = fredholmIndex v + fredholmIndex u := by
  obtain ⟨pu, hpu⟩ := hu.exists_isQuasiInverse
  obtain ⟨pv, hpv⟩ := hv.exists_isQuasiInverse
  have hqi : (pu ∘L pv).IsQuasiInverse (v.comp u) := hpu.comp hpv
  have hvu : IsFredholm (v.comp u) := IsFredholm.of_isQuasiInverse hqi
  refine ⟨hvu, ?_⟩
  have : FiniteDimensional 𝕜 (LinearMap.ker ((v : F →ₗ[𝕜] G) ∘ₗ (u : E →ₗ[𝕜] F))) :=
    hvu.finite_ker
  have : FiniteDimensional 𝕜 (LinearMap.ker (v : F →ₗ[𝕜] G)) := hv.finite_ker
  have : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (u : E →ₗ[𝕜] F)) := hu.finite_coker
  have : FiniteDimensional 𝕜 (G ⧸ LinearMap.range ((v : F →ₗ[𝕜] G) ∘ₗ (u : E →ₗ[𝕜] F))) :=
    hvu.finite_coker
  simp only [fredholmIndex]
  exact LinearMap.finrank_ker_sub_finrank_coker_comp (u : E →ₗ[𝕜] F) (v : F →ₗ[𝕜] G)

/-- **Quasi-inverses have opposite indices.**  If `q` is a quasi-inverse of `u` then `q ∘ u` is the
identity plus a finite-rank operator, hence of index `0`; additivity then forces
`ind q = -ind u`.  This is the step that turns the openness of the Fredholm property into the local
constancy of the index. -/
theorem fredholmIndex_add_eq_zero_of_isQuasiInverse [CompleteSpace 𝕜] [CompleteSpace E]
    [CompleteSpace F] {u : E →L[𝕜] F} {q : F →L[𝕜] E} (h : q.IsQuasiInverse u)
    (hq : IsFredholm q) (hu : IsFredholm u) :
    fredholmIndex q + fredholmIndex u = 0 := by
  have hN : ((q.comp u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E).HasNoetherianRange := by
    have h0 : ((q.comp u - 1 : E →L[𝕜] E) : E →ₗ[𝕜] E)
        = (q : F →ₗ[𝕜] E) ∘ₗ (u : E →ₗ[𝕜] F) - LinearMap.id := rfl
    rw [h0]
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp h.1
  have hone : q.comp u = 1 + (q.comp u - 1) := by abel
  rw [← (fredholmIndex_comp hu hq).2, hone, fredholmIndex_eq_zero_of_one_add hN]

/-- **The index is locally constant.**  Fredholm operators form an open set, and on it the index is
constant near each point; in particular the index is invariant under small perturbations.

Let `q` be a quasi-inverse of `u`.  For `w` with `‖q‖ ‖w - u‖ < 1`,
`exists_isQuasiInverse_add_of_norm_lt` produces the quasi-inverse `p ∘ q` of `w`, where `p` is the
inverse of `1 + q (w - u)` given by the Neumann series; in particular `w` is Fredholm.  Applying
`fredholmIndex_add_eq_zero_of_isQuasiInverse` twice, to `(q, u)` and to `(p ∘ q, w)`, and noting
that `ind (p ∘ q) = ind q` because `p` is invertible, the two relations `ind q + ind u = 0` and
`ind q + ind w = 0` give `ind w = ind u`. -/
theorem fredholmIndex_locally_constant [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
    {u : E →L[𝕜] F} (hu : IsFredholm u) :
    ∀ᶠ v in 𝓝 u, IsFredholm v ∧ fredholmIndex v = fredholmIndex u := by
  obtain ⟨qu, hqu⟩ := hu.exists_isQuasiInverse
  have hquF : IsFredholm qu := IsFredholm.of_isQuasiInverse hqu.symm
  have hsum : fredholmIndex qu + fredholmIndex u = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hqu hquF hu
  have hcont : Continuous fun w : E →L[𝕜] F => ‖qu‖ * ‖w - u‖ := by fun_prop
  have htend : Filter.Tendsto (fun w : E →L[𝕜] F => ‖qu‖ * ‖w - u‖) (𝓝 u) (𝓝 0) :=
    hcont.tendsto' u 0 (by simp)
  filter_upwards [htend.eventually_lt_const one_pos] with w hw
  obtain ⟨p, hpl, hpr, hqi⟩ := exists_isQuasiInverse_add_of_norm_lt hqu hw
  have hwu : u + (w - u) = w := by abel
  rw [hwu] at hqi
  have hwF : IsFredholm w := IsFredholm.of_isQuasiInverse hqi
  have hpquF : IsFredholm (p ∘L qu) := IsFredholm.of_isQuasiInverse hqi.symm
  have hpF : IsFredholm p :=
    IsFredholm.of_isQuasiInverse (isQuasiInverse_of_comp_eq_one hpl hpr)
  have hpbij : Function.Bijective p :=
    Function.bijective_iff_has_inverse.mpr
      ⟨(1 + qu ∘L (w - u) : E →L[𝕜] E), fun y => DFunLike.congr_fun hpl y,
        fun y => DFunLike.congr_fun hpr y⟩
  have hsum2 : fredholmIndex (p ∘L qu) + fredholmIndex w = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hqi hpquF hwF
  have hpqu : fredholmIndex (p ∘L qu) = fredholmIndex qu := by
    rw [(fredholmIndex_comp hquF hpF).2, fredholmIndex_eq_zero_of_bijective hpbij, zero_add]
  exact ⟨hwF, by omega⟩

/-- **A finite-rank perturbation changes neither the Fredholm property nor the index.**

A quasi-inverse `q` of `u` is again a quasi-inverse of `u + k`, because `q (u + k) - 1
= (q u - 1) + q k` and `(u + k) q - 1 = (u q - 1) + k q` both still have finite-dimensional range;
`fredholmIndex_add_eq_zero_of_isQuasiInverse` then computes both indices as `-ind q`.

This is the elementary half of the invariance of the index under compact perturbations; the general
statement, for `k` compact, needs Riesz–Schauder and is not proved here. -/
theorem isFredholm_add_and_fredholmIndex_eq_of_hasNoetherianRange [CompleteSpace 𝕜]
    [CompleteSpace E] [CompleteSpace F] {u k : E →L[𝕜] F} (hu : IsFredholm u)
    (hk : ((k : E →ₗ[𝕜] F)).HasNoetherianRange) :
    IsFredholm (u + k) ∧ fredholmIndex (u + k) = fredholmIndex u := by
  obtain ⟨q, hq⟩ := hu.exists_isQuasiInverse
  have hqF : IsFredholm q := IsFredholm.of_isQuasiInverse hq.symm
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
      ((u + k : E →L[𝕜] F) : E →ₗ[𝕜] F) := LinearMap.isQuasiInverse_of_left_of_right hleft hright
  have hukF : IsFredholm (u + k) := IsFredholm.of_isQuasiInverse hqi
  have h1 : fredholmIndex q + fredholmIndex (u + k) = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hqi hqF hukF
  have h2 : fredholmIndex q + fredholmIndex u = 0 :=
    fredholmIndex_add_eq_zero_of_isQuasiInverse hq hqF hu
  exact ⟨hukF, by omega⟩

end ContinuousLinearMap
