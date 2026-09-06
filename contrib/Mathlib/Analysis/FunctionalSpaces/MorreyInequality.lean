/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Morrey's inequality

This file proves **Morrey's inequality**, the supercritical companion of the
Gagliardo–Nirenberg–Sobolev inequality in
`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`.

That file bounds the `Lᵍ` norm of a compactly supported `C¹` function by the `Lᵖ` norm of
its derivative under the hypothesis `p < finrank ℝ E`. Morrey's inequality is the
complementary statement for `finrank ℝ E < p`: the function is then bounded, indeed Hölder
continuous of exponent `1 - n / p`, with the Hölder seminorm controlled by the same `Lᵖ`
norm of the derivative.

Together the two files cover the whole range of exponents apart from the critical case
`p = finrank ℝ E`.

## Main results

* `MeasureTheory.enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`: the Hölder estimate
  `‖u x - u z‖ₑ ≤ C * ‖x - z‖ₑ ^ (1 - n / p) * eLpNorm (fderiv ℝ u) p μ`.
* `MeasureTheory.eLpNorm_top_le_eLpNorm_fderiv`: the resulting bound on the essential
  supremum, for a function supported in a bounded set.

## Proof outline

The classical route, in three steps. The analytic tool underlying the first two is the
generalized polar coordinate change of
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`, which represents an additive Haar
measure on an `n`-dimensional normed space as the product of the sphere measure
`MeasureTheory.Measure.toSphere` and Lebesgue measure on `(0, ∞)` taken with density
`r ^ (n - 1)` (`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`), together
with its two radial corollaries
`MeasureTheory.integrableOn_fun_norm_addHaar` and `MeasureTheory.integral_fun_norm_addHaar`.

1. `MeasureTheory.lintegral_ball_rpow_neg_lt_top`: the Riesz kernel `y ↦ ‖y - x‖ ^ (-a)` is
   integrable on a ball as soon as `a < n`. Its integrand is radial, so polar coordinates
   reduce the statement to the convergence of `∫_0^r ρ ^ (n - 1 - a) dρ`. Applied with
   `a = (n - 1) * q`, where `q` is the conjugate exponent of `p`, the condition `a < n` is
   exactly the hypothesis `n < p`. **This is where supercriticality enters**, and it is the
   only place it is used.

2. `MeasureTheory.lintegral_ball_enorm_sub_le_lintegral_riesz`: for `u` of class `C¹` and a
   ball `B = ball x r`, averaging the fundamental theorem of calculus along the rays out of
   `x` gives
   `∫⁻ y in B, ‖u y - u x‖ₑ ∂μ ≤ r ^ n / n * ∫⁻ y in B, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ (n-1) ∂μ`.
   The right-hand side is a Riesz potential of the derivative. The integrand here is not
   radial, so this step uses the polar decomposition itself rather than its radial corollary.

3. Hölder against that kernel turns step 2 into
   `⨍_B ‖u y - u x‖ ≤ C r ^ (1 - n / p) * ‖fderiv ℝ u‖_{Lᵖ}`, and comparing the averages over
   two balls of radius `‖x - z‖` around `x` and `z` gives the Hölder estimate. For a function
   supported in a bounded set `s`, walking out of `s` along a ray from `x` produces a point
   `z` at distance `Metric.diam s` at which `u` vanishes, and that turns the Hölder estimate
   into the bound on the essential supremum.

## Status

**Draft.** The statements and the constants are final. Two of the four results are proved in
full: `MeasureTheory.lintegral_ball_rpow_neg_lt_top`, step 1 and the point at which the
hypothesis `n < p` is consumed, and `MeasureTheory.eLpNorm_top_le_eLpNorm_fderiv`, the second
half of step 3, which derives the bound on the essential supremum from the Hölder estimate.

Step 2, `MeasureTheory.lintegral_ball_enorm_sub_le_lintegral_riesz`, and the Hölder estimate
`MeasureTheory.enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv` are the work remaining;
each carries a docstring naming the ingredient it needs.

## References

* [L. C. Evans, *Partial Differential Equations*][evans2010], §5.6.2
* [E. H. Lieb and M. Loss, *Analysis*][liebLoss2001], §8.4
-/

open scoped ENNReal NNReal
open Set Function MeasureTheory Measure Filter Module Metric

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section RieszKernel

/-- **Integrability of the Riesz kernel on a ball.**

The kernel `y ↦ ‖y - x‖ ^ (-a)` is integrable on `ball x r` exactly when `a < n`. In Morrey's
inequality it is applied with `a = (n - 1) * q`, where `q` is the conjugate exponent of `p`;
the condition `a < n` is then equivalent to `n < p`, so this lemma is where the supercritical
hypothesis is consumed.

The proof translates the ball to the origin and appeals to
`MeasureTheory.integrableOn_ball_of_norm_le_rpow`, which is the polar coordinate change of
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` specialised to radial integrands: it
reduces the statement to the convergence of `∫_0^r ρ ^ (n - 1 - a) dρ`. -/
theorem lintegral_ball_rpow_neg_lt_top [Nontrivial E] (x : E) {r a : ℝ} (_hr : 0 < r)
    (_ha : 0 ≤ a) (han : a < finrank ℝ E) :
    (∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ) < ⊤ := by
  -- Translate the ball to the origin: `μ` is invariant under `· + x`.
  have hpre : (fun z : E => z + x) ⁻¹' ball x r = ball (0 : E) r := by
    ext z
    rw [Set.mem_preimage, mem_ball_iff_norm, mem_ball_zero_iff, add_sub_cancel_right]
  have htrans :
      (∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ) = ∫⁻ z in ball (0 : E) r, ‖z‖ₑ ^ (-a) ∂μ := by
    have h := (measurePreserving_add_right μ x).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight x) (fun y : E => ‖y - x‖ₑ ^ (-a)) (ball x r)
    rw [hpre] at h
    simp only [add_sub_cancel_right] at h
    exact h.symm
  rw [htrans]
  -- The radial function `z ↦ ‖z‖ ^ (-a)` is integrable on the ball, by polar coordinates.
  have hint : IntegrableOn (fun z : E => ‖z‖ ^ (-a)) (ball (0 : E) r) μ := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) Module.finrank_pos han ?_
      (measurable_norm.pow_const (-a)).aestronglyMeasurable
    filter_upwards with z
    refine le_of_eq ?_
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  -- Away from the origin the two integrands agree.
  have hae : (fun z : E => ‖z‖ₑ ^ (-a)) =ᵐ[μ.restrict (ball (0 : E) r)]
      fun z : E => ‖(‖z‖ ^ (-a) : ℝ)‖ₑ := by
    have h0 : ∀ᵐ z ∂(μ.restrict (ball (0 : E) r)), z ≠ 0 := ae_iff.2 (by simp)
    filter_upwards [h0] with z hz
    have hz' : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg z) _), ← ofReal_norm z,
      ENNReal.ofReal_rpow_of_pos hz']
  rw [lintegral_congr_ae hae]
  exact hint.2

/-- The value of the integral in `lintegral_ball_rpow_neg_lt_top`, as a constant depending
only on `E`, `μ` and the exponents. Keeping it named, rather than existential, is what lets
the constants in the main statements below be written down explicitly. -/
noncomputable irreducible_def rieszKernelConst [Nontrivial E] (a : ℝ) (r : ℝ) : ℝ≥0 :=
  ((finrank ℝ E : ℝ) / (finrank ℝ E - a)).toNNReal *
    (μ (ball (0 : E) 1)).toNNReal * r.toNNReal ^ (finrank ℝ E - a)

end RieszKernel

section Potential

variable (E) in
/-- The constant `r ^ n / n` in the Riesz potential estimate
`lintegral_ball_enorm_sub_le_lintegral_riesz`. It is the value of `∫_0^r ρ ^ (n - 1) dρ`,
which is what integrating the fundamental theorem of calculus along the rays out of the
centre of the ball produces.

Unlike `rieszKernelConst` it does not involve `μ`, and it cannot: both sides of that estimate
are homogeneous of degree one in `μ`, so the constant relating them must be homogeneous of
degree zero. -/
noncomputable irreducible_def rieszPotentialConst (r : ℝ) : ℝ≥0 :=
  (finrank ℝ E : ℝ≥0)⁻¹ * r.toNNReal ^ finrank ℝ E

/-- **The Riesz potential estimate.**

For `u` of class `C¹`, the mean oscillation of `u` on a ball is controlled by the Riesz
potential of its derivative:
`∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ ≤ (r ^ n / n) * (Riesz potential of the derivative)`.

*To prove:* write `u y - u x = ∫_0^1 (fderiv ℝ u (x + t (y - x))) (y - x) dt` and integrate
over the ball, exchanging the order of integration. Unlike
`lintegral_ball_rpow_neg_lt_top`, the integrand here is not radial, so the radial
specialisation `MeasureTheory.integrableOn_fun_norm_addHaar` does not apply: what is needed
is the polar decomposition itself,
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`, together with Fubini's
theorem for the resulting product of `MeasureTheory.Measure.toSphere` and
`MeasureTheory.Measure.volumeIoiPow`. In those coordinates both sides become integrals over
the unit sphere of `∫_0^r ‖fderiv ℝ u (x + t ω)‖ dt`, the left-hand side carrying the extra
factor `∫_0^r ρ ^ (n - 1) dρ = r ^ n / n`, which is `rieszPotentialConst E r`. Mathlib has
the one-dimensional fundamental theorem of calculus along a segment, and `Measure.addHaar_ball`
for the scaling. -/
theorem lintegral_ball_enorm_sub_le_lintegral_riesz [Nontrivial E]
    {u : E → F} (hu : ContDiff ℝ 1 u) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ) ≤
      rieszPotentialConst E r *
        ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ := by
  sorry

end Potential

section Morrey

variable (E) in
/-- The constant in the Hölder estimate of Morrey's inequality. It depends only on `E`, `μ`
and `p`.

Its three factors are the three steps of the proof: `2 ^ (n + 1) / n` collects the constant
`r ^ n / n` of the Riesz potential estimate and the two-fold comparison of the averages over
`ball x ‖x - z‖` and `ball z ‖x - z‖` with the average over their intersection, which
contains a ball of half the radius; `rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q)` is the
kernel factor coming out of Hölder's inequality, for `q` the conjugate exponent of `p`; and
`(μ (ball 0 1)).toNNReal⁻¹` normalises the averages. Note the resulting homogeneity in `μ`:
the constant is homogeneous of degree `1 / q - 1 = -1 / p`, which is what makes the estimate
itself invariant under rescaling `μ`, since `eLpNorm · p` is homogeneous of degree `1 / p`. -/
noncomputable irreducible_def morreyConst [Nontrivial E] (p : ℝ≥0) : ℝ≥0 :=
  let n : ℝ := finrank ℝ E
  let q : ℝ := (1 - 1 / p)⁻¹          -- the conjugate exponent of `p`
  2 ^ (finrank ℝ E + 1) / (finrank ℝ E : ℝ≥0) *
    rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q) * (μ (ball (0 : E) 1)).toNNReal⁻¹

/-- **Morrey's inequality, Hölder form.**

Let `u` be a continuously differentiable function on a normed space `E` of finite dimension
`n`, equipped with a Haar measure, and let `finrank ℝ E < p`. Then `u` is Hölder continuous
of exponent `1 - n / p`, with seminorm bounded by the `Lᵖ` norm of its derivative.

This is the supercritical counterpart of `MeasureTheory.eLpNorm_le_eLpNorm_fderiv`, whose
hypothesis is `p < finrank ℝ E`.

*To prove:* apply Hölder's inequality to the Riesz potential produced by
`lintegral_ball_enorm_sub_le_lintegral_riesz`, using `lintegral_ball_rpow_neg_lt_top` — with
`a = (n - 1) * q` for `q` the conjugate exponent of `p`, which is where `finrank ℝ E < p`
enters — to control the kernel factor, and then compare the averages of `u` over the two
balls of radius `‖x - z‖` centred at `x` and at `z` with the average over their intersection,
which contains a ball of radius `‖x - z‖ / 2` about the midpoint. -/
theorem enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv [Nontrivial E]
    {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) < p) (x z : E) :
    ‖u x - u z‖ₑ ≤
      morreyConst E μ p * ‖x - z‖ₑ ^ (1 - (finrank ℝ E : ℝ) / p) *
        eLpNorm (fderiv ℝ u) p μ := by
  sorry

variable (E) in
/-- The constant in the essential-supremum form of Morrey's inequality. Besides `E`, `μ` and
`p` it depends on the support `s`, through its diameter — exactly as the constant of
`eLpNorm_le_eLpNorm_fderiv_of_le` depends on `s` through its measure. -/
noncomputable irreducible_def morreyEssSupConst [Nontrivial E] (s : Set E) (p : ℝ≥0) : ℝ≥0 :=
  morreyConst E μ p * (Metric.diam s).toNNReal ^ (1 - (finrank ℝ E : ℝ) / p)

/-- **Morrey's inequality.**

A continuously differentiable function supported in a bounded set, on a space of dimension
`n < p`, is essentially bounded by a constant times the `Lᵖ` norm of its derivative.

This is the statement that supplies the Sobolev embedding `W^{1,p} ↪ L^∞` for `p > n`. -/
theorem eLpNorm_top_le_eLpNorm_fderiv [Nontrivial E]
    {u : E → F} {s : Set E} (hu : ContDiff ℝ 1 u) (h2u : u.support ⊆ s)
    {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) < p) (hs : Bornology.IsBounded s) :
    eLpNorm u ⊤ μ ≤ morreyEssSupConst E μ s p * eLpNorm (fderiv ℝ u) p μ := by
  have hnp : (finrank ℝ E : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) hnp
  have hexp : (0 : ℝ) ≤ 1 - (finrank ℝ E : ℝ) / (p : ℝ) :=
    sub_nonneg.2 ((div_le_one hp0).2 hnp.le)
  have hd0 : (0 : ℝ) ≤ Metric.diam s := Metric.diam_nonneg
  -- The support is closed and bounded in a finite-dimensional space, hence compact.
  have hcs : HasCompactSupport u :=
    hs.isCompact_closure.of_isClosed_subset isClosed_closure (closure_mono h2u)
  have hcu : Continuous u := hu.continuous
  have hofReal : ∀ t : ℝ, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := fun _ => rfl
  -- A unit vector, along which we walk out of `s`.
  obtain ⟨v, hv1⟩ : ∃ v : E, ‖v‖ = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : E)
    exact ⟨‖w‖⁻¹ • w, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]⟩
  rw [eLpNorm_exponent_top]
  refine eLpNormEssSup_le_of_ae_enorm_bound (.of_forall fun x => ?_)
  rcases eq_or_ne (u x) 0 with hux | hux
  · simp [hux]
  have hxs : x ∈ s := h2u (Function.mem_support.mpr hux)
  have hnormsub : ∀ θ : ℝ, 0 ≤ θ → ‖x - (x + θ • v)‖ = θ := by
    intro θ hθ
    have hxx : x - (x + θ • v) = -(θ • v) := by abel
    rw [hxx, norm_neg, norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_of_nonneg hθ]
  -- Beyond distance `diam s` from `x` the function vanishes.
  have hzero : ∀ θ : ℝ, Metric.diam s < θ → u (x + θ • v) = 0 := by
    intro θ hθ
    by_contra hne
    have hmem : x + θ • v ∈ s := h2u (Function.mem_support.mpr hne)
    have hle : dist x (x + θ • v) ≤ Metric.diam s := Metric.dist_le_diam_of_mem hs hxs hmem
    rw [dist_eq_norm, hnormsub θ (hd0.trans hθ.le)] at hle
    exact absurd hle (not_le.2 hθ)
  -- By continuity it already vanishes at distance exactly `diam s`.
  have huz : u (x + Metric.diam s • v) = 0 := by
    have hgc : Continuous fun θ : ℝ => u (x + θ • v) := by fun_prop
    have hcl : IsClosed {θ : ℝ | u (x + θ • v) = 0} := isClosed_eq hgc continuous_const
    have hsub : Ioi (Metric.diam s) ⊆ {θ : ℝ | u (x + θ • v) = 0} := fun θ hθ => hzero θ hθ
    have hcls := hcl.closure_subset_iff.2 hsub
    rw [closure_Ioi] at hcls
    exact hcls self_mem_Ici
  have key := enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv μ hu hcs hp x
    (x + Metric.diam s • v)
  rw [huz, sub_zero] at key
  refine key.trans (le_of_eq ?_)
  have hnorm : ‖x - (x + Metric.diam s • v)‖ₑ = ENNReal.ofReal (Metric.diam s) := by
    rw [← ofReal_norm, hnormsub _ hd0]
  rw [hnorm, morreyEssSupConst_def, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hexp,
    hofReal]

end Morrey

end MeasureTheory
