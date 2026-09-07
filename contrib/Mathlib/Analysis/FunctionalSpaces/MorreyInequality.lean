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

Two lemmas of independent interest are proved on the way:

* `MeasureTheory.lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi`: polar coordinates
  for a Lebesgue integral against an additive Haar measure, for a general non-negative
  measurable integrand.
* `MeasureTheory.lintegral_ball_enorm_sub_le_lintegral_riesz`: the mean oscillation of a `C¹`
  function on a ball is bounded by the Riesz potential of its derivative.

## Proof outline

The classical route, in three steps. The analytic tool underlying the first two is the
generalized polar coordinate change of
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`, which represents an additive Haar
measure on an `n`-dimensional normed space as the product of the sphere measure
`MeasureTheory.Measure.toSphere` and Lebesgue measure on `(0, ∞)` taken with density
`r ^ (n - 1)` (`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`).

That theorem is exposed upstream only through its radial corollaries
`MeasureTheory.integrableOn_fun_norm_addHaar` and `MeasureTheory.integral_fun_norm_addHaar`,
so this file first records its general `lintegral` form,
`MeasureTheory.lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi`, together with the
version localised to a ball,
`MeasureTheory.setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo`. Those two are
independent of Morrey's inequality and are stated for a general non-negative measurable
integrand.

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
   radial, so this step uses the polar decomposition itself rather than its radial corollary:
   in polar coordinates the density `ρ ^ (n - 1)` cancels the Riesz kernel exactly, and what
   is left on each ray is the fundamental theorem of calculus.

3. Hölder against that kernel turns step 2 into
   `⨍_B ‖u y - u x‖ ≤ C r ^ (1 - n / p) * ‖fderiv ℝ u‖_{Lᵖ}`, and comparing the averages over
   two balls of radius `‖x - z‖` around `x` and `z` gives the Hölder estimate. For a function
   supported in a bounded set `s`, walking out of `s` along a ray from `x` produces a point
   `z` at distance `Metric.diam s` at which `u` vanishes, and that turns the Hölder estimate
   into the bound on the essential supremum.

## Status

**Draft.** The statements and the constants are final. Everything is proved except the
Hölder estimate `MeasureTheory.enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`, which
carries a `sorry` and a docstring saying what is left to do. In particular the two polar
coordinate lemmas, the Riesz kernel integrability
`MeasureTheory.lintegral_ball_rpow_neg_lt_top` (the point at which the hypothesis `n < p` is
consumed), the Riesz potential estimate
`MeasureTheory.lintegral_ball_enorm_sub_le_lintegral_riesz` and the passage from the Hölder
estimate to the bound on the essential supremum
`MeasureTheory.eLpNorm_top_le_eLpNorm_fderiv` are complete. Note that the last of these,
though its own proof is complete, still depends on the assumed Hölder estimate.

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

section PolarCoordinates

/-- **Polar coordinates for a Lebesgue integral against an additive Haar measure.**

Let `μ` be an additive Haar measure on a nontrivial finite-dimensional real normed space `E`
of dimension `n`. Then the integral of a non-negative measurable function against `μ`
decomposes as an integral over the unit sphere, with respect to the sphere measure
`MeasureTheory.Measure.toSphere`, of a radial integral carrying the density `r ^ (n - 1)`.

This is the `lintegral` form of
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`, for a general integrand.
The Bochner and integrability corollaries of that theorem,
`MeasureTheory.integral_fun_norm_addHaar` and
`MeasureTheory.integrableOn_fun_norm_addHaar`, are both restricted to radial integrands. -/
theorem lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi [Nontrivial E]
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ ω : sphere (0 : E) 1,
        (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * f (r • (ω : E)))
          ∂μ.toSphere := by
  have hmeas : Measurable fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f ((p.2 : ℝ) • (p.1 : E)) :=
    hf.comp (by fun_prop)
  calc ∫⁻ x, f x ∂μ
      = ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton (0 : E)).compl,
          restrict_compl_singleton]
    _ = ∫⁻ p : sphere (0 : E) 1 × Ioi (0 : ℝ), f ((p.2 : ℝ) • (p.1 : E))
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) := by
        rw [← μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) fun p => f ((p.2 : ℝ) • (p.1 : E))]
        refine lintegral_congr fun x => ?_
        rw [← homeomorphUnitSphereProd_symm_apply_coe, Homeomorph.symm_apply_apply]
    _ = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ r : Ioi (0 : ℝ), f ((r : ℝ) • (ω : E))
            ∂(Measure.volumeIoiPow (finrank ℝ E - 1))) ∂μ.toSphere :=
        lintegral_prod _ hmeas.aemeasurable
    _ = _ := by
        refine lintegral_congr fun ω => ?_
        simp only [Measure.volumeIoiPow]
        rw [lintegral_withDensity_eq_lintegral_mul (Measure.comap Subtype.val volume)
          (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ (finrank ℝ E - 1)))
          (by fun_prop)
          (g := fun r : Ioi (0 : ℝ) => f ((r : ℝ) • (ω : E))) (hf.comp (by fun_prop))]
        simp only [Pi.mul_apply]
        exact lintegral_subtype_comap measurableSet_Ioi
          (fun t : ℝ => ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E)))

/-- Polar coordinates centred at `c` for a Lebesgue integral over the ball `ball c R`, the
localised form of `lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi`. The radial
integral now runs over `Ioo 0 R`. -/
theorem setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo [Nontrivial E] (c : E) (R : ℝ)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in ball c R, f y ∂μ =
      ∫⁻ ω : sphere (0 : E) 1,
        (∫⁻ ρ in Ioo (0 : ℝ) R,
          ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) * f (c + ρ • (ω : E))) ∂μ.toSphere := by
  set g : E → ℝ≥0∞ := (ball (0 : E) R).indicator fun z => f (c + z) with hg
  have hgm : Measurable g := (hf.comp (measurable_const_add c)).indicator measurableSet_ball
  have h1 : ∫⁻ y in ball c R, f y ∂μ = ∫⁻ z, g z ∂μ := by
    have h := (measurePreserving_add_left μ c).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addLeft c) f (ball c R)
    have hpre : (fun z : E => c + z) ⁻¹' ball c R = ball (0 : E) R := by
      ext z
      rw [Set.mem_preimage, mem_ball_iff_norm, mem_ball_zero_iff, add_sub_cancel_left]
    rw [hpre] at h
    rw [← h, hg, lintegral_indicator measurableSet_ball]
  rw [h1, lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi μ hgm]
  refine lintegral_congr fun ω => ?_
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  have h2 : EqOn (fun ρ : ℝ => ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) * g (ρ • (ω : E)))
      ((Ioo (0 : ℝ) R).indicator
        fun ρ => ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) * f (c + ρ • (ω : E))) (Ioi 0) := by
    intro ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    have hnorm : ‖ρ • (ω : E)‖ = ρ := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hρ0]
    by_cases hR : ρ < R
    · rw [Set.indicator_of_mem (Set.mem_Ioo.2 ⟨hρ0, hR⟩)]
      simp only [hg]
      rw [Set.indicator_of_mem (mem_ball_zero_iff.2 (by rw [hnorm]; exact hR))]
    · rw [Set.indicator_of_notMem (by simp [Set.mem_Ioo, hR])]
      simp only [hg]
      rw [Set.indicator_of_notMem (by simp [hnorm, hR]), mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.2 Ioo_subset_Ioi_self]

end PolarCoordinates

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
  (r ^ finrank ℝ E / (finrank ℝ E : ℝ)).toNNReal

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Along a ray with unit direction `ω`, the increment of a continuously differentiable
function is bounded by the integral of the enorm of its derivative. This is the fundamental
theorem of calculus in the form needed for Morrey's inequality.

The target space is not assumed complete, so the Bochner integral behind the fundamental
theorem of calculus is taken in `UniformSpace.Completion F`, into which `F` embeds
isometrically. -/
theorem enorm_sub_le_lintegral_Ioc_enorm_fderiv
    {u : E → F} (hu : ContDiff ℝ 1 u) (x : E) {ω : E} (hω : ‖ω‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖u (x + ρ • ω) - u x‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) ρ, ‖fderiv ℝ u (x + t • ω)‖ₑ := by
  -- the derivative of `u` along the ray through `x` in the direction `ω`
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u (x + s • ω)) (fderiv ℝ u (x + t • ω) ω) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => x + s • ω) ω t := by
      simpa using ((hasDerivAt_id t).smul_const ω).const_add x
    exact HasFDerivAt.comp_hasDerivAt t
      ((hu.differentiable one_ne_zero) (x + t • ω)).hasFDerivAt h1
  set I : F →L[ℝ] UniformSpace.Completion F := UniformSpace.Completion.toComplL with hI
  have hIe : ∀ y : F, ‖I y‖ₑ = ‖y‖ₑ := by
    intro y
    rw [hI, UniformSpace.Completion.coe_toComplL, UniformSpace.Completion.enorm_coe]
  have hdI : ∀ t : ℝ, HasDerivAt (fun s : ℝ => I (u (x + s • ω)))
      (I (fderiv ℝ u (x + t • ω) ω)) t := fun t =>
    HasFDerivAt.comp_hasDerivAt t I.hasFDerivAt (hd t)
  have hcontI : Continuous fun t : ℝ => I (fderiv ℝ u (x + t • ω) ω) := by
    have h0 : Continuous fun t : ℝ => fderiv ℝ u (x + t • ω) :=
      (hu.continuous_fderiv one_ne_zero).comp (by fun_prop)
    exact I.continuous.comp (h0.clm_apply continuous_const)
  have hFTC : I (u (x + ρ • ω)) - I (u x)
      = ∫ t in (0 : ℝ)..ρ, I (fderiv ℝ u (x + t • ω) ω) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => I (u (x + s • ω)))
      (f' := fun t : ℝ => I (fderiv ℝ u (x + t • ω) ω)) (fun t _ => hdI t)
      (hcontI.intervalIntegrable 0 ρ)
    rw [h]
    simp
  calc ‖u (x + ρ • ω) - u x‖ₑ = ‖I (u (x + ρ • ω)) - I (u x)‖ₑ := by
        rw [← map_sub I, hIe]
    _ = ‖∫ t in Ioc (0 : ℝ) ρ, I (fderiv ℝ u (x + t • ω) ω)‖ₑ := by
        rw [hFTC, intervalIntegral.integral_of_le hρ]
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) ρ, ‖I (fderiv ℝ u (x + t • ω) ω)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) ρ, ‖fderiv ℝ u (x + t • ω)‖ₑ := by
      refine lintegral_mono fun t => ?_
      rw [hIe]
      refine (ContinuousLinearMap.le_opENorm _ _).trans_eq ?_
      rw [← ofReal_norm ω, hω, ENNReal.ofReal_one, mul_one]

/-- **The Riesz potential estimate.**

For `u` of class `C¹`, the mean oscillation of `u` on a ball is controlled by the Riesz
potential of its derivative:
`∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ ≤ (r ^ n / n) * (Riesz potential of the derivative)`.

The proof reads both sides in polar coordinates about `x`, using
`setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo`. On the right the radial density
`ρ ^ (n - 1)` cancels the Riesz kernel exactly, leaving
`∫_0^r ‖fderiv ℝ u (x + t ω)‖ dt` on each ray; on the left the fundamental theorem of
calculus (`enorm_sub_le_lintegral_Ioc_enorm_fderiv`) bounds the integrand on each ray by that
same quantity, and integrating the density `ρ ^ (n - 1)` over `(0, r)` produces the factor
`rieszPotentialConst E r = r ^ n / n`. -/
theorem lintegral_ball_enorm_sub_le_lintegral_riesz [Nontrivial E]
    {u : E → F} (hu : ContDiff ℝ 1 u) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ) ≤
      rieszPotentialConst E r *
        ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ := by
  have hn : 1 ≤ finrank ℝ E := Module.finrank_pos
  have hn0 : finrank ℝ E ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hofReal : ∀ t : ℝ, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := fun _ => rfl
  have hcast : ((finrank ℝ E : ℝ) - 1) = ((finrank ℝ E - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  -- measurability of the two integrands
  have hLm : Measurable fun y : E => ‖u y - u x‖ₑ :=
    ((hu.continuous.sub continuous_const).enorm).measurable
  have hDu : Measurable fun y : E => ‖fderiv ℝ u y‖ₑ :=
    ((hu.continuous_fderiv one_ne_zero).enorm).measurable
  have hRm : Measurable fun y : E =>
      ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) := by
    simp only [div_eq_mul_inv]
    exact hDu.mul ((((continuous_id.sub continuous_const).enorm).measurable).pow_const _).inv
  -- the radial density integrates to `r ^ n / n`
  have hpow : (∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)))
      = (rieszPotentialConst E r : ℝ≥0∞) := by
    have hc : Continuous fun ρ : ℝ => ρ ^ (finrank ℝ E - 1) := by fun_prop
    have hint : IntegrableOn (fun ρ : ℝ => ρ ^ (finrank ℝ E - 1)) (Ioo 0 r) volume :=
      (hc.integrableOn_Icc (a := 0) (b := r)).mono_set Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)] fun ρ : ℝ => ρ ^ (finrank ℝ E - 1) :=
      ae_restrict_of_forall_mem measurableSet_Ioo fun ρ hρ => pow_nonneg hρ.1.le _
    have hval : (∫ ρ in Ioo (0 : ℝ) r, ρ ^ (finrank ℝ E - 1))
        = r ^ finrank ℝ E / (finrank ℝ E : ℝ) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le, integral_pow,
        Nat.sub_add_cancel hn, zero_pow hn0, sub_zero, Nat.cast_sub hn]
      norm_num
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval, rieszPotentialConst_def, hofReal]
  -- polar form of the right-hand side: the radial density cancels the Riesz kernel
  have hRHS : (∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ)
      = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ ρ in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + ρ • (ω : E))‖ₑ) ∂μ.toSphere := by
    rw [setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r hRm]
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun ρ hρ => ?_
    have hρ0 : (0 : ℝ) < ρ := hρ.1
    have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    have h1 : x + ρ • (ω : E) - x = ρ • (ω : E) := by abel
    have h2 : ‖ρ • (ω : E)‖ₑ = ENNReal.ofReal ρ := by
      rw [← ofReal_norm, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hρ0]
    have h4 : (ENNReal.ofReal ρ) ^ ((finrank ℝ E : ℝ) - 1)
        = ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) := by
      rw [ENNReal.ofReal_rpow_of_pos hρ0, hcast, Real.rpow_natCast]
    rw [h1, h2, h4]
    exact ENNReal.mul_div_cancel (ENNReal.ofReal_pos.2 (pow_pos hρ0 _)).ne'
      ENNReal.ofReal_ne_top
  -- compare the two ray integrals
  rw [setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r hLm, hRHS,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun ω => ?_
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  have hstep : ∀ ρ ∈ Ioo (0 : ℝ) r,
      ‖u (x + ρ • (ω : E)) - u x‖ₑ
        ≤ ∫⁻ t in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + t • (ω : E))‖ₑ := fun ρ hρ =>
    (enorm_sub_le_lintegral_Ioc_enorm_fderiv hu x hω hρ.1.le).trans
      (lintegral_mono_set fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hρ.2⟩)
  calc (∫⁻ ρ in Ioo (0 : ℝ) r,
          ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) * ‖u (x + ρ • (ω : E)) - u x‖ₑ)
      ≤ ∫⁻ _ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (_ρ ^ (finrank ℝ E - 1)) *
          ∫⁻ t in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + t • (ω : E))‖ₑ :=
        setLIntegral_mono' measurableSet_Ioo fun ρ hρ => mul_le_mul_right (hstep ρ hρ) _
    _ = (∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (ρ ^ (finrank ℝ E - 1))) *
          ∫⁻ t in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + t • (ω : E))‖ₑ :=
        lintegral_mul_const'' _ (by fun_prop)
    _ = _ := by rw [hpow]

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

*To prove.* This is the one step of the file that is still assumed. Both of its inputs are
available: `lintegral_ball_enorm_sub_le_lintegral_riesz` bounds the mean oscillation of `u`
on a ball by the Riesz potential of its derivative, and `lintegral_ball_rpow_neg_lt_top`
says that the Riesz kernel is integrable on a ball. What is missing is the two steps that
join them.

First, Hölder's inequality (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) applied to
`‖fderiv ℝ u y‖ₑ * ‖y - x‖ₑ ^ (1 - n)` with exponents `p` and its conjugate `q` turns the
potential estimate into
`⨍_{ball x r} ‖u y - u x‖ ≤ C * r ^ (1 - n / p) * ‖fderiv ℝ u‖_{Lᵖ}`. The kernel factor is
`(∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-(n - 1) * q)) ^ (1 / q)`, which is finite by
`lintegral_ball_rpow_neg_lt_top` — the condition `(n - 1) * q < n` there is exactly
`finrank ℝ E < p`, and this is the only place the supercritical hypothesis is used. Turning
that finiteness into the explicit value `rieszKernelConst μ ((n - 1) * q) r` needs a
quantitative form of that lemma, which the polar coordinate lemmas of this file make
routine but which is not yet recorded.

Second, one compares the averages of `u` over the two balls of radius `d = ‖x - z‖` centred
at `x` and at `z` with the average over their intersection, which contains
`ball ((x + z) / 2) (d / 2)` and therefore has measure at least `2 ^ (-n) * μ (ball x d)`
(`Measure.addHaar_ball`). Writing `u x - u z = (u x - u y) + (u y - u z)` and averaging over
that intersection gives the stated estimate, with the constant `morreyConst E μ p`. -/
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
