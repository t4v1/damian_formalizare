/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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

The classical route, in three steps.

1. `MeasureTheory.lintegral_ball_enorm_sub_le_lintegral_riesz`: for `u` of class `C¹` and a
   ball `B = ball x r`, averaging the fundamental theorem of calculus along the rays out of
   `x` gives
   `∫⁻ y in B, ‖u y - u x‖ₑ ∂μ ≤ C n * r ^ n * ∫⁻ y in B, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ (n-1) ∂μ`.
   The right-hand side is a Riesz potential of the derivative.

2. `MeasureTheory.lintegral_ball_rpow_neg_lt_top`: the Riesz kernel `‖y - x‖ ^ (-(n-1)q)` is
   integrable on a ball exactly when `(n - 1) * q < n`, and for `q` the conjugate exponent of
   `p` that is exactly the hypothesis `n < p`. **This is where supercriticality enters**, and
   it is the only place it is used.

3. Hölder against that kernel turns step 1 into
   `⨍_B ‖u y - u x‖ ≤ C r ^ (1 - n / p) * ‖fderiv ℝ u‖_{Lᵖ}`, and comparing the averages over
   two balls of radius `‖x - z‖` around `x` and `z` gives the Hölder estimate. For a function
   supported in a bounded set `s`, choosing `z` outside `s` turns that into the bound on the
   essential supremum.

## Status

**Draft.** The statements are final; the analytic steps carry `sorry` and are the work
remaining. Each is marked with the ingredient it needs.

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

*To prove:* polar coordinates reduce this to `∫_0^r ρ ^ (n - 1 - a) dρ < ∞`, i.e. to
`Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`. Mathlib has no polar-coordinates
change of variables in this generality; the layer-cake formula
(`MeasureTheory.lintegral_eq_lintegral_meas_lt`) together with `Measure.addHaar_ball` is the
route that avoids needing one. -/
theorem lintegral_ball_rpow_neg_lt_top [Nontrivial E] (x : E) {r a : ℝ} (hr : 0 < r)
    (ha : 0 ≤ a) (han : a < finrank ℝ E) :
    (∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ) < ⊤ := by
  sorry

/-- The value of the integral in `lintegral_ball_rpow_neg_lt_top`, as a constant depending
only on `E`, `μ` and the exponents. Keeping it named, rather than existential, is what lets
the constants in the main statements below be written down explicitly. -/
noncomputable irreducible_def rieszKernelConst [Nontrivial E] (a : ℝ) (r : ℝ) : ℝ≥0 :=
  ((finrank ℝ E : ℝ) / (finrank ℝ E - a)).toNNReal *
    (μ (ball (0 : E) 1)).toNNReal * r.toNNReal ^ (finrank ℝ E - a)

end RieszKernel

section Potential

/-- **The Riesz potential estimate.**

For `u` of class `C¹`, the mean oscillation of `u` on a ball is controlled by the Riesz
potential of its derivative:
`∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ ≤ C * r ^ n * (Riesz potential of the derivative)`.

*To prove:* write `u y - u x = ∫_0^1 (fderiv ℝ u (x + t (y - x))) (y - x) dt` and integrate
over the ball, exchanging the order of integration. Mathlib has the one-dimensional
fundamental theorem of calculus along a segment
(`Convex.inner_smul_le_norm_mul_norm`-adjacent API, and
`MeasureTheory.integral_comp_smul_deriv`), and `Measure.addHaar_ball` for the scaling. -/
theorem lintegral_ball_enorm_sub_le_lintegral_riesz [Nontrivial E]
    {u : E → F} (hu : ContDiff ℝ 1 u) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ) ≤
      rieszKernelConst μ 0 r *
        ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ := by
  sorry

end Potential

section Morrey

variable (E) in
/-- The constant in the Hölder estimate of Morrey's inequality. It depends only on `E`, `μ`
and `p`. -/
noncomputable irreducible_def morreyConst [Nontrivial E] (p : ℝ≥0) : ℝ≥0 :=
  let n : ℝ := finrank ℝ E
  let q : ℝ := (1 - 1 / p)⁻¹          -- the conjugate exponent of `p`
  2 * rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q) * (μ (ball (0 : E) 1)).toNNReal

/-- **Morrey's inequality, Hölder form.**

Let `u` be a continuously differentiable function on a normed space `E` of finite dimension
`n`, equipped with a Haar measure, and let `finrank ℝ E < p`. Then `u` is Hölder continuous
of exponent `1 - n / p`, with seminorm bounded by the `Lᵖ` norm of its derivative.

This is the supercritical counterpart of `MeasureTheory.eLpNorm_le_eLpNorm_fderiv`, whose
hypothesis is `p < finrank ℝ E`. -/
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
  sorry

end Morrey

end MeasureTheory
