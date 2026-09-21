import MorseFloer.Part2.CauchyHolder

/-!
# A mean value inequality for almost holomorphic functions

A helper for Proposition 6.6.2 of Audin–Damian.  A holomorphic function is the average of its
values on a disc.  For a `C¹` function `P` that is only *almost* holomorphic — its `∂̄` is
bounded by `a` on the disc of radius `r` about `z₁` — the same holds up to an error:

`‖P z₁‖ ≤ K₀ r⁻² ∫_{|ξ| < r} ‖P (z₁ - ξ)‖ + K₂ a r`,

with universal constants `K₀`, `K₂` (`norm_le_of_dbar_le`).  The proof is the Cauchy–Pompeiu
formula of `Part2/CauchyPompeiu.lean` applied to `χ P`, where `χ` is a cut-off equal to `1`
near `z₁` and supported in the disc: `P z₁ = T(∂̄(χ P))(z₁)`, and
`∂̄(χ P) = χ ∂̄P + P ∂̄χ`.  The first term is integrated against the Riesz kernel `1/|ξ|`,
whose mass on the disc is proportional to `r`; the second lives on the annulus
`r/2 ≤ |ξ| ≤ 3r/4`, where the kernel is at most `2/r` and `|∂̄χ|` at most `K/r`.

This is what replaces the bubbling analysis on the torus: applied to `∂u/∂s`, which solves a
linear Cauchy–Riemann equation with bounded zeroth-order term, it bounds the gradient of a
Floer solution at the centre of a disc by its energy on the disc.
-/

open MeasureTheory Filter Topology Metric Set
open scoped Real ContDiff

namespace MorseFloer
namespace MeanValue

open CauchyPompeiu CauchyHolder

/-- The unit bump: one on the disc of radius `1/2`, zero outside the disc of radius `3/4`. -/
noncomputable def bump : ContDiffBump (0 : ℂ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

/-- The cut-off at scale `r` about `z₁`. -/
noncomputable def cut (z₁ : ℂ) (r : ℝ) (z : ℂ) : ℂ := ((bump ((r⁻¹ : ℝ) • (z - z₁)) : ℝ) : ℂ)

theorem contDiff_cut (z₁ : ℂ) (r : ℝ) : ContDiff ℝ ∞ (cut z₁ r) := by
  have hA : ContDiff ℝ ∞ fun z : ℂ => (r⁻¹ : ℝ) • (z - z₁) :=
    (contDiff_id.sub contDiff_const).const_smul _
  exact Complex.ofRealCLM.contDiff.comp (bump.contDiff.comp hA)

theorem norm_smul_sub (z₁ z : ℂ) {r : ℝ} (hr : 0 < r) :
    ‖(r⁻¹ : ℝ) • (z - z₁)‖ = ‖z - z₁‖ / r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), div_eq_inv_mul]

theorem cut_eq_one {z₁ z : ℂ} {r : ℝ} (hr : 0 < r) (h : ‖z - z₁‖ ≤ r / 2) : cut z₁ r z = 1 := by
  have hmem : (r⁻¹ : ℝ) • (z - z₁) ∈ closedBall (0 : ℂ) bump.rIn := by
    rw [mem_closedBall, dist_zero_right, norm_smul_sub z₁ z hr, div_le_iff₀ hr]
    show ‖z - z₁‖ ≤ 1 / 2 * r
    linarith
  rw [cut, bump.one_of_mem_closedBall hmem]
  simp

theorem cut_eq_zero {z₁ z : ℂ} {r : ℝ} (hr : 0 < r) (h : 3 / 4 * r ≤ ‖z - z₁‖) :
    cut z₁ r z = 0 := by
  have hle : bump.rOut ≤ dist ((r⁻¹ : ℝ) • (z - z₁)) 0 := by
    rw [dist_zero_right, norm_smul_sub z₁ z hr, le_div_iff₀ hr]
    exact h
  rw [cut, bump.zero_of_le_dist hle]
  simp

theorem norm_cut_le_one (z₁ : ℂ) (r : ℝ) (z : ℂ) : ‖cut z₁ r z‖ ≤ 1 := by
  rw [cut, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
  exact bump.le_one

theorem hasCompactSupport_cut (z₁ : ℂ) {r : ℝ} (hr : 0 < r) : HasCompactSupport (cut z₁ r) := by
  refine HasCompactSupport.intro (isCompact_closedBall z₁ r) fun z hz => ?_
  rw [mem_closedBall, not_le, dist_eq_norm] at hz
  exact cut_eq_zero hr (by linarith)

/-- Where a function is locally constant its `∂̄` vanishes. -/
theorem dbar_eq_zero_of_eventually_const {w : ℂ → ℂ} {c z : ℂ} (h : w =ᶠ[𝓝 z] fun _ => c) :
    dbar w z = 0 := by
  have : fderiv ℝ w z = 0 := by
    rw [h.fderiv_eq]
    exact fderiv_const_apply c
  rw [dbar, this]
  simp

/-- **The `∂̄` of the cut-off is `O(1/r)`.** -/
theorem exists_norm_dbar_cut_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z₁ : ℂ) (r : ℝ), 0 < r → ∀ z, ‖dbar (cut z₁ r) z‖ ≤ K / r := by
  have hχ : ContDiff ℝ ∞ fun z : ℂ => ((bump z : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hχc : HasCompactSupport fun z : ℂ => ((bump z : ℝ) : ℂ) :=
    bump.hasCompactSupport.comp_left Complex.ofReal_zero
  obtain ⟨C, hC⟩ := (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hχc.fderiv ℝ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨2 * C, by positivity, fun z₁ r hr z => ?_⟩
  have hA : HasFDerivAt (fun z : ℂ => (r⁻¹ : ℝ) • (z - z₁))
      ((r⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).sub_const z₁).const_smul (r⁻¹ : ℝ)
  have hχd : HasFDerivAt (fun z : ℂ => ((bump z : ℝ) : ℂ))
      (fderiv ℝ (fun z : ℂ => ((bump z : ℝ) : ℂ)) ((r⁻¹ : ℝ) • (z - z₁)))
      ((r⁻¹ : ℝ) • (z - z₁)) :=
    ((hχ.differentiable (by simp)) _).hasFDerivAt
  have hcomp := hχd.comp z hA
  have hcut : HasFDerivAt (cut z₁ r)
      ((fderiv ℝ (fun z : ℂ => ((bump z : ℝ) : ℂ)) ((r⁻¹ : ℝ) • (z - z₁))).comp
        ((r⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ)) z := hcomp
  have hv : ∀ v : ℂ, ‖fderiv ℝ (cut z₁ r) z v‖ ≤ C / r * ‖v‖ := by
    intro v
    rw [hcut.fderiv]
    show ‖fderiv ℝ (fun z : ℂ => ((bump z : ℝ) : ℂ)) ((r⁻¹ : ℝ) • (z - z₁))
      ((r⁻¹ : ℝ) • v)‖ ≤ C / r * ‖v‖
    calc ‖fderiv ℝ (fun z : ℂ => ((bump z : ℝ) : ℂ)) ((r⁻¹ : ℝ) • (z - z₁)) ((r⁻¹ : ℝ) • v)‖
        ≤ ‖fderiv ℝ (fun z : ℂ => ((bump z : ℝ) : ℂ)) ((r⁻¹ : ℝ) • (z - z₁))‖
            * ‖(r⁻¹ : ℝ) • v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * (r⁻¹ * ‖v‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
          exact mul_le_mul_of_nonneg_right (hC _) (by positivity)
      _ = C / r * ‖v‖ := by rw [div_eq_mul_inv]; ring
  have h1 := hv 1
  have hI := hv Complex.I
  rw [norm_one, mul_one] at h1
  rw [Complex.norm_I, mul_one] at hI
  calc ‖dbar (cut z₁ r) z‖
      ≤ ‖fderiv ℝ (cut z₁ r) z 1‖ + ‖Complex.I * fderiv ℝ (cut z₁ r) z Complex.I‖ :=
        norm_add_le _ _
    _ ≤ C / r + C / r := by
        rw [norm_mul, Complex.norm_I, one_mul]
        exact add_le_add h1 hI
    _ = 2 * C / r := by ring

/-- **The mean value inequality for almost holomorphic functions.** -/
theorem norm_le_of_dbar_le : ∃ K₀ K₂ : ℝ, 0 ≤ K₀ ∧ 0 ≤ K₂ ∧
    ∀ P : ℂ → ℂ, ContDiff ℝ 1 P → ∀ (z₁ : ℂ) (r a : ℝ), 0 < r →
      (∀ z ∈ ball z₁ r, ‖dbar P z‖ ≤ a) →
      ‖P z₁‖ ≤ K₀ / r ^ 2 * (∫ ξ in ball (0 : ℂ) r, ‖P (z₁ - ξ)‖) + K₂ * a * r := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_dbar_cut_le
  have hm0 : 0 ≤ ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(1 : ℝ)) :=
    setIntegral_nonneg measurableSet_ball fun ξ _ => Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨(2 * π)⁻¹ * (2 * K), (2 * π)⁻¹ * ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(1 : ℝ)),
    by positivity, by positivity, fun P hP z₁ r a hr ha => ?_⟩
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha z₁ (mem_ball_self hr))
  have hPd : Differentiable ℝ P := hP.differentiable one_ne_zero
  have hχ := contDiff_cut z₁ r
  have hχd : Differentiable ℝ (cut z₁ r) := hχ.differentiable (by simp)
  have hw1 : ContDiff ℝ 1 fun z => cut z₁ r z * P z := (hχ.of_le (by simp)).mul hP
  have hwc : HasCompactSupport fun z => cut z₁ r z * P z :=
    (hasCompactSupport_cut z₁ hr).mul_right
  -- the value at the centre, through the Cauchy transform
  have hval : P z₁ = cauchyTransform (dbar fun z => cut z₁ r z * P z) z₁ := by
    rw [cauchyTransform_dbar hw1 hwc]
    show P z₁ = cut z₁ r z₁ * P z₁
    rw [cut_eq_one hr (by rw [sub_self, norm_zero]; positivity), one_mul]
  -- the pointwise bound on the integrand
  have hpt : ∀ ξ : ℂ, ‖ξ‖⁻¹ * ‖dbar (fun z => cut z₁ r z * P z) (z₁ - ξ)‖
      ≤ (ball (0 : ℂ) r).indicator
          (fun ξ => a * ‖ξ‖ ^ (-(1 : ℝ)) + 2 * K / r ^ 2 * ‖P (z₁ - ξ)‖) ξ := by
    intro ξ
    have hdist : ‖z₁ - ξ - z₁‖ = ‖ξ‖ := by
      rw [sub_sub_cancel_left, norm_neg]
    by_cases hξ : ξ ∈ ball (0 : ℂ) r
    · rw [indicator_of_mem hξ]
      rw [mem_ball, dist_zero_right] at hξ
      have hζ : z₁ - ξ ∈ ball z₁ r := by
        rw [mem_ball, dist_eq_norm, hdist]
        exact hξ
      rw [dbar_mul hχd hPd, Real.rpow_neg_one]
      have hinv0 : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      -- the kernel against the `∂̄` of the cut-off
      have hker : ‖ξ‖⁻¹ * ‖dbar (cut z₁ r) (z₁ - ξ)‖ ≤ 2 * K / r ^ 2 := by
        rcases lt_or_ge ‖ξ‖ (r / 2) with hlt | hge
        · have hev : cut z₁ r =ᶠ[𝓝 (z₁ - ξ)] fun _ => (1 : ℂ) := by
            have hopen : IsOpen {z : ℂ | ‖z - z₁‖ < r / 2} :=
              isOpen_lt (by fun_prop) continuous_const
            filter_upwards [hopen.mem_nhds (show ‖z₁ - ξ - z₁‖ < r / 2 by rw [hdist]; exact hlt)]
              with z hz using cut_eq_one hr (le_of_lt hz)
          rw [dbar_eq_zero_of_eventually_const hev, norm_zero, mul_zero]
          positivity
        · have hξpos : 0 < ‖ξ‖ := lt_of_lt_of_le (by positivity) hge
          have h1 : ‖ξ‖⁻¹ ≤ 2 / r := by
            rw [inv_le_comm₀ hξpos (by positivity), inv_div]
            exact hge
          calc ‖ξ‖⁻¹ * ‖dbar (cut z₁ r) (z₁ - ξ)‖ ≤ 2 / r * (K / r) :=
                mul_le_mul h1 (hK z₁ r hr _) (norm_nonneg _) (by positivity)
            _ = 2 * K / r ^ 2 := by field_simp
      calc ‖ξ‖⁻¹ * ‖cut z₁ r (z₁ - ξ) * dbar P (z₁ - ξ) + P (z₁ - ξ) * dbar (cut z₁ r) (z₁ - ξ)‖
          ≤ ‖ξ‖⁻¹ * (1 * a + ‖P (z₁ - ξ)‖ * ‖dbar (cut z₁ r) (z₁ - ξ)‖) := by
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hinv0
            rw [norm_mul, norm_mul]
            exact add_le_add (mul_le_mul (norm_cut_le_one _ _ _) (ha _ hζ) (norm_nonneg _)
              zero_le_one) le_rfl
        _ = a * ‖ξ‖⁻¹ + (‖ξ‖⁻¹ * ‖dbar (cut z₁ r) (z₁ - ξ)‖) * ‖P (z₁ - ξ)‖ := by ring
        _ ≤ a * ‖ξ‖⁻¹ + 2 * K / r ^ 2 * ‖P (z₁ - ξ)‖ := by
            gcongr
    · rw [indicator_of_notMem hξ]
      rw [mem_ball, dist_zero_right, not_lt] at hξ
      have hev : (fun z => cut z₁ r z * P z) =ᶠ[𝓝 (z₁ - ξ)] fun _ => (0 : ℂ) := by
        have hopen : IsOpen {z : ℂ | 3 / 4 * r < ‖z - z₁‖} :=
          isOpen_lt continuous_const (by fun_prop)
        filter_upwards [hopen.mem_nhds
          (show 3 / 4 * r < ‖z₁ - ξ - z₁‖ by rw [hdist]; linarith)] with z hz
        rw [cut_eq_zero hr (le_of_lt hz), zero_mul]
      rw [dbar_eq_zero_of_eventually_const hev, norm_zero, mul_zero]
  -- integrate
  have hPc : Continuous fun ξ : ℂ => ‖P (z₁ - ξ)‖ :=
    (hP.continuous.comp (continuous_const.sub continuous_id)).norm
  have hPint : IntegrableOn (fun ξ : ℂ => ‖P (z₁ - ξ)‖) (ball (0 : ℂ) r) :=
    (hPc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set
      ball_subset_closedBall
  have hRint : IntegrableOn (fun ξ : ℂ => ‖ξ‖ ^ (-(1 : ℝ))) (ball (0 : ℂ) r) :=
    integrableOn_rpow_neg_ball (by norm_num)
  have hGint : IntegrableOn
      (fun ξ : ℂ => a * ‖ξ‖ ^ (-(1 : ℝ)) + 2 * K / r ^ 2 * ‖P (z₁ - ξ)‖) (ball (0 : ℂ) r) :=
    (hRint.const_mul a).add (hPint.const_mul _)
  have hint : ∫ ξ : ℂ, ‖ξ‖⁻¹ * ‖dbar (fun z => cut z₁ r z * P z) (z₁ - ξ)‖
      ≤ a * (r * ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(1 : ℝ)))
        + 2 * K / r ^ 2 * ∫ ξ in ball (0 : ℂ) r, ‖P (z₁ - ξ)‖ := by
    calc ∫ ξ : ℂ, ‖ξ‖⁻¹ * ‖dbar (fun z => cut z₁ r z * P z) (z₁ - ξ)‖
        ≤ ∫ ξ : ℂ, (ball (0 : ℂ) r).indicator
            (fun ξ => a * ‖ξ‖ ^ (-(1 : ℝ)) + 2 * K / r ^ 2 * ‖P (z₁ - ξ)‖) ξ :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun ξ => mul_nonneg (inv_nonneg.2 (norm_nonneg _))
              (norm_nonneg _))
            ((integrable_indicator_iff measurableSet_ball).2 hGint)
            (Eventually.of_forall hpt)
      _ = ∫ ξ in ball (0 : ℂ) r, (a * ‖ξ‖ ^ (-(1 : ℝ)) + 2 * K / r ^ 2 * ‖P (z₁ - ξ)‖) :=
          integral_indicator measurableSet_ball
      _ = a * (r * ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(1 : ℝ)))
            + 2 * K / r ^ 2 * ∫ ξ in ball (0 : ℂ) r, ‖P (z₁ - ξ)‖ := by
          rw [integral_add (hRint.const_mul a) (hPint.const_mul _), integral_const_mul,
            integral_const_mul, integral_rpow_neg_ball 1 hr]
          norm_num
  have h2π : (0 : ℝ) < (2 * π)⁻¹ := by positivity
  calc ‖P z₁‖ = ‖cauchyTransform (dbar fun z => cut z₁ r z * P z) z₁‖ := by rw [← hval]
    _ = (2 * π)⁻¹ * ‖∫ ξ : ℂ, (ξ⁻¹ : ℂ) • dbar (fun z => cut z₁ r z * P z) (z₁ - ξ)‖ := by
        rw [cauchyTransform, norm_smul, Real.norm_eq_abs, abs_of_pos h2π]
    _ ≤ (2 * π)⁻¹ * ∫ ξ : ℂ, ‖ξ‖⁻¹ * ‖dbar (fun z => cut z₁ r z * P z) (z₁ - ξ)‖ := by
        refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq ?_) h2π.le
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [norm_smul, norm_inv]
    _ ≤ (2 * π)⁻¹ * (a * (r * ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(1 : ℝ)))
          + 2 * K / r ^ 2 * ∫ ξ in ball (0 : ℂ) r, ‖P (z₁ - ξ)‖) :=
        mul_le_mul_of_nonneg_left hint h2π.le
    _ = (2 * π)⁻¹ * (2 * K) / r ^ 2 * (∫ ξ in ball (0 : ℂ) r, ‖P (z₁ - ξ)‖)
          + (2 * π)⁻¹ * (∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(1 : ℝ))) * a * r := by ring

end MeanValue
end MorseFloer
