import MorseFloer.Part2.CauchyPompeiu
import MorseFloer.Part2.Weyl

/-!
# The Cauchy transform of Hölder data

`Part2/CauchyPompeiu.lean` proves that for compactly supported `C¹` data the Cauchy transform
`T f` solves `∂(T f)/∂x + i ∂(T f)/∂y = f`, and that its other derivative is the Beurling
transform.  Schauder theory needs the same for merely Hölder data, and that is what this file
supplies, by mollification.

Mollification is well behaved on Hölder classes: it preserves the Hölder constant, and it
converges *uniformly*, at the Hölder rate `ε^α` — no measure-theoretic differentiation is
needed.  The Beurling transform is stable under such convergence, because the two-parameter
estimate splits it into a near part controlled by the Hölder constant, which is uniform, and a
far part controlled by the `L¹` norm, which goes to zero.  The Cauchy transform is stable for
the same reason, its kernel being locally integrable.  A uniform limit of derivatives is the
derivative of the limit, so the identities pass to the limit.

## Main results

* `norm_smooth_sub_le`: mollification of Hölder data converges uniformly at rate `ε^α`;
* `hasFDerivAt_cauchyTransform_holder`: for compactly supported Hölder data the Cauchy
  transform is differentiable, with the derivative given by `f` and the Beurling transform;
* `dbar_cauchyTransform_holder`, `dz_cauchyTransform_holder`: the two identities.
-/

open MeasureTheory Filter Topology Metric Set
open scoped Real ContDiff

namespace MorseFloer
namespace CauchyHolder

open CauchyPompeiu Weyl

/-! ### Mollification of Hölder data -/

variable {f : ℂ → ℂ} {C α : ℝ}

theorem integrable_moll_smul {ε : ℝ} (hε : 0 < ε) (hfc : Continuous f) (x : ℂ) :
    Integrable fun t : ℂ => moll ε t • f (x - t) := by
  have hcont : Continuous fun t : ℂ => moll ε t • f (x - t) :=
    (moll_continuous ε).smul (hfc.comp (continuous_const.sub continuous_id))
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_moll hε).smul_right

/-- **Mollification preserves the Hölder constant.** -/
theorem holder_smooth {ε : ℝ} (hε : 0 < ε) (hfc : Continuous f)
    (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (ξ η : ℂ) :
    ‖smooth ε f ξ - smooth ε f η‖ ≤ C * ‖ξ - η‖ ^ α := by
  have hC0 : 0 ≤ C := holder_const_nonneg hf
  have hpow : (0 : ℝ) ≤ C * ‖ξ - η‖ ^ α := mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg _) _)
  rw [smooth_apply, smooth_apply,
    ← integral_sub (integrable_moll_smul hε hfc ξ) (integrable_moll_smul hε hfc η)]
  have hpt : ∀ t : ℂ, ‖moll ε t • f (ξ - t) - moll ε t • f (η - t)‖
      ≤ moll ε t * (C * ‖ξ - η‖ ^ α) := by
    intro t
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (moll_nonneg hε t)]
    refine mul_le_mul_of_nonneg_left ?_ (moll_nonneg hε t)
    have h := hf (ξ - t) (η - t)
    have he : ξ - t - (η - t) = ξ - η := by ring
    rwa [he] at h
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (integral_mono
    ((integrable_moll_smul hε hfc ξ).sub (integrable_moll_smul hε hfc η)).norm
    ((integrable_moll hε).mul_const (C * ‖ξ - η‖ ^ α)) hpt) ?_
  rw [integral_mul_const, integral_moll hε, one_mul]

/-- **Mollification of Hölder data converges uniformly**, at the Hölder rate. -/
theorem norm_smooth_sub_le {ε : ℝ} (hε : 0 < ε) (hfc : Continuous f) (hα : 0 < α)
    (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (x : ℂ) :
    ‖smooth ε f x - f x‖ ≤ C * ε ^ α := by
  have hC0 : 0 ≤ C := holder_const_nonneg hf
  have hconst : f x = ∫ t : ℂ, moll ε t • f x := by
    rw [integral_smul_const, integral_moll hε, one_smul]
  rw [smooth_apply, hconst,
    ← integral_sub (integrable_moll_smul hε hfc x) ((integrable_moll hε).smul_const (f x))]
  have hpt : ∀ t : ℂ, ‖moll ε t • f (x - t) - moll ε t • f x‖ ≤ moll ε t * (C * ε ^ α) := by
    intro t
    by_cases ht : ‖t‖ < ε
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (moll_nonneg hε t)]
      refine mul_le_mul_of_nonneg_left ?_ (moll_nonneg hε t)
      have h := hf (x - t) x
      have he : x - t - x = -t := by ring
      rw [he, norm_neg] at h
      refine le_trans h (mul_le_mul_of_nonneg_left ?_ hC0)
      exact Real.rpow_le_rpow (norm_nonneg _) ht.le hα.le
    · rw [moll_eq_zero_of_le hε (not_lt.mp ht)]
      simp
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (integral_mono
    ((integrable_moll_smul hε hfc x).sub ((integrable_moll hε).smul_const (f x))).norm
    ((integrable_moll hε).mul_const (C * ε ^ α)) hpt) ?_
  rw [integral_mul_const, integral_moll hε, one_mul]

/-- Mollification enlarges the support by at most the mollification radius. -/
theorem smooth_eq_zero_of_le {ε R : ℝ} (hε : 0 < ε) (hR : ∀ ζ : ℂ, R ≤ ‖ζ‖ → f ζ = 0) {x : ℂ}
    (hx : R + ε ≤ ‖x‖) : smooth ε f x = 0 := by
  have hzero : (fun t : ℂ => moll ε t • f (x - t)) = fun _ => 0 := by
    funext t
    by_cases ht : ‖t‖ < ε
    · have h1 : R ≤ ‖x - t‖ := by
        have h2 := norm_sub_norm_le x t
        linarith
      rw [hR _ h1, smul_zero]
    · rw [moll_eq_zero_of_le hε (not_lt.mp ht), zero_smul]
  rw [smooth_apply, hzero, integral_zero]

theorem hasCompactSupport_smooth {ε R : ℝ} (hε : 0 < ε) (hR : ∀ ζ : ℂ, R ≤ ‖ζ‖ → f ζ = 0) :
    HasCompactSupport (smooth ε f) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + ε)) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hx
  exact smooth_eq_zero_of_le hε hR hx.le

/-! ### Stability of the two transforms -/

/-- The two-parameter bound for the Beurling transform, at an arbitrary cut-off radius. -/
theorem norm_beurling_le_of_radius {g : ℂ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hα : 0 < α) (hg : ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖beurling g z‖ ≤ C * ρ ^ α * (∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α)))
      + (ρ ^ 2)⁻¹ * ∫ ζ : ℂ, ‖g ζ‖ := by
  rw [← beurlingWith_eq hgc hgs hα hg z hρ]
  unfold beurlingWith
  exact le_trans (norm_add_le _ _)
    (add_le_add (norm_integral_beurling_near_le hgc hα hg z hρ)
      (norm_integral_beurling_far_le hgc hgs z hρ))

/-- The Cauchy transform is additive. -/
theorem cauchyTransform_sub {g h : ℂ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hhc : Continuous h) (hhs : HasCompactSupport h) (z : ℂ) :
    cauchyTransform (fun ζ => g ζ - h ζ) z = cauchyTransform g z - cauchyTransform h z := by
  unfold cauchyTransform
  rw [← smul_sub,
    ← integral_sub (integrable_inv_smul hgc hgs z) (integrable_inv_smul hhc hhs z)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [smul_sub]

/-- The Cauchy transform of a small, compactly supported function is small. -/
theorem norm_cauchyTransform_le {g : ℂ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {M R : ℝ} (hM : ∀ x : ℂ, ‖g x‖ ≤ M) (hR : ∀ ζ : ℂ, R ≤ ‖ζ‖ → g ζ = 0) (z : ℂ) :
    ‖cauchyTransform g z‖
      ≤ (2 * π)⁻¹ * (M * ∫ ξ in ball (0 : ℂ) (R + ‖z‖ + 1), ‖ξ‖⁻¹) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hint : Integrable fun ξ : ℂ => (ξ⁻¹ : ℂ) • g (z - ξ) := integrable_inv_smul hgc hgs z
  have hzero : ∀ ξ : ℂ, ξ ∉ ball (0 : ℂ) (R + ‖z‖ + 1) → ‖(ξ⁻¹ : ℂ) • g (z - ξ)‖ = 0 := by
    intro ξ hξ
    rw [mem_ball, dist_zero_right, not_lt] at hξ
    have h1 : R ≤ ‖z - ξ‖ := by
      have h2 := norm_sub_norm_le ξ z
      rw [norm_sub_rev] at h2
      linarith
    rw [hR _ h1, smul_zero, norm_zero]
  have hbound : ∀ ξ ∈ ball (0 : ℂ) (R + ‖z‖ + 1), ‖(ξ⁻¹ : ℂ) • g (z - ξ)‖ ≤ M * ‖ξ‖⁻¹ := by
    intro ξ _
    rw [norm_smul, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
  rw [cauchyTransform, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_integral_le_integral_norm _) ?_
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← integral_const_mul]
  exact setIntegral_mono_on hint.norm.integrableOn
    (integrableOn_inv_norm_ball.const_mul M) measurableSet_ball hbound

/-- The `L¹` size of a small function supported in a disc. -/
theorem integral_norm_sub_le {g h : ℂ → ℂ} {M R : ℝ} (hM : ∀ x : ℂ, ‖g x - h x‖ ≤ M)
    (hzero : ∀ ζ : ℂ, R ≤ ‖ζ‖ → g ζ - h ζ = 0) (hR0 : 0 ≤ R) :
    (∫ ζ : ℂ, ‖g ζ - h ζ‖) ≤ M * (π * R ^ 2) := by
  have hzero' : ∀ ζ : ℂ, ζ ∉ ball (0 : ℂ) R → ‖g ζ - h ζ‖ = 0 := by
    intro ζ hζ
    rw [mem_ball, dist_zero_right, not_lt] at hζ
    rw [hzero ζ hζ, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero']
  have hpt : ∀ ζ ∈ ball (0 : ℂ) R, ‖‖g ζ - h ζ‖‖ ≤ M := by
    intro ζ _
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hM ζ
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℂ))
    measure_ball_lt_top hpt
  have hvr : volume.real (ball (0 : ℂ) R) = π * R ^ 2 := by
    rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hR0, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  rw [hvr] at hbound
  exact le_trans (Real.le_norm_self _) hbound

/-! ### The general form of a real derivative on the plane -/

/-- The real-linear map `h ↦ (a h + b h̄)/2`.  Every real-linear map of the plane is of this
form, with `a` read off by `∂/∂x - i ∂/∂y` and `b` by `∂/∂x + i ∂/∂y`. -/
noncomputable def dPair (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  ((2 : ℂ)⁻¹ * a) • ContinuousLinearMap.id ℝ ℂ
    + ((2 : ℂ)⁻¹ * b) • (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap

@[simp]
theorem dPair_apply (a b h : ℂ) :
    dPair a b h = (a * h + b * (starRingEnd ℂ) h) / 2 := by
  simp [dPair]
  ring

theorem dPair_sub (a b a' b' : ℂ) : dPair a b - dPair a' b' = dPair (a - a') (b - b') := by
  ext h
  simp [dPair_apply]
  ring

theorem dPair_dz (a b : ℂ) : dPair a b 1 - Complex.I * dPair a b Complex.I = a := by
  simp [dPair_apply]
  linear_combination (b / 2 - a / 2) * Complex.I_sq

theorem dPair_dbar (a b : ℂ) : dPair a b 1 + Complex.I * dPair a b Complex.I = b := by
  simp [dPair_apply]
  linear_combination (a / 2 - b / 2) * Complex.I_sq

theorem norm_dPair_le (a b : ℂ) : ‖dPair a b‖ ≤ (‖a‖ + ‖b‖) / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [dPair_apply, norm_div, Complex.norm_ofNat]
  refine div_le_of_le_mul₀ (by norm_num) (by positivity) ?_
  calc ‖a * h + b * (starRingEnd ℂ) h‖ ≤ ‖a * h‖ + ‖b * (starRingEnd ℂ) h‖ := norm_add_le _ _
    _ = ‖a‖ * ‖h‖ + ‖b‖ * ‖h‖ := by rw [norm_mul, norm_mul, RCLike.norm_conj]
    _ = (‖a‖ + ‖b‖) / 2 * ‖h‖ * 2 := by ring

/-- **Every real-linear map of the plane splits into its two Wirtinger parts.** -/
theorem eq_dPair (T : ℂ →L[ℝ] ℂ) :
    T = dPair (T 1 - Complex.I * T Complex.I) (T 1 + Complex.I * T Complex.I) := by
  ext h
  have hT : T h = (h.re : ℝ) • T 1 + (h.im : ℝ) • T Complex.I := by
    have he : h = (h.re : ℝ) • (1 : ℂ) + (h.im : ℝ) • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    conv_lhs => rw [he]
    rw [map_add, map_smul, map_smul]
  have hconj : (starRingEnd ℂ) h = (h.re : ℂ) - (h.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [dPair_apply, hT, hconj, Complex.real_smul, Complex.real_smul]
  linear_combination ((T 1 - T Complex.I * Complex.I) / 2) * (Complex.re_add_im h)
    + ((h.im : ℂ) * T Complex.I) * Complex.I_sq

/-! ### The Cauchy transform of Hölder data -/

/-- **The Cauchy transform of compactly supported Hölder data is differentiable**, with the
derivative given by `f` in one Wirtinger direction and by the Beurling transform in the other.
The proof mollifies: the mollified data are `C¹`, keep the Hölder constant, and converge
uniformly, so both Wirtinger parts of the derivative converge uniformly, and a uniform limit of
derivatives is the derivative of the limit. -/
theorem hasFDerivAt_cauchyTransform_holder (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ) :
    HasFDerivAt (cauchyTransform f) (dPair (-(π⁻¹ : ℝ) • beurling f z) (f z)) z := by
  have hC0 : 0 ≤ C := holder_const_nonneg hf
  have hloc : LocallyIntegrable f := hfc.locallyIntegrable
  obtain ⟨R, hR0, hR⟩ := exists_radius hfs
  have hεn0 : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hεn1 : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hεnlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hεα : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1)) ^ α) atTop (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ α) 0 :=
      Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
    have h : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1)) ^ α) atTop (𝓝 ((0 : ℝ) ^ α)) :=
      hcont.tendsto.comp hεnlim
    rwa [Real.zero_rpow (ne_of_gt hα)] at h
  set fn : ℕ → ℂ → ℂ := fun n => smooth (1 / (n + 1)) f with hfndef
  have hfnC1 : ∀ n, ContDiff ℝ 1 (fn n) := fun n => smooth_contDiff (hεn0 n) hloc
  have hfnc : ∀ n, Continuous (fn n) := fun n => (hfnC1 n).continuous
  have hfnz : ∀ (n : ℕ) (ζ : ℂ), R + 1 ≤ ‖ζ‖ → fn n ζ = 0 := by
    intro n ζ hζ
    exact smooth_eq_zero_of_le (hεn0 n) (fun ξ h => (hR ξ h).1) (by linarith [hεn1 n])
  have hfns : ∀ n, HasCompactSupport (fn n) := by
    intro n
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) fun x hx => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hfnz n x hx.le
  have hfnh : ∀ (n : ℕ) (ξ η : ℂ), ‖fn n ξ - fn n η‖ ≤ C * ‖ξ - η‖ ^ α := fun n =>
    holder_smooth (hεn0 n) hfc hf
  have hfnsup : ∀ (n : ℕ) (x : ℂ), ‖fn n x - f x‖ ≤ C * ((1 : ℝ) / (n + 1)) ^ α := fun n x =>
    norm_smooth_sub_le (hεn0 n) hfc hα hf x
  have hdiffc : ∀ n, Continuous fun ζ => fn n ζ - f ζ := fun n => (hfnc n).sub hfc
  have hdiffs : ∀ n, HasCompactSupport fun ζ => fn n ζ - f ζ := fun n => (hfns n).sub hfs
  have hdiffh : ∀ (n : ℕ) (ξ η : ℂ),
      ‖fn n ξ - f ξ - (fn n η - f η)‖ ≤ 2 * C * ‖ξ - η‖ ^ α := by
    intro n ξ η
    have h1 := hfnh n ξ η
    have h2 := hf ξ η
    have he : fn n ξ - f ξ - (fn n η - f η) = fn n ξ - fn n η - (f ξ - f η) := by ring
    rw [he]
    calc ‖fn n ξ - fn n η - (f ξ - f η)‖ ≤ ‖fn n ξ - fn n η‖ + ‖f ξ - f η‖ := norm_sub_le _ _
      _ ≤ 2 * C * ‖ξ - η‖ ^ α := by linarith
  have hdiffzero : ∀ (n : ℕ) (ζ : ℂ), R + 1 ≤ ‖ζ‖ → fn n ζ - f ζ = 0 := by
    intro n ζ hζ
    rw [hfnz n ζ hζ, (hR ζ (by linarith)).1, sub_zero]
  have hL1 : ∀ n : ℕ, (∫ ζ : ℂ, ‖fn n ζ - f ζ‖)
      ≤ (C * ((1 : ℝ) / (n + 1)) ^ α) * (π * (R + 1) ^ 2) := fun n =>
    integral_norm_sub_le (fun x => hfnsup n x) (hdiffzero n) (by linarith)
  set Mass : ℝ := ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α)) with hMassdef
  have hMass0 : (0 : ℝ) ≤ Mass :=
    integral_nonneg fun ξ => Real.rpow_nonneg (norm_nonneg _) _
  have hBdiff : ∀ (n : ℕ) (x : ℂ) (ρ : ℝ), 0 < ρ →
      ‖beurling (fn n) x - beurling f x‖
        ≤ 2 * C * ρ ^ α * Mass
          + (ρ ^ 2)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α) * (π * (R + 1) ^ 2)) := by
    intro n x ρ hρ
    have hsub : beurling (fun ζ => fn n ζ - f ζ) x = beurling (fn n) x - beurling f x :=
      beurling_sub (hfnc n) (hfns n) hα (hfnh n) hfc hfs hf x
    rw [← hsub]
    refine le_trans (norm_beurling_le_of_radius (hdiffc n) (hdiffs n) hα (hdiffh n) x hρ) ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hL1 n) (by positivity))
  -- the derivatives of the mollified transforms
  have hTn : ∀ (n : ℕ) (x : ℂ), HasFDerivAt (cauchyTransform (fn n))
      (dPair (-(π⁻¹ : ℝ) • beurling (fn n) x) (fn n x)) x := by
    intro n x
    have h := hasFDerivAt_cauchyTransform (hfnC1 n) (hfns n) x
    have hd : HasFDerivAt (cauchyTransform (fn n))
        (fderiv ℝ (cauchyTransform (fn n)) x) x := h.differentiableAt.hasFDerivAt
    have heq : fderiv ℝ (cauchyTransform (fn n)) x
        = dPair (-(π⁻¹ : ℝ) • beurling (fn n) x) (fn n x) := by
      conv_lhs => rw [eq_dPair (fderiv ℝ (cauchyTransform (fn n)) x)]
      congr 1
      · exact dz_cauchyTransform_eq_beurling (hfnC1 n) (hfns n) x
      · exact dbar_cauchyTransform (hfnC1 n) (hfns n) x
    rwa [heq] at hd
  -- the derivatives converge uniformly
  have hunif : TendstoUniformly
      (fun (n : ℕ) (x : ℂ) => dPair (-(π⁻¹ : ℝ) • beurling (fn n) x) (fn n x))
      (fun x => dPair (-(π⁻¹ : ℝ) • beurling f x) (f x)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    set K : ℝ := π⁻¹ * (2 * C * Mass) with hKdef
    have hK0 : (0 : ℝ) ≤ K := by
      rw [hKdef]
      exact mul_nonneg (by positivity) (mul_nonneg (by linarith) hMass0)
    have hK1 : (0 : ℝ) < 4 * (K + 1) := by linarith
    set t : ℝ := δ / (4 * (K + 1)) with htdef
    have ht0 : (0 : ℝ) < t := div_pos hδ hK1
    obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ π⁻¹ * (2 * C * ρ ^ α * Mass) < δ / 2 := by
      refine ⟨t ^ (α⁻¹), Real.rpow_pos_of_pos ht0 _, ?_⟩
      have hrw : π⁻¹ * (2 * C * (t ^ α⁻¹) ^ α * Mass) = K * ((t ^ α⁻¹) ^ α) := by
        rw [hKdef]; ring
      rw [hrw, Real.rpow_inv_rpow ht0.le (ne_of_gt hα)]
      have ht4 : (K + 1) * t = δ / 4 := by
        rw [htdef]
        field_simp
      have h1 : K * t ≤ δ / 4 := by
        rw [← ht4]
        exact mul_le_mul_of_nonneg_right (by linarith) ht0.le
      linarith
    have hfin : Tendsto (fun n : ℕ =>
        π⁻¹ * ((ρ ^ 2)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α) * (π * (R + 1) ^ 2)))
          + C * ((1 : ℝ) / (n + 1)) ^ α) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => C * ((1 : ℝ) / (n + 1)) ^ α) atTop (𝓝 0) := by
        simpa using hεα.const_mul C
      have h2 : Tendsto (fun n : ℕ =>
          π⁻¹ * ((ρ ^ 2)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α) * (π * (R + 1) ^ 2)))) atTop
          (𝓝 0) := by
        simpa using ((h1.mul_const (π * (R + 1) ^ 2)).const_mul ((ρ ^ 2)⁻¹)).const_mul π⁻¹
      simpa using h2.add h1
    filter_upwards [hfin.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by linarith))] with n hn x
    have hdist : dist (dPair (-(π⁻¹ : ℝ) • beurling f x) (f x))
        (dPair (-(π⁻¹ : ℝ) • beurling (fn n) x) (fn n x))
        ≤ (‖-(π⁻¹ : ℝ) • beurling f x - -(π⁻¹ : ℝ) • beurling (fn n) x‖
            + ‖f x - fn n x‖) / 2 := by
      rw [dist_eq_norm, dPair_sub]
      exact norm_dPair_le _ _
    have hb1 : ‖-(π⁻¹ : ℝ) • beurling f x - -(π⁻¹ : ℝ) • beurling (fn n) x‖
        = π⁻¹ * ‖beurling (fn n) x - beurling f x‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ π⁻¹), norm_sub_rev]
    have hb2 : ‖f x - fn n x‖ = ‖fn n x - f x‖ := norm_sub_rev _ _
    have hb3 := hBdiff n x ρ hρ0
    have hb4 := hfnsup n x
    have hπ0 : (0 : ℝ) ≤ π⁻¹ := by positivity
    refine lt_of_le_of_lt hdist ?_
    rw [hb1, hb2]
    have hb5 : π⁻¹ * ‖beurling (fn n) x - beurling f x‖
        ≤ π⁻¹ * (2 * C * ρ ^ α * Mass
          + (ρ ^ 2)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α) * (π * (R + 1) ^ 2))) :=
      mul_le_mul_of_nonneg_left hb3 hπ0
    have hexp : π⁻¹ * (2 * C * ρ ^ α * Mass
        + (ρ ^ 2)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α) * (π * (R + 1) ^ 2)))
        = π⁻¹ * (2 * C * ρ ^ α * Mass)
          + π⁻¹ * ((ρ ^ 2)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α) * (π * (R + 1) ^ 2))) := by
      ring
    rw [hexp] at hb5
    linarith
  -- the transforms converge pointwise
  have hpt : ∀ x : ℂ,
      Tendsto (fun n => cauchyTransform (fn n) x) atTop (𝓝 (cauchyTransform f x)) := by
    intro x
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hb : ∀ n : ℕ, ‖cauchyTransform (fn n) x - cauchyTransform f x‖
        ≤ (2 * π)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α)
          * ∫ ξ in ball (0 : ℂ) (R + 1 + ‖x‖ + 1), ‖ξ‖⁻¹) := by
      intro n
      rw [← cauchyTransform_sub (hfnc n) (hfns n) hfc hfs x]
      exact norm_cauchyTransform_le (hdiffc n) (hdiffs n) (fun y => hfnsup n y) (hdiffzero n) x
    have hlim : Tendsto (fun n : ℕ => (2 * π)⁻¹ * ((C * ((1 : ℝ) / (n + 1)) ^ α)
        * ∫ ξ in ball (0 : ℂ) (R + 1 + ‖x‖ + 1), ‖ξ‖⁻¹)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => C * ((1 : ℝ) / (n + 1)) ^ α) atTop (𝓝 0) := by
        simpa using hεα.const_mul C
      simpa using
        ((h1.mul_const (∫ ξ in ball (0 : ℂ) (R + 1 + ‖x‖ + 1), ‖ξ‖⁻¹)).const_mul ((2 * π)⁻¹))
    exact squeeze_zero (fun n => norm_nonneg _) hb hlim
  exact hasFDerivAt_of_tendstoUniformly hunif hTn hpt z

/-- **The Cauchy transform solves the inhomogeneous equation for Hölder data.** -/
theorem dbar_cauchyTransform_holder (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ) :
    dbar (cauchyTransform f) z = f z := by
  rw [dbar, (hasFDerivAt_cauchyTransform_holder hfc hfs hα hf z).fderiv]
  exact dPair_dbar _ _

/-- **The other derivative of the Cauchy transform of Hölder data is the Beurling
transform.** -/
theorem dz_cauchyTransform_holder (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ) :
    dz (cauchyTransform f) z = -(π⁻¹ : ℝ) • beurling f z := by
  rw [dz, (hasFDerivAt_cauchyTransform_holder hfc hfs hα hf z).fderiv]
  exact dPair_dz _ _

/-- **The Schauder estimate for the solution operator.**  For compactly supported `C^{0,α}` data
with `0 < α < 1`, the derivative of the Cauchy transform is itself `C^{0,α}`: one Wirtinger part
is `f`, the other is the Beurling transform, and the Calderón–Zygmund estimate controls it.  So
the solution operator of the inhomogeneous Cauchy–Riemann equation gains a full derivative
without losing the Hölder exponent. -/
theorem holder_fderiv_cauchyTransform (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hα : 0 < α) (hα1 : α < 1) (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z₁ z₂ : ℂ) :
    ‖fderiv ℝ (cauchyTransform f) z₁ - fderiv ℝ (cauchyTransform f) z₂‖
      ≤ (π⁻¹ * (4 * (∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α))) + 14 * π
            + 10 * (∫ ξ in (ball (0 : ℂ) 1)ᶜ, ‖ξ‖ ^ (-(3 - α)))) + 1) * C / 2
          * ‖z₁ - z₂‖ ^ α := by
  have hπ0 : (0 : ℝ) ≤ π⁻¹ := by positivity
  rw [(hasFDerivAt_cauchyTransform_holder hfc hfs hα hf z₁).fderiv,
    (hasFDerivAt_cauchyTransform_holder hfc hfs hα hf z₂).fderiv, dPair_sub]
  refine le_trans (norm_dPair_le _ _) ?_
  have hb1 : ‖-(π⁻¹ : ℝ) • beurling f z₁ - -(π⁻¹ : ℝ) • beurling f z₂‖
      = π⁻¹ * ‖beurling f z₁ - beurling f z₂‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hπ0]
  have hb2 := mul_le_mul_of_nonneg_left
    (norm_beurling_sub_le_holder hfc hfs hα hα1 hf z₁ z₂) hπ0
  have hb3 := hf z₁ z₂
  rw [hb1]
  linarith

/-! ### The Hölder scale

The Schauder estimate above is the case `k = 0` of `C^{k,α} → C^{k+1,α}`.  To run the induction
on `k` without the bookkeeping of iterated multilinear derivatives, the scale is defined
recursively through directional derivatives: one step up means "differentiable, with every
directional derivative one step lower".  That is the same scale, and it is exactly what the
induction consumes, since the first derivative of `T f` is a fixed linear combination of `f`
and of `T (∂f/∂z)`, and `∂f/∂z` sits one step lower.
-/

/-- `IsHolderC k α C f`: the function `f` is `k` times differentiable and each of its `k`-th
directional derivatives, in directions of norm at most one, is `α`-Hölder with constant `C`. -/
def IsHolderC : ℕ → ℝ → ℝ → (ℂ → ℂ) → Prop
  | 0, α, C, f => ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α
  | (k + 1), α, C, f =>
      Differentiable ℝ f ∧ ∀ v : ℂ, ‖v‖ ≤ 1 → IsHolderC k α C fun z => fderiv ℝ f z v

theorem isHolderC_zero_iff {α C : ℝ} {f : ℂ → ℂ} :
    IsHolderC 0 α C f ↔ ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α := Iff.rfl

theorem isHolderC_succ_iff {k : ℕ} {α C : ℝ} {f : ℂ → ℂ} :
    IsHolderC (k + 1) α C f
      ↔ Differentiable ℝ f ∧ ∀ v : ℂ, ‖v‖ ≤ 1 → IsHolderC k α C fun z => fderiv ℝ f z v :=
  Iff.rfl

/-- A Hölder function is continuous. -/
theorem continuous_of_holder {g : ℂ → ℂ} (hα : 0 < α)
    (hg : ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ C * ‖ξ - η‖ ^ α) : Continuous g := by
  have hC0 : 0 ≤ C := holder_const_nonneg hg
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine Metric.continuous_iff.2 fun b ε hε => ?_
  refine ⟨(ε / (C + 1)) ^ (α⁻¹), Real.rpow_pos_of_pos (div_pos hε hC1) _, fun a hab => ?_⟩
  rw [dist_eq_norm] at hab ⊢
  refine lt_of_le_of_lt (hg a b) ?_
  have h1 : ‖a - b‖ ^ α ≤ ((ε / (C + 1)) ^ (α⁻¹)) ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) hab.le hα.le
  rw [Real.rpow_inv_rpow (div_pos hε hC1).le (ne_of_gt hα)] at h1
  calc C * ‖a - b‖ ^ α ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hC1]
        nlinarith

theorem IsHolderC.continuous {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (hα : 0 < α)
    (h : IsHolderC k α C' g) : Continuous g := by
  cases k with
  | zero => exact continuous_of_holder hα h
  | succ k => exact h.1.continuous

theorem IsHolderC.mono {k : ℕ} {C₁ C₂ : ℝ} {g : ℂ → ℂ} (h : IsHolderC k α C₁ g)
    (hC : C₁ ≤ C₂) : IsHolderC k α C₂ g := by
  induction k generalizing g with
  | zero =>
      intro ξ η
      refine le_trans (h ξ η) ?_
      exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (norm_nonneg _) _)
  | succ k ih => exact ⟨h.1, fun v hv => ih (h.2 v hv)⟩

theorem IsHolderC.const_mul {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (a : ℂ) (h : IsHolderC k α C' g) :
    IsHolderC k α (‖a‖ * C') fun z => a * g z := by
  induction k generalizing g with
  | zero =>
      intro ξ η
      have h1 : a * g ξ - a * g η = a * (g ξ - g η) := by ring
      rw [h1, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h ξ η) (norm_nonneg a)
  | succ k ih =>
      refine ⟨fun z => (h.1 z).const_mul a, fun v hv => ?_⟩
      have hfun : (fun z => fderiv ℝ (fun z => a * g z) z v) = fun z => a * fderiv ℝ g z v := by
        funext z
        rw [((h.1 z).hasFDerivAt.const_mul a).fderiv]
        simp
      rw [hfun]
      exact ih (h.2 v hv)

theorem IsHolderC.add {k : ℕ} {C₁ C₂ : ℝ} {g h : ℂ → ℂ} (hg : IsHolderC k α C₁ g)
    (hh : IsHolderC k α C₂ h) : IsHolderC k α (C₁ + C₂) fun z => g z + h z := by
  induction k generalizing g h with
  | zero =>
      intro ξ η
      have h1 : g ξ + h ξ - (g η + h η) = g ξ - g η + (h ξ - h η) := by ring
      rw [h1]
      refine le_trans (norm_add_le _ _) ?_
      have := hg ξ η
      have := hh ξ η
      nlinarith [Real.rpow_nonneg (norm_nonneg (ξ - η)) α]
  | succ k ih =>
      refine ⟨fun z => (hg.1 z).add (hh.1 z), fun v hv => ?_⟩
      have hfun : (fun z => fderiv ℝ (fun z => g z + h z) z v)
          = fun z => fderiv ℝ g z v + fderiv ℝ h z v := by
        funext z
        have h2 : fderiv ℝ (fun z => g z + h z) z = fderiv ℝ g z + fderiv ℝ h z :=
          ((hg.1 z).hasFDerivAt.add (hh.1 z).hasFDerivAt).fderiv
        rw [h2]
        simp
      rw [hfun]
      exact ih (hg.2 v hv) (hh.2 v hv)

/-- The pairing of the two Wirtinger parts is Lipschitz, hence continuous. -/
theorem continuous_dPair : Continuous fun p : ℂ × ℂ => dPair p.1 p.2 := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun p q => ?_)
  rw [dist_eq_norm, dPair_sub, NNReal.coe_one, one_mul, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
  refine le_trans (norm_dPair_le _ _) ?_
  have h1 : ‖p.1 - q.1‖ ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := le_max_left _ _
  have h2 : ‖p.2 - q.2‖ ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := le_max_right _ _
  linarith

set_option maxHeartbeats 1000000 in
/-- One step up the scale means continuously differentiable. -/
theorem IsHolderC.contDiff_one {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (hα : 0 < α)
    (h : IsHolderC (k + 1) α C' g) : ContDiff ℝ 1 g := by
  have h1 : Continuous fun z => fderiv ℝ g z 1 :=
    (h.2 1 (by simp)).continuous hα
  have hI : Continuous fun z => fderiv ℝ g z Complex.I :=
    (h.2 Complex.I (by simp)).continuous hα
  have hpair : Continuous fun z : ℂ => ((fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I),
      (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I)) :=
    (h1.sub (continuous_const.mul hI)).prodMk (h1.add (continuous_const.mul hI))
  have hcont : Continuous fun z : ℂ =>
      dPair (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I)
        (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) := continuous_dPair.comp hpair
  have heq : fderiv ℝ g
      = fun z => dPair (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I)
        (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) := by
    funext z
    exact eq_dPair (fderiv ℝ g z)
  exact contDiff_one_iff_fderiv.2 ⟨h.1, by rw [heq]; exact hcont⟩

/-- A continuously differentiable function with compact support is Hölder of every exponent
at most one. -/
theorem exists_holder_of_contDiff_one {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgs : HasCompactSupport g) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C' : ℝ, ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ C' * ‖ξ - η‖ ^ α := by
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨L, hL⟩ := (hgs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hfd
  obtain ⟨M, hM⟩ := hgs.exists_bound_of_continuous hg.continuous
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hlip : ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ L * ‖ξ - η‖ := fun ξ η =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x) (fun x _ => hL x)
      convex_univ (mem_univ η) (mem_univ ξ)
  refine ⟨L + 2 * M, fun ξ η => ?_⟩
  have hpow : (0 : ℝ) ≤ ‖ξ - η‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hd : ‖ξ - η‖ ≤ 1
  · have h1 : ‖ξ - η‖ ≤ ‖ξ - η‖ ^ α := by
      rcases eq_or_lt_of_le (norm_nonneg (ξ - η)) with h0 | h0
      · rw [← h0, Real.zero_rpow (ne_of_gt hα)]
      · calc ‖ξ - η‖ = ‖ξ - η‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ ‖ξ - η‖ ^ α := Real.rpow_le_rpow_of_exponent_ge h0 hd hα1
    calc ‖g ξ - g η‖ ≤ L * ‖ξ - η‖ := hlip ξ η
      _ ≤ L * ‖ξ - η‖ ^ α := mul_le_mul_of_nonneg_left h1 hL0
      _ ≤ (L + 2 * M) * ‖ξ - η‖ ^ α := by nlinarith
  · have h1 : (1 : ℝ) ≤ ‖ξ - η‖ ^ α := by
      have h2 : (1 : ℝ) ≤ ‖ξ - η‖ := le_of_lt (not_le.mp hd)
      calc (1 : ℝ) = (1 : ℝ) ^ α := (Real.one_rpow α).symm
        _ ≤ ‖ξ - η‖ ^ α := Real.rpow_le_rpow zero_le_one h2 hα.le
    calc ‖g ξ - g η‖ ≤ ‖g ξ‖ + ‖g η‖ := norm_sub_le _ _
      _ ≤ 2 * M := by have := hM ξ; have := hM η; linarith
      _ ≤ (L + 2 * M) * ‖ξ - η‖ ^ α := by nlinarith

/-- The `∂/∂z` of a function sits one step lower on the scale. -/
theorem isHolderC_dz {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (h : IsHolderC (k + 1) α C' g) :
    IsHolderC k α (2 * C') (dz g) := by
  have h1 : IsHolderC k α C' fun z => fderiv ℝ g z 1 := h.2 1 (by simp)
  have hI := IsHolderC.const_mul (-Complex.I) (h.2 Complex.I (by simp))
  have hsum := h1.add hI
  have heq : (fun z => fderiv ℝ g z 1 + -Complex.I * fderiv ℝ g z Complex.I) = dz g := by
    funext z
    rw [dz]
    ring
  rw [heq] at hsum
  refine hsum.mono ?_
  rw [norm_neg, Complex.norm_I]
  linarith

theorem IsHolderC.const_nonneg {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (h : IsHolderC k α C' g) :
    0 ≤ C' := by
  induction k generalizing g with
  | zero => exact holder_const_nonneg h
  | succ k ih => exact ih (h.2 1 (by simp))

/-- **The Schauder scale for the solution operator.**  For every `k`, the Cauchy transform takes
compactly supported `C^{k,α}` data to `C^{k+1,α}` functions, with `0 < α < 1`.

The induction is on `k`, and the step is short because of the two identities already proved:
the first derivative of `T f` in a direction `v` is the fixed linear combination
`(v/2) T(∂f/∂z) + (v̄/2) f`, in which `∂f/∂z` sits one step lower on the scale, so the induction
hypothesis applies to it, and `f` itself sits at the right level already. -/
theorem isHolderC_cauchyTransform (hα : 0 < α) (hα1 : α < 1) :
    ∀ (k : ℕ) (g : ℂ → ℂ) (C' : ℝ), HasCompactSupport g → IsHolderC k α C' g →
      ∃ C'' : ℝ, 0 ≤ C'' ∧ IsHolderC (k + 1) α C'' (cauchyTransform g) := by
  intro k
  induction k with
  | zero =>
      intro g C' hgs hg
      have hgc : Continuous g := continuous_of_holder hα hg
      have hC'0 : 0 ≤ C' := holder_const_nonneg hg
      have hMass0 : (0 : ℝ) ≤ ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α)) :=
        integral_nonneg fun ξ => Real.rpow_nonneg (norm_nonneg _) _
      have hTail0 : (0 : ℝ) ≤ ∫ ξ in (ball (0 : ℂ) 1)ᶜ, ‖ξ‖ ^ (-(3 - α)) :=
        integral_nonneg fun ξ => Real.rpow_nonneg (norm_nonneg _) _
      refine ⟨(π⁻¹ * (4 * (∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α))) + 14 * π
          + 10 * (∫ ξ in (ball (0 : ℂ) 1)ᶜ, ‖ξ‖ ^ (-(3 - α)))) + 1) * C' / 2, ?_, ?_, ?_⟩
      · have hπ : (0 : ℝ) < π := Real.pi_pos
        have h1 : (0 : ℝ) ≤ π⁻¹ * (4 * (∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α))) + 14 * π
            + 10 * (∫ ξ in (ball (0 : ℂ) 1)ᶜ, ‖ξ‖ ^ (-(3 - α)))) := by
          refine mul_nonneg (by positivity) ?_
          nlinarith
        nlinarith
      · exact fun z => (hasFDerivAt_cauchyTransform_holder hgc hgs hα hg z).differentiableAt
      · intro v hv ξ η
        have h1 : fderiv ℝ (cauchyTransform g) ξ v - fderiv ℝ (cauchyTransform g) η v
            = (fderiv ℝ (cauchyTransform g) ξ - fderiv ℝ (cauchyTransform g) η) v := rfl
        rw [h1]
        have h2 := (fderiv ℝ (cauchyTransform g) ξ
          - fderiv ℝ (cauchyTransform g) η).le_opNorm v
        have h3 := holder_fderiv_cauchyTransform hgc hgs hα hα1 hg ξ η
        have h4 : (0 : ℝ) ≤ ‖fderiv ℝ (cauchyTransform g) ξ - fderiv ℝ (cauchyTransform g) η‖ :=
          norm_nonneg _
        nlinarith [norm_nonneg v]
  | succ k ih =>
      intro g C' hgs hg
      have hC'0 : 0 ≤ C' := hg.const_nonneg
      have hgC1 : ContDiff ℝ 1 g := hg.contDiff_one hα
      have hgc : Continuous g := hgC1.continuous
      obtain ⟨Cg, hCg⟩ := exists_holder_of_contDiff_one hgC1 hgs hα hα1.le
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih (dz g) (2 * C') (hasCompactSupport_dz hgs) (isHolderC_dz hg)
      have hfderiv : ∀ z v : ℂ, fderiv ℝ (cauchyTransform g) z v
          = v / 2 * cauchyTransform (dz g) z + (starRingEnd ℂ) v / 2 * g z := by
        intro z v
        rw [(hasFDerivAt_cauchyTransform_holder hgc hgs hα hCg z).fderiv, dPair_apply]
        have hb : -(π⁻¹ : ℝ) • beurling g z = cauchyTransform (dz g) z := by
          rw [← dz_cauchyTransform_eq_beurling hgC1 hgs z, dz_cauchyTransform hgC1 hgs z]
        rw [hb]
        ring
      refine ⟨(C₂ + C') / 2, by linarith, ?_, fun v hv => ?_⟩
      · exact fun z => (hasFDerivAt_cauchyTransform_holder hgc hgs hα hCg z).differentiableAt
      · have hfun : (fun z => fderiv ℝ (cauchyTransform g) z v)
            = fun z => v / 2 * cauchyTransform (dz g) z + (starRingEnd ℂ) v / 2 * g z := by
          funext z
          exact hfderiv z v
        rw [hfun]
        have h1 := IsHolderC.const_mul (v / 2) hC₂
        have h2 := IsHolderC.const_mul ((starRingEnd ℂ) v / 2) hg
        refine (h1.add h2).mono ?_
        have hv2 : ‖v / 2‖ ≤ 1 / 2 := by
          rw [norm_div, Complex.norm_ofNat]
          linarith
        have hcv2 : ‖(starRingEnd ℂ) v / 2‖ ≤ 1 / 2 := by
          rw [norm_div, RCLike.norm_conj, Complex.norm_ofNat]
          linarith
        nlinarith [norm_nonneg (v / 2), norm_nonneg ((starRingEnd ℂ) v / 2)]

/-- A function on the Hölder scale is continuously differentiable to the matching order: the
scale defined here is the usual one. -/
theorem IsHolderC.contDiff {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (hα : 0 < α)
    (h : IsHolderC k α C' g) : ContDiff ℝ k g := by
  induction k generalizing g with
  | zero => exact contDiff_zero.2 (h.continuous hα)
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hcast]
      refine contDiff_succ_iff_fderiv_apply.2
        ⟨h.1, fun hc => absurd hc (by norm_num), fun y => ?_⟩
      have h1 : ContDiff ℝ k fun z => fderiv ℝ g z 1 := ih (h.2 1 (by simp))
      have hI : ContDiff ℝ k fun z => fderiv ℝ g z Complex.I := ih (h.2 Complex.I (by simp))
      have hy : (fun z => fderiv ℝ g z y)
          = fun z => (y.re : ℝ) • fderiv ℝ g z 1 + (y.im : ℝ) • fderiv ℝ g z Complex.I := by
        funext z
        have he : y = (y.re : ℝ) • (1 : ℂ) + (y.im : ℝ) • Complex.I := by
          simp [Complex.real_smul, Complex.re_add_im]
        conv_lhs => rw [he]
        rw [map_add, map_smul, map_smul]
      rw [hy]
      exact (h1.const_smul (y.re : ℝ)).add (hI.const_smul (y.im : ℝ))

/-- **The Cauchy transform gains a derivative on every level of the Hölder scale.**  This is the
Schauder estimate `C^{k,α} → C^{k+1,α}` for the solution operator of the inhomogeneous
Cauchy–Riemann equation, in the form used by the elliptic bootstrap: compactly supported data
of class `C^{k,α}` give a transform of class `C^{k+1}`, with the sharp Hölder exponent on the
top derivative. -/
theorem contDiff_cauchyTransform_of_isHolderC (hα : 0 < α) (hα1 : α < 1) (k : ℕ) {g : ℂ → ℂ}
    {C' : ℝ} (hgs : HasCompactSupport g) (hg : IsHolderC k α C' g) :
    ContDiff ℝ (k + 1) (cauchyTransform g) := by
  obtain ⟨C'', -, hC''⟩ := isHolderC_cauchyTransform hα hα1 k g C' hgs hg
  exact hC''.contDiff hα

/-! ### The bootstrap

With the Schauder scale in hand the elliptic bootstrap is short, because a compactly supported
`C¹` function is *equal* to the Cauchy transform of its own `∂̄` (`cauchyTransform_dbar`): its
regularity is exactly that of that transform, and the scale lifts the regularity of `∂̄u` by one
derivative at every level.
-/

/-- A uniform Hölder constant over all directions follows from the two coordinate directions,
since a directional derivative depends linearly on the direction. -/
theorem isHolderC_of_basis {k : ℕ} {C₁ C₂ : ℝ} {g : ℂ → ℂ} (hdiff : Differentiable ℝ g)
    (h1 : IsHolderC k α C₁ fun z => fderiv ℝ g z 1)
    (hI : IsHolderC k α C₂ fun z => fderiv ℝ g z Complex.I) :
    IsHolderC (k + 1) α (C₁ + C₂) g := by
  refine ⟨hdiff, fun v hv => ?_⟩
  have hfun : (fun z => fderiv ℝ g z v)
      = fun z => (v.re : ℂ) * fderiv ℝ g z 1 + (v.im : ℂ) * fderiv ℝ g z Complex.I := by
    funext z
    have he : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    conv_lhs => rw [he]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hfun]
  refine ((IsHolderC.const_mul (v.re : ℂ) h1).add (IsHolderC.const_mul (v.im : ℂ) hI)).mono ?_
  have hre : |v.re| ≤ 1 := le_trans (Complex.abs_re_le_norm v) hv
  have him : |v.im| ≤ 1 := le_trans (Complex.abs_im_le_norm v) hv
  have hC1 : 0 ≤ C₁ := h1.const_nonneg
  have hC2 : 0 ≤ C₂ := hI.const_nonneg
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith

/-- A compactly supported `C^{k+1}` function sits on the `k`-th level of the Hölder scale. -/
theorem exists_isHolderC_of_contDiff (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (k : ℕ) (g : ℂ → ℂ), ContDiff ℝ (k + 1) g → HasCompactSupport g →
      ∃ C : ℝ, IsHolderC k α C g := by
  intro k
  induction k with
  | zero =>
      intro g hg hgs
      exact exists_holder_of_contDiff_one hg hgs hα hα1
  | succ k ih =>
      intro g hg hgs
      obtain ⟨hdiff, -, happly⟩ := contDiff_succ_iff_fderiv_apply.1 hg
      have hs : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ g z v := fun v =>
        (hgs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
      obtain ⟨C₁, hC₁⟩ := ih _ (happly 1) (hs 1)
      obtain ⟨C₂, hC₂⟩ := ih _ (happly Complex.I) (hs Complex.I)
      exact ⟨C₁ + C₂, isHolderC_of_basis hdiff hC₁ hC₂⟩

/-- **The elliptic bootstrap for compactly supported data.**  A compactly supported `C¹`
function whose `∂̄` is smooth is itself smooth: it equals the Cauchy transform of its `∂̄`, and
the Schauder scale lifts the regularity of that datum by one derivative at every level. -/
theorem contDiff_infty_of_dbar {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u)
    (hdbar : ContDiff ℝ ∞ (dbar u)) : ContDiff ℝ ∞ u := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hdbs : HasCompactSupport (dbar u) := hasCompactSupport_dbar hus
  have heq : cauchyTransform (dbar u) = u := cauchyTransform_dbar hu hus
  rw [contDiff_infty]
  intro n
  cases n with
  | zero => exact hu.of_le (by norm_num)
  | succ k =>
      obtain ⟨C, hC⟩ := exists_isHolderC_of_contDiff (α := 1 / 2) hα hα1.le k (dbar u)
        ((contDiff_infty.1 hdbar) (k + 1)) hdbs
      rw [← heq]
      exact contDiff_cauchyTransform_of_isHolderC hα hα1 k hdbs hC

/-- On compactly supported functions the scale is decreasing: one derivative more than needed
gives the lower level, because the top derivative is then Lipschitz on its support. -/
theorem isHolderC_of_succ (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (k : ℕ) (g : ℂ → ℂ) (C' : ℝ), IsHolderC (k + 1) α C' g → HasCompactSupport g →
      ∃ C'' : ℝ, IsHolderC k α C'' g := by
  intro k
  induction k with
  | zero =>
      intro g C' h hgs
      exact exists_holder_of_contDiff_one (h.contDiff_one hα) hgs hα hα1
  | succ k ih =>
      intro g C' h hgs
      have hs : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ g z v := fun v =>
        (hgs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
      obtain ⟨C₁, hC₁⟩ := ih _ _ (h.2 1 (by simp)) (hs 1)
      obtain ⟨C₂, hC₂⟩ := ih _ _ (h.2 Complex.I (by simp)) (hs Complex.I)
      exact ⟨C₁ + C₂, isHolderC_of_basis h.1 hC₁ hC₂⟩

/-- **Multiplying by a smooth compactly supported factor preserves the level of the scale.**
This is what localises the bootstrap: a cut-off may be applied without losing regularity. -/
theorem exists_isHolderC_mul (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (k : ℕ) (χ g : ℂ → ℂ) (C' : ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      IsHolderC k α C' g → HasCompactSupport g →
      ∃ C'' : ℝ, IsHolderC k α C'' fun z => χ z * g z := by
  intro k
  induction k with
  | zero =>
      intro χ g C' hχ hχs hg hgs
      obtain ⟨Mχ, hMχ⟩ := hχs.exists_bound_of_continuous hχ.continuous
      obtain ⟨Mg, hMg⟩ := hgs.exists_bound_of_continuous (hg.continuous hα)
      obtain ⟨Cχ, hCχ⟩ := exists_holder_of_contDiff_one (hχ.of_le (by simp)) hχs hα hα1
      have hMχ0 : 0 ≤ Mχ := le_trans (norm_nonneg _) (hMχ 0)
      have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0)
      refine ⟨Mχ * C' + Mg * Cχ, fun ξ η => ?_⟩
      have hsplit : χ ξ * g ξ - χ η * g η = χ ξ * (g ξ - g η) + (χ ξ - χ η) * g η := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖χ ξ‖ * ‖g ξ - g η‖ ≤ Mχ * (C' * ‖ξ - η‖ ^ α) :=
        mul_le_mul (hMχ ξ) (hg ξ η) (norm_nonneg _) hMχ0
      have h2 : ‖χ ξ - χ η‖ * ‖g η‖ ≤ (Cχ * ‖ξ - η‖ ^ α) * Mg :=
        mul_le_mul (hCχ ξ η) (hMg η) (norm_nonneg _)
          (mul_nonneg (holder_const_nonneg hCχ) (Real.rpow_nonneg (norm_nonneg _) _))
      nlinarith
  | succ k ih =>
      intro χ g C' hχ hχs hg hgs
      have hdiffχ : Differentiable ℝ χ := hχ.differentiable (by simp)
      have hprod : Differentiable ℝ fun z => χ z * g z := fun z => (hdiffχ z).mul (hg.1 z)
      obtain ⟨Cg, hCg⟩ := isHolderC_of_succ hα hα1 k g C' hg hgs
      have hχ' : ∀ v : ℂ, ContDiff ℝ ∞ fun z => fderiv ℝ χ z v := fun v =>
        (hχ.fderiv_right (by simp)).clm_apply contDiff_const
      have hχ's : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ χ z v := fun v =>
        (hχs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
      have hgs' : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ g z v := fun v =>
        (hgs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
      have hstep : ∀ v : ℂ, ‖v‖ ≤ 1 → ∃ C'' : ℝ,
          IsHolderC k α C'' fun z => fderiv ℝ (fun z => χ z * g z) z v := by
        intro v hv
        obtain ⟨C₁, hC₁⟩ := ih (fun z => fderiv ℝ χ z v) g Cg (hχ' v) (hχ's v) hCg hgs
        obtain ⟨C₂, hC₂⟩ := ih χ (fun z => fderiv ℝ g z v) C' hχ hχs (hg.2 v hv) (hgs' v)
        refine ⟨C₁ + C₂, ?_⟩
        have hfun : (fun z => fderiv ℝ (fun z => χ z * g z) z v)
            = fun z => fderiv ℝ χ z v * g z + χ z * fderiv ℝ g z v := by
          funext z
          have h2 : fderiv ℝ (fun z => χ z * g z) z
              = χ z • fderiv ℝ g z + g z • fderiv ℝ χ z :=
            ((hdiffχ z).hasFDerivAt.mul (hg.1 z).hasFDerivAt).fderiv
          rw [h2]
          simp only [add_apply, smul_apply, smul_eq_mul]
          ring
        rw [hfun]
        exact hC₁.add hC₂
      obtain ⟨C₁, hC₁⟩ := hstep 1 (by simp)
      obtain ⟨C₂, hC₂⟩ := hstep Complex.I (by simp)
      exact ⟨C₁ + C₂, isHolderC_of_basis hprod hC₁ hC₂⟩

/-! ### The local bootstrap

A solution is not compactly supported, so it is cut off.  The cut-off costs a commutator term,
which involves the solution only where the previous cut-off was already one, so the induction
runs on shrinking discs: at each round the regularity gained on the larger disc feeds the
commutator on the smaller one.
-/

/-- A smooth cut-off, one on the closed disc of radius `r` and supported in the disc of radius
`2r`. -/
theorem exists_cutoff (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ
      ∧ (∀ z, dist z z₀ ≤ r → χ z = 1) ∧ ∀ z, 2 * r ≤ dist z z₀ → χ z = 0 := by
  have hlt : r < 2 * r := by linarith
  set f : ContDiffBump z₀ := ⟨r, 2 * r, hr, hlt⟩ with hfdef
  refine ⟨fun z => ((f z : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · refine HasCompactSupport.intro (isCompact_closedBall z₀ (2 * r)) fun z hz => ?_
    rw [mem_closedBall, not_le] at hz
    show ((f z : ℝ) : ℂ) = 0
    rw [f.zero_of_le_dist (show f.rOut ≤ dist z z₀ from hz.le)]
    simp
  · intro z hz
    show ((f z : ℝ) : ℂ) = 1
    rw [f.one_of_mem_closedBall (show dist z z₀ ≤ f.rIn from hz)]
    simp
  · intro z hz
    show ((f z : ℝ) : ℂ) = 0
    rw [f.zero_of_le_dist (show f.rOut ≤ dist z z₀ from hz)]
    simp

/-- The Leibniz rule for `∂̄`. -/
theorem dbar_mul {χ u : ℂ → ℂ} (hχ : Differentiable ℝ χ) (hu : Differentiable ℝ u) (z : ℂ) :
    dbar (fun z => χ z * u z) z = χ z * dbar u z + u z * dbar χ z := by
  have h1 : fderiv ℝ (fun z => χ z * u z) z = χ z • fderiv ℝ u z + u z • fderiv ℝ χ z :=
    ((hχ z).hasFDerivAt.mul (hu z).hasFDerivAt).fderiv
  rw [dbar, dbar, dbar, h1]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem contDiff_dbar {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (dbar χ) := by
  have h1 : ContDiff ℝ ∞ fun z => fderiv ℝ χ z 1 :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ fun z => fderiv ℝ χ z Complex.I :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  exact h1.add (contDiff_const.mul hI)

/-- **The bootstrap, on shrinking discs.**  A `C¹` function with smooth `∂̄` is, after a cut-off,
on every level of the Hölder scale. -/
theorem exists_cutoff_isHolderC (hα : 0 < α) (hα1 : α < 1) {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u)
    (hdb : ContDiff ℝ ∞ (dbar u)) :
    ∀ (k : ℕ) (z₀ : ℂ) (r : ℝ), 0 < r →
      ∃ (χ : ℂ → ℂ) (C : ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ
        ∧ (∀ z, dist z z₀ ≤ r → χ z = 1) ∧ IsHolderC k α C fun z => χ z * u z := by
  have hdiffu : Differentiable ℝ u := hu.differentiable one_ne_zero
  intro k
  induction k with
  | zero =>
      intro z₀ r hr
      obtain ⟨χ, hχ, hχs, hχ1, -⟩ := exists_cutoff z₀ hr
      have hv1 : ContDiff ℝ 1 fun z => χ z * u z := (hχ.of_le (by simp)).mul hu
      obtain ⟨C, hC⟩ := exists_holder_of_contDiff_one hv1 hχs.mul_right hα hα1.le
      exact ⟨χ, C, hχ, hχs, hχ1, hC⟩
  | succ k ih =>
      intro z₀ r hr
      obtain ⟨χ₀, C₀, hχ₀, hχ₀s, hχ₀1, hC₀⟩ := ih z₀ (4 * r) (by linarith)
      obtain ⟨χ, hχ, hχs, hχ1, hχ0⟩ := exists_cutoff z₀ hr
      have hdiffχ : Differentiable ℝ χ := hχ.differentiable (by simp)
      have hv1 : ContDiff ℝ 1 fun z => χ z * u z := (hχ.of_le (by simp)).mul hu
      have hvs : HasCompactSupport fun z => χ z * u z := hχs.mul_right
      have htsup : tsupport χ ⊆ closedBall z₀ (2 * r) := by
        refine closure_minimal (fun z hz => ?_) isClosed_closedBall
        by_contra hcon
        rw [mem_closedBall, not_le] at hcon
        exact hz (hχ0 z hcon.le)
      have hone : ∀ z : ℂ, dbar χ z ≠ 0 → χ₀ z = 1 := by
        intro z hz
        have hfd : fderiv ℝ χ z ≠ 0 := by
          intro h0
          apply hz
          rw [dbar, h0]
          simp
        have hzt : z ∈ tsupport χ := support_fderiv_subset (𝕜 := ℝ) hfd
        have hdist := htsup hzt
        rw [mem_closedBall] at hdist
        exact hχ₀1 z (by linarith)
      have hdbv : ∀ z : ℂ, dbar (fun z => χ z * u z) z
          = χ z * dbar u z + dbar χ z * (χ₀ z * u z) := by
        intro z
        rw [dbar_mul hdiffχ hdiffu z]
        by_cases hz : dbar χ z = 0
        · rw [hz]
          ring
        · rw [hone z hz]
          ring
      obtain ⟨C₁, hC₁⟩ := exists_isHolderC_of_contDiff hα hα1.le k (fun z => χ z * dbar u z)
        ((hχ.mul hdb).of_le (by exact_mod_cast (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤)))
        hχs.mul_right
      obtain ⟨C₂, hC₂⟩ := exists_isHolderC_mul hα hα1.le k (dbar χ) (fun z => χ₀ z * u z) C₀
        (contDiff_dbar hχ) (hasCompactSupport_dbar hχs) hC₀ hχ₀s.mul_right
      have hsum : IsHolderC k α (C₁ + C₂) (dbar fun z => χ z * u z) := by
        have hfun : (dbar fun z => χ z * u z)
            = fun z => χ z * dbar u z + dbar χ z * (χ₀ z * u z) := funext hdbv
        rw [hfun]
        exact hC₁.add hC₂
      obtain ⟨C, -, hC⟩ := isHolderC_cauchyTransform hα hα1 k _ _
        (hasCompactSupport_dbar hvs) hsum
      refine ⟨χ, C, hχ, hχs, hχ1, ?_⟩
      rw [← cauchyTransform_dbar hv1 hvs]
      exact hC

/-- **Elliptic regularity for the Cauchy–Riemann operator.**  A `C¹` function whose
`∂u/∂x + i ∂u/∂y` is smooth is itself smooth.  This is the bootstrap: near any point the
function is cut off, the cut-off function is the Cauchy transform of its own `∂̄`, and the
Schauder scale lifts the regularity of that datum by one derivative at every round, the
commutator term being fed by the regularity already gained on a larger disc. -/
theorem contDiff_infty_of_dbar_contDiff {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u)
    (hdb : ContDiff ℝ ∞ (dbar u)) : ContDiff ℝ ∞ u := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 : ℝ) / 2 < 1 := by norm_num
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro z₀
  obtain ⟨χ, C, hχ, hχs, hχ1, hC⟩ :=
    exists_cutoff_isHolderC (α := 1 / 2) hα hα1 hu hdb n z₀ 1 one_pos
  have h1 : ContDiff ℝ n fun z => χ z * u z := hC.contDiff hα
  have heq : u =ᶠ[𝓝 z₀] fun z => χ z * u z := by
    filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    rw [mem_ball] at hz
    rw [hχ1 z hz.le, one_mul]
  exact h1.contDiffAt.congr_of_eventuallyEq heq

/-! ### The chain rule on the scale

The Floer equation is nonlinear: its right-hand side is as regular as the solution, so the
bootstrap needs the Hölder scale to be stable under composition with a smooth function.  The
derivative of such a composition is a combination of the two Wirtinger derivatives of the outer
function, composed with the inner one, against the derivative of the inner one; so the
induction needs products, conjugation, and constants.
-/

theorem contDiff_dz {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (dz χ) := by
  have h1 : ContDiff ℝ ∞ fun z => fderiv ℝ χ z 1 :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ fun z => fderiv ℝ χ z Complex.I :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  exact h1.sub (contDiff_const.mul hI)

/-- Adding a constant does not move a function on the scale. -/
theorem IsHolderC.add_const {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (h : IsHolderC k α C' g) (c : ℂ) :
    IsHolderC k α C' fun z => g z + c := by
  cases k with
  | zero =>
      intro ξ η
      have he : g ξ + c - (g η + c) = g ξ - g η := by ring
      rw [he]
      exact h ξ η
  | succ k =>
      refine ⟨fun z => (h.1 z).add_const c, fun v hv => ?_⟩
      have hfun : (fun z => fderiv ℝ (fun z => g z + c) z v) = fun z => fderiv ℝ g z v := by
        funext z
        rw [((h.1 z).hasFDerivAt.add_const c).fderiv]
      rw [hfun]
      exact h.2 v hv

/-- Conjugation does not move a function on the scale. -/
theorem IsHolderC.conj {k : ℕ} {C' : ℝ} {g : ℂ → ℂ} (h : IsHolderC k α C' g) :
    IsHolderC k α C' fun z => (starRingEnd ℂ) (g z) := by
  induction k generalizing g with
  | zero =>
      intro ξ η
      have he : (starRingEnd ℂ) (g ξ) - (starRingEnd ℂ) (g η) = (starRingEnd ℂ) (g ξ - g η) := by
        rw [map_sub]
      rw [he, RCLike.norm_conj]
      exact h ξ η
  | succ k ih =>
      have hdiff : Differentiable ℝ fun z => (starRingEnd ℂ) (g z) := fun z =>
        (Complex.conjCLE.differentiableAt).comp z (h.1 z)
      refine ⟨hdiff, fun v hv => ?_⟩
      have hfun : (fun z => fderiv ℝ (fun z => (starRingEnd ℂ) (g z)) z v)
          = fun z => (starRingEnd ℂ) (fderiv ℝ g z v) := by
        funext z
        have h1 : HasFDerivAt (fun z => (starRingEnd ℂ) (g z))
            ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g z)) z :=
          Complex.conjCLE.hasFDerivAt.comp z (h.1 z).hasFDerivAt
        rw [h1.fderiv]
        rfl
      rw [hfun]
      exact ih (h.2 v hv)

/-- **The product of two compactly supported functions of the scale stays on the scale.** -/
theorem exists_isHolderC_mul_mul (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (k : ℕ) (f g : ℂ → ℂ) (C₁ C₂ : ℝ), IsHolderC k α C₁ f → HasCompactSupport f →
      IsHolderC k α C₂ g → HasCompactSupport g →
      ∃ C' : ℝ, IsHolderC k α C' fun z => f z * g z := by
  intro k
  induction k with
  | zero =>
      intro f g C₁ C₂ hf hfs hg hgs
      obtain ⟨Mf, hMf⟩ := hfs.exists_bound_of_continuous (hf.continuous hα)
      obtain ⟨Mg, hMg⟩ := hgs.exists_bound_of_continuous (hg.continuous hα)
      have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf 0)
      have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0)
      refine ⟨Mf * C₂ + Mg * C₁, fun ξ η => ?_⟩
      have hsplit : f ξ * g ξ - f η * g η = f ξ * (g ξ - g η) + (f ξ - f η) * g η := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖f ξ‖ * ‖g ξ - g η‖ ≤ Mf * (C₂ * ‖ξ - η‖ ^ α) :=
        mul_le_mul (hMf ξ) (hg ξ η) (norm_nonneg _) hMf0
      have h2 : ‖f ξ - f η‖ * ‖g η‖ ≤ (C₁ * ‖ξ - η‖ ^ α) * Mg :=
        mul_le_mul (hf ξ η) (hMg η) (norm_nonneg _)
          (mul_nonneg (holder_const_nonneg hf) (Real.rpow_nonneg (norm_nonneg _) _))
      nlinarith
  | succ k ih =>
      intro f g C₁ C₂ hf hfs hg hgs
      obtain ⟨Cf, hCf⟩ := isHolderC_of_succ hα hα1 k f C₁ hf hfs
      obtain ⟨Cg, hCg⟩ := isHolderC_of_succ hα hα1 k g C₂ hg hgs
      have hfs' : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ f z v := fun v =>
        (hfs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
      have hgs' : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ g z v := fun v =>
        (hgs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
      have hstep : ∀ v : ℂ, ‖v‖ ≤ 1 → ∃ C : ℝ,
          IsHolderC k α C fun z => fderiv ℝ (fun z => f z * g z) z v := by
        intro v hv
        obtain ⟨D₁, hD₁⟩ := ih (fun z => fderiv ℝ f z v) g C₁ Cg (hf.2 v hv) (hfs' v) hCg hgs
        obtain ⟨D₂, hD₂⟩ := ih f (fun z => fderiv ℝ g z v) Cf C₂ hCf hfs (hg.2 v hv) (hgs' v)
        refine ⟨D₁ + D₂, ?_⟩
        have hfun : (fun z => fderiv ℝ (fun z => f z * g z) z v)
            = fun z => fderiv ℝ f z v * g z + f z * fderiv ℝ g z v := by
          funext z
          have h2 : fderiv ℝ (fun z => f z * g z) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
            ((hf.1 z).hasFDerivAt.mul (hg.1 z).hasFDerivAt).fderiv
          rw [h2]
          simp only [add_apply, smul_apply, smul_eq_mul]
          ring
        rw [hfun]
        exact hD₁.add hD₂
      obtain ⟨D₁, hD₁⟩ := hstep 1 (by simp)
      obtain ⟨D₂, hD₂⟩ := hstep Complex.I (by simp)
      exact ⟨D₁ + D₂, isHolderC_of_basis (fun z => (hf.1 z).mul (hg.1 z)) hD₁ hD₂⟩

/-- **The chain rule on the Hölder scale.**  Composing a compactly supported function of the
scale with a smooth function keeps it on the scale, once the value at the origin is subtracted
so that the composite again has compact support. -/
theorem exists_isHolderC_comp (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (k : ℕ) (F w : ℂ → ℂ) (C : ℝ), ContDiff ℝ ∞ F → IsHolderC k α C w → HasCompactSupport w →
      ∃ C' : ℝ, IsHolderC k α C' fun z => F (w z) - F 0 := by
  intro k
  induction k with
  | zero =>
      intro F w C hF hw hws
      obtain ⟨R, hR⟩ := hws.exists_bound_of_continuous (hw.continuous hα)
      have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg _) (hR 0)
      obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
        (hF.continuous_fderiv (by simp)).continuousOn
      have hdiffF : Differentiable ℝ F := hF.differentiable (by simp)
      have hmem : ∀ z : ℂ, w z ∈ closedBall (0 : ℂ) R := by
        intro z
        rw [mem_closedBall, dist_zero_right]
        exact hR z
      have hL0 : (0 : ℝ) ≤ L :=
        le_trans (norm_nonneg _) (hL 0 (by rw [mem_closedBall, dist_self]; exact hR0))
      refine ⟨L * C, fun ξ η => ?_⟩
      have he : F (w ξ) - F 0 - (F (w η) - F 0) = F (w ξ) - F (w η) := by ring
      rw [he]
      calc ‖F (w ξ) - F (w η)‖ ≤ L * ‖w ξ - w η‖ :=
            Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiffF x)
              (fun x hx => hL x hx) (convex_closedBall _ _) (hmem η) (hmem ξ)
        _ ≤ L * (C * ‖ξ - η‖ ^ α) := mul_le_mul_of_nonneg_left (hw ξ η) hL0
        _ = L * C * ‖ξ - η‖ ^ α := by ring
  | succ k ih =>
      intro F w C hF hw hws
      have hdiffF : Differentiable ℝ F := hF.differentiable (by simp)
      have hcs : ∀ H : ℂ → ℂ, HasCompactSupport fun z => H (w z) - H 0 := by
        intro H
        refine HasCompactSupport.intro hws fun z hz => ?_
        rw [image_eq_zero_of_notMem_tsupport hz]
        ring
      obtain ⟨Cw, hCw⟩ := isHolderC_of_succ hα hα1 k w C hw hws
      obtain ⟨A₁, hA₁⟩ := ih (dz F) w Cw (contDiff_dz hF) hCw hws
      obtain ⟨A₂, hA₂⟩ := ih (dbar F) w Cw (contDiff_dbar hF) hCw hws
      have hdiffcomp : Differentiable ℝ fun z => F (w z) - F 0 := fun z =>
        ((hdiffF (w z)).comp z (hw.1 z)).sub_const _
      have hstep : ∀ v : ℂ, ‖v‖ ≤ 1 → ∃ D : ℝ,
          IsHolderC k α D fun z => fderiv ℝ (fun z => F (w z) - F 0) z v := by
        intro v hv
        have hwv : IsHolderC k α C fun z => fderiv ℝ w z v := hw.2 v hv
        have hwvs : HasCompactSupport fun z => fderiv ℝ w z v :=
          (hws.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
        have hwvc : IsHolderC k α C fun z => (starRingEnd ℂ) (fderiv ℝ w z v) := hwv.conj
        have hwvcs : HasCompactSupport fun z => (starRingEnd ℂ) (fderiv ℝ w z v) :=
          hwvs.comp_left (g := starRingEnd ℂ) (by simp)
        obtain ⟨D₁, hD₁⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₁ C hA₁ (hcs (dz F)) hwv hwvs
        obtain ⟨D₂, hD₂⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₂ C hA₂ (hcs (dbar F))
          hwvc hwvcs
        have hsum := (hD₁.add (IsHolderC.const_mul (dz F 0) hwv)).add
          (hD₂.add (IsHolderC.const_mul (dbar F 0) hwvc))
        have hhalf := IsHolderC.const_mul ((2 : ℂ)⁻¹) hsum
        have hfun : (fun z => fderiv ℝ (fun z => F (w z) - F 0) z v)
            = fun z => (2 : ℂ)⁻¹ * ((dz F (w z) - dz F 0) * fderiv ℝ w z v
                + dz F 0 * fderiv ℝ w z v
                + ((dbar F (w z) - dbar F 0) * (starRingEnd ℂ) (fderiv ℝ w z v)
                  + dbar F 0 * (starRingEnd ℂ) (fderiv ℝ w z v))) := by
          funext z
          have hchain : HasFDerivAt (fun z => F (w z) - F 0)
              ((fderiv ℝ F (w z)).comp (fderiv ℝ w z)) z :=
            (((hdiffF (w z)).hasFDerivAt).comp z ((hw.1 z).hasFDerivAt)).sub_const _
          rw [hchain.fderiv]
          show fderiv ℝ F (w z) (fderiv ℝ w z v) = _
          rw [eq_dPair (fderiv ℝ F (w z)), dPair_apply]
          simp only [dz, dbar]
          ring
        rw [hfun]
        exact ⟨_, hhalf⟩
      obtain ⟨D₁, hD₁⟩ := hstep 1 (by simp)
      obtain ⟨D₂, hD₂⟩ := hstep Complex.I (by simp)
      exact ⟨D₁ + D₂, isHolderC_of_basis hdiffcomp hD₁ hD₂⟩

/-! ### The nonlinear bootstrap -/

/-- **The bootstrap for a nonlinear right-hand side, on shrinking discs.**  The equation is
`∂̄u = F ∘ u`, so the right-hand side is only as regular as the solution; the chain rule on the
scale is what lets the round still gain a derivative. -/
theorem exists_cutoff_isHolderC_comp (hα : 0 < α) (hα1 : α < 1) {u F : ℂ → ℂ}
    (hu : ContDiff ℝ 1 u) (hF : ContDiff ℝ ∞ F) (heq : ∀ z, dbar u z = F (u z)) :
    ∀ (k : ℕ) (z₀ : ℂ) (r : ℝ), 0 < r →
      ∃ (χ : ℂ → ℂ) (C : ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ
        ∧ (∀ z, dist z z₀ ≤ r → χ z = 1) ∧ IsHolderC k α C fun z => χ z * u z := by
  have hdiffu : Differentiable ℝ u := hu.differentiable one_ne_zero
  intro k
  induction k with
  | zero =>
      intro z₀ r hr
      obtain ⟨χ, hχ, hχs, hχ1, -⟩ := exists_cutoff z₀ hr
      have hv1 : ContDiff ℝ 1 fun z => χ z * u z := (hχ.of_le (by simp)).mul hu
      obtain ⟨C, hC⟩ := exists_holder_of_contDiff_one hv1 hχs.mul_right hα hα1.le
      exact ⟨χ, C, hχ, hχs, hχ1, hC⟩
  | succ k ih =>
      intro z₀ r hr
      obtain ⟨χ₀, C₀, hχ₀, hχ₀s, hχ₀1, hC₀⟩ := ih z₀ (4 * r) (by linarith)
      obtain ⟨χ, hχ, hχs, hχ1, hχ0⟩ := exists_cutoff z₀ hr
      have hdiffχ : Differentiable ℝ χ := hχ.differentiable (by simp)
      have hv1 : ContDiff ℝ 1 fun z => χ z * u z := (hχ.of_le (by simp)).mul hu
      have hvs : HasCompactSupport fun z => χ z * u z := hχs.mul_right
      have hws : HasCompactSupport fun z => χ₀ z * u z := hχ₀s.mul_right
      have htsup : tsupport χ ⊆ closedBall z₀ (2 * r) := by
        refine closure_minimal (fun z hz => ?_) isClosed_closedBall
        by_contra hcon
        rw [mem_closedBall, not_le] at hcon
        exact hz (hχ0 z hcon.le)
      have hone : ∀ z : ℂ, z ∈ tsupport χ → χ₀ z = 1 := by
        intro z hz
        have hdist := htsup hz
        rw [mem_closedBall] at hdist
        exact hχ₀1 z (by linarith)
      have honeχ : ∀ z : ℂ, χ z ≠ 0 → χ₀ z = 1 := fun z hz => hone z (subset_tsupport _ hz)
      have honedb : ∀ z : ℂ, dbar χ z ≠ 0 → χ₀ z = 1 := by
        intro z hz
        have hfd : fderiv ℝ χ z ≠ 0 := by
          intro h0
          apply hz
          rw [dbar, h0]
          simp
        exact hone z (support_fderiv_subset (𝕜 := ℝ) hfd)
      -- the right-hand side, rewritten through the previous cut-off
      have hrhs : ∀ z : ℂ, χ z * dbar u z
          = χ z * (F (χ₀ z * u z) - F 0) + χ z * F 0 := by
        intro z
        rw [heq z]
        by_cases hz : χ z = 0
        · rw [hz]
          ring
        · rw [honeχ z hz, one_mul]
          ring
      have hcomps : HasCompactSupport fun z => F (χ₀ z * u z) - F 0 := by
        refine HasCompactSupport.intro hws fun z hz => ?_
        rw [image_eq_zero_of_notMem_tsupport hz]
        ring
      obtain ⟨A, hA⟩ := exists_isHolderC_comp hα hα1.le k F (fun z => χ₀ z * u z) C₀ hF hC₀ hws
      obtain ⟨B₁, hB₁⟩ := exists_isHolderC_mul hα hα1.le k χ (fun z => F (χ₀ z * u z) - F 0) A
        hχ hχs hA hcomps
      obtain ⟨B₂, hB₂⟩ := exists_isHolderC_of_contDiff hα hα1.le k (fun z => χ z * F 0)
        ((hχ.mul contDiff_const).of_le (by exact_mod_cast (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤)))
        hχs.mul_right
      obtain ⟨B₃, hB₃⟩ := exists_isHolderC_mul hα hα1.le k (dbar χ) (fun z => χ₀ z * u z) C₀
        (contDiff_dbar hχ) (hasCompactSupport_dbar hχs) hC₀ hws
      have hdbv : ∀ z : ℂ, dbar (fun z => χ z * u z) z
          = χ z * (F (χ₀ z * u z) - F 0) + χ z * F 0 + dbar χ z * (χ₀ z * u z) := by
        intro z
        rw [dbar_mul hdiffχ hdiffu z, hrhs z]
        by_cases hz : dbar χ z = 0
        · rw [hz]
          ring
        · rw [honedb z hz]
          ring
      have hsum : IsHolderC k α (B₁ + B₂ + B₃) (dbar fun z => χ z * u z) := by
        have hfun : (dbar fun z => χ z * u z)
            = fun z => χ z * (F (χ₀ z * u z) - F 0) + χ z * F 0
              + dbar χ z * (χ₀ z * u z) := funext hdbv
        rw [hfun]
        exact (hB₁.add hB₂).add hB₃
      obtain ⟨C, -, hC⟩ := isHolderC_cauchyTransform hα hα1 k _ _
        (hasCompactSupport_dbar hvs) hsum
      refine ⟨χ, C, hχ, hχs, hχ1, ?_⟩
      rw [← cauchyTransform_dbar hv1 hvs]
      exact hC

/-- **Elliptic regularity for a nonlinear Cauchy–Riemann equation.**  A `C¹` solution of
`∂u/∂x + i ∂u/∂y = F ∘ u`, with `F` smooth, is smooth.  This is the analytic core of the
regularity statement for the Floer equation: the right-hand side is only as regular as the
solution, and the chain rule on the Hölder scale is what lets each round gain a derivative. -/
theorem contDiff_infty_of_dbar_comp {u F : ℂ → ℂ} (hu : ContDiff ℝ 1 u) (hF : ContDiff ℝ ∞ F)
    (heq : ∀ z, dbar u z = F (u z)) : ContDiff ℝ ∞ u := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 : ℝ) / 2 < 1 := by norm_num
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro z₀
  obtain ⟨χ, C, hχ, hχs, hχ1, hC⟩ :=
    exists_cutoff_isHolderC_comp (α := 1 / 2) hα hα1 hu hF heq n z₀ 1 one_pos
  have h1 : ContDiff ℝ n fun z => χ z * u z := hC.contDiff hα
  have hfeq : u =ᶠ[𝓝 z₀] fun z => χ z * u z := by
    filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    rw [mem_ball] at hz
    rw [hχ1 z hz.le, one_mul]
  exact h1.contDiffAt.congr_of_eventuallyEq hfeq

/-! ### A nonlinearity that depends on the point as well

In the Floer equation the Hamiltonian depends on time, so the right-hand side is `F z (u z)`
and not `F (u z)`.  Rather than carry an unbounded variable through the estimates, the point is
treated as a second inner function: near the disc where the bootstrap works, `z` may be
replaced by `χ z * z`, which is smooth with compact support and so sits on every level of the
scale.  What is needed is therefore the chain rule for a smooth function of *two* complex
variables composed with two functions of the scale.
-/

/-- The `∂/∂z` of the first variable of a function of two complex variables. -/
noncomputable def dz₁ (G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℝ G p (1, 0) - Complex.I * fderiv ℝ G p (Complex.I, 0)

/-- The `∂/∂z̄` of the first variable. -/
noncomputable def dbar₁ (G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℝ G p (1, 0) + Complex.I * fderiv ℝ G p (Complex.I, 0)

/-- The `∂/∂z` of the second variable. -/
noncomputable def dz₂ (G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℝ G p (0, 1) - Complex.I * fderiv ℝ G p (0, Complex.I)

/-- The `∂/∂z̄` of the second variable. -/
noncomputable def dbar₂ (G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℝ G p (0, 1) + Complex.I * fderiv ℝ G p (0, Complex.I)

theorem contDiff_dz₁ {G : ℂ × ℂ → ℂ} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dz₁ G) :=
  ((hG.fderiv_right (by simp)).clm_apply contDiff_const).sub
    (contDiff_const.mul ((hG.fderiv_right (by simp)).clm_apply contDiff_const))

theorem contDiff_dbar₁ {G : ℂ × ℂ → ℂ} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dbar₁ G) :=
  ((hG.fderiv_right (by simp)).clm_apply contDiff_const).add
    (contDiff_const.mul ((hG.fderiv_right (by simp)).clm_apply contDiff_const))

theorem contDiff_dz₂ {G : ℂ × ℂ → ℂ} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dz₂ G) :=
  ((hG.fderiv_right (by simp)).clm_apply contDiff_const).sub
    (contDiff_const.mul ((hG.fderiv_right (by simp)).clm_apply contDiff_const))

theorem contDiff_dbar₂ {G : ℂ × ℂ → ℂ} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dbar₂ G) :=
  ((hG.fderiv_right (by simp)).clm_apply contDiff_const).add
    (contDiff_const.mul ((hG.fderiv_right (by simp)).clm_apply contDiff_const))

/-- **The derivative of a composition with two inner functions**, in Wirtinger form. -/
theorem fderiv_comp₂_apply {G : ℂ × ℂ → ℂ} (hG : Differentiable ℝ G) {w₁ w₂ : ℂ → ℂ}
    (h₁ : Differentiable ℝ w₁) (h₂ : Differentiable ℝ w₂) (z v : ℂ) :
    fderiv ℝ (fun z => G (w₁ z, w₂ z)) z v
      = (dz₁ G (w₁ z, w₂ z) * fderiv ℝ w₁ z v
          + dbar₁ G (w₁ z, w₂ z) * (starRingEnd ℂ) (fderiv ℝ w₁ z v)
          + (dz₂ G (w₁ z, w₂ z) * fderiv ℝ w₂ z v
            + dbar₂ G (w₁ z, w₂ z) * (starRingEnd ℂ) (fderiv ℝ w₂ z v))) / 2 := by
  have hW : ∀ y : ℂ, HasFDerivAt (fun z => (w₁ z, w₂ z))
      ((fderiv ℝ w₁ y).prod (fderiv ℝ w₂ y)) y := fun y =>
    (h₁ y).hasFDerivAt.prodMk (h₂ y).hasFDerivAt
  have hchain : fderiv ℝ (fun z => G (w₁ z, w₂ z)) z
      = (fderiv ℝ G (w₁ z, w₂ z)).comp ((fderiv ℝ w₁ z).prod (fderiv ℝ w₂ z)) :=
    (((hG _).hasFDerivAt).comp z (hW z)).fderiv
  rw [hchain]
  show fderiv ℝ G (w₁ z, w₂ z) (fderiv ℝ w₁ z v, fderiv ℝ w₂ z v) = _
  have hsplit : ((fderiv ℝ w₁ z v, fderiv ℝ w₂ z v) : ℂ × ℂ)
      = (fderiv ℝ w₁ z v, 0) + (0, fderiv ℝ w₂ z v) := by simp
  rw [hsplit, map_add]
  have hL₁ : ∀ a : ℂ, fderiv ℝ G (w₁ z, w₂ z) (a, 0)
      = ((fderiv ℝ G (w₁ z, w₂ z)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) a := fun a => rfl
  have hL₂ : ∀ a : ℂ, fderiv ℝ G (w₁ z, w₂ z) (0, a)
      = ((fderiv ℝ G (w₁ z, w₂ z)).comp (ContinuousLinearMap.inr ℝ ℂ ℂ)) a := fun a => rfl
  rw [hL₁, hL₂]
  rw [eq_dPair ((fderiv ℝ G (w₁ z, w₂ z)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)),
    eq_dPair ((fderiv ℝ G (w₁ z, w₂ z)).comp (ContinuousLinearMap.inr ℝ ℂ ℂ)),
    dPair_apply, dPair_apply]
  simp only [dz₁, dbar₁, dz₂, dbar₂, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  ring

/-- **The chain rule on the scale, for a function of two variables.** -/
theorem exists_isHolderC_comp₂ (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (k : ℕ) (G : ℂ × ℂ → ℂ) (w₁ w₂ : ℂ → ℂ) (C₁ C₂ : ℝ), ContDiff ℝ ∞ G →
      IsHolderC k α C₁ w₁ → HasCompactSupport w₁ →
      IsHolderC k α C₂ w₂ → HasCompactSupport w₂ →
      ∃ C' : ℝ, IsHolderC k α C' fun z => G (w₁ z, w₂ z) - G (0, 0) := by
  intro k
  induction k with
  | zero =>
      intro G w₁ w₂ C₁ C₂ hG hw₁ hw₁s hw₂ hw₂s
      obtain ⟨R₁, hR₁⟩ := hw₁s.exists_bound_of_continuous (hw₁.continuous hα)
      obtain ⟨R₂, hR₂⟩ := hw₂s.exists_bound_of_continuous (hw₂.continuous hα)
      have hR0 : (0 : ℝ) ≤ max R₁ R₂ :=
        le_trans (le_trans (norm_nonneg (w₁ 0)) (hR₁ 0)) (le_max_left _ _)
      obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ × ℂ) (max R₁ R₂)).exists_bound_of_continuousOn
        (hG.continuous_fderiv (by simp)).continuousOn
      have hdiffG : Differentiable ℝ G := hG.differentiable (by simp)
      have hmem : ∀ z : ℂ, ((w₁ z, w₂ z) : ℂ × ℂ) ∈ closedBall (0 : ℂ × ℂ) (max R₁ R₂) := by
        intro z
        rw [mem_closedBall, dist_zero_right, Prod.norm_mk, max_le_iff]
        exact ⟨le_trans (hR₁ z) (le_max_left _ _), le_trans (hR₂ z) (le_max_right _ _)⟩
      have hL0 : (0 : ℝ) ≤ L :=
        le_trans (norm_nonneg _) (hL 0 (by rw [mem_closedBall, dist_self]; exact hR0))
      refine ⟨L * (C₁ + C₂), fun ξ η => ?_⟩
      have he : G (w₁ ξ, w₂ ξ) - G (0, 0) - (G (w₁ η, w₂ η) - G (0, 0))
          = G (w₁ ξ, w₂ ξ) - G (w₁ η, w₂ η) := by ring
      rw [he]
      have hlip : ‖G (w₁ ξ, w₂ ξ) - G (w₁ η, w₂ η)‖ ≤ L * ‖((w₁ ξ, w₂ ξ) : ℂ × ℂ) - (w₁ η, w₂ η)‖ :=
        Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiffG x) (fun x hx => hL x hx)
          (convex_closedBall _ _) (hmem η) (hmem ξ)
      have hnorm : ‖((w₁ ξ, w₂ ξ) : ℂ × ℂ) - (w₁ η, w₂ η)‖ ≤ ‖w₁ ξ - w₁ η‖ + ‖w₂ ξ - w₂ η‖ := by
        rw [Prod.mk_sub_mk, Prod.norm_mk, max_le_iff]
        exact ⟨by linarith [norm_nonneg (w₂ ξ - w₂ η)], by linarith [norm_nonneg (w₁ ξ - w₁ η)]⟩
      have h1 := hw₁ ξ η
      have h2 := hw₂ ξ η
      have hpow : (0 : ℝ) ≤ ‖ξ - η‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
      calc ‖G (w₁ ξ, w₂ ξ) - G (w₁ η, w₂ η)‖
          ≤ L * (‖w₁ ξ - w₁ η‖ + ‖w₂ ξ - w₂ η‖) :=
            le_trans hlip (mul_le_mul_of_nonneg_left hnorm hL0)
        _ ≤ L * (C₁ * ‖ξ - η‖ ^ α + C₂ * ‖ξ - η‖ ^ α) := by nlinarith
        _ = L * (C₁ + C₂) * ‖ξ - η‖ ^ α := by ring
  | succ k ih =>
      intro G w₁ w₂ C₁ C₂ hG hw₁ hw₁s hw₂ hw₂s
      have hdiffG : Differentiable ℝ G := hG.differentiable (by simp)
      have hcs : ∀ H : ℂ × ℂ → ℂ, HasCompactSupport fun z => H (w₁ z, w₂ z) - H (0, 0) := by
        intro H
        refine HasCompactSupport.intro (hw₁s.union hw₂s) fun z hz => ?_
        rw [image_eq_zero_of_notMem_tsupport (fun hc => hz (Or.inl hc)),
          image_eq_zero_of_notMem_tsupport (fun hc => hz (Or.inr hc))]
        ring
      obtain ⟨Cw₁, hCw₁⟩ := isHolderC_of_succ hα hα1 k w₁ C₁ hw₁ hw₁s
      obtain ⟨Cw₂, hCw₂⟩ := isHolderC_of_succ hα hα1 k w₂ C₂ hw₂ hw₂s
      obtain ⟨A₁, hA₁⟩ := ih (dz₁ G) w₁ w₂ Cw₁ Cw₂ (contDiff_dz₁ hG) hCw₁ hw₁s hCw₂ hw₂s
      obtain ⟨A₂, hA₂⟩ := ih (dbar₁ G) w₁ w₂ Cw₁ Cw₂ (contDiff_dbar₁ hG) hCw₁ hw₁s hCw₂ hw₂s
      obtain ⟨A₃, hA₃⟩ := ih (dz₂ G) w₁ w₂ Cw₁ Cw₂ (contDiff_dz₂ hG) hCw₁ hw₁s hCw₂ hw₂s
      obtain ⟨A₄, hA₄⟩ := ih (dbar₂ G) w₁ w₂ Cw₁ Cw₂ (contDiff_dbar₂ hG) hCw₁ hw₁s hCw₂ hw₂s
      have hdiffcomp : Differentiable ℝ fun z => G (w₁ z, w₂ z) - G (0, 0) := fun z =>
        ((hdiffG _).comp z ((hw₁.1 z).prodMk (hw₂.1 z))).sub_const _
      have hstep : ∀ v : ℂ, ‖v‖ ≤ 1 → ∃ D : ℝ,
          IsHolderC k α D fun z => fderiv ℝ (fun z => G (w₁ z, w₂ z) - G (0, 0)) z v := by
        intro v hv
        have hd₁ : IsHolderC k α C₁ fun z => fderiv ℝ w₁ z v := hw₁.2 v hv
        have hd₂ : IsHolderC k α C₂ fun z => fderiv ℝ w₂ z v := hw₂.2 v hv
        have hd₁s : HasCompactSupport fun z => fderiv ℝ w₁ z v :=
          (hw₁s.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
        have hd₂s : HasCompactSupport fun z => fderiv ℝ w₂ z v :=
          (hw₂s.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
        have hc₁ : IsHolderC k α C₁ fun z => (starRingEnd ℂ) (fderiv ℝ w₁ z v) := hd₁.conj
        have hc₂ : IsHolderC k α C₂ fun z => (starRingEnd ℂ) (fderiv ℝ w₂ z v) := hd₂.conj
        have hc₁s : HasCompactSupport fun z => (starRingEnd ℂ) (fderiv ℝ w₁ z v) :=
          hd₁s.comp_left (g := starRingEnd ℂ) (by simp)
        have hc₂s : HasCompactSupport fun z => (starRingEnd ℂ) (fderiv ℝ w₂ z v) :=
          hd₂s.comp_left (g := starRingEnd ℂ) (by simp)
        obtain ⟨D₁, hD₁⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₁ C₁ hA₁ (hcs (dz₁ G)) hd₁ hd₁s
        obtain ⟨D₂, hD₂⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₂ C₁ hA₂ (hcs (dbar₁ G))
          hc₁ hc₁s
        obtain ⟨D₃, hD₃⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₃ C₂ hA₃ (hcs (dz₂ G)) hd₂ hd₂s
        obtain ⟨D₄, hD₄⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₄ C₂ hA₄ (hcs (dbar₂ G))
          hc₂ hc₂s
        have hsum := ((hD₁.add (IsHolderC.const_mul (dz₁ G (0, 0)) hd₁)).add
          (hD₂.add (IsHolderC.const_mul (dbar₁ G (0, 0)) hc₁))).add
          ((hD₃.add (IsHolderC.const_mul (dz₂ G (0, 0)) hd₂)).add
            (hD₄.add (IsHolderC.const_mul (dbar₂ G (0, 0)) hc₂)))
        have hhalf := IsHolderC.const_mul ((2 : ℂ)⁻¹) hsum
        have hfun : (fun z => fderiv ℝ (fun z => G (w₁ z, w₂ z) - G (0, 0)) z v)
            = fun z => (2 : ℂ)⁻¹ * ((((dz₁ G (w₁ z, w₂ z) - dz₁ G (0, 0)) * fderiv ℝ w₁ z v
                  + dz₁ G (0, 0) * fderiv ℝ w₁ z v)
                + ((dbar₁ G (w₁ z, w₂ z) - dbar₁ G (0, 0))
                    * (starRingEnd ℂ) (fderiv ℝ w₁ z v)
                  + dbar₁ G (0, 0) * (starRingEnd ℂ) (fderiv ℝ w₁ z v)))
              + (((dz₂ G (w₁ z, w₂ z) - dz₂ G (0, 0)) * fderiv ℝ w₂ z v
                  + dz₂ G (0, 0) * fderiv ℝ w₂ z v)
                + ((dbar₂ G (w₁ z, w₂ z) - dbar₂ G (0, 0))
                    * (starRingEnd ℂ) (fderiv ℝ w₂ z v)
                  + dbar₂ G (0, 0) * (starRingEnd ℂ) (fderiv ℝ w₂ z v)))) := by
          funext z
          have hd : fderiv ℝ (fun z => G (w₁ z, w₂ z) - G (0, 0)) z v
              = fderiv ℝ (fun z => G (w₁ z, w₂ z)) z v := by
            have h1 : HasFDerivAt (fun z => G (w₁ z, w₂ z) - G (0, 0))
                (fderiv ℝ (fun z => G (w₁ z, w₂ z)) z) z :=
              (((hdiffG _).comp z ((hw₁.1 z).prodMk (hw₂.1 z))).hasFDerivAt).sub_const _
            rw [h1.fderiv]
          rw [hd, fderiv_comp₂_apply hdiffG hw₁.1 hw₂.1 z v]
          ring
        rw [hfun]
        exact ⟨_, hhalf⟩
      obtain ⟨D₁, hD₁⟩ := hstep 1 (by simp)
      obtain ⟨D₂, hD₂⟩ := hstep Complex.I (by simp)
      exact ⟨D₁ + D₂, isHolderC_of_basis hdiffcomp hD₁ hD₂⟩

/-- **The bootstrap for a point-dependent nonlinear right-hand side, on shrinking discs.**  The
equation is `∂̄u = G (·, u)`, so the right-hand side depends on the point as well as on the
solution; the point is fed to the chain rule as a second inner function, cut off by the same
cut-off as the solution. -/
theorem exists_cutoff_isHolderC_comp₂ (hα : 0 < α) (hα1 : α < 1) {u : ℂ → ℂ} {G : ℂ × ℂ → ℂ}
    (hu : ContDiff ℝ 1 u) (hG : ContDiff ℝ ∞ G) (heq : ∀ z, dbar u z = G (z, u z)) :
    ∀ (k : ℕ) (z₀ : ℂ) (r : ℝ), 0 < r →
      ∃ (χ : ℂ → ℂ) (C : ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ
        ∧ (∀ z, dist z z₀ ≤ r → χ z = 1) ∧ IsHolderC k α C fun z => χ z * u z := by
  have hdiffu : Differentiable ℝ u := hu.differentiable one_ne_zero
  intro k
  induction k with
  | zero =>
      intro z₀ r hr
      obtain ⟨χ, hχ, hχs, hχ1, -⟩ := exists_cutoff z₀ hr
      have hv1 : ContDiff ℝ 1 fun z => χ z * u z := (hχ.of_le (by simp)).mul hu
      obtain ⟨C, hC⟩ := exists_holder_of_contDiff_one hv1 hχs.mul_right hα hα1.le
      exact ⟨χ, C, hχ, hχs, hχ1, hC⟩
  | succ k ih =>
      intro z₀ r hr
      obtain ⟨χ₀, C₀, hχ₀, hχ₀s, hχ₀1, hC₀⟩ := ih z₀ (4 * r) (by linarith)
      obtain ⟨χ, hχ, hχs, hχ1, hχ0⟩ := exists_cutoff z₀ hr
      have hdiffχ : Differentiable ℝ χ := hχ.differentiable (by simp)
      have hv1 : ContDiff ℝ 1 fun z => χ z * u z := (hχ.of_le (by simp)).mul hu
      have hvs : HasCompactSupport fun z => χ z * u z := hχs.mul_right
      have hws : HasCompactSupport fun z => χ₀ z * u z := hχ₀s.mul_right
      have htsup : tsupport χ ⊆ closedBall z₀ (2 * r) := by
        refine closure_minimal (fun z hz => ?_) isClosed_closedBall
        by_contra hcon
        rw [mem_closedBall, not_le] at hcon
        exact hz (hχ0 z hcon.le)
      have hone : ∀ z : ℂ, z ∈ tsupport χ → χ₀ z = 1 := by
        intro z hz
        have hdist := htsup hz
        rw [mem_closedBall] at hdist
        exact hχ₀1 z (by linarith)
      have honeχ : ∀ z : ℂ, χ z ≠ 0 → χ₀ z = 1 := fun z hz => hone z (subset_tsupport _ hz)
      have honedb : ∀ z : ℂ, dbar χ z ≠ 0 → χ₀ z = 1 := by
        intro z hz
        have hfd : fderiv ℝ χ z ≠ 0 := by
          intro h0
          apply hz
          rw [dbar, h0]
          simp
        exact hone z (support_fderiv_subset (𝕜 := ℝ) hfd)
      have hrhs : ∀ z : ℂ, χ z * dbar u z
          = χ z * (G (χ₀ z * z, χ₀ z * u z) - G (0, 0)) + χ z * G (0, 0) := by
        intro z
        rw [heq z]
        by_cases hz : χ z = 0
        · rw [hz]
          ring
        · rw [honeχ z hz, one_mul, one_mul]
          ring
      have hcomps : HasCompactSupport fun z => G (χ₀ z * z, χ₀ z * u z) - G (0, 0) := by
        refine HasCompactSupport.intro hχ₀s fun z hz => ?_
        rw [image_eq_zero_of_notMem_tsupport hz]
        simp
      obtain ⟨Cid, hCid⟩ := exists_isHolderC_of_contDiff hα hα1.le k (fun z => χ₀ z * z)
        ((hχ₀.mul contDiff_id).of_le (by exact_mod_cast (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤)))
        hχ₀s.mul_right
      obtain ⟨A, hA⟩ := exists_isHolderC_comp₂ hα hα1.le k G (fun z => χ₀ z * z)
        (fun z => χ₀ z * u z) Cid C₀ hG hCid hχ₀s.mul_right hC₀ hws
      obtain ⟨B₁, hB₁⟩ := exists_isHolderC_mul hα hα1.le k χ
        (fun z => G (χ₀ z * z, χ₀ z * u z) - G (0, 0)) A hχ hχs hA hcomps
      obtain ⟨B₂, hB₂⟩ := exists_isHolderC_of_contDiff hα hα1.le k (fun z => χ z * G (0, 0))
        ((hχ.mul contDiff_const).of_le (by exact_mod_cast (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤)))
        hχs.mul_right
      obtain ⟨B₃, hB₃⟩ := exists_isHolderC_mul hα hα1.le k (dbar χ) (fun z => χ₀ z * u z) C₀
        (contDiff_dbar hχ) (hasCompactSupport_dbar hχs) hC₀ hws
      have hdbv : ∀ z : ℂ, dbar (fun z => χ z * u z) z
          = χ z * (G (χ₀ z * z, χ₀ z * u z) - G (0, 0)) + χ z * G (0, 0)
            + dbar χ z * (χ₀ z * u z) := by
        intro z
        rw [dbar_mul hdiffχ hdiffu z, hrhs z]
        by_cases hz : dbar χ z = 0
        · rw [hz]
          ring
        · rw [honedb z hz]
          ring
      have hsum : IsHolderC k α (B₁ + B₂ + B₃) (dbar fun z => χ z * u z) := by
        have hfun : (dbar fun z => χ z * u z)
            = fun z => χ z * (G (χ₀ z * z, χ₀ z * u z) - G (0, 0)) + χ z * G (0, 0)
              + dbar χ z * (χ₀ z * u z) := funext hdbv
        rw [hfun]
        exact (hB₁.add hB₂).add hB₃
      obtain ⟨C, -, hC⟩ := isHolderC_cauchyTransform hα hα1 k _ _
        (hasCompactSupport_dbar hvs) hsum
      refine ⟨χ, C, hχ, hχs, hχ1, ?_⟩
      rw [← cauchyTransform_dbar hv1 hvs]
      exact hC

/-- **Elliptic regularity with a point-dependent nonlinearity.**  A `C¹` solution of
`∂u/∂x + i ∂u/∂y = G (z, u z)`, with `G` smooth in both variables, is smooth.  This is the form
the Floer equation takes once the Hamiltonian is allowed to depend on time. -/
theorem contDiff_infty_of_dbar_comp₂ {u : ℂ → ℂ} {G : ℂ × ℂ → ℂ} (hu : ContDiff ℝ 1 u)
    (hG : ContDiff ℝ ∞ G) (heq : ∀ z, dbar u z = G (z, u z)) : ContDiff ℝ ∞ u := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 : ℝ) / 2 < 1 := by norm_num
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro z₀
  obtain ⟨χ, C, hχ, hχs, hχ1, hC⟩ :=
    exists_cutoff_isHolderC_comp₂ (α := 1 / 2) hα hα1 hu hG heq n z₀ 1 one_pos
  have h1 : ContDiff ℝ n fun z => χ z * u z := hC.contDiff hα
  have hfeq : u =ᶠ[𝓝 z₀] fun z => χ z * u z := by
    filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    rw [mem_ball] at hz
    rw [hχ1 z hz.le, one_mul]
  exact h1.contDiffAt.congr_of_eventuallyEq hfeq

/-! ### Several inner functions

For a system the right-hand side of one equation depends on all the unknowns, so the chain rule
is needed for an outer function of `n` complex variables.  The proof is the one above with a
sum over the variables in place of two terms.
-/

theorem isHolderC_zero_fun (k : ℕ) (β : ℝ) : IsHolderC k β 0 fun _ : ℂ => (0 : ℂ) := by
  induction k with
  | zero =>
      intro ξ η
      simp
  | succ k ih =>
      refine ⟨differentiable_const 0, fun v hv => ?_⟩
      have hfun : (fun z : ℂ => fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z v) = fun _ : ℂ => (0 : ℂ) := by
        funext z
        simp
      rw [hfun]
      exact ih

theorem exists_isHolderC_finsetSum {ι : Type*} (k : ℕ) (s : Finset ι)
    {f : ι → ℂ → ℂ} {C : ℝ} (h : ∀ i ∈ s, IsHolderC k α C (f i)) :
    ∃ C' : ℝ, IsHolderC k α C' fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simpa using isHolderC_zero_fun k α⟩
  | insert a s ha ih =>
      obtain ⟨C₁, hC₁⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ha' := h a (Finset.mem_insert_self a s)
      refine ⟨C + C₁, ?_⟩
      have hfun : (fun z => ∑ i ∈ insert a s, f i z) = fun z => f a z + ∑ i ∈ s, f i z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact ha'.add hC₁

theorem exists_isHolderC_sumPi {k n : ℕ} {f : Fin n → ℂ → ℂ}
    (h : ∀ i, ∃ C, IsHolderC k α C (f i)) : ∃ C' : ℝ, IsHolderC k α C' fun z => ∑ i, f i z := by
  classical
  choose C hC using h
  refine exists_isHolderC_finsetSum k Finset.univ (C := ∑ i, C i) fun i _ => ?_
  exact (hC i).mono (Finset.single_le_sum (fun j _ => (hC j).const_nonneg) (Finset.mem_univ i))

variable {n : ℕ}

/-- The `∂/∂z` of the `i`-th variable of a function of `n` complex variables. -/
noncomputable def dzPi (G : (Fin n → ℂ) → ℂ) (i : Fin n) (p : Fin n → ℂ) : ℂ :=
  fderiv ℝ G p (Pi.single i 1) - Complex.I * fderiv ℝ G p (Pi.single i Complex.I)

/-- The `∂/∂z̄` of the `i`-th variable. -/
noncomputable def dbarPi (G : (Fin n → ℂ) → ℂ) (i : Fin n) (p : Fin n → ℂ) : ℂ :=
  fderiv ℝ G p (Pi.single i 1) + Complex.I * fderiv ℝ G p (Pi.single i Complex.I)

theorem contDiff_dzPi {G : (Fin n → ℂ) → ℂ} (hG : ContDiff ℝ ∞ G) (i : Fin n) :
    ContDiff ℝ ∞ (dzPi G i) :=
  ((hG.fderiv_right (by simp)).clm_apply contDiff_const).sub
    (contDiff_const.mul ((hG.fderiv_right (by simp)).clm_apply contDiff_const))

theorem contDiff_dbarPi {G : (Fin n → ℂ) → ℂ} (hG : ContDiff ℝ ∞ G) (i : Fin n) :
    ContDiff ℝ ∞ (dbarPi G i) :=
  ((hG.fderiv_right (by simp)).clm_apply contDiff_const).add
    (contDiff_const.mul ((hG.fderiv_right (by simp)).clm_apply contDiff_const))

/-- **The derivative of a composition with several inner functions**, in Wirtinger form. -/
theorem fderiv_compPi_apply {G : (Fin n → ℂ) → ℂ} (hG : Differentiable ℝ G) {w : Fin n → ℂ → ℂ}
    (hw : ∀ i, Differentiable ℝ (w i)) (z v : ℂ) :
    fderiv ℝ (fun z => G fun i => w i z) z v
      = ∑ i, (dzPi G i (fun j => w j z) * fderiv ℝ (w i) z v
          + dbarPi G i (fun j => w j z) * (starRingEnd ℂ) (fderiv ℝ (w i) z v)) / 2 := by
  have hW : HasFDerivAt (fun z => fun i => w i z)
      (ContinuousLinearMap.pi fun i => fderiv ℝ (w i) z) z :=
    hasFDerivAt_pi.2 fun i => (hw i z).hasFDerivAt
  have hchain : fderiv ℝ (fun z => G fun i => w i z) z
      = (fderiv ℝ G (fun i => w i z)).comp (ContinuousLinearMap.pi fun i => fderiv ℝ (w i) z) :=
    (((hG _).hasFDerivAt).comp z hW).fderiv
  rw [hchain]
  show fderiv ℝ G (fun i => w i z) (fun i => fderiv ℝ (w i) z v) = _
  rw [← ContinuousLinearMap.sum_comp_single (L := fderiv ℝ G fun j => w j z)
    (v := fun i => fderiv ℝ (w i) z v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eq_dPair ((fderiv ℝ G fun j => w j z).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i)), dPair_apply]
  simp only [dzPi, dbarPi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]

/-- **The chain rule on the scale, for a function of `n` variables.** -/
theorem exists_isHolderC_compPi (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ (k : ℕ) (G : (Fin n → ℂ) → ℂ) (w : Fin n → ℂ → ℂ) (C : ℝ), ContDiff ℝ ∞ G →
      (∀ i, IsHolderC k α C (w i)) → (∀ i, HasCompactSupport (w i)) → 0 ≤ C →
      ∃ C' : ℝ, IsHolderC k α C' fun z => G (fun i => w i z) - G 0 := by
  intro k
  induction k with
  | zero =>
      intro G w C hG hw hws hC0
      have hb : ∀ i, ∃ R : ℝ, ∀ z, ‖w i z‖ ≤ R := fun i =>
        (hws i).exists_bound_of_continuous ((hw i).continuous hα)
      choose R hR using hb
      have hR0 : ∀ i, (0 : ℝ) ≤ R i := fun i => le_trans (norm_nonneg _) (hR i 0)
      have hS0 : (0 : ℝ) ≤ ∑ i, R i := Finset.sum_nonneg fun i _ => hR0 i
      have hmem : ∀ z : ℂ, (fun i => w i z) ∈ closedBall (0 : Fin n → ℂ) (∑ i, R i) := by
        intro z
        rw [mem_closedBall, dist_zero_right]
        refine (pi_norm_le_iff_of_nonneg hS0).2 fun i => ?_
        exact le_trans (hR i z) (Finset.single_le_sum (fun j _ => hR0 j) (Finset.mem_univ i))
      obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : Fin n → ℂ) (∑ i, R i)).exists_bound_of_continuousOn
        (hG.continuous_fderiv (by simp)).continuousOn
      have hdiffG : Differentiable ℝ G := hG.differentiable (by simp)
      have hL0 : (0 : ℝ) ≤ L :=
        le_trans (norm_nonneg _) (hL 0 (by rw [mem_closedBall, dist_self]; exact hS0))
      refine ⟨L * C, fun ξ η => ?_⟩
      have he : G (fun i => w i ξ) - G 0 - (G (fun i => w i η) - G 0)
          = G (fun i => w i ξ) - G (fun i => w i η) := by ring
      rw [he]
      have hnorm : ‖(fun i => w i ξ) - fun i => w i η‖ ≤ C * ‖ξ - η‖ ^ α := by
        refine (pi_norm_le_iff_of_nonneg
          (mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg _) _))).2 fun i => ?_
        simpa using hw i ξ η
      calc ‖G (fun i => w i ξ) - G (fun i => w i η)‖
          ≤ L * ‖(fun i => w i ξ) - fun i => w i η‖ :=
            Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiffG x) (fun x hx => hL x hx)
              (convex_closedBall _ _) (hmem η) (hmem ξ)
        _ ≤ L * (C * ‖ξ - η‖ ^ α) := mul_le_mul_of_nonneg_left hnorm hL0
        _ = L * C * ‖ξ - η‖ ^ α := by ring
  | succ k ih =>
      intro G w C hG hw hws hC0
      have hdiffG : Differentiable ℝ G := hG.differentiable (by simp)
      have hdiffW : ∀ z : ℂ, DifferentiableAt ℝ (fun z => fun i => w i z) z := fun z =>
        (hasFDerivAt_pi.2 fun i => ((hw i).1 z).hasFDerivAt).differentiableAt
      have hcs : ∀ H : (Fin n → ℂ) → ℂ, HasCompactSupport fun z => H (fun i => w i z) - H 0 := by
        intro H
        refine HasCompactSupport.intro (isCompact_iUnion fun i => hws i) fun z hz => ?_
        have h0 : (fun i => w i z) = 0 := by
          funext i
          exact image_eq_zero_of_notMem_tsupport fun hc => hz (Set.mem_iUnion.2 ⟨i, hc⟩)
        rw [h0]
        ring
      have hlow : ∀ i, ∃ C' : ℝ, IsHolderC k α C' (w i) := fun i =>
        isHolderC_of_succ hα hα1 k (w i) C (hw i) (hws i)
      choose Ci hCi using hlow
      have hCw0 : (0 : ℝ) ≤ ∑ j, Ci j := Finset.sum_nonneg fun j _ => (hCi j).const_nonneg
      have hCw : ∀ i, IsHolderC k α (∑ j, Ci j) (w i) := fun i =>
        (hCi i).mono (Finset.single_le_sum (fun j _ => (hCi j).const_nonneg) (Finset.mem_univ i))
      have hdiffcomp : Differentiable ℝ fun z => G (fun i => w i z) - G 0 := fun z =>
        ((hdiffG _).comp z (hdiffW z)).sub_const _
      have hstep : ∀ v : ℂ, ‖v‖ ≤ 1 → ∃ D : ℝ,
          IsHolderC k α D fun z => fderiv ℝ (fun z => G (fun i => w i z) - G 0) z v := by
        intro v hv
        have hd : ∀ i, IsHolderC k α C fun z => fderiv ℝ (w i) z v := fun i => (hw i).2 v hv
        have hds : ∀ i, HasCompactSupport fun z => fderiv ℝ (w i) z v := fun i =>
          ((hws i).fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) rfl
        have hsummand : ∀ i : Fin n, ∃ D : ℝ, IsHolderC k α D fun z =>
            (dzPi G i (fun j => w j z) * fderiv ℝ (w i) z v
              + dbarPi G i (fun j => w j z) * (starRingEnd ℂ) (fderiv ℝ (w i) z v)) / 2 := by
          intro i
          obtain ⟨A₁, hA₁⟩ := ih (dzPi G i) w (∑ j, Ci j) (contDiff_dzPi hG i) hCw hws hCw0
          obtain ⟨A₂, hA₂⟩ := ih (dbarPi G i) w (∑ j, Ci j) (contDiff_dbarPi hG i) hCw hws hCw0
          obtain ⟨D₁, hD₁⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₁ C hA₁ (hcs (dzPi G i))
            (hd i) (hds i)
          obtain ⟨D₂, hD₂⟩ := exists_isHolderC_mul_mul hα hα1 k _ _ A₂ C hA₂ (hcs (dbarPi G i))
            (hd i).conj ((hds i).comp_left (g := starRingEnd ℂ) (by simp))
          have hsum := (hD₁.add (IsHolderC.const_mul (dzPi G i 0) (hd i))).add
            (hD₂.add (IsHolderC.const_mul (dbarPi G i 0) (hd i).conj))
          have hhalf := IsHolderC.const_mul ((2 : ℂ)⁻¹) hsum
          have hfun : (fun z => (dzPi G i (fun j => w j z) * fderiv ℝ (w i) z v
                + dbarPi G i (fun j => w j z) * (starRingEnd ℂ) (fderiv ℝ (w i) z v)) / 2)
              = fun z => (2 : ℂ)⁻¹ * (((dzPi G i (fun j => w j z) - dzPi G i 0)
                      * fderiv ℝ (w i) z v + dzPi G i 0 * fderiv ℝ (w i) z v)
                  + ((dbarPi G i (fun j => w j z) - dbarPi G i 0)
                      * (starRingEnd ℂ) (fderiv ℝ (w i) z v)
                    + dbarPi G i 0 * (starRingEnd ℂ) (fderiv ℝ (w i) z v))) := by
            funext z
            ring
          rw [hfun]
          exact ⟨_, hhalf⟩
        obtain ⟨D, hD⟩ := exists_isHolderC_sumPi hsummand
        have hfun : (fun z => fderiv ℝ (fun z => G (fun i => w i z) - G 0) z v)
            = fun z => ∑ i, (dzPi G i (fun j => w j z) * fderiv ℝ (w i) z v
                + dbarPi G i (fun j => w j z) * (starRingEnd ℂ) (fderiv ℝ (w i) z v)) / 2 := by
          funext z
          have hd2 : fderiv ℝ (fun z => G (fun i => w i z) - G 0) z v
              = fderiv ℝ (fun z => G (fun i => w i z)) z v := by
            have h1 : HasFDerivAt (fun z => G (fun i => w i z) - G 0)
                (fderiv ℝ (fun z => G (fun i => w i z)) z) z :=
              (((hdiffG _).comp z (hdiffW z)).hasFDerivAt).sub_const _
            rw [h1.fderiv]
          rw [hd2, fderiv_compPi_apply hdiffG (fun i => (hw i).1) z v]
        rw [hfun]
        exact ⟨D, hD⟩
      obtain ⟨D₁, hD₁⟩ := hstep 1 (by simp)
      obtain ⟨D₂, hD₂⟩ := hstep Complex.I (by simp)
      exact ⟨D₁ + D₂, isHolderC_of_basis hdiffcomp hD₁ hD₂⟩

/-! ### A system of equations

The Floer equation for maps into `ℝ^{2n}` is, after the identification with `ℂⁿ`, a system of
`n` scalar equations coupled only through the right-hand side.  The bootstrap therefore runs on
all components at once: if all of them are on level `k`, each right-hand side is too, by the
chain rule of the previous section, and every component climbs to level `k + 1`.
-/

/-- **The bootstrap for a system, on shrinking discs.** -/
theorem exists_cutoff_isHolderC_system (hα : 0 < α) (hα1 : α < 1) {u : Fin n → ℂ → ℂ}
    {G : Fin n → (Fin (n + 1) → ℂ) → ℂ} (hu : ∀ i, ContDiff ℝ 1 (u i))
    (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (heq : ∀ (i : Fin n) (z : ℂ), dbar (u i) z = G i (Fin.cons z fun j => u j z)) :
    ∀ (k : ℕ) (z₀ : ℂ) (r : ℝ), 0 < r →
      ∃ (χ : ℂ → ℂ) (C : ℝ), 0 ≤ C ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ
        ∧ (∀ z, dist z z₀ ≤ r → χ z = 1) ∧ ∀ i, IsHolderC k α C fun z => χ z * u i z := by
  have hdiffu : ∀ i, Differentiable ℝ (u i) := fun i => (hu i).differentiable one_ne_zero
  intro k
  induction k with
  | zero =>
      intro z₀ r hr
      obtain ⟨χ, hχ, hχs, hχ1, -⟩ := exists_cutoff z₀ hr
      have hbase : ∀ i, ∃ C : ℝ, IsHolderC 0 α C fun z => χ z * u i z := by
        intro i
        exact exists_holder_of_contDiff_one ((hχ.of_le (by simp)).mul (hu i)) hχs.mul_right
          hα hα1.le
      choose Cf hCf using hbase
      refine ⟨χ, ∑ i, Cf i, Finset.sum_nonneg fun i _ => (hCf i).const_nonneg, hχ, hχs, hχ1,
        fun i => (hCf i).mono
          (Finset.single_le_sum (fun j _ => (hCf j).const_nonneg) (Finset.mem_univ i))⟩
  | succ k ih =>
      intro z₀ r hr
      obtain ⟨χ₀, C₀, hC₀0, hχ₀, hχ₀s, hχ₀1, hC₀⟩ := ih z₀ (4 * r) (by linarith)
      obtain ⟨χ, hχ, hχs, hχ1, hχ0⟩ := exists_cutoff z₀ hr
      have hdiffχ : Differentiable ℝ χ := hχ.differentiable (by simp)
      have hv1 : ∀ i, ContDiff ℝ 1 fun z => χ z * u i z := fun i =>
        (hχ.of_le (by simp)).mul (hu i)
      have hvs : ∀ i, HasCompactSupport fun z => χ z * u i z := fun i => hχs.mul_right
      have htsup : tsupport χ ⊆ closedBall z₀ (2 * r) := by
        refine closure_minimal (fun z hz => ?_) isClosed_closedBall
        by_contra hcon
        rw [mem_closedBall, not_le] at hcon
        exact hz (hχ0 z hcon.le)
      have hone : ∀ z : ℂ, z ∈ tsupport χ → χ₀ z = 1 := by
        intro z hz
        have hdist := htsup hz
        rw [mem_closedBall] at hdist
        exact hχ₀1 z (by linarith)
      have honeχ : ∀ z : ℂ, χ z ≠ 0 → χ₀ z = 1 := fun z hz => hone z (subset_tsupport _ hz)
      have honedb : ∀ z : ℂ, dbar χ z ≠ 0 → χ₀ z = 1 := by
        intro z hz
        have hfd : fderiv ℝ χ z ≠ 0 := by
          intro h0
          apply hz
          rw [dbar, h0]
          simp
        exact hone z (support_fderiv_subset (𝕜 := ℝ) hfd)
      -- the inner functions of the chain rule: the cut-off point, and the cut-off components
      obtain ⟨Cid, hCid⟩ := exists_isHolderC_of_contDiff hα hα1.le k (fun z => χ₀ z * z)
        ((hχ₀.mul contDiff_id).of_le (by exact_mod_cast (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤)))
        hχ₀s.mul_right
      have hCid0 : (0 : ℝ) ≤ Cid := hCid.const_nonneg
      set w : Fin (n + 1) → ℂ → ℂ := Fin.cons (fun z => χ₀ z * z) fun j z => χ₀ z * u j z with hw0
      have hwapp : ∀ z : ℂ, (fun i => w i z) = Fin.cons (χ₀ z * z) fun j => χ₀ z * u j z := by
        intro z
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [hw0]
        · intro j
          simp [hw0]
      have hw : ∀ i, IsHolderC k α (Cid + C₀) (w i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · have h : IsHolderC k α (Cid + C₀) fun z => χ₀ z * z := hCid.mono (by linarith)
          simpa [hw0] using h
        · intro j
          have h : IsHolderC k α (Cid + C₀) fun z => χ₀ z * u j z :=
            (hC₀ j).mono (by linarith)
          simpa [hw0] using h
      have hws : ∀ i, HasCompactSupport (w i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · have h : HasCompactSupport fun z => χ₀ z * z := hχ₀s.mul_right
          simpa [hw0] using h
        · intro j
          have h : HasCompactSupport fun z => χ₀ z * u j z := hχ₀s.mul_right
          simpa [hw0] using h
      have hcompcs : ∀ i : Fin n, HasCompactSupport fun z => G i (fun l => w l z) - G i 0 := by
        intro i
        refine HasCompactSupport.intro (isCompact_iUnion fun l => hws l) fun z hz => ?_
        have h0 : (fun l => w l z) = 0 := by
          funext l
          exact image_eq_zero_of_notMem_tsupport fun hc => hz (Set.mem_iUnion.2 ⟨l, hc⟩)
        rw [h0]
        ring
      have hrhs : ∀ (i : Fin n) (z : ℂ), χ z * dbar (u i) z
          = χ z * (G i (fun l => w l z) - G i 0) + χ z * G i 0 := by
        intro i z
        rw [heq i z]
        by_cases hz : χ z = 0
        · rw [hz]
          ring
        · rw [hwapp z, honeχ z hz]
          simp only [one_mul]
          ring
      have hfinal : ∀ i : Fin n, ∃ C' : ℝ, IsHolderC (k + 1) α C' fun z => χ z * u i z := by
        intro i
        obtain ⟨A, hA⟩ := exists_isHolderC_compPi hα hα1.le k (G i) w (Cid + C₀) (hG i) hw hws
          (by linarith)
        obtain ⟨B₁, hB₁⟩ := exists_isHolderC_mul hα hα1.le k χ
          (fun z => G i (fun l => w l z) - G i 0) A hχ hχs hA (hcompcs i)
        obtain ⟨B₂, hB₂⟩ := exists_isHolderC_of_contDiff hα hα1.le k (fun z => χ z * G i 0)
          ((hχ.mul contDiff_const).of_le (by exact_mod_cast (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤)))
          hχs.mul_right
        obtain ⟨B₃, hB₃⟩ := exists_isHolderC_mul hα hα1.le k (dbar χ) (fun z => χ₀ z * u i z) C₀
          (contDiff_dbar hχ) (hasCompactSupport_dbar hχs) (hC₀ i) hχ₀s.mul_right
        have hdbv : ∀ z : ℂ, dbar (fun z => χ z * u i z) z
            = χ z * (G i (fun l => w l z) - G i 0) + χ z * G i 0
              + dbar χ z * (χ₀ z * u i z) := by
          intro z
          rw [dbar_mul hdiffχ (hdiffu i) z, hrhs i z]
          by_cases hz : dbar χ z = 0
          · rw [hz]
            ring
          · rw [honedb z hz]
            ring
        have hsum : IsHolderC k α (B₁ + B₂ + B₃) (dbar fun z => χ z * u i z) := by
          have hfun : (dbar fun z => χ z * u i z)
              = fun z => χ z * (G i (fun l => w l z) - G i 0) + χ z * G i 0
                + dbar χ z * (χ₀ z * u i z) := funext (hdbv)
          rw [hfun]
          exact (hB₁.add hB₂).add hB₃
        obtain ⟨C', -, hC'⟩ := isHolderC_cauchyTransform hα hα1 k _ _
          (hasCompactSupport_dbar (hvs i)) hsum
        refine ⟨C', ?_⟩
        rw [← cauchyTransform_dbar (hv1 i) (hvs i)]
        exact hC'
      choose Cf hCf using hfinal
      refine ⟨χ, ∑ i, Cf i, Finset.sum_nonneg fun i _ => (hCf i).const_nonneg, hχ, hχs, hχ1,
        fun i => (hCf i).mono
          (Finset.single_le_sum (fun j _ => (hCf j).const_nonneg) (Finset.mem_univ i))⟩

/-- **Elliptic regularity for a system.**  A `C¹` solution of the system
`∂̄u_i = G_i (z, u_1, …, u_n)`, with every `G_i` smooth, is smooth.  This is the form the Floer
equation takes for maps into `ℝ^{2n} ≅ ℂⁿ` with a time-dependent Hamiltonian. -/
theorem contDiff_infty_of_dbar_system {u : Fin n → ℂ → ℂ} {G : Fin n → (Fin (n + 1) → ℂ) → ℂ}
    (hu : ∀ i, ContDiff ℝ 1 (u i)) (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (heq : ∀ (i : Fin n) (z : ℂ), dbar (u i) z = G i (Fin.cons z fun j => u j z)) (i : Fin n) :
    ContDiff ℝ ∞ (u i) := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 : ℝ) / 2 < 1 := by norm_num
  rw [contDiff_infty]
  intro m
  rw [contDiff_iff_contDiffAt]
  intro z₀
  obtain ⟨χ, C, -, hχ, hχs, hχ1, hC⟩ :=
    exists_cutoff_isHolderC_system (α := 1 / 2) hα hα1 hu hG heq m z₀ 1 one_pos
  have h1 : ContDiff ℝ m fun z => χ z * u i z := (hC i).contDiff hα
  have hfeq : u i =ᶠ[𝓝 z₀] fun z => χ z * u i z := by
    filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    rw [mem_ball] at hz
    rw [hχ1 z hz.le, one_mul]
  exact h1.contDiffAt.congr_of_eventuallyEq hfeq

end CauchyHolder
end MorseFloer
