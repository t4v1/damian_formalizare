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
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
          ring
        rw [hfun]
        exact hC₁.add hC₂
      obtain ⟨C₁, hC₁⟩ := hstep 1 (by simp)
      obtain ⟨C₂, hC₂⟩ := hstep Complex.I (by simp)
      exact ⟨C₁ + C₂, isHolderC_of_basis hprod hC₁ hC₂⟩

end CauchyHolder
end MorseFloer
