import Mathlib

/-!
# The Cauchy–Pompeiu formula for compactly supported functions

For a compactly supported `C¹` function `w : ℂ → ℂ` and every `z : ℂ`,

`∫ ξ, (∂w/∂x + i ∂w/∂y) (z - ξ) / ξ = 2π w z`.

Equivalently, the Cauchy transform `v = -(1/2π) (1/ξ) ⋆ w` solves `∂̄v = w`: this is the
inhomogeneous companion of `Part2/Weyl.lean`, which handles `∂̄u = 0`.

## Why this file exists

Chapter 6 assumes elliptic regularity for the Floer equation (Proposition 6.5.3): a `C¹`
solution of `∂̄u = -∇H_t(u)` is `C^∞`.  Mathlib has no elliptic theory at all, and the
route to that statement is

1. this file: solve `∂̄v = w` for compactly supported `w`, with `v` given by an explicit
   convolution against the Cauchy kernel `1/ξ` (`cauchyTransform`);
2. Hölder estimates for that convolution (`C^{k,α} → C^{k+1,α}`, Schauder theory), which
   is the step that actually gains a derivative and which this file does **not** contain;
3. bootstrapping: `u - v` is holomorphic by `Part2/Weyl.lean`, hence `C^∞`, so `u` is as
   smooth as `v`.

Step 2 is what remains before Proposition 6.5.3 can be proved.  Note that the `C^k` scale
alone is not enough: the Cauchy transform of a `C^k` function is `C^k`, not `C^{k+1}`, so
the bootstrap needs the Hölder scale.

## Main results

* `MorseFloer.CauchyPompeiu.integral_dbar_div_eq`: the formula above.
* `MorseFloer.CauchyPompeiu.cauchyTransform`: the solution operator
  `T f (z) = (2π)⁻¹ ∫ f (z - ξ) / ξ`, together with the two halves of the statement that it
  inverts the Cauchy–Riemann operator on compactly supported `C¹` functions,
  `cauchyTransform_dbar` (`T (∂w/∂x + i ∂w/∂y) = w`) and `dbar_cauchyTransform`
  (`∂(T f)/∂x + i ∂(T f)/∂y = f`).
* `MorseFloer.CauchyPompeiu.integrableOn_inv_norm_ball`: the Cauchy kernel `1/ξ` is locally
  integrable in the plane, which is what makes the transform well defined and lets the
  derivative be taken under the integral sign.

## Proof

Everything happens in polar coordinates centred at `z`.  Writing `g r θ = w (z - r e^{iθ})`,
the chain rule gives the pointwise identity

`(∂w/∂x + i ∂w/∂y) (z - r e^{iθ}) · e^{-iθ} = -(∂g/∂r) - (i/r) (∂g/∂θ)`

(`dbar_polar_eq`).  The `∂g/∂θ` term integrates to zero over a full turn, by periodicity,
and the `∂g/∂r` term integrates, by the fundamental theorem of calculus in `r`, to
`-2π w z`, because `g 0 θ = w z` and `g r θ = 0` for large `r`.  The passage between the
plane and polar coordinates is `Complex.integral_comp_polarCoord_symm`, and the derivative
of `r ↦ ∫ g r θ dθ` is taken under the integral sign.
-/

open MeasureTheory Filter Topology Metric Set
open scoped Real ContDiff ENNReal NNReal

namespace MorseFloer
namespace CauchyPompeiu

/-! ### The unit circle as a function of the angle -/

/-- `circ θ = e^{iθ}`. -/
noncomputable def circ (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

theorem norm_circ (θ : ℝ) : ‖circ θ‖ = 1 := by
  simp [circ]

theorem circ_ne_zero (θ : ℝ) : circ θ ≠ 0 := Complex.exp_ne_zero _

theorem continuous_circ : Continuous circ := by
  unfold circ; fun_prop

theorem hasDerivAt_circ (θ : ℝ) : HasDerivAt circ (Complex.I * circ θ) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
  have h2 := h1.cexp
  rw [mul_comm] at h2
  exact h2

theorem circ_pi : circ π = -1 := by
  simp [circ, Complex.exp_mul_I]

theorem circ_neg_pi : circ (-π) = -1 := by
  simp [circ]

/-- Polar coordinates in `ℂ` in terms of `circ`. -/
theorem polarCoord_symm_eq (r θ : ℝ) : Complex.polarCoord.symm (r, θ) = r * circ θ := by
  rw [Complex.polarCoord_symm_apply, circ, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-! ### The Cauchy–Riemann operator -/

/-- The Cauchy–Riemann operator `∂/∂x + i ∂/∂y`, twice the usual `∂̄`.  This is the form in
which the weak equation is written in `Part2/Ch12.lean` and `Part2/Weyl.lean`. -/
noncomputable def dbar (w : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  fderiv ℝ w ζ 1 + Complex.I * fderiv ℝ w ζ Complex.I

theorem continuous_dbar {w : ℂ → ℂ} (hw : ContDiff ℝ 1 w) : Continuous (dbar w) := by
  have h : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  unfold dbar
  exact (h.clm_apply continuous_const).add
    (continuous_const.mul (h.clm_apply continuous_const))

theorem hasCompactSupport_dbar {w : ℂ → ℂ} (hc : HasCompactSupport w) :
    HasCompactSupport (dbar w) := by
  have h : HasCompactSupport (fderiv ℝ w) := hc.fderiv (𝕜 := ℝ)
  apply HasCompactSupport.intro h
  intro ζ hζ
  have h0 : fderiv ℝ w ζ = 0 := image_eq_zero_of_notMem_tsupport hζ
  simp [dbar, h0]

/-- The algebraic identity behind the polar form of `dbar`: for a real-linear `L` and an
angle `θ`, `(L 1 + i L i) e^{-iθ} = L (e^{iθ}) + i L (i e^{iθ})`. -/
theorem dbar_circ_eq (L : ℂ →L[ℝ] ℂ) (θ : ℝ) :
    (L 1 + Complex.I * L Complex.I) * (circ θ)⁻¹
      = L (circ θ) + Complex.I * L (Complex.I * circ θ) := by
  have hc : circ θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [circ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hpy : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.sin_sq_add_cos_sq θ)
  -- `L` on a real combination of `1` and `i`
  have hL : ∀ a b : ℝ, L ((a : ℂ) + (b : ℂ) * Complex.I)
      = (a : ℂ) * L 1 + (b : ℂ) * L Complex.I := by
    intro a b
    have he : ((a : ℂ) + (b : ℂ) * Complex.I) = a • (1 : ℂ) + b • Complex.I := by
      simp [Complex.real_smul]
    rw [he, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hmul : circ θ * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) = 1 := by
    rw [hc]
    linear_combination (-(Real.sin θ : ℂ) ^ 2) * Complex.I_sq + hpy
  have hinv : (circ θ)⁻¹ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I :=
    inv_eq_of_mul_eq_one_right hmul
  have hIc : Complex.I * circ θ
      = ((-Real.sin θ : ℝ) : ℂ) + ((Real.cos θ : ℝ) : ℂ) * Complex.I := by
    rw [hc, Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * Complex.I_sq
  have h1 : L (circ θ) = (Real.cos θ : ℂ) * L 1 + (Real.sin θ : ℂ) * L Complex.I := by
    rw [hc, hL]
  have h2 : L (Complex.I * circ θ)
      = ((-Real.sin θ : ℝ) : ℂ) * L 1 + (Real.cos θ : ℂ) * L Complex.I := by
    rw [hIc, hL]
  rw [h1, h2, hinv, Complex.ofReal_neg]
  linear_combination (-(Real.sin θ : ℂ) * L Complex.I) * Complex.I_sq

/-! ### The polar form of a compactly supported function -/

variable {w : ℂ → ℂ} {z : ℂ}

/-- `polarFn w z r θ = w (z - r e^{iθ})`. -/
noncomputable def polarFn (w : ℂ → ℂ) (z : ℂ) (r θ : ℝ) : ℂ := w (z - r * circ θ)

theorem continuous_polarFn (hw : Continuous w) (z : ℂ) :
    Continuous fun p : ℝ × ℝ => polarFn w z p.1 p.2 := by
  unfold polarFn
  have : Continuous fun p : ℝ × ℝ => z - (p.1 : ℂ) * circ p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) := Complex.continuous_ofReal.comp
      continuous_fst
    exact continuous_const.sub (h1.mul (continuous_circ.comp continuous_snd))
  exact hw.comp this

/-- The `r`-derivative of `w (z - r e^{iθ})`. -/
theorem hasDerivAt_polarFn_fst (hw : Differentiable ℝ w) (z : ℂ) (r θ : ℝ) :
    HasDerivAt (fun r : ℝ => polarFn w z r θ)
      (-(fderiv ℝ w (z - r * circ θ) (circ θ))) r := by
  have h1 : HasDerivAt (fun r : ℝ => z - (r : ℂ) * circ θ) (-(circ θ)) r := by
    have : HasDerivAt (fun r : ℝ => (r : ℂ) * circ θ) (circ θ) r := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (circ θ)
    simpa using this.const_sub z
  have h2 := (hw (z - r * circ θ)).hasFDerivAt.comp_hasDerivAt r h1
  rw [map_neg] at h2
  exact h2

/-- The `θ`-derivative of `w (z - r e^{iθ})`. -/
theorem hasDerivAt_polarFn_snd (hw : Differentiable ℝ w) (z : ℂ) (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => polarFn w z r θ)
      (-(fderiv ℝ w (z - r * circ θ) (Complex.I * (r : ℂ) * circ θ))) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => z - (r : ℂ) * circ θ)
      (-((r : ℂ) * (Complex.I * circ θ))) θ := by
    have := ((hasDerivAt_circ θ).const_mul (r : ℂ))
    simpa using this.const_sub z
  have h2 := (hw (z - r * circ θ)).hasFDerivAt.comp_hasDerivAt θ h1
  rw [map_neg, show ((r : ℂ) * (Complex.I * circ θ)) = Complex.I * (r : ℂ) * circ θ by ring] at h2
  exact h2

/-- **The polar form of the Cauchy–Riemann operator.**  Along the ray of angle `θ`,
`(∂w/∂x + i ∂w/∂y)(z - r e^{iθ}) e^{-iθ}` is `-(∂/∂r) - (i/r)(∂/∂θ)` applied to
`w (z - r e^{iθ})`. -/
theorem dbar_polar_eq (_hw : Differentiable ℝ w) (z : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    dbar w (z - r * circ θ) * (circ θ)⁻¹
      = -(-(fderiv ℝ w (z - r * circ θ) (circ θ)))
        - (Complex.I / r) * -(fderiv ℝ w (z - r * circ θ) (Complex.I * (r : ℂ) * circ θ)) := by
  set L := fderiv ℝ w (z - r * circ θ) with hL
  have hI : L (Complex.I * (r : ℂ) * circ θ) = (r : ℂ) * L (Complex.I * circ θ) := by
    have : Complex.I * (r : ℂ) * circ θ = (r : ℝ) • (Complex.I * circ θ) := by
      simp [Complex.real_smul]; ring
    rw [this, map_smul, Complex.real_smul]
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  rw [dbar, ← hL, dbar_circ_eq L θ, hI]
  field_simp
  ring


/-! ### The Cauchy–Pompeiu formula -/

/-- The integrand of the Cauchy–Pompeiu integral in polar coordinates centred at `z`:
`polarDbar w z (r, θ) = (∂w/∂x + i ∂w/∂y) (z - r e^{iθ}) e^{-iθ}`. -/
noncomputable def polarDbar (w : ℂ → ℂ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  dbar w (z - p.1 * circ p.2) * (circ p.2)⁻¹

theorem continuous_shift (z : ℂ) : Continuous fun p : ℝ × ℝ => z - (p.1 : ℂ) * circ p.2 := by
  have h1 : Continuous fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  exact continuous_const.sub (h1.mul (continuous_circ.comp continuous_snd))

theorem continuous_polarDbar (hw : ContDiff ℝ 1 w) (z : ℂ) : Continuous (polarDbar w z) :=
  ((continuous_dbar hw).comp (continuous_shift z)).mul
    (((continuous_circ.comp continuous_snd)).inv₀ fun p => circ_ne_zero p.2)

/-- A radius outside which both `w` and `∂w/∂x + i ∂w/∂y` vanish. -/
theorem exists_radius (hc : HasCompactSupport w) :
    ∃ R : ℝ, 0 < R ∧ ∀ ζ : ℂ, R ≤ ‖ζ‖ → w ζ = 0 ∧ fderiv ℝ w ζ = 0 := by
  obtain ⟨R₁, h₁⟩ := (IsCompact.isBounded hc).subset_closedBall (0 : ℂ)
  obtain ⟨R₂, h₂⟩ := (IsCompact.isBounded (hc.fderiv (𝕜 := ℝ))).subset_closedBall (0 : ℂ)
  refine ⟨max 1 (max R₁ R₂) + 1, by positivity, fun ζ hζ => ⟨?_, ?_⟩⟩
  · refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h3 := h₁ hmem
    rw [mem_closedBall, dist_zero_right] at h3
    have h4 : R₁ ≤ max 1 (max R₁ R₂) := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  · refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h3 := h₂ hmem
    rw [mem_closedBall, dist_zero_right] at h3
    have h4 : R₂ ≤ max 1 (max R₁ R₂) := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith

theorem norm_shift_ge {z : ℂ} (r θ : ℝ) (hr : 0 ≤ r) : r - ‖z‖ ≤ ‖z - (r : ℂ) * circ θ‖ := by
  have h1 : ‖(r : ℂ) * circ θ‖ = r := by
    rw [norm_mul, norm_circ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have h2 := norm_sub_norm_le ((r : ℂ) * circ θ) z
  rw [h1] at h2
  rwa [norm_sub_rev]

/-- Passage to polar coordinates centred at `z`. -/
theorem integral_dbar_div_eq_polar (z : ℂ) :
    ∫ ξ : ℂ, dbar w (z - ξ) / ξ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, polarDbar w z p := by
  rw [← Complex.integral_comp_polarCoord_symm fun ξ => dbar w (z - ξ) / ξ, polarCoord_target]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨hr, -⟩
  have hr' : (0 : ℝ) < r := hr
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr'.ne'
  simp only [polarDbar, polarCoord_symm_eq, Complex.real_smul]
  field_simp

/-- The polar integrand is integrable: it is continuous, bounded, and vanishes for large
radius. -/
theorem integrableOn_polarDbar (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport w) (z : ℂ) :
    IntegrableOn (polarDbar w z) (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
  obtain ⟨R, hR0, hR⟩ := exists_radius hc
  obtain ⟨C, hC⟩ := (hasCompactSupport_dbar hc).exists_bound_of_continuous (continuous_dbar hw)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set S : ℝ := R + ‖z‖ + 1 with hS
  set box : Set (ℝ × ℝ) := Icc 0 S ×ˢ Icc (-π) π with hbox
  have hboxc : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hbound : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ‖polarDbar w z p‖ ≤ box.indicator (fun _ => C) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    have hr' : (0 : ℝ) < r := hr
    by_cases hrS : r ≤ S
    · rw [indicator_of_mem (show (r, θ) ∈ box from ⟨⟨hr'.le, hrS⟩, ⟨hθ.1.le, hθ.2.le⟩⟩)]
      simp only [polarDbar, norm_mul, norm_inv, norm_circ, inv_one, mul_one]
      exact hC _
    · have hfz : fderiv ℝ w (z - (r : ℂ) * circ θ) = 0 := by
        refine (hR _ ?_).2
        have h1 := norm_shift_ge (z := z) r θ hr'.le
        have h2 : S < r := not_le.mp hrS
        rw [hS] at h2
        linarith
      have hz : dbar w (z - (r : ℂ) * circ θ) = 0 := by simp [dbar, hfz]
      simp only [polarDbar, hz, zero_mul, norm_zero]
      exact indicator_nonneg (fun _ _ => hC0) _
  have hind : Integrable (box.indicator fun _ => C)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-π) π)) := by
    refine (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr ?_
    refine integrableOn_const ?_
    exact ne_top_of_le_ne_top hboxc.measure_lt_top.ne (Measure.le_iff'.1 Measure.restrict_le_self _)
  refine Integrable.mono' hind (continuous_polarDbar hw z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  exact hbound p hp

/-- The angular integral: the `∂/∂θ` term integrates to zero over a full turn, leaving the
radial derivative. -/
theorem integral_theta_polarDbar (hw : ContDiff ℝ 1 w) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ θ in Ioo (-π) π, polarDbar w z (r, θ)
      = ∫ θ in Ioo (-π) π, fderiv ℝ w (z - (r : ℂ) * circ θ) (circ θ) := by
  have hdiff : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hshift : Continuous fun θ : ℝ => z - (r : ℂ) * circ θ := by
    have := continuous_shift (z := z)
    exact this.comp (continuous_const.prodMk continuous_id)
  have hc1 : Continuous fun θ : ℝ => fderiv ℝ w (z - (r : ℂ) * circ θ) (circ θ) :=
    (hfd.comp hshift).clm_apply continuous_circ
  have hc2 : Continuous fun θ : ℝ =>
      fderiv ℝ w (z - (r : ℂ) * circ θ) (Complex.I * (r : ℂ) * circ θ) :=
    (hfd.comp hshift).clm_apply (continuous_const.mul continuous_circ)
  have key : ∀ θ : ℝ, polarDbar w z (r, θ)
      = fderiv ℝ w (z - (r : ℂ) * circ θ) (circ θ)
        + (Complex.I / r) * fderiv ℝ w (z - (r : ℂ) * circ θ) (Complex.I * (r : ℂ) * circ θ) := by
    intro θ
    have h := dbar_polar_eq hdiff z hr.ne' θ
    simp only [polarDbar]
    rw [h]
    ring
  have hzero : ∫ θ in Ioo (-π) π,
      fderiv ℝ w (z - (r : ℂ) * circ θ) (Complex.I * (r : ℂ) * circ θ) = 0 := by
    have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
    have hFTC : (∫ θ in (-π : ℝ)..π,
        -(fderiv ℝ w (z - (r : ℂ) * circ θ) (Complex.I * (r : ℂ) * circ θ)))
        = polarFn w z r π - polarFn w z r (-π) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ => hasDerivAt_polarFn_snd hdiff z r θ)
        (hc2.neg.intervalIntegrable (-π) π)
    have hends : polarFn w z r π - polarFn w z r (-π) = 0 := by
      simp [polarFn, circ_pi, circ_neg_pi]
    rw [hends, intervalIntegral.integral_neg, neg_eq_zero] at hFTC
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi]
    exact hFTC
  rw [setIntegral_congr_fun measurableSet_Ioo fun θ _ => key θ,
    integral_add ((hc1.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self)
      (((hc2.const_mul _).integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self),
    integral_const_mul, hzero, mul_zero, add_zero]

/-- **The Cauchy–Pompeiu formula for compactly supported functions.** -/
theorem integral_dbar_div_eq (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport w) (z : ℂ) :
    ∫ ξ : ℂ, dbar w (z - ξ) / ξ = (2 * π : ℝ) • w z := by
  have hdiff : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  obtain ⟨R, hR0, hR⟩ := exists_radius hc
  obtain ⟨C, hC⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hfd
  set S : ℝ := R + ‖z‖ + 1 with hS
  -- the average of `w` over the circle of radius `r`, as an interval integral
  set G : ℝ → ℂ := fun r => ∫ θ in (-π)..π, polarFn w z r θ with hG
  set G' : ℝ → ℂ := fun r => ∫ θ in (-π)..π,
    -(fderiv ℝ w (z - (r : ℂ) * circ θ) (circ θ)) with hG'
  have hcont : ∀ r : ℝ, Continuous fun θ : ℝ => fderiv ℝ w (z - (r : ℂ) * circ θ) (circ θ) := by
    intro r
    have hshift : Continuous fun θ : ℝ => z - (r : ℂ) * circ θ :=
      (continuous_shift (z := z)).comp (continuous_const.prodMk continuous_id)
    exact (hfd.comp hshift).clm_apply continuous_circ
  have hcontw : ∀ r : ℝ, Continuous fun θ : ℝ => polarFn w z r θ := by
    intro r
    have hshift : Continuous fun θ : ℝ => z - (r : ℂ) * circ θ :=
      (continuous_shift (z := z)).comp (continuous_const.prodMk continuous_id)
    exact hw.continuous.comp hshift
  -- `G` is differentiable, with derivative `G'`, by differentiating under the integral sign
  have hbnd : ∀ x θ : ℝ, ‖-(fderiv ℝ w (z - (x : ℂ) * circ θ) (circ θ))‖ ≤ C := by
    intro x θ
    rw [norm_neg]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [norm_circ, mul_one]
    exact hC _
  have hderiv : ∀ r : ℝ, HasDerivAt G (G' r) r := by
    intro r
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x : ℝ => fun θ : ℝ => polarFn w z x θ)
      (F' := fun x : ℝ => fun θ : ℝ => -(fderiv ℝ w (z - (x : ℂ) * circ θ) (circ θ)))
      (x₀ := r) (s := Set.univ) (bound := fun _ : ℝ => C) (a := -π) (b := π)
      univ_mem
      (Eventually.of_forall fun x => (hcontw x).aestronglyMeasurable)
      ((hcontw r).intervalIntegrable _ _)
      ((hcont r).neg.aestronglyMeasurable)
      (Eventually.of_forall fun θ _ x _ => hbnd x θ)
      intervalIntegrable_const
      (Eventually.of_forall fun θ _ x _ => hasDerivAt_polarFn_fst hdiff z x θ)).2
  have hS0 : (0 : ℝ) < S := by rw [hS]; positivity
  -- `G'` is continuous, vanishes beyond radius `S`, and `G` vanishes there too
  have hG'cont : Continuous G' := by
    have huncurry : Continuous (Function.uncurry fun (x : ℝ) (θ : ℝ) =>
        -(fderiv ℝ w (z - (x : ℂ) * circ θ) (circ θ))) :=
      (((hfd.comp (continuous_shift (z := z))).clm_apply
        (continuous_circ.comp continuous_snd))).neg
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' huncurry _ _
  have hG'zero : ∀ r ∈ Ioi S, G' r = 0 := by
    intro r hr
    have hrS : S < r := hr
    have hz : ∀ θ : ℝ, -(fderiv ℝ w (z - (r : ℂ) * circ θ) (circ θ)) = 0 := by
      intro θ
      have h0 : fderiv ℝ w (z - (r : ℂ) * circ θ) = 0 := by
        refine (hR _ ?_).2
        have h1 := norm_shift_ge (z := z) r θ (by linarith)
        rw [hS] at hrS
        linarith
      simp [h0]
    simp only [hG']
    rw [intervalIntegral.integral_congr fun θ _ => hz θ, intervalIntegral.integral_zero]
  have hGS : G S = 0 := by
    have hz : ∀ θ : ℝ, polarFn w z S θ = 0 := by
      intro θ
      refine (hR _ ?_).1
      have h1 := norm_shift_ge (z := z) S θ hS0.le
      rw [hS] at h1
      linarith
    simp only [hG]
    rw [intervalIntegral.integral_congr fun θ _ => hz θ, intervalIntegral.integral_zero]
  have hG0 : G 0 = (2 * π : ℝ) • w z := by
    simp only [hG, polarFn, Complex.ofReal_zero, zero_mul, sub_zero]
    rw [intervalIntegral.integral_const]
    congr 1
    ring
  -- the radial integral, by the fundamental theorem of calculus
  have hdisj : Disjoint (Ioc (0 : ℝ) S) (Ioi S) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ hx'
    exact absurd hx' (not_lt.mpr hx)
  have hint1 : IntegrableOn G' (Ioc (0 : ℝ) S) :=
    (hG'cont.integrableOn_Icc (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn G' (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun r hr => (hG'zero r hr).symm) measurableSet_Ioi
  have hIoi : ∫ r in Ioi (0 : ℝ), G' r = ∫ r in Ioc (0 : ℝ) S, G' r := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS0.le,
      setIntegral_union hdisj measurableSet_Ioi hint1 hint2,
      setIntegral_eq_zero_of_forall_eq_zero hG'zero, add_zero]
  have hinner : ∀ r ∈ Ioi (0 : ℝ),
      (∫ θ in Ioo (-π) π, polarDbar w z (r, θ)) = -G' r := by
    intro r hr
    rw [integral_theta_polarDbar hw z hr]
    simp only [hG']
    rw [intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo, integral_neg, neg_neg]
  rw [integral_dbar_div_eq_polar z, Measure.volume_eq_prod,
    setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact integrableOn_polarDbar hw hc z),
    setIntegral_congr_fun measurableSet_Ioi hinner, integral_neg, hIoi,
    ← intervalIntegral.integral_of_le hS0.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r)
      (hG'cont.intervalIntegrable _ _), hGS, hG0]
  simp

/-! ### The Cauchy transform -/

/-- `ξ ↦ ‖ξ‖⁻¹` is integrable on every ball of `ℂ`: in polar coordinates the singularity is
exactly cancelled by the area element `r dr dθ`. -/
theorem integrableOn_inv_norm_ball {R : ℝ} :
    IntegrableOn (fun ξ : ℂ => ‖ξ‖⁻¹) (ball (0 : ℂ) R) := by
  refine ⟨(measurable_norm.inv).aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_ball,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hmono : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 •
          (ball (0 : ℂ) R).indicator (fun ξ : ℂ => ‖‖ξ‖⁻¹‖ₑ) (Complex.polarCoord.symm p)
        ≤ (Ioo (0 : ℝ) R ×ˢ Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    have hr' : (0 : ℝ) < r := hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hr'
    by_cases hrR : r < R
    · rw [indicator_of_mem
        (show ((r, θ) : ℝ × ℝ) ∈ Ioo (0 : ℝ) R ×ˢ Ioo (-π) π from ⟨⟨hr', hrR⟩, hθ⟩),
        indicator_of_mem (show Complex.polarCoord.symm (r, θ) ∈ ball (0 : ℂ) R by
          rw [mem_ball, dist_zero_right, hnorm]; exact hrR),
        hnorm, Real.enorm_eq_ofReal (by positivity), smul_eq_mul,
        ← ENNReal.ofReal_mul hr'.le, mul_inv_cancel₀ hr'.ne', ENNReal.ofReal_one]
    · rw [indicator_of_notMem (show Complex.polarCoord.symm (r, θ) ∉ ball (0 : ℂ) R by
        rw [mem_ball, dist_zero_right, hnorm]; exact not_lt.mpr (not_lt.mp hrR))]
      simp
  refine lt_of_le_of_lt (setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo) hmono) ?_
  calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        (Ioo (0 : ℝ) R ×ˢ Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) p
      ≤ ∫⁻ p, (Ioo (0 : ℝ) R ×ˢ Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) p :=
        setLIntegral_le_lintegral _ _
    _ = volume (Ioo (0 : ℝ) R ×ˢ Ioo (-π) π) := by
        rw [lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
        simp
    _ < ⊤ := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The integrand of the Cauchy transform is integrable, for continuous data with compact
support and values in any normed space over `ℂ`. -/
theorem integrable_inv_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {g : ℂ → G} (hgc : Continuous g) (hgs : HasCompactSupport g) (z : ℂ) :
    Integrable fun ξ : ℂ => (ξ⁻¹ : ℂ) • g (z - ξ) := by
  obtain ⟨C, hC⟩ := hgs.exists_bound_of_continuous hgc
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  obtain ⟨R₀, hR₀⟩ := (IsCompact.isBounded hgs).subset_closedBall (0 : ℂ)
  set R : ℝ := ‖z‖ + max R₀ 1 + 1 with hRdef
  have hvanish : ∀ ξ : ℂ, R ≤ ‖ξ‖ → g (z - ξ) = 0 := by
    intro ξ hξ
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h1 := hR₀ hmem
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : ‖ξ‖ - ‖z‖ ≤ ‖z - ξ‖ := by
      have := norm_sub_norm_le ξ z
      rwa [norm_sub_rev] at this
    have h3 : R₀ ≤ max R₀ 1 := le_max_left _ _
    rw [hRdef] at hξ
    linarith
  refine Integrable.mono' (g := fun ξ : ℂ => C * (ball (0 : ℂ) R).indicator (fun ξ => ‖ξ‖⁻¹) ξ)
    ((integrableOn_inv_norm_ball.integrable_indicator measurableSet_ball).const_mul C) ?_ ?_
  · exact ((measurable_inv.aestronglyMeasurable).smul
      (hgc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · refine Eventually.of_forall fun ξ => ?_
    by_cases hξ : ξ ∈ ball (0 : ℂ) R
    · rw [indicator_of_mem hξ, norm_smul, norm_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (by positivity)
    · have h0 : g (z - ξ) = 0 := by
        refine hvanish ξ ?_
        rw [mem_ball, dist_zero_right, not_lt] at hξ
        exact hξ
      rw [h0, smul_zero, norm_zero, indicator_of_notMem hξ, mul_zero]

/-- The **Cauchy transform** `T f (z) = (2π)⁻¹ ∫ f (z - ξ) / ξ`, the solution operator of
`∂v/∂x + i ∂v/∂y = f`. -/
noncomputable def cauchyTransform (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * π : ℝ)⁻¹ • ∫ ξ : ℂ, (ξ⁻¹ : ℂ) • f (z - ξ)

theorem two_pi_ne_zero : (2 * π : ℝ) ≠ 0 := by positivity

/-- The Cauchy transform inverts the Cauchy–Riemann operator on compactly supported `C¹`
functions: `T (∂w/∂x + i ∂w/∂y) = w`.  This is `integral_dbar_div_eq` restated. -/
theorem cauchyTransform_dbar (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport w) :
    cauchyTransform (dbar w) = w := by
  funext z
  have h : ∫ ξ : ℂ, (ξ⁻¹ : ℂ) • dbar w (z - ξ) = ∫ ξ : ℂ, dbar w (z - ξ) / ξ := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp [smul_eq_mul, div_eq_inv_mul]
  rw [cauchyTransform, h, integral_dbar_div_eq hw hc z, smul_smul,
    inv_mul_cancel₀ two_pi_ne_zero, one_smul]

/-- **The Cauchy transform solves the inhomogeneous equation.**  For compactly supported `C¹`
data, `∂(T f)/∂x + i ∂(T f)/∂y = f`. -/
theorem dbar_cauchyTransform (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (z : ℂ) :
    dbar (cauchyTransform f) z = f z := by
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hfds : HasCompactSupport (fderiv ℝ f) := hc.fderiv (𝕜 := ℝ)
  -- the derivative falls on the data, the kernel being independent of `z`
  have hFD : HasFDerivAt (cauchyTransform f)
      ((2 * π : ℝ)⁻¹ • ∫ ξ : ℂ, (ξ⁻¹ : ℂ) • fderiv ℝ f (z - ξ)) z := by
    have hmain : HasFDerivAt (fun z : ℂ => ∫ ξ : ℂ, (ξ⁻¹ : ℂ) • f (z - ξ))
        (∫ ξ : ℂ, (ξ⁻¹ : ℂ) • fderiv ℝ f (z - ξ)) z := by
      obtain ⟨C, hC⟩ := hfds.exists_bound_of_continuous hfd
      have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
      obtain ⟨R₀, hR₀⟩ := (IsCompact.isBounded hfds).subset_closedBall (0 : ℂ)
      set R : ℝ := ‖z‖ + max R₀ 1 + 2 with hRdef
      have hvanish : ∀ x ξ : ℂ, ‖x - z‖ < 1 → R ≤ ‖ξ‖ → fderiv ℝ f (x - ξ) = 0 := by
        intro x ξ hx hξ
        refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
        have h1 := hR₀ hmem
        rw [mem_closedBall, dist_zero_right] at h1
        have h2 : ‖ξ‖ - ‖x‖ ≤ ‖x - ξ‖ := by
          have := norm_sub_norm_le ξ x
          rwa [norm_sub_rev] at this
        have h3 : ‖x‖ ≤ ‖z‖ + 1 := by
          have := norm_sub_norm_le x z
          linarith [le_of_lt hx]
        have h4 : R₀ ≤ max R₀ 1 := le_max_left _ _
        rw [hRdef] at hξ
        linarith
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball z 1)
        (F := fun (x : ℂ) (ξ : ℂ) => (ξ⁻¹ : ℂ) • f (x - ξ))
        (F' := fun (x : ℂ) (ξ : ℂ) => (ξ⁻¹ : ℂ) • fderiv ℝ f (x - ξ))
        (bound := fun ξ : ℂ => C * (ball (0 : ℂ) R).indicator (fun ξ => ‖ξ‖⁻¹) ξ)
        (ball_mem_nhds z one_pos)
        (Eventually.of_forall fun x =>
          (integrable_inv_smul hf.continuous hc x).aestronglyMeasurable)
        (integrable_inv_smul hf.continuous hc z)
        (integrable_inv_smul hfd hfds z).aestronglyMeasurable
        (Eventually.of_forall fun ξ x hx => ?_)
        ((integrableOn_inv_norm_ball.integrable_indicator measurableSet_ball).const_mul C)
        (Eventually.of_forall fun ξ x _ => ?_)
      · by_cases hξ : ξ ∈ ball (0 : ℂ) R
        · rw [indicator_of_mem hξ, norm_smul, norm_inv, mul_comm]
          exact mul_le_mul_of_nonneg_right (hC _) (by positivity)
        · have h0 : fderiv ℝ f (x - ξ) = 0 := by
            refine hvanish x ξ ?_ ?_
            · rw [mem_ball, dist_eq_norm] at hx; exact hx
            · rw [mem_ball, dist_zero_right, not_lt] at hξ; exact hξ
          rw [h0, smul_zero, norm_zero, indicator_of_notMem hξ, mul_zero]
      · have h1 : HasFDerivAt (fun x : ℂ => f (x - ξ)) (fderiv ℝ f (x - ξ)) x := by
          have h2 : HasFDerivAt (fun x : ℂ => x - ξ) (ContinuousLinearMap.id ℝ ℂ) x :=
            (hasFDerivAt_id x).sub_const ξ
          have h3 := (hdiff (x - ξ)).hasFDerivAt.comp x h2
          rw [ContinuousLinearMap.comp_id] at h3
          exact h3
        exact h1.const_smul (ξ⁻¹ : ℂ)
    exact hmain.const_smul ((2 * π : ℝ)⁻¹)
  -- apply the derivative to `1` and to `i`, and use the Cauchy–Pompeiu formula
  have hint : Integrable fun ξ : ℂ => (ξ⁻¹ : ℂ) • fderiv ℝ f (z - ξ) :=
    integrable_inv_smul hfd hfds z
  have happly : ∀ v : ℂ, fderiv ℝ (cauchyTransform f) z v
      = (2 * π : ℝ)⁻¹ • ∫ ξ : ℂ, (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) v := by
    intro v
    have hv : ((∫ ξ : ℂ, (ξ⁻¹ : ℂ) • fderiv ℝ f (z - ξ)) : ℂ →L[ℝ] ℂ) v
        = ∫ ξ : ℂ, (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) v := by
      rw [ContinuousLinearMap.integral_apply hint]
      simp [smul_eq_mul]
    rw [hFD.fderiv, smul_apply, hv]
  have hint1 : Integrable fun ξ : ℂ => (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) 1 := by
    have := integrable_inv_smul (G := ℂ) (hfd.clm_apply continuous_const)
      (hfds.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) rfl) z
    simpa [smul_eq_mul] using this
  have hint2 : Integrable fun ξ : ℂ => (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) Complex.I := by
    have := integrable_inv_smul (G := ℂ) (hfd.clm_apply continuous_const)
      (hfds.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) rfl) z
    simpa [smul_eq_mul] using this
  -- the two directional derivatives recombine into the Cauchy–Pompeiu integral
  have hAB : (∫ ξ : ℂ, (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) 1)
      + Complex.I * ∫ ξ : ℂ, (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) Complex.I
      = (2 * π : ℝ) • f z := by
    have hcongr : ∀ ξ : ℂ, (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) 1
        + Complex.I * ((ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) Complex.I) = dbar f (z - ξ) / ξ := by
      intro ξ
      rw [dbar, div_eq_mul_inv]
      ring
    rw [← integral_const_mul, ← integral_add hint1 (hint2.const_mul Complex.I),
      integral_congr_ae (Eventually.of_forall hcongr), integral_dbar_div_eq hf hc z]
  have hI : Complex.I * ((2 * π : ℝ)⁻¹ • ∫ ξ : ℂ, (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) Complex.I)
      = (2 * π : ℝ)⁻¹ • (Complex.I * ∫ ξ : ℂ, (ξ⁻¹ : ℂ) * fderiv ℝ f (z - ξ) Complex.I) := by
    rw [Complex.real_smul, Complex.real_smul]
    ring
  rw [dbar, happly 1, happly Complex.I, hI, ← smul_add, hAB, smul_smul,
    inv_mul_cancel₀ two_pi_ne_zero, one_smul]

/-! ### Towards the Beurling transform

The derivative of the Cauchy transform in the *other* direction, `∂(T f)/∂z`, is the Beurling
transform, a singular integral: the kernel `(z - ζ)⁻²` is not locally integrable.  For Hölder
data the integral is rescued by subtracting the value at the centre, `f ζ - f z`, which is the
standard principal-value regularisation.  This section sets up that operator: the Riesz kernel
estimate that makes the regularised integral absolutely convergent, and the two halves of the
definition.  The Hölder *estimate* for the operator, the Calderón–Zygmund step, is not here.
-/

/-- **The Riesz kernel is locally integrable in the plane below the critical exponent.**  In
polar coordinates `‖ξ‖ ^ (-a)` becomes `r ^ (1 - a)`, which is integrable at the origin exactly
when `a < 2`.  For `a = 2 - α` with `α > 0` this is what makes the regularised Beurling integral
converge. -/
theorem integrableOn_rpow_neg_ball {a R : ℝ} (ha : a < 2) :
    IntegrableOn (fun ξ : ℂ => ‖ξ‖ ^ (-a)) (ball (0 : ℂ) R) := by
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.mpr hR]
    exact integrableOn_empty
  refine ⟨(by fun_prop : Measurable fun ξ : ℂ => ‖ξ‖ ^ (-a)).aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_ball,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hmono : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 •
          (ball (0 : ℂ) R).indicator (fun ξ : ℂ => ‖‖ξ‖ ^ (-a)‖ₑ) (Complex.polarCoord.symm p)
        ≤ (Ioo (0 : ℝ) R).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) p.1
            * (Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    have hr' : (0 : ℝ) < r := hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hr'
    by_cases hrR : r < R
    · rw [indicator_of_mem (show ((r, θ) : ℝ × ℝ).1 ∈ Ioo (0 : ℝ) R from ⟨hr', hrR⟩),
        indicator_of_mem (show ((r, θ) : ℝ × ℝ).2 ∈ Ioo (-π) π from hθ),
        indicator_of_mem (show Complex.polarCoord.symm (r, θ) ∈ ball (0 : ℂ) R by
          rw [mem_ball, dist_zero_right, hnorm]; exact hrR),
        hnorm, Real.enorm_eq_ofReal (Real.rpow_nonneg hr'.le _), smul_eq_mul, mul_one,
        ← ENNReal.ofReal_mul hr'.le]
      rw [sub_eq_add_neg, Real.rpow_add hr', Real.rpow_one]
    · rw [indicator_of_notMem (show Complex.polarCoord.symm (r, θ) ∉ ball (0 : ℂ) R by
        rw [mem_ball, dist_zero_right, hnorm]; exact not_lt.mpr (not_lt.mp hrR))]
      simp
  refine lt_of_le_of_lt (setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo) hmono) ?_
  have hrad : ∫⁻ r, (Ioo (0 : ℝ) R).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) r < ⊤ := by
    rw [lintegral_indicator measurableSet_Ioo]
    have hint : IntegrableOn (fun x : ℝ => x ^ (1 - a)) (Ioo 0 R) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hR).2 (by linarith)
    have hfin := hint.2
    rw [hasFiniteIntegral_iff_enorm] at hfin
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hx.1.le _)]
  have hang : ∫⁻ θ, (Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) θ < ⊤ := by
    rw [lintegral_indicator measurableSet_Ioo]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        (Ioo (0 : ℝ) R).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) p.1
          * (Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) p.2
      ≤ ∫⁻ p : ℝ × ℝ, (Ioo (0 : ℝ) R).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) p.1
          * (Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) p.2 := setLIntegral_le_lintegral _ _
    _ = (∫⁻ r, (Ioo (0 : ℝ) R).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) r)
          * ∫⁻ θ, (Ioo (-π) π).indicator (fun _ => (1 : ℝ≥0∞)) θ := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul
          (((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (1 - a))).indicator
            measurableSet_Ioo).aemeasurable)
          ((measurable_const.indicator measurableSet_Ioo).aemeasurable)
    _ < ⊤ := ENNReal.mul_lt_top hrad hang

/-- The Riesz kernel centred at an arbitrary point, by translation invariance. -/
theorem integrableOn_rpow_neg_ball' {a R : ℝ} (ha : a < 2) (z : ℂ) :
    IntegrableOn (fun ζ : ℂ => ‖ζ - z‖ ^ (-a)) (ball z R) := by
  have hpre : (fun x : ℂ => x - z) ⁻¹' ball (0 : ℂ) R = ball z R := by
    ext x; simp [mem_ball, dist_eq_norm]
  have := ((measurePreserving_sub_right (volume : Measure ℂ) z).integrableOn_comp_preimage
    (measurableEmbedding_subRight z) (f := fun ξ : ℂ => ‖ξ‖ ^ (-a))
    (s := ball (0 : ℂ) R)).2 (integrableOn_rpow_neg_ball ha)
  rwa [hpre] at this

/-- The **Beurling transform** of a Hölder continuous, compactly supported function, written
with the principal value made explicit: near the pole the value at the centre is subtracted,
far from it the kernel is harmless.  The splitting radius is fixed to `1`. -/
noncomputable def beurling (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∫ ζ in ball z 1, (f ζ - f z) / (z - ζ) ^ 2) + ∫ ζ in (ball z 1)ᶜ, f ζ / (z - ζ) ^ 2

/-- A Hölder constant is nonnegative. -/
theorem holder_const_nonneg {f : ℂ → ℂ} {C α : ℝ}
    (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) : 0 ≤ C := by
  have h := hf 1 0
  have h1 : ‖(1 : ℂ) - 0‖ ^ α = 1 := by rw [sub_zero, norm_one, Real.one_rpow]
  rw [h1, mul_one] at h
  exact le_trans (norm_nonneg _) h

/-- **The regularised integrand is dominated by a Riesz kernel below the critical exponent.**
Subtracting the value at the centre turns the non-integrable `‖ζ - z‖⁻²` into
`‖ζ - z‖^{α-2}`, and `α > 0` puts that below the threshold. -/
theorem norm_beurling_integrand_le {f : ℂ → ℂ} {C α : ℝ}
    (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z ζ : ℂ) :
    ‖(f ζ - f z) / (z - ζ) ^ 2‖ ≤ C * ‖ζ - z‖ ^ (-(2 - α)) := by
  have hC0 : 0 ≤ C := holder_const_nonneg hf
  rcases eq_or_ne ζ z with rfl | hζ
  · have h0 : (0 : ℝ) ≤ C * ‖(ζ : ℂ) - ζ‖ ^ (-(2 - α)) :=
      mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg _) _)
    simpa using h0
  · have hnz : ‖ζ - z‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hζ)
    have hpos : 0 < ‖ζ - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnz)
    rw [norm_div, norm_pow, ← norm_neg (z - ζ), neg_sub]
    rw [div_le_iff₀ (by positivity)]
    calc ‖f ζ - f z‖ ≤ C * ‖ζ - z‖ ^ α := hf ζ z
      _ = C * ‖ζ - z‖ ^ (-(2 - α)) * ‖ζ - z‖ ^ 2 := by
          rw [mul_assoc]
          congr 1
          rw [← Real.rpow_natCast ‖ζ - z‖ 2, ← Real.rpow_add hpos]
          congr 1
          push_cast
          ring

/-- **The regularised integral converges absolutely.** -/
theorem integrableOn_beurling_near {f : ℂ → ℂ} (hfc : Continuous f) {C α : ℝ} (hα : 0 < α)
    (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ) {ρ : ℝ} :
    IntegrableOn (fun ζ : ℂ => (f ζ - f z) / (z - ζ) ^ 2) (ball z ρ) := by
  refine Integrable.mono' (g := fun ζ : ℂ => C * ‖ζ - z‖ ^ (-(2 - α)))
    ((integrableOn_rpow_neg_ball' (by linarith) z).const_mul C) ?_ ?_
  · exact (((hfc.measurable.sub measurable_const).div
      ((measurable_const.sub measurable_id).pow_const 2))).aestronglyMeasurable
  · exact Eventually.of_forall fun ζ => norm_beurling_integrand_le hf z ζ

/-- Far from the pole the Beurling integrand is dominated by `f` itself. -/
theorem integrableOn_beurling_far {f : ℂ → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun ζ : ℂ => f ζ / (z - ζ) ^ 2) (ball z ρ)ᶜ := by
  have hI : Integrable (fun ζ : ℂ => (ρ ^ 2)⁻¹ * ‖f ζ‖) volume :=
    ((hfc.integrable_of_hasCompactSupport hfs).norm).const_mul _
  refine Integrable.mono' (g := fun ζ : ℂ => (ρ ^ 2)⁻¹ * ‖f ζ‖) hI.integrableOn ?_ ?_
  · exact ((hfc.measurable.div
      ((measurable_const.sub measurable_id).pow_const 2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with ζ hζ
    have h1 : ρ ≤ ‖z - ζ‖ := by
      rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt, ← norm_neg, neg_sub] at hζ
      exact hζ
    have h2 : ρ ^ 2 ≤ ‖z - ζ‖ ^ 2 := by nlinarith [hρ.le]
    rw [norm_div, norm_pow, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hρ 2) h2

/-! ### The cancellation that makes the principal value exist -/

/-- The quarter turn `ξ ↦ i ξ` of the plane, as a linear isometry.  It preserves Lebesgue
measure and it reverses the sign of the Beurling kernel, which is the whole of the cancellation
below. -/
noncomputable def rotI : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩

@[simp]
theorem rotI_apply (ξ : ℂ) : rotI ξ = Complex.I * ξ := rfl

/-- **The Beurling kernel integrates to zero on every set invariant under the quarter turn.**
Rotating by `i` fixes the set and preserves the measure, while `(iξ)² = -ξ²` flips the sign of
the integrand; an integral equal to its own negative vanishes.  No integrability is needed:
where the integral fails to converge both sides are zero by convention. -/
theorem setIntegral_inv_sq_eq_zero {s : Set ℂ} (hs : (fun ξ : ℂ => Complex.I * ξ) ⁻¹' s = s) :
    ∫ ξ in s, (ξ ^ 2)⁻¹ = 0 := by
  have key := (rotI.measurePreserving).setIntegral_preimage_emb
    rotI.toHomeomorph.measurableEmbedding (fun ξ : ℂ => (ξ ^ 2)⁻¹) s
  have hs' : (rotI : ℂ → ℂ) ⁻¹' s = s := hs
  rw [hs'] at key
  have h2 : ∀ ξ : ℂ, (rotI ξ ^ 2)⁻¹ = -(ξ ^ 2)⁻¹ := fun ξ => by
    rw [rotI_apply, mul_pow, Complex.I_sq]; ring
  simp only [h2, integral_neg] at key
  linear_combination -key / 2

/-- Annuli centred at the origin are invariant under the quarter turn. -/
theorem preimage_mulI_annulus (r₁ r₂ : ℝ) :
    (fun ξ : ℂ => Complex.I * ξ) ⁻¹' (ball (0 : ℂ) r₂ \ ball 0 r₁)
      = ball (0 : ℂ) r₂ \ ball 0 r₁ := by
  ext x; simp [mem_ball, dist_eq_norm]

/-- **The Beurling kernel has zero mean on every annulus centred at its pole.**  This is the
cancellation behind the principal value: it is why the singular integral may be cut off at any
radius, and why subtracting the constant `f z` near the pole costs nothing. -/
theorem setIntegral_beurling_kernel_annulus (z : ℂ) (r₁ r₂ : ℝ) :
    ∫ ζ in ball z r₂ \ ball z r₁, ((z - ζ) ^ 2)⁻¹ = 0 := by
  have hpre : (fun ξ : ℂ => z + ξ) ⁻¹' (ball z r₂ \ ball z r₁) = ball (0 : ℂ) r₂ \ ball 0 r₁ := by
    ext x; simp [mem_ball, dist_eq_norm]
  have key := (measurePreserving_add_left (volume : Measure ℂ) z).setIntegral_preimage_emb
    (measurableEmbedding_addLeft z) (fun ζ : ℂ => ((z - ζ) ^ 2)⁻¹) (ball z r₂ \ ball z r₁)
  rw [hpre] at key
  rw [← key]
  have h2 : ∀ ξ : ℂ, ((z - (z + ξ)) ^ 2)⁻¹ = (ξ ^ 2)⁻¹ := fun ξ => by ring_nf
  simp only [h2]
  exact setIntegral_inv_sq_eq_zero (preimage_mulI_annulus r₁ r₂)

/-- The two-piece expression defining the Beurling transform, with a general cut-off radius. -/
noncomputable def beurlingWith (f : ℂ → ℂ) (z : ℂ) (ρ : ℝ) : ℂ :=
  (∫ ζ in ball z ρ, (f ζ - f z) / (z - ζ) ^ 2) + ∫ ζ in (ball z ρ)ᶜ, f ζ / (z - ζ) ^ 2

theorem beurling_eq_beurlingWith_one (f : ℂ → ℂ) (z : ℂ) : beurling f z = beurlingWith f z 1 :=
  rfl

/-- Enlarging the cut-off radius changes neither piece by more than it changes the other: what
moves from the far integral to the near one is the same integral over the annulus, because the
constant `f z` subtracted there integrates to zero against the kernel. -/
theorem beurlingWith_eq_of_le {f : ℂ → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    {C α : ℝ} (hα : 0 < α) (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    beurlingWith f z r = beurlingWith f z R := by
  have hAmeas : MeasurableSet (ball z R \ ball z r) := measurableSet_ball.diff measurableSet_ball
  have hnear_r : IntegrableOn (fun ζ : ℂ => (f ζ - f z) / (z - ζ) ^ 2) (ball z r) :=
    integrableOn_beurling_near hfc hα hf z
  have hnear_A : IntegrableOn (fun ζ : ℂ => (f ζ - f z) / (z - ζ) ^ 2) (ball z R \ ball z r) :=
    (integrableOn_beurling_near hfc hα hf z (ρ := R)).mono_set sdiff_subset
  have hfar_r : IntegrableOn (fun ζ : ℂ => f ζ / (z - ζ) ^ 2) (ball z r)ᶜ :=
    integrableOn_beurling_far hfc hfs z hr
  have hfar_R : IntegrableOn (fun ζ : ℂ => f ζ / (z - ζ) ^ 2) (ball z R)ᶜ :=
    integrableOn_beurling_far hfc hfs z (lt_of_lt_of_le hr hrR)
  have hfar_A : IntegrableOn (fun ζ : ℂ => f ζ / (z - ζ) ^ 2) (ball z R \ ball z r) :=
    hfar_r.mono_set fun x hx => hx.2
  have hsplit_near : ∫ ζ in ball z R, (f ζ - f z) / (z - ζ) ^ 2
      = (∫ ζ in ball z r, (f ζ - f z) / (z - ζ) ^ 2)
        + ∫ ζ in ball z R \ ball z r, (f ζ - f z) / (z - ζ) ^ 2 := by
    rw [← setIntegral_union disjoint_sdiff_right hAmeas hnear_r hnear_A,
      union_sdiff_cancel (ball_subset_ball hrR)]
  have hsetc : (ball z R \ ball z r) ∪ (ball z R)ᶜ = (ball z r)ᶜ := by
    ext x
    simp only [mem_union, Set.mem_sdiff, mem_compl_iff, mem_ball]
    constructor
    · rintro (⟨-, hx⟩ | hx)
      · exact hx
      · exact fun hxr => hx (lt_of_lt_of_le hxr hrR)
    · intro hx
      by_cases hR : dist x z < R
      · exact Or.inl ⟨hR, hx⟩
      · exact Or.inr hR
  have hsplit_far : ∫ ζ in (ball z r)ᶜ, f ζ / (z - ζ) ^ 2
      = (∫ ζ in ball z R \ ball z r, f ζ / (z - ζ) ^ 2)
        + ∫ ζ in (ball z R)ᶜ, f ζ / (z - ζ) ^ 2 := by
    rw [← hsetc, setIntegral_union (disjoint_compl_right.mono_left sdiff_subset)
      measurableSet_ball.compl hfar_A hfar_R]
  have hcancel : ∫ ζ in ball z R \ ball z r, (f ζ - f z) / (z - ζ) ^ 2
      = ∫ ζ in ball z R \ ball z r, f ζ / (z - ζ) ^ 2 := by
    have hzero : ∫ ζ in ball z R \ ball z r,
        (f ζ / (z - ζ) ^ 2 - (f ζ - f z) / (z - ζ) ^ 2) = 0 := by
      have hpt : ∀ ζ : ℂ, f ζ / (z - ζ) ^ 2 - (f ζ - f z) / (z - ζ) ^ 2
          = f z * ((z - ζ) ^ 2)⁻¹ := fun ζ => by
        rw [div_sub_div_same, sub_sub_cancel, div_eq_mul_inv]
      simp only [hpt]
      rw [integral_const_mul, setIntegral_beurling_kernel_annulus z r R, mul_zero]
    rw [integral_sub hfar_A hnear_A] at hzero
    linear_combination -hzero
  unfold beurlingWith
  rw [hsplit_near, hsplit_far, hcancel]
  ring

/-- **The cut-off radius is immaterial**: for Hölder data with compact support the two-piece
expression is the same for every positive radius, so the Beurling transform is well defined as
a principal value. -/
theorem beurlingWith_eq {f : ℂ → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    {C α : ℝ} (hα : 0 < α) (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) : beurlingWith f z ρ = beurling f z := by
  rw [beurling_eq_beurlingWith_one]
  rcases le_total ρ 1 with h | h
  · exact beurlingWith_eq_of_le hfc hfs hα hf z hρ h
  · exact (beurlingWith_eq_of_le hfc hfs hα hf z one_pos h).symm

/-- **The Beurling transform of a compactly supported Hölder function is bounded.**  The near
integral is dominated by the mass of the Riesz kernel on the unit disc, which does not depend
on the centre, and the far one by the `L¹` norm of `f`; neither bound involves the point, so
the transform is bounded on the whole plane. -/
theorem norm_beurling_le {f : ℂ → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    {C α : ℝ} (hα : 0 < α) (hf : ∀ ξ η : ℂ, ‖f ξ - f η‖ ≤ C * ‖ξ - η‖ ^ α) (z : ℂ) :
    ‖beurling f z‖ ≤ C * (∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α))) + ∫ ζ : ℂ, ‖f ζ‖ := by
  have hnear : IntegrableOn (fun ζ : ℂ => (f ζ - f z) / (z - ζ) ^ 2) (ball z 1) :=
    integrableOn_beurling_near hfc hα hf z
  have hdom : IntegrableOn (fun ζ : ℂ => C * ‖ζ - z‖ ^ (-(2 - α))) (ball z 1) :=
    (integrableOn_rpow_neg_ball' (by linarith) z).const_mul C
  have htrans : (∫ ζ in ball z 1, C * ‖ζ - z‖ ^ (-(2 - α)))
      = C * ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α)) := by
    rw [integral_const_mul]
    congr 1
    have hpre : (fun ξ : ℂ => z + ξ) ⁻¹' ball z 1 = ball (0 : ℂ) 1 := by
      ext x; simp [mem_ball, dist_eq_norm]
    have key := (measurePreserving_add_left (volume : Measure ℂ) z).setIntegral_preimage_emb
      (measurableEmbedding_addLeft z) (fun ζ : ℂ => ‖ζ - z‖ ^ (-(2 - α))) (ball z 1)
    rw [hpre] at key
    rw [← key]
    simp
  have hn1 : ‖∫ ζ in ball z 1, (f ζ - f z) / (z - ζ) ^ 2‖
      ≤ C * ∫ ξ in ball (0 : ℂ) 1, ‖ξ‖ ^ (-(2 - α)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [← htrans]
    exact integral_mono hnear.norm hdom fun ζ => norm_beurling_integrand_le hf z ζ
  have hI : Integrable (fun ζ : ℂ => ‖f ζ‖) volume :=
    (hfc.integrable_of_hasCompactSupport hfs).norm
  have hfar : IntegrableOn (fun ζ : ℂ => f ζ / (z - ζ) ^ 2) (ball z 1)ᶜ :=
    integrableOn_beurling_far hfc hfs z one_pos
  have hf1 : ‖∫ ζ in (ball z 1)ᶜ, f ζ / (z - ζ) ^ 2‖ ≤ ∫ ζ : ℂ, ‖f ζ‖ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_trans (integral_mono_ae hfar.norm hI.integrableOn ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with ζ hζ
      have h1 : (1 : ℝ) ≤ ‖z - ζ‖ := by
        rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt, ← norm_neg, neg_sub] at hζ
        exact hζ
      rw [norm_div, norm_pow]
      refine div_le_self (norm_nonneg _) ?_
      nlinarith [h1]
    · exact setIntegral_le_integral hI (Eventually.of_forall fun ζ => norm_nonneg _)
  unfold beurling
  exact le_trans (norm_add_le _ _) (add_le_add hn1 hf1)

end CauchyPompeiu
end MorseFloer
