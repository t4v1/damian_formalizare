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
   convolution against the Cauchy kernel `1/ξ`;
2. Hölder estimates for that convolution (`C^{k,α} → C^{k+1,α}`, Schauder theory), which
   is the step that actually gains a derivative and which this file does **not** contain;
3. bootstrapping: `u - v` is holomorphic by `Part2/Weyl.lean`, hence `C^∞`, so `u` is as
   smooth as `v`.

Step 2 is what remains before Proposition 6.5.3 can be proved.  Note that the `C^k` scale
alone is not enough: the Cauchy transform of a `C^k` function is `C^k`, not `C^{k+1}`, so
the bootstrap needs the Hölder scale.

## Main results

* `MorseFloer.CauchyPompeiu.integral_dbar_div_eq`: the formula above.
* `MorseFloer.CauchyPompeiu.integral_theta_polarDbar`: the angular integral, where the
  `∂/∂θ` term drops out by periodicity.

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
open scoped Real ContDiff

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

end CauchyPompeiu
end MorseFloer
