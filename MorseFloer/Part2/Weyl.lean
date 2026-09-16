import Mathlib

/-!
# Weyl's lemma for `∂̄`

A locally integrable weak solution of the Cauchy–Riemann equation
`∂u/∂s + i ∂u/∂t = 0` on an open set `U ⊆ ℂ` agrees almost everywhere with a
holomorphic function.  This is the distributional form of Lemma 12.1.1 of
Audin–Damian, the regularity statement that upgrades the `L^p` solutions produced
by the analysis of Part II to genuine smooth ones; `Part2/Ch12.lean` restates it
as `exists_differentiable_of_isWeakCauchyRiemann`.

## The proof

The proof is the classical one by mollification, arranged so that no elliptic
estimate and no `L¹` convergence of mollifiers is needed.

* A **radial mollifier** `moll ε` is built by hand — `ψ (‖w‖²)` for a
  one-dimensional bump `ψ` — because radiality is what makes a holomorphic
  function equal to its own mollification, and Mathlib's `ContDiffBump` does not
  expose that property.
* The mollification `moll ε ⋆ u` is smooth, and its `∂̄` at `x` is the weak
  equation tested against `w ↦ moll ε (x − w)`, so it vanishes: `moll ε ⋆ u` is
  holomorphic wherever the test function fits inside `U`
  (`differentiableAt_smooth`).
* **Mean value property against a radial weight**
  (`integral_moll_smul_eq_of_differentiableOn`): for `h` holomorphic on a disc
  around `z` containing the support of `moll ε`, `∫ moll ε t • h (z − t) = h z`.
  This is polar coordinates (`Complex.integral_comp_polarCoord_symm`), Fubini,
  and Cauchy's formula on each circle through `circleAverage`.
* Consequently two mollifications `moll ε ⋆ u` and `moll δ ⋆ u` agree where both
  are holomorphic (`smooth_eq_smooth`): `moll δ ⋆ (moll ε ⋆ u) = moll ε ⋆ u` by
  the mean value property, and convolution is associative and commutative.
* Mollifications converge almost everywhere to `u` (`ae_tendsto_smooth`), by the
  Lebesgue differentiation theorem in the form
  `tendsto_integral_smul_of_tendsto_average_norm_sub`.
* Hence, locally, a single mollification is holomorphic and equals `u` almost
  everywhere (`exists_local`); the local functions are glued by uniqueness of
  continuous representatives (`Measure.eqOn_open_of_ae_eq`) and a countable
  cover (`exists_differentiableOn_ae_eq`).
-/

open MeasureTheory Filter Topology Metric Set
open scoped Convolution Real ContDiff

namespace MorseFloer
namespace Weyl

/-! ### A radial mollifier -/

/-- A one-dimensional bump of inner radius `ε²/2` and outer radius `ε²`; for
`ε = 0` an arbitrary bump, never used. -/
noncomputable def bump1 (ε : ℝ) : ContDiffBump (0 : ℝ) :=
  if h : ε = 0 then ⟨1 / 2, 1, by norm_num, by norm_num⟩
  else ⟨ε ^ 2 / 2, ε ^ 2, by positivity, by
    have : 0 < ε ^ 2 := by positivity
    linarith⟩

theorem bump1_rOut {ε : ℝ} (hε : ε ≠ 0) : (bump1 ε).rOut = ε ^ 2 := by
  simp [bump1, hε]

theorem bump1_rIn {ε : ℝ} (hε : ε ≠ 0) : (bump1 ε).rIn = ε ^ 2 / 2 := by
  simp [bump1, hε]

/-- The unnormalised radial bump `ψ (‖w‖²)`. -/
noncomputable def rawMoll (ε : ℝ) (w : ℂ) : ℝ := bump1 ε (‖w‖ ^ 2)

/-- Its total mass. -/
noncomputable def mollNorm (ε : ℝ) : ℝ := ∫ w : ℂ, rawMoll ε w

/-- The radial mollifier of radius `ε`: smooth, nonnegative, supported in the
disc of radius `ε`, of total mass one. -/
noncomputable def moll (ε : ℝ) (w : ℂ) : ℝ := rawMoll ε w / mollNorm ε

theorem rawMoll_contDiff (ε : ℝ) : ContDiff ℝ ∞ (rawMoll ε) :=
  (bump1 ε).contDiff.comp (contDiff_norm_sq ℝ)

theorem moll_contDiff (ε : ℝ) : ContDiff ℝ ∞ (moll ε) :=
  (rawMoll_contDiff ε).div_const _

theorem moll_contDiff_one (ε : ℝ) : ContDiff ℝ 1 (moll ε) :=
  (moll_contDiff ε).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))

theorem moll_differentiable (ε : ℝ) : Differentiable ℝ (moll ε) :=
  (moll_contDiff_one ε).differentiable one_ne_zero

theorem continuous_fderiv_moll (ε : ℝ) : Continuous (fderiv ℝ (moll ε)) :=
  (moll_contDiff_one ε).continuous_fderiv one_ne_zero

theorem rawMoll_nonneg (ε : ℝ) (w : ℂ) : 0 ≤ rawMoll ε w := (bump1 ε).nonneg

theorem rawMoll_le_one (ε : ℝ) (w : ℂ) : rawMoll ε w ≤ 1 := (bump1 ε).le_one

theorem rawMoll_eq_zero_of_le {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : ε ≤ ‖w‖) :
    rawMoll ε w = 0 := by
  apply (bump1 ε).zero_of_le_dist
  rw [bump1_rOut hε.ne', Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg w]

theorem rawMoll_eq_one_of_le {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : ‖w‖ ≤ ε / 2) :
    rawMoll ε w = 1 := by
  apply (bump1 ε).one_of_mem_closedBall
  rw [mem_closedBall, bump1_rIn hε.ne', Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg w]

theorem rawMoll_continuous (ε : ℝ) : Continuous (rawMoll ε) :=
  (rawMoll_contDiff ε).continuous

theorem support_rawMoll_subset {ε : ℝ} (hε : 0 < ε) :
    Function.support (rawMoll ε) ⊆ closedBall 0 ε := by
  intro w hw
  rw [Function.mem_support] at hw
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hw (rawMoll_eq_zero_of_le hε (not_le.mp h).le)

theorem hasCompactSupport_rawMoll {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (rawMoll ε) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ε) fun w hw => by
    by_contra h
    exact hw (support_rawMoll_subset hε h)

theorem integrable_rawMoll {ε : ℝ} (hε : 0 < ε) : Integrable (rawMoll ε) :=
  (rawMoll_continuous ε).integrable_of_hasCompactSupport (hasCompactSupport_rawMoll hε)

/-- The mass of the mollifier is at least the volume of the disc of radius `ε/2`,
on which the raw bump equals `1`. -/
theorem volume_closedBall_le_mollNorm {ε : ℝ} (hε : 0 < ε) :
    (volume : Measure ℂ).real (closedBall 0 (ε / 2)) ≤ mollNorm ε := by
  have h1 : (volume : Measure ℂ).real (closedBall 0 (ε / 2))
      = ∫ w in closedBall (0 : ℂ) (ε / 2), rawMoll ε w := by
    rw [setIntegral_congr_fun measurableSet_closedBall (g := fun _ => (1 : ℝ))
      (fun w hw => rawMoll_eq_one_of_le hε (by simpa using hw))]
    simp
  rw [h1]
  exact setIntegral_le_integral (integrable_rawMoll hε)
    (Eventually.of_forall fun w => rawMoll_nonneg ε w)

theorem mollNorm_pos {ε : ℝ} (hε : 0 < ε) : 0 < mollNorm ε := by
  refine lt_of_lt_of_le ?_ (volume_closedBall_le_mollNorm hε)
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_closedBall_pos _ _ (by positivity)).ne'
    measure_closedBall_lt_top.ne

theorem moll_nonneg {ε : ℝ} (hε : 0 < ε) (w : ℂ) : 0 ≤ moll ε w :=
  div_nonneg (rawMoll_nonneg ε w) (mollNorm_pos hε).le

theorem moll_continuous (ε : ℝ) : Continuous (moll ε) := (moll_contDiff ε).continuous

theorem moll_eq_zero_of_le {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : ε ≤ ‖w‖) : moll ε w = 0 := by
  unfold moll
  rw [rawMoll_eq_zero_of_le hε hw, zero_div]

theorem support_moll_subset {ε : ℝ} (hε : 0 < ε) :
    Function.support (moll ε) ⊆ closedBall 0 ε := by
  intro w hw
  rw [Function.mem_support] at hw
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hw (moll_eq_zero_of_le hε (not_le.mp h).le)

theorem hasCompactSupport_moll {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (moll ε) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ε) fun w hw => by
    by_contra h
    exact hw (support_moll_subset hε h)

theorem integrable_moll {ε : ℝ} (hε : 0 < ε) : Integrable (moll ε) :=
  (moll_continuous ε).integrable_of_hasCompactSupport (hasCompactSupport_moll hε)

theorem integral_moll {ε : ℝ} (hε : 0 < ε) : ∫ w : ℂ, moll ε w = 1 := by
  unfold moll
  rw [integral_div]
  exact div_self (mollNorm_pos hε).ne'

/-- The mollifier depends only on the norm. -/
theorem moll_eq_of_norm_eq (ε : ℝ) {w w' : ℂ} (h : ‖w‖ = ‖w'‖) : moll ε w = moll ε w' := by
  simp only [moll, rawMoll, h]

/-- The uniform bound `moll ε ≤ 4 / vol (closedBall x ε)`, in the form the Lebesgue
differentiation theorem wants. -/
theorem moll_le {ε : ℝ} (hε : 0 < ε) (x w : ℂ) :
    |moll ε w| ≤ 4 / (volume : Measure ℂ).real (closedBall x ε) := by
  have hB1 : (volume : Measure ℂ) (closedBall (0 : ℂ) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hB1' : (volume : Measure ℂ) (closedBall (0 : ℂ) 1) ≠ 0 :=
    (measure_closedBall_pos _ _ one_pos).ne'
  have hsmall : (volume : Measure ℂ).real (closedBall (0 : ℂ) (ε / 2))
      = (volume : Measure ℂ).real (closedBall x ε) / 4 := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_closedBall _ _ (by positivity),
      Measure.addHaar_closedBall _ _ hε.le, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      Complex.finrank_real_complex]
    ring
  have hpos : 0 < (volume : Measure ℂ).real (closedBall x ε) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos _ _ hε).ne' measure_closedBall_lt_top.ne
  have hN : (volume : Measure ℂ).real (closedBall x ε) / 4 ≤ mollNorm ε :=
    hsmall ▸ volume_closedBall_le_mollNorm hε
  rw [abs_of_nonneg (moll_nonneg hε w)]
  unfold moll
  rw [div_le_div_iff₀ (mollNorm_pos hε) hpos]
  calc rawMoll ε w * (volume : Measure ℂ).real (closedBall x ε)
      ≤ 1 * (volume : Measure ℂ).real (closedBall x ε) := by
        gcongr; exact rawMoll_le_one ε w
    _ = 4 * ((volume : Measure ℂ).real (closedBall x ε) / 4) := by ring
    _ ≤ 4 * mollNorm ε := by gcongr

/-! ### Mollification -/

/-- The mollification `moll ε ⋆ u` of a function `u : ℂ → ℂ`, with the real
scalar action as the bilinear pairing. -/
noncomputable def smooth (ε : ℝ) (u : ℂ → ℂ) : ℂ → ℂ :=
  moll ε ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ), volume] u

/-- The bilinear pairing used in `smooth`, named once. -/
noncomputable abbrev L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ

/-- The pairing that appears in the derivative of a mollification. -/
noncomputable abbrev L' : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℂ := L.precompL ℂ

theorem smooth_apply (ε : ℝ) (u : ℂ → ℂ) (x : ℂ) :
    smooth ε u x = ∫ t, moll ε t • u (x - t) := by
  simp only [smooth, convolution_def, ContinuousLinearMap.lsmul_apply]

theorem smooth_apply' (ε : ℝ) (u : ℂ → ℂ) (x : ℂ) :
    smooth ε u x = ∫ t, moll ε (x - t) • u t := by
  simp only [smooth, convolution_eq_swap, ContinuousLinearMap.lsmul_apply]

theorem smooth_contDiff {ε : ℝ} (hε : 0 < ε) {u : ℂ → ℂ} (hu : LocallyIntegrable u) :
    ContDiff ℝ 1 (smooth ε u) :=
  (hasCompactSupport_moll hε).contDiff_convolution_left _ (moll_contDiff_one ε) hu

set_option maxSynthPendingDepth 3 in
/-- The integrand of the derivative of a mollification is integrable. -/
theorem integrable_fderiv_moll_smul {ε : ℝ} (hε : 0 < ε) {u : ℂ → ℂ} (hu : LocallyIntegrable u)
    (x : ℂ) : Integrable fun t => L' (fderiv ℝ (moll ε) t) (u (x - t)) := by
  have hc : HasCompactSupport (fderiv ℝ (moll ε)) := (hasCompactSupport_moll hε).fderiv (𝕜 := ℝ)
  have hf : Continuous (fderiv ℝ (moll ε)) := continuous_fderiv_moll ε
  exact hc.convolutionExists_left (L := L') hf hu x

set_option maxSynthPendingDepth 3 in
/-- The derivative of the mollification in a direction `v`: the derivative falls
on the mollifier. -/
theorem fderiv_smooth_apply {ε : ℝ} (hε : 0 < ε) {u : ℂ → ℂ} (hu : LocallyIntegrable u)
    (x v : ℂ) :
    fderiv ℝ (smooth ε u) x v = ∫ t, (fderiv ℝ (moll ε) t v) • u (x - t) := by
  have hd := (hasCompactSupport_moll hε).hasFDerivAt_convolution_left L (moll_contDiff_one ε) hu x
  unfold smooth
  rw [hd.fderiv, convolution_def,
    ContinuousLinearMap.integral_apply (integrable_fderiv_moll_smul hε hu x)]
  rfl

/-- The test function `w ↦ moll ε (x − w)`, as a complex-valued function. -/
noncomputable def testFn (ε : ℝ) (x : ℂ) (w : ℂ) : ℂ := (moll ε (x - w) : ℂ)

theorem testFn_contDiff (ε : ℝ) (x : ℂ) : ContDiff ℝ ∞ (testFn ε x) :=
  Complex.ofRealCLM.contDiff.comp ((moll_contDiff ε).comp (contDiff_const.sub contDiff_id))

theorem testFn_hasCompactSupport {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    HasCompactSupport (testFn ε x) := by
  have h1 : HasCompactSupport (fun w => moll ε (x - w)) :=
    (hasCompactSupport_moll hε).comp_homeomorph (Homeomorph.subLeft x)
  exact h1.comp_left Complex.ofReal_zero

theorem tsupport_testFn_subset {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    tsupport (testFn ε x) ⊆ closedBall x ε := by
  refine closure_minimal ?_ isClosed_closedBall
  intro w hw
  rw [Function.mem_support] at hw
  rw [mem_closedBall, dist_comm, dist_eq_norm]
  by_contra h
  apply hw
  simp only [testFn]
  rw [moll_eq_zero_of_le hε (not_le.mp h).le, Complex.ofReal_zero]

theorem fderiv_testFn (ε : ℝ) (x w v : ℂ) :
    fderiv ℝ (testFn ε x) w v = -((fderiv ℝ (moll ε) (x - w) v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun w : ℂ => x - w) (-(ContinuousLinearMap.id ℝ ℂ)) w :=
    (hasFDerivAt_id w).const_sub x
  have h2 : HasFDerivAt (moll ε) (fderiv ℝ (moll ε) (x - w)) (x - w) :=
    (moll_differentiable ε _).hasFDerivAt
  have h3 := (Complex.ofRealCLM.hasFDerivAt.comp (x - w) h2).comp w h1
  have h4 : HasFDerivAt (testFn ε x)
      ((Complex.ofRealCLM ∘L fderiv ℝ (moll ε) (x - w)) ∘L (-(ContinuousLinearMap.id ℝ ℂ))) w :=
    h3
  rw [h4.fderiv]
  simp

/-- **The mollification of a weak solution is a classical solution.**  If the
weak Cauchy–Riemann equation holds on `U` and the disc `closedBall x ε` lies in
`U`, then `∂̄ (moll ε ⋆ u) x = 0`. -/
theorem dbar_smooth_eq_zero {U : Set ℂ} {u : ℂ → ℂ} (hu : LocallyIntegrable u)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z : ℂ, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I) * u z = 0)
    {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : closedBall x ε ⊆ U) :
    fderiv ℝ (smooth ε u) x 1 + Complex.I * fderiv ℝ (smooth ε u) x Complex.I = 0 := by
  have hweak := h (testFn ε x) (testFn_contDiff ε x) (testFn_hasCompactSupport hε x)
    ((tsupport_testFn_subset hε x).trans hx)
  simp only [fderiv_testFn] at hweak
  -- the integrand is `-F (x - w)` with `F t = (D t 1 + i D t I) • u (x - t)`
  set F : ℂ → ℂ := fun t =>
    (((fderiv ℝ (moll ε) t 1 : ℝ) : ℂ) + Complex.I * ((fderiv ℝ (moll ε) t Complex.I : ℝ) : ℂ))
      * u (x - t) with hF
  have hcongr : (fun w => (-((fderiv ℝ (moll ε) (x - w) 1 : ℝ) : ℂ)
      + Complex.I * -((fderiv ℝ (moll ε) (x - w) Complex.I : ℝ) : ℂ)) * u w)
      = fun w => -F (x - w) := by
    funext w
    simp only [hF, sub_sub_cancel]
    ring
  rw [hcongr, integral_neg, neg_eq_zero, integral_sub_left_eq_self F volume x] at hweak
  have hint : ∀ v : ℂ, Integrable fun t => (fderiv ℝ (moll ε) t v) • u (x - t) := fun v =>
    Integrable.apply_continuousLinearMap (integrable_fderiv_moll_smul hε hu x) v
  have hFeq : F = fun t => (fderiv ℝ (moll ε) t 1) • u (x - t)
      + Complex.I * ((fderiv ℝ (moll ε) t Complex.I) • u (x - t)) := by
    funext t
    simp only [hF, Complex.real_smul]
    ring
  rw [hFeq, integral_add (hint 1) ((hint Complex.I).const_mul _), integral_const_mul] at hweak
  rw [fderiv_smooth_apply hε hu x 1, fderiv_smooth_apply hε hu x Complex.I]
  exact hweak

/-! ### The mean value property against a radial weight -/

/-- Cauchy's formula as a circle average: a holomorphic function on a closed disc
is the average of its values on the boundary circle. -/
theorem circleAverage_eq_of_differentiableOn {h : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (closedBall z r)) : Real.circleAverage h z r = h z := by
  rw [Real.circleAverage_eq_circleIntegral hr.ne',
    hh.circleIntegral_sub_inv_smul (mem_ball_self hr), smul_smul,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]

/-- The integral over `(-π, π)` of `h (z - r e^{iθ})` is `2π h z`. -/
theorem integral_Ioo_eq_of_differentiableOn {h : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (closedBall z r)) :
    ∫ θ in Ioo (-π) π, h (z - Complex.polarCoord.symm (r, θ)) = (2 * π : ℝ) • h z := by
  have hcirc : ∀ θ : ℝ, z - Complex.polarCoord.symm (r, θ) = circleMap z r (θ + π) := by
    intro θ
    simp only [Complex.polarCoord_symm_apply, circleMap]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  simp_rw [hcirc]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π),
    intervalIntegral.integral_comp_add_right (fun θ => h (circleMap z r θ)) π,
    show -π + π = (0 : ℝ) by ring, show π + π = 2 * π by ring]
  have := circleAverage_eq_of_differentiableOn hr hh
  rw [Real.circleAverage_def] at this
  rw [← this, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- Polar coordinates for a compactly supported continuous function:
`∫ F = ∫_{r>0} r • ∫_{θ ∈ (-π,π)} F (r e^{iθ})`. -/
theorem integral_eq_polar {F : ℂ → ℂ} (hF : Continuous F) {ε : ℝ} (hε : 0 < ε)
    (hsupp : ∀ w, ε ≤ ‖w‖ → F w = 0) :
    ∫ w, F w
      = ∫ r in Ioi (0 : ℝ), r • ∫ θ in Ioo (-π) π, F (Complex.polarCoord.symm (r, θ)) := by
  set G : ℝ × ℝ → ℂ := fun p => p.1 • F (Complex.polarCoord.symm p) with hG
  have hGc : Continuous G := by
    have : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    exact continuous_fst.smul (hF.comp this)
  have hint : IntegrableOn G (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : ℂ) ε).exists_bound_of_continuousOn hF.continuousOn
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self hε.le))
    set box : Set (ℝ × ℝ) := Icc (-ε) ε ×ˢ Icc (-π) π with hbox
    have hboxc : IsCompact box := isCompact_Icc.prod isCompact_Icc
    have hbound : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ‖G p‖ ≤ box.indicator (fun _ => ε * C) p := by
      rintro ⟨r, θ⟩ ⟨hr, hθ⟩
      have hr' : (0 : ℝ) < r := hr
      simp only [hG, norm_smul, Real.norm_eq_abs, abs_of_pos hr']
      by_cases hrε : r ≤ ε
      · rw [indicator_of_mem (show (r, θ) ∈ box from ⟨⟨by linarith, hrε⟩, ⟨hθ.1.le, hθ.2.le⟩⟩)]
        have h1 : ‖F (Complex.polarCoord.symm (r, θ))‖ ≤ C := hC _ (by
          rw [mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hr']
          exact hrε)
        exact mul_le_mul hrε h1 (norm_nonneg _) hε.le
      · rw [hsupp _ (by rw [Complex.norm_polarCoord_symm, abs_of_pos hr']; exact (not_le.mp hrε).le),
          norm_zero, mul_zero]
        exact indicator_nonneg (fun _ _ => by positivity) _
    have hind : Integrable (box.indicator fun _ => ε * C)
        (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-π) π)) := by
      refine (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr ?_
      refine integrableOn_const ?_
      exact ne_top_of_le_ne_top hboxc.measure_lt_top.ne (Measure.le_iff'.1 Measure.restrict_le_self _)
    refine Integrable.mono' hind hGc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    exact hbound p hp
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    setIntegral_prod G (by rw [← Measure.volume_eq_prod]; exact hint)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [hG]
  rw [integral_smul]

/-- The mollification identity for a general `g`: if the circle integrals of
`g` around `z` are all equal to `c`, then `∫ moll ε t • g (z − t)` is `c` times
the radial mass `∫_{r>0} r moll ε r`. -/
theorem integral_moll_smul_eq_aux {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} {z : ℂ}
    (hF : Continuous fun t => moll ε t • g (z - t)) {c : ℂ}
    (hc : ∀ r : ℝ, 0 < r → r < ε →
      ∫ θ in Ioo (-π) π, g (z - Complex.polarCoord.symm (r, θ)) = c) :
    ∫ t, moll ε t • g (z - t) = (∫ r in Ioi (0 : ℝ), r * moll ε (r : ℂ)) • c := by
  rw [integral_eq_polar hF hε (fun w hw => by rw [moll_eq_zero_of_le hε hw, zero_smul]),
    ← integral_smul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  have hm : ∀ θ : ℝ, moll ε (Complex.polarCoord.symm (r, θ)) = moll ε (r : ℂ) := fun θ =>
    moll_eq_of_norm_eq ε (by rw [Complex.norm_polarCoord_symm, Complex.norm_real, Real.norm_eq_abs])
  simp only [hm]
  rw [integral_smul]
  by_cases hrε : r < ε
  · rw [hc r hr' hrε, smul_smul]
  · rw [moll_eq_zero_of_le hε (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr']
      exact not_lt.mp hrε), zero_smul, smul_zero, mul_zero, zero_smul]

/-- **The mean value property against a radial weight.**  If `h` is holomorphic on
a disc around `z` of radius larger than `ε`, then `∫ moll ε t • h (z − t) = h z`. -/
theorem integral_moll_smul_eq {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ} {z : ℂ} {R : ℝ} (hR : ε < R)
    (hh : DifferentiableOn ℂ h (ball z R)) :
    ∫ t, moll ε t • h (z - t) = h z := by
  have hcont : Continuous fun t => moll ε t • h (z - t) := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : ‖t‖ < R
    · have hmem : z - t ∈ ball z R := by
        rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact ht
      have h1 : ContinuousAt h (z - t) :=
        hh.continuousOn.continuousAt (isOpen_ball.mem_nhds hmem)
      exact (moll_continuous ε).continuousAt.smul
        (h1.comp (continuous_const.sub continuous_id).continuousAt)
    · have hev : (fun t => moll ε t • h (z - t)) =ᶠ[𝓝 t] fun _ => 0 := by
        have hopen : IsOpen {w : ℂ | ε < ‖w‖} := isOpen_lt continuous_const continuous_norm
        filter_upwards [hopen.mem_nhds (show ε < ‖t‖ by linarith [not_lt.mp ht])] with w hw
        rw [moll_eq_zero_of_le hε (le_of_lt hw), zero_smul]
      exact continuousAt_const.congr hev.symm
  have hkey := integral_moll_smul_eq_aux hε hcont (c := (2 * π : ℝ) • h z)
    (fun r hr hrε => integral_Ioo_eq_of_differentiableOn hr
      (hh.mono (closedBall_subset_ball (by linarith))))
  have hone := integral_moll_smul_eq_aux hε (g := fun _ => (1 : ℂ)) (z := z)
    ((moll_continuous ε).smul continuous_const) (c := (2 * π : ℝ) • (1 : ℂ))
    (fun r _ _ => by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      congr 1
      ring)
  rw [integral_smul_const, integral_moll hε, one_smul, smul_smul] at hone
  have hA : (∫ r in Ioi (0 : ℝ), r * moll ε (r : ℂ)) * (2 * π) = 1 := by
    have := hone
    rw [Complex.real_smul, mul_one] at this
    exact_mod_cast this.symm
  rw [hkey, smul_smul, hA, one_smul]

/-! ### Independence of the mollification radius -/

/-- Convolution of two mollifiers is commutative. -/
theorem moll_conv_comm (ε δ : ℝ) (w : ℂ) :
    (moll ε ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] moll δ) w
      = (moll δ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] moll ε) w := by
  rw [convolution_eq_swap, convolution_def]
  congr 1
  funext t
  rw [ContinuousLinearMap.mul_apply', ContinuousLinearMap.mul_apply', mul_comm]

/-- Associativity, in the form needed: `moll a ⋆ (moll b ⋆ u) = (moll a ⋆ moll b) ⋆ u`. -/
theorem smooth_smooth_eq {u : ℂ → ℂ} (hu : Integrable u) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) :
    (moll a ⋆[L, volume] (moll b ⋆[L, volume] u)) z
      = ((moll a ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] moll b) ⋆[L, volume] u) z := by
  symm
  have hfg : ConvolutionExists (moll a) (moll b) (ContinuousLinearMap.mul ℝ ℝ) volume :=
    (hasCompactSupport_moll hb).convolutionExists_right _ (integrable_moll ha).locallyIntegrable
      (moll_continuous b)
  have hgk : ConvolutionExists (fun x => ‖moll b x‖) (fun x => ‖u x‖)
      (ContinuousLinearMap.mul ℝ ℝ) volume :=
    (hasCompactSupport_moll hb).norm.convolutionExists_left (𝕜 := ℝ)
      (ContinuousLinearMap.mul ℝ ℝ) (moll_continuous b).norm hu.norm.locallyIntegrable
  have hcont : Continuous ((fun x => ‖moll b x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      fun x => ‖u x‖) :=
    (hasCompactSupport_moll hb).norm.continuous_convolution_left (𝕜 := ℝ)
      (ContinuousLinearMap.mul ℝ ℝ) (moll_continuous b).norm hu.norm.locallyIntegrable
  have hfgk : ConvolutionExists (fun x => ‖moll a x‖)
      ((fun x => ‖moll b x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖u x‖)
      (ContinuousLinearMap.mul ℝ ℝ) volume :=
    (hasCompactSupport_moll ha).norm.convolutionExists_left (𝕜 := ℝ)
      (ContinuousLinearMap.mul ℝ ℝ) (moll_continuous a).norm hcont.locallyIntegrable
  exact convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) L L L (fun x y w => mul_smul x y w)
    (moll_continuous a).aestronglyMeasurable (moll_continuous b).aestronglyMeasurable
    hu.aestronglyMeasurable (Eventually.of_forall hfg) (Eventually.of_forall hgk) (hfgk z)

/-- **Two mollifications agree where both are holomorphic.**  If `moll ε ⋆ u` and
`moll δ ⋆ u` are holomorphic on a disc of radius `R > ε, δ` around `z`, they
take the same value at `z`. -/
theorem smooth_eq_smooth {u : ℂ → ℂ} (hu : Integrable u) {ε δ R : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hεR : ε < R) (hδR : δ < R) {z : ℂ}
    (h1 : DifferentiableOn ℂ (smooth ε u) (ball z R))
    (h2 : DifferentiableOn ℂ (smooth δ u) (ball z R)) :
    smooth ε u z = smooth δ u z := by
  have e1 : smooth ε u z = (moll δ ⋆[L, volume] smooth ε u) z := by
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
    exact (integral_moll_smul_eq hδ hδR h1).symm
  have e2 : smooth δ u z = (moll ε ⋆[L, volume] smooth δ u) z := by
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
    exact (integral_moll_smul_eq hε hεR h2).symm
  rw [e1, e2]
  unfold smooth
  rw [smooth_smooth_eq hu hδ hε, smooth_smooth_eq hu hε hδ]
  have hcomm : (moll δ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] moll ε)
      = (moll ε ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] moll δ) := funext (moll_conv_comm δ ε)
  rw [hcomm]

/-! ### Almost-everywhere convergence of mollifications -/

/-- Mollifications of an integrable function converge to it almost everywhere,
by the Lebesgue differentiation theorem. -/
theorem ae_tendsto_smooth {u : ℂ → ℂ} (hu : Integrable u) :
    ∀ᵐ x₀ ∂(volume : Measure ℂ), Tendsto (fun ε => smooth ε u x₀) (𝓝[>] 0) (𝓝 (u x₀)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure ℂ)).ae_tendsto_average_norm_sub
    hu.locallyIntegrable] with x₀ hx₀
  have hf : Tendsto (fun ε : ℝ => ⨍ y in closedBall x₀ ε, ‖u y - u x₀‖) (𝓝[>] 0) (𝓝 0) :=
    hx₀.comp (Besicovitch.tendsto_filterAt volume x₀)
  have key := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
    (a := fun ε => closedBall x₀ ε) (l := 𝓝[>] 0) (f := u) (c := u x₀)
    (g := fun ε y => moll ε (x₀ - y)) 4 hf ?_ ?_ ?_ ?_
  · refine key.congr fun ε => ?_
    rw [smooth_apply']
  · exact Eventually.of_forall fun ε => hu.integrableOn
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [integral_sub_left_eq_self (moll ε) volume x₀, integral_moll hε]
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    intro y hy
    rw [Function.mem_support] at hy
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    by_contra h
    exact hy (moll_eq_zero_of_le hε (not_le.mp h).le)
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    intro y
    exact moll_le hε x₀ (x₀ - y)

/-! ### Weyl's lemma -/

/-- **Local form.**  Around every point of `U` there is a disc on which a single
mollification of `u` is holomorphic and equals `u` almost everywhere. -/
theorem exists_local {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ} (hu : LocallyIntegrableOn u U)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z : ℂ, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I) * u z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ U ∧ ∃ v : ℂ → ℂ, DifferentiableOn ℂ v (ball z₀ r) ∧
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball z₀ r → u z = v z := by
  obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set R := r' / 5 with hR
  have hRpos : 0 < R := by positivity
  set K := closedBall z₀ (4 * R) with hKdef
  have hK : K ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
  set w : ℂ → ℂ := K.indicator u with hw
  have hwint : Integrable w :=
    ((hu.mono_set hK).integrableOn_isCompact (isCompact_closedBall _ _)).integrable_indicator
      measurableSet_closedBall
  -- the weak equation, for the cut-off `w` and test functions inside the disc
  have hweak : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball z₀ (4 * R) →
      ∫ z, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I) * w z = 0 := by
    intro φ hφ hφc hφs
    rw [← h φ hφ hφc (hφs.trans (ball_subset_closedBall.trans hK))]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · have hzK : z ∈ K := ball_subset_closedBall (hφs hz)
      simp only [hw, indicator_of_mem hzK]
    · have hev : φ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
      have h0 : fderiv ℝ φ z = 0 := by
        rw [hev.fderiv_eq]
        simp
      simp [h0]
  -- every small mollification of `w` is holomorphic on the disc of radius `3R`
  have hhol : ∀ ε : ℝ, 0 < ε → ε < R → DifferentiableOn ℂ (smooth ε w) (ball z₀ (3 * R)) := by
    intro ε hε hεR z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨(smooth_contDiff hε hwint.locallyIntegrable).differentiable one_ne_zero z, ?_⟩
    have hcb : closedBall z ε ⊆ ball z₀ (4 * R) := by
      intro y hy
      rw [mem_ball] at hz ⊢
      rw [mem_closedBall] at hy
      calc dist y z₀ ≤ dist y z + dist z z₀ := dist_triangle _ _ _
        _ < 4 * R := by linarith
    have hcr := dbar_smooth_eq_zero hwint.locallyIntegrable hweak hε hcb
    rw [smul_eq_mul]
    linear_combination (-Complex.I) * hcr + (fderiv ℝ (smooth ε w) z Complex.I) * Complex.I_sq
  -- and they all agree on the disc of radius `2R`
  have hind : ∀ ε δ : ℝ, 0 < ε → ε < R → 0 < δ → δ < R → ∀ z ∈ ball z₀ (2 * R),
      smooth ε w z = smooth δ w z := by
    intro ε δ hε hεR hδ hδR z hz
    have hsub : ball z R ⊆ ball z₀ (3 * R) := by
      intro y hy
      rw [mem_ball] at hy hz ⊢
      linarith [dist_triangle y z z₀]
    exact smooth_eq_smooth hwint hε hδ hεR hδR ((hhol ε hε hεR).mono hsub)
      ((hhol δ hδ hδR).mono hsub)
  refine ⟨R, hRpos, ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hK), smooth (R / 2) w,
    (hhol _ (by positivity) (by linarith)).mono (ball_subset_ball (by linarith)), ?_⟩
  filter_upwards [ae_tendsto_smooth hwint] with z hz hzball
  have hzK : z ∈ K :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hzball
  have hwz : w z = u z := by simp only [hw, indicator_of_mem hzK]
  have hconst : Tendsto (fun ε => smooth ε w z) (𝓝[>] 0) (𝓝 (smooth (R / 2) w z)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hRpos] with ε hε
    exact hind (R / 2) ε (by positivity) (by linarith) hε.1 hε.2 z
      (ball_subset_ball (by linarith) hzball)
  rw [← hwz]
  exact tendsto_nhds_unique hz hconst

/-- **Weyl's lemma for `∂̄`.**  A locally integrable weak solution of the
Cauchy–Riemann equation on an open set agrees almost everywhere with a
holomorphic function. -/
theorem exists_differentiableOn_ae_eq {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : LocallyIntegrableOn u U)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z : ℂ, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I) * u z = 0) :
    ∃ v : ℂ → ℂ, DifferentiableOn ℂ v U ∧
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → u z = v z := by
  choose! r hr hrU v hv hae using fun z (hz : z ∈ U) => exists_local hU hu h hz
  have hagree : ∀ z₀ ∈ U, ∀ z ∈ ball z₀ (r z₀), v z z = v z₀ z := by
    intro z₀ hz₀ z hz
    have hzU : z ∈ U := hrU z₀ hz₀ hz
    set W := ball z (r z) ∩ ball z₀ (r z₀) with hW
    have hWo : IsOpen W := isOpen_ball.inter isOpen_ball
    have hae' : v z =ᵐ[volume.restrict W] v z₀ := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hWo.measurableSet]
      filter_upwards [hae z hzU, hae z₀ hz₀] with y h1 h2 hy
      rw [← h1 hy.1, ← h2 hy.2]
    have := Measure.eqOn_open_of_ae_eq hae' hWo
      ((hv z hzU).continuousOn.mono inter_subset_left)
      ((hv z₀ hz₀).continuousOn.mono inter_subset_right)
    exact this ⟨mem_ball_self (hr z hzU), hz⟩
  refine ⟨fun z => v z z, ?_, ?_⟩
  · intro z₀ hz₀
    have hev : (fun z => v z z) =ᶠ[𝓝 z₀] v z₀ :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self (hr z₀ hz₀)))
        fun z hz => hagree z₀ hz₀ z hz
    exact (((hv z₀ hz₀).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr z₀ hz₀)))).congr_of_eventuallyEq hev)
      |>.differentiableWithinAt
  · obtain ⟨t, htU, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := U)
      (f := fun z => ball z (r z)) fun z hz =>
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))
    have hall : ∀ᵐ y ∂(volume : Measure ℂ), ∀ z ∈ t, y ∈ ball z (r z) → u y = v z y :=
      (ae_ball_iff htc).mpr fun z hz => hae z (htU hz)
    filter_upwards [hall] with y hy hyU
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (hcover hyU)
    rw [hy z hzt hyz]
    exact (hagree z (htU hzt) y hyz).symm

end Weyl
end MorseFloer
