import MorseFloer.Part2.MeanValue

/-!
# Locally uniform limits of solutions of `∂̄w = f`

A helper for Theorem 6.5.4 of Audin–Damian.  Let `W n` be `C¹` functions on `ℂ` with
`∂̄ W n = f n`, converging locally uniformly to `V`, while `f n` converges locally uniformly to a
Lipschitz `g`, and let `V` be Lipschitz.  Then `V` is `C¹` and `∂̄ V = g`
(`contDiff_one_of_tendsto_dbar`).

No weak formulation and no distribution theory is needed.  On a disc, a compactly supported `C¹`
function is the Cauchy transform of its own `∂̄` (`cauchyTransform_dbar`), so for a cut-off `χ`
at the centre,

`χ W n = T(χ f n + W n ∂̄χ)`,

and both sides pass to the limit: `χ V = T(χ g) + T(V ∂̄χ)`.  The two data on the right are
Lipschitz with compact support, hence Hölder, so their Cauchy transforms are `C¹` with the
prescribed `∂̄` (`contDiff_cauchyTransform_of_isHolderC`, `dbar_cauchyTransform_holder`).  Near
the centre `χ = 1` and `∂̄χ = 0`, which gives `∂̄V = g` there.
-/

open MeasureTheory Filter Topology Metric Set
open scoped Real ContDiff

namespace MorseFloer
namespace DbarLimit

open CauchyPompeiu CauchyHolder MeanValue

/-- A `C¹` function with compact support is Lipschitz. -/
theorem exists_lipschitz_of_contDiff {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : HasCompactSupport ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ξ η : ℂ, ‖ψ ξ - ψ η‖ ≤ K * ‖ξ - η‖ := by
  obtain ⟨K, hK⟩ := (hψ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hψs.fderiv ℝ)
  refine ⟨K, (norm_nonneg _).trans (hK 0), fun ξ η => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hψ.differentiable one_ne_zero x) (fun x _ => hK x) convex_univ
    (Set.mem_univ η) (Set.mem_univ ξ)

/-- A Lipschitz function with compact support is Hölder of exponent `1/2`. -/
theorem exists_holder_half {g : ℂ → ℂ} {L : ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (hg : ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ L * ‖ξ - η‖) :
    ∃ C : ℝ, ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ C * ‖ξ - η‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hg' : ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ |L| * ‖ξ - η‖ := fun ξ η =>
    (hg ξ η).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
  refine ⟨|L| + 2 * M, fun ξ η => ?_⟩
  by_cases hξη : ξ = η
  · subst hξη
    rw [sub_self, norm_zero, sub_self, norm_zero, Real.zero_rpow (by norm_num), mul_zero]
  have hd0 : 0 ≤ ‖ξ - η‖ := norm_nonneg _
  have hpos : 0 < ‖ξ - η‖ := norm_pos_iff.2 (sub_ne_zero.2 hξη)
  have hr0 : 0 ≤ ‖ξ - η‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hd0 _
  rcases le_or_gt ‖ξ - η‖ 1 with h | h
  · have h1 : ‖ξ - η‖ ≤ ‖ξ - η‖ ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hpos h (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    calc ‖g ξ - g η‖ ≤ |L| * ‖ξ - η‖ := hg' ξ η
      _ ≤ |L| * ‖ξ - η‖ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ (|L| + 2 * M) * ‖ξ - η‖ ^ (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by linarith) hr0
  · have h1 : (1 : ℝ) ≤ ‖ξ - η‖ ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow zero_le_one h.le (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      rwa [Real.one_rpow] at this
    calc ‖g ξ - g η‖ ≤ ‖g ξ‖ + ‖g η‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM ξ, hM η]
      _ ≤ 2 * M * ‖ξ - η‖ ^ (1 / 2 : ℝ) := le_mul_of_one_le_right (by positivity) h1
      _ ≤ (|L| + 2 * M) * ‖ξ - η‖ ^ (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) hr0

/-- The product of a Lipschitz function with a Lipschitz cut-off supported in the unit disc
about `z₀` is Lipschitz: away from the disc both sides vanish, and on it `g` is bounded. -/
theorem lipschitz_mul_cut {ψ g : ℂ → ℂ} {z₀ : ℂ} {Lψ Mψ Lg : ℝ} (hMψ : 0 ≤ Mψ)
    (hψ0 : ∀ z, 1 ≤ ‖z - z₀‖ → ψ z = 0)
    (hψlip : ∀ ξ η : ℂ, ‖ψ ξ - ψ η‖ ≤ Lψ * ‖ξ - η‖) (hψb : ∀ z, ‖ψ z‖ ≤ Mψ)
    (hg : ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ Lg * ‖ξ - η‖) (ξ η : ℂ) :
    ‖ψ ξ * g ξ - ψ η * g η‖ ≤ (Mψ * Lg + Lψ * (‖g z₀‖ + Lg)) * ‖ξ - η‖ := by
  have hLg : 0 ≤ Lg := by
    have := hg (z₀ + 1) z₀
    simp only [add_sub_cancel_left, norm_one, mul_one] at this
    exact (norm_nonneg _).trans this
  have hLψ : 0 ≤ Lψ := by
    have := hψlip (z₀ + 1) z₀
    simp only [add_sub_cancel_left, norm_one, mul_one] at this
    exact (norm_nonneg _).trans this
  -- the estimate when the second point lies in the disc
  have key : ∀ ξ η : ℂ, ‖η - z₀‖ < 1 →
      ‖ψ ξ * g ξ - ψ η * g η‖ ≤ (Mψ * Lg + Lψ * (‖g z₀‖ + Lg)) * ‖ξ - η‖ := by
    intro ξ η hη
    have hgη : ‖g η‖ ≤ ‖g z₀‖ + Lg := by
      calc ‖g η‖ = ‖g z₀ + (g η - g z₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖g z₀‖ + ‖g η - g z₀‖ := norm_add_le _ _
        _ ≤ ‖g z₀‖ + Lg * ‖η - z₀‖ := add_le_add le_rfl (hg _ _)
        _ ≤ ‖g z₀‖ + Lg := by nlinarith
    calc ‖ψ ξ * g ξ - ψ η * g η‖
        = ‖ψ ξ * (g ξ - g η) + (ψ ξ - ψ η) * g η‖ := by congr 1; ring
      _ ≤ ‖ψ ξ‖ * ‖g ξ - g η‖ + ‖ψ ξ - ψ η‖ * ‖g η‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ Mψ * (Lg * ‖ξ - η‖) + Lψ * ‖ξ - η‖ * (‖g z₀‖ + Lg) := by
          gcongr
          · exact hψb ξ
          · exact hg ξ η
          · exact hψlip ξ η
      _ = (Mψ * Lg + Lψ * (‖g z₀‖ + Lg)) * ‖ξ - η‖ := by ring
  rcases lt_or_ge ‖η - z₀‖ 1 with hη | hη
  · exact key ξ η hη
  rcases lt_or_ge ‖ξ - z₀‖ 1 with hξ | hξ
  · rw [norm_sub_rev, norm_sub_rev ξ η]
    exact key η ξ hξ
  · rw [hψ0 ξ hξ, hψ0 η hη, zero_mul, zero_mul, sub_zero, norm_zero]
    positivity

theorem cauchyTransform_add {g h : ℂ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hhc : Continuous h) (hhs : HasCompactSupport h) (z : ℂ) :
    cauchyTransform (fun ζ => g ζ + h ζ) z = cauchyTransform g z + cauchyTransform h z := by
  have hneg : cauchyTransform (fun ζ => -h ζ) z = -cauchyTransform h z := by
    unfold cauchyTransform
    simp only [smul_neg, integral_neg]
  have this : cauchyTransform (fun ζ => g ζ - -h ζ) z
      = cauchyTransform g z - cauchyTransform (fun ζ => -h ζ) z :=
    cauchyTransform_sub hgc hgs hhc.neg hhs.neg z
  rw [hneg] at this
  simp only [sub_neg_eq_add] at this
  exact this

/-- The `∂̄` of a sum. -/
theorem dbar_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  have h : HasFDerivAt (fun w => f w + g w) (fderiv ℝ f z + fderiv ℝ g z) z :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  rw [dbar, dbar, dbar, h.fderiv, add_apply, add_apply]
  ring

/-- **The Cauchy transform is continuous under uniform convergence of data with supports in a
fixed disc.** -/
theorem tendsto_cauchyTransform {a : ℕ → ℂ → ℂ} {b : ℂ → ℂ} {R : ℝ}
    (hac : ∀ n, Continuous (a n)) (has : ∀ n, HasCompactSupport (a n))
    (hbc : Continuous b) (hbs : HasCompactSupport b)
    (hR : ∀ n ζ, R ≤ ‖ζ‖ → a n ζ = 0) (hRb : ∀ ζ, R ≤ ‖ζ‖ → b ζ = 0)
    (hunif : TendstoUniformlyOn a b atTop (closedBall 0 R)) (z : ℂ) :
    Tendsto (fun n => cauchyTransform (a n) z) atTop (𝓝 (cauchyTransform b z)) := by
  set I : ℝ := ∫ ξ in ball (0 : ℂ) (R + ‖z‖ + 1), ‖ξ‖⁻¹ with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun ξ _ => inv_nonneg.2 (norm_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_order.2 ⟨fun c hc => Eventually.of_forall fun n => hc.trans_le (norm_nonneg _),
    fun ε hε => ?_⟩
  have hδ : 0 < ε / (2 * ((2 * π)⁻¹ * I + 1)) := by positivity
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  filter_upwards [hunif _ hδ] with n hn
  have hdiff : ∀ x, ‖(fun ζ => a n ζ - b ζ) x‖ ≤ ε / (2 * ((2 * π)⁻¹ * I + 1)) := by
    intro x
    by_cases hx : x ∈ closedBall (0 : ℂ) R
    · have := hn x hx
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le
    · rw [mem_closedBall, dist_zero_right, not_le] at hx
      show ‖a n x - b x‖ ≤ _
      rw [hR n x hx.le, hRb x hx.le, sub_self, norm_zero]
      exact hδ.le
  have hzero : ∀ ζ : ℂ, R ≤ ‖ζ‖ → (fun ζ => a n ζ - b ζ) ζ = 0 := fun ζ hζ => by
    show a n ζ - b ζ = 0
    rw [hR n ζ hζ, hRb ζ hζ, sub_self]
  have h1 := norm_cauchyTransform_le ((hac n).sub hbc) ((has n).sub hbs) hdiff hzero z
  rw [← cauchyTransform_sub (hac n) (has n) hbc hbs z]
  have hc0 : 0 ≤ (2 * π)⁻¹ * I := by positivity
  have hfrac : (2 * π)⁻¹ * I / (2 * ((2 * π)⁻¹ * I + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc ‖cauchyTransform (fun ζ => a n ζ - b ζ) z‖
      ≤ (2 * π)⁻¹ * (ε / (2 * ((2 * π)⁻¹ * I + 1)) * I) := h1
    _ = ε * ((2 * π)⁻¹ * I / (2 * ((2 * π)⁻¹ * I + 1))) := by ring
    _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left hfrac hε.le
    _ < ε := by linarith

/-- **Locally uniform limits of solutions of `∂̄w = f` solve `∂̄V = g`, and are `C¹`.** -/
theorem contDiff_one_of_tendsto_dbar {W : ℕ → ℂ → ℂ} {f : ℕ → ℂ → ℂ} {V g : ℂ → ℂ} {L Lg : ℝ}
    (hW : ∀ n, ContDiff ℝ 1 (W n)) (hfc : ∀ n, Continuous (f n))
    (heq : ∀ n z, dbar (W n) z = f n z)
    (hV : ∀ ξ η : ℂ, ‖V ξ - V η‖ ≤ L * ‖ξ - η‖) (hg : ∀ ξ η : ℂ, ‖g ξ - g η‖ ≤ Lg * ‖ξ - η‖)
    (hWlim : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn W V atTop K)
    (hflim : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn f g atTop K) :
    ContDiff ℝ 1 V ∧ ∀ z, dbar V z = g z := by
  have hL : 0 ≤ L := by
    have := hV 1 0
    simp only [sub_zero, norm_one, mul_one] at this
    exact (norm_nonneg _).trans this
  have hLg : 0 ≤ Lg := by
    have := hg 1 0
    simp only [sub_zero, norm_one, mul_one] at this
    exact (norm_nonneg _).trans this
  have hVc : Continuous V := LipschitzWith.continuous (K := NNReal.mk L hL)
    (LipschitzWith.of_dist_le_mul fun ξ η => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]; exact hV ξ η)
  have hgc : Continuous g := LipschitzWith.continuous (K := NNReal.mk Lg hLg)
    (LipschitzWith.of_dist_le_mul fun ξ η => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]; exact hg ξ η)
  -- the local statement
  have key : ∀ z₀ : ℂ, ∃ Φ : ℂ → ℂ, ContDiff ℝ 1 Φ ∧ (∀ z ∈ ball z₀ (1 / 2), Φ z = V z) ∧
      dbar Φ z₀ = g z₀ := by
    intro z₀
    set χ : ℂ → ℂ := cut z₀ 1 with hχdef
    have hχ : ContDiff ℝ ∞ χ := contDiff_cut z₀ 1
    have hχ1' : ContDiff ℝ 1 χ := hχ.of_le (by simp)
    have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
    have hχs : HasCompactSupport χ := hasCompactSupport_cut z₀ one_pos
    have hχ1 : ∀ z, ‖z - z₀‖ ≤ 1 / 2 → χ z = 1 := fun z hz => cut_eq_one one_pos hz
    have hχ0 : ∀ z, 3 / 4 ≤ ‖z - z₀‖ → χ z = 0 := fun z hz =>
      cut_eq_zero one_pos (by rw [mul_one]; exact hz)
    have hχb : ∀ z, ‖χ z‖ ≤ 1 := norm_cut_le_one z₀ 1
    -- `∂̄χ`
    set ψ : ℂ → ℂ := dbar χ with hψdef
    have hψ : ContDiff ℝ ∞ ψ := contDiff_dbar hχ
    have hψc : Continuous ψ := hψ.continuous
    have hψ0 : ∀ z, 3 / 4 < ‖z - z₀‖ → ψ z = 0 := by
      intro z hz
      have hopen : IsOpen {w : ℂ | 3 / 4 < ‖w - z₀‖} := isOpen_lt continuous_const (by fun_prop)
      have hev : χ =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hz] with w hw using hχ0 w (le_of_lt hw)
      exact dbar_eq_zero_of_eventually_const hev
    have hψ0' : ∀ z, 1 ≤ ‖z - z₀‖ → ψ z = 0 := fun z hz => hψ0 z (by linarith)
    have hψs : HasCompactSupport ψ := by
      refine HasCompactSupport.intro (isCompact_closedBall z₀ 1) fun z hz => ?_
      rw [mem_closedBall, not_le, dist_eq_norm] at hz
      exact hψ0' z hz.le
    have hψz₀ : ψ z₀ = 0 := by
      have hev : χ =ᶠ[𝓝 z₀] fun _ => (1 : ℂ) := by
        filter_upwards [Metric.closedBall_mem_nhds z₀ (show (0 : ℝ) < 1 / 2 by norm_num)] with w hw
        rw [mem_closedBall, dist_eq_norm] at hw
        exact hχ1 w hw
      exact dbar_eq_zero_of_eventually_const hev
    obtain ⟨Mψ, hMψ⟩ := hψc.bounded_above_of_compact_support hψs
    have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
    obtain ⟨Lχ, -, hχlip⟩ := exists_lipschitz_of_contDiff hχ1' hχs
    obtain ⟨Lψ, -, hψlip⟩ := exists_lipschitz_of_contDiff (hψ.of_le (by simp)) hψs
    have hχ0' : ∀ z, 1 ≤ ‖z - z₀‖ → χ z = 0 := fun z hz => hχ0 z (by linarith)
    -- the data
    set A : ℕ → ℂ → ℂ := fun n z => χ z * f n z + W n z * ψ z with hAdef
    set B : ℂ → ℂ := fun z => χ z * g z + V z * ψ z with hBdef
    have hAc : ∀ n, Continuous (A n) := fun n =>
      (hχ.continuous.mul (hfc n)).add ((hW n).continuous.mul hψc)
    have hAs : ∀ n, HasCompactSupport (A n) := fun n => (hχs.mul_right).add (hψs.mul_left)
    have hBc : Continuous B := (hχ.continuous.mul hgc).add (hVc.mul hψc)
    have hBs : HasCompactSupport B := (hχs.mul_right).add (hψs.mul_left)
    -- the identity for each `n`
    have hid : ∀ n z, χ z * W n z = cauchyTransform (A n) z := by
      intro n z
      have hw1 : ContDiff ℝ 1 fun w => χ w * W n w := hχ1'.mul (hW n)
      have hws : HasCompactSupport fun w => χ w * W n w := hχs.mul_right
      have hdb : dbar (fun w => χ w * W n w) = A n := by
        funext w
        rw [dbar_mul hχd ((hW n).differentiable one_ne_zero) w, heq n w]
      have := cauchyTransform_dbar hw1 hws
      rw [hdb] at this
      exact (congrFun this z).symm
    -- passing to the limit
    have hR : ∀ ζ : ℂ, ‖z₀‖ + 1 ≤ ‖ζ‖ → 1 ≤ ‖ζ - z₀‖ := fun ζ hζ => by
      have := norm_sub_norm_le ζ z₀
      linarith
    have hAR : ∀ n ζ, ‖z₀‖ + 1 ≤ ‖ζ‖ → A n ζ = 0 := fun n ζ hζ => by
      show χ ζ * f n ζ + W n ζ * ψ ζ = 0
      rw [hχ0' ζ (hR ζ hζ), hψ0' ζ (hR ζ hζ), zero_mul, mul_zero, add_zero]
    have hBR : ∀ ζ, ‖z₀‖ + 1 ≤ ‖ζ‖ → B ζ = 0 := fun ζ hζ => by
      show χ ζ * g ζ + V ζ * ψ ζ = 0
      rw [hχ0' ζ (hR ζ hζ), hψ0' ζ (hR ζ hζ), zero_mul, mul_zero, add_zero]
    have hAB : TendstoUniformlyOn A B atTop (closedBall 0 (‖z₀‖ + 1)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hK : IsCompact (closedBall (0 : ℂ) (‖z₀‖ + 1)) := isCompact_closedBall _ _
      have h1 := (Metric.tendstoUniformlyOn_iff.1 (hflim _ hK)) (ε / 4) (by positivity)
      have h2 := (Metric.tendstoUniformlyOn_iff.1 (hWlim _ hK)) (ε / (4 * (Mψ + 1)))
        (by positivity)
      filter_upwards [h1, h2] with n hn1 hn2 x hx
      have e1 := hn1 x hx
      have e2 := hn2 x hx
      rw [dist_eq_norm] at e1 e2 ⊢
      have hkey : Mψ * (ε / (4 * (Mψ + 1))) ≤ ε / 4 := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc ‖B x - A n x‖
          = ‖χ x * (g x - f n x) + (V x - W n x) * ψ x‖ := by
            show ‖χ x * g x + V x * ψ x - (χ x * f n x + W n x * ψ x)‖ = _
            congr 1; ring
        _ ≤ ‖χ x‖ * ‖g x - f n x‖ + ‖V x - W n x‖ * ‖ψ x‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ 1 * (ε / 4) + ε / (4 * (Mψ + 1)) * Mψ := by
            gcongr
            · exact hχb x
            · exact hMψ x
        _ < ε := by rw [mul_comm (ε / (4 * (Mψ + 1)))]; linarith
    have hlim : ∀ z, χ z * V z = cauchyTransform B z := by
      intro z
      have h1 : Tendsto (fun n => χ z * W n z) atTop (𝓝 (χ z * V z)) :=
        tendsto_const_nhds.mul ((hWlim {z} isCompact_singleton).tendsto_at (mem_singleton z))
      have h2 : Tendsto (fun n => cauchyTransform (A n) z) atTop (𝓝 (cauchyTransform B z)) :=
        tendsto_cauchyTransform hAc hAs hBc hBs hAR hBR hAB z
      have h1' : Tendsto (fun n => cauchyTransform (A n) z) atTop (𝓝 (χ z * V z)) := by
        refine h1.congr fun n => ?_
        exact hid n z
      exact tendsto_nhds_unique h1' h2
    -- the two transforms are `C¹`
    have hχg : ∀ ξ η : ℂ, ‖χ ξ * g ξ - χ η * g η‖
        ≤ (1 * Lg + Lχ * (‖g z₀‖ + Lg)) * ‖ξ - η‖ :=
      lipschitz_mul_cut zero_le_one hχ0' hχlip hχb hg
    have hVψ : ∀ ξ η : ℂ, ‖ψ ξ * V ξ - ψ η * V η‖
        ≤ (Mψ * L + Lψ * (‖V z₀‖ + L)) * ‖ξ - η‖ :=
      lipschitz_mul_cut hMψ0 hψ0' hψlip hMψ hV
    have hχgc : Continuous fun ζ => χ ζ * g ζ := hχ.continuous.mul hgc
    have hχgs : HasCompactSupport fun ζ => χ ζ * g ζ := hχs.mul_right
    have hVψc : Continuous fun ζ => ψ ζ * V ζ := hψc.mul hVc
    have hVψs : HasCompactSupport fun ζ => ψ ζ * V ζ := hψs.mul_right
    obtain ⟨C₁, hC₁⟩ := exists_holder_half hχgc hχgs hχg
    obtain ⟨C₂, hC₂⟩ := exists_holder_half hVψc hVψs hVψ
    have hT₁ : ContDiff ℝ 1 (cauchyTransform fun ζ => χ ζ * g ζ) := by
      have h := contDiff_cauchyTransform_of_isHolderC (α := 1 / 2) (by norm_num) (by norm_num) 0
        hχgs (isHolderC_zero_iff.2 hC₁)
      exact_mod_cast h
    have hT₂ : ContDiff ℝ 1 (cauchyTransform fun ζ => ψ ζ * V ζ) := by
      have h := contDiff_cauchyTransform_of_isHolderC (α := 1 / 2) (by norm_num) (by norm_num) 0
        hVψs (isHolderC_zero_iff.2 hC₂)
      exact_mod_cast h
    have hBsplit : ∀ z, cauchyTransform B z
        = cauchyTransform (fun ζ => χ ζ * g ζ) z + cauchyTransform (fun ζ => ψ ζ * V ζ) z := by
      intro z
      have e : B = fun ζ => χ ζ * g ζ + ψ ζ * V ζ := by
        funext ζ
        show χ ζ * g ζ + V ζ * ψ ζ = _
        ring
      rw [e]
      exact cauchyTransform_add hχgc hχgs hVψc hVψs z
    refine ⟨fun z => cauchyTransform (fun ζ => χ ζ * g ζ) z
      + cauchyTransform (fun ζ => ψ ζ * V ζ) z, hT₁.add hT₂, fun z hz => ?_, ?_⟩
    · show cauchyTransform (fun ζ => χ ζ * g ζ) z + cauchyTransform (fun ζ => ψ ζ * V ζ) z = V z
      rw [← hBsplit z, ← hlim z, hχ1 z (by rw [mem_ball, dist_eq_norm] at hz; exact hz.le),
        one_mul]
    · rw [dbar_add (hT₁.differentiable one_ne_zero z₀) (hT₂.differentiable one_ne_zero z₀),
        dbar_cauchyTransform_holder hχgc hχgs (by norm_num : (0 : ℝ) < 1 / 2) hC₁,
        dbar_cauchyTransform_holder hVψc hVψs (by norm_num : (0 : ℝ) < 1 / 2) hC₂]
      show χ z₀ * g z₀ + ψ z₀ * V z₀ = g z₀
      rw [hχ1 z₀ (by rw [sub_self, norm_zero]; norm_num), hψz₀, one_mul, zero_mul, add_zero]
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro z₀
    obtain ⟨Φ, hΦ, hΦV, -⟩ := key z₀
    have hev : V =ᶠ[𝓝 z₀] Φ := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show (0 : ℝ) < 1 / 2 by norm_num))]
        with z hz using (hΦV z hz).symm
    exact hΦ.contDiffAt.congr_of_eventuallyEq hev
  · intro z₀
    obtain ⟨Φ, -, hΦV, hd⟩ := key z₀
    have hev : V =ᶠ[𝓝 z₀] Φ := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show (0 : ℝ) < 1 / 2 by norm_num))]
        with z hz using (hΦV z hz).symm
    rw [dbar, hev.fderiv_eq, ← dbar, hd]

end DbarLimit
end MorseFloer
