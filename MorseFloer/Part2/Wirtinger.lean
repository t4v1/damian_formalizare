import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Wirtinger's inequality and Yorke's theorem (Proposition 6.1.5)

This file proves the analytic input behind Proposition 6.1.5 of the book: if a
vector field `X` on a Euclidean space is `K`-Lipschitz with `K < 2π`, then every
`1`-periodic solution of `ẋ = X(x)` is constant.  The book credits the bound to
Yorke and proves it by Fourier series; that is what is done here.

## Wirtinger's inequality

For a `C¹` function `f` on `ℝ` with `f 1 = f 0` and `∫₀¹ f = 0`,

`∫₀¹ ‖f‖² ≤ (1 / 4π²) ∫₀¹ ‖f'‖²`.

The proof is Parseval's identity (`hasSum_sq_fourierCoeffOn`) applied to `f` and
to `f'`, together with the integration by parts
`fourierCoeffOn_of_hasDerivAt`, which reads `f̂(n) = f̂'(n) / (2πi n)` once the
boundary term `f 1 − f 0` is gone.  The zeroth coefficient of `f` is its mean,
which vanishes by hypothesis, and for `n ≠ 0` one has `|f̂(n)|² ≤ |f̂'(n)|² / 4π²`
because `n² ≥ 1`.  This is `Wirtinger.complex`, for complex-valued `f`; the
version for a finite-dimensional real inner product space, `Wirtinger.inner_space`,
follows by expanding `‖v‖²` along an orthonormal basis.

## Yorke's theorem

Given a `1`-periodic solution `x` and a shift `t`, the function
`y(s) = x(s + t) − x(s)` is `C¹`, `1`-periodic, has mean zero, and satisfies
`‖y'(s)‖ = ‖X(x(s + t)) − X(x(s))‖ ≤ K ‖y(s)‖`.  Wirtinger gives
`∫ ‖y‖² ≤ (K² / 4π²) ∫ ‖y‖²`, so `∫ ‖y‖² = 0` when `K < 2π`, hence `y = 0` on
`[0, 1]` by continuity and in particular `x t = x 0`.  This is `Wirtinger.yorke`,
which Chapter 6 restates as Proposition 6.1.5.
-/

open Set Function Real Complex MeasureTheory intervalIntegral
open scoped RealInnerProductSpace NNReal

namespace MorseFloer
namespace Wirtinger

/-- A continuous nonnegative function on `ℝ` whose integral over `[0, 1]`
vanishes is zero on `[0, 1]`. -/
theorem eq_zero_of_integral_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ t, 0 ≤ f t) (h : (∫ t in (0:ℝ)..1, f t) = 0) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : f t = 0 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    hf.intervalIntegrable a b
  have hFzero : ∀ τ ∈ Set.Icc (0:ℝ) 1, (∫ σ in (0:ℝ)..τ, f σ) = 0 := by
    intro τ hτ
    have hadd : (∫ σ in (0:ℝ)..τ, f σ) + (∫ σ in τ..(1:ℝ), f σ) = ∫ σ in (0:ℝ)..(1:ℝ), f σ :=
      intervalIntegral.integral_add_adjacent_intervals (hint 0 τ) (hint τ 1)
    have h1 : 0 ≤ ∫ σ in (0:ℝ)..τ, f σ :=
      intervalIntegral.integral_nonneg hτ.1 fun u _ => hpos u
    have h2 : 0 ≤ ∫ σ in τ..(1:ℝ), f σ :=
      intervalIntegral.integral_nonneg hτ.2 fun u _ => hpos u
    rw [h] at hadd
    linarith
  have hIoo : Set.EqOn f (fun _ => (0:ℝ)) (Set.Ioo (0:ℝ) 1) := by
    intro τ hτ
    have hEq : (fun τ => ∫ σ in (0:ℝ)..τ, f σ) =ᶠ[nhds τ] fun _ => (0:ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hτ] with u hu
      exact hFzero u (Set.Ioo_subset_Icc_self hu)
    have hd : deriv (fun τ => ∫ σ in (0:ℝ)..τ, f σ) τ = 0 := by
      rw [hEq.deriv_eq]
      simp
    rw [Continuous.deriv_integral f hf 0 τ] at hd
    exact hd
  have hIcc : Set.EqOn f (fun _ => (0:ℝ)) (Set.Icc (0:ℝ) 1) := by
    have hcl := hIoo.closure hf continuous_const
    rwa [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hcl
  exact hIcc ht

/-- **Wirtinger's inequality** on `[0, 1]`, complex-valued: for a `C¹` function
`f` with `f 1 = f 0` and mean zero, `∫₀¹ |f|² ≤ (1 / 4π²) ∫₀¹ |f'|²`. -/
theorem complex {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hper : f 1 = f 0) (hmean : ∫ x in (0:ℝ)..1, f x = 0) :
    ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2 ≤ (1 / (4 * π ^ 2)) * ∫ x in (0:ℝ)..1, ‖f' x‖ ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have h01 : (0:ℝ) < 1 := one_pos
  have hL2 : ∀ {g : ℝ → ℂ}, Continuous g → MemLp g 2 (volume.restrict (Ioc (0:ℝ) 1)) := by
    intro g hg
    rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
    exact (hg.norm.pow 2).integrableOn_Ioc
  have hsf := hasSum_sq_fourierCoeffOn h01 (hL2 hfc)
  have hsf' := hasSum_sq_fourierCoeffOn h01 (hL2 hf'c)
  simp only [sub_zero, inv_one, smul_eq_mul, one_mul] at hsf hsf'
  refine hasSum_le (fun i => ?_) hsf (hsf'.mul_left (1 / (4 * π ^ 2)))
  rcases eq_or_ne i 0 with rfl | hi
  · have h0 : fourierCoeffOn h01 f 0 = 0 := by
      rw [fourierCoeffOn_eq_integral]
      simp [hmean]
    rw [h0, norm_zero, zero_pow two_ne_zero]
    positivity
  · have heq := fourierCoeffOn_of_hasDerivAt h01 hi (fun x _ => hf x)
      (hf'c.intervalIntegrable 0 1)
    simp only [hper, sub_self, mul_zero, zero_sub, Complex.ofReal_one, Complex.ofReal_zero,
      sub_zero, one_mul] at heq
    have habs : (1:ℝ) ≤ |(i:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
    have hnorm : ‖fourierCoeffOn h01 f i‖ ≤ (1 / (2 * π)) * ‖fourierCoeffOn h01 f' i‖ := by
      rw [heq, norm_mul, norm_neg, norm_div, norm_one]
      have h1 : ‖(-2 * π * I * i : ℂ)‖ = 2 * π * |(i:ℝ)| := by
        simp [abs_of_pos Real.pi_pos]
      rw [h1]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply one_div_le_one_div_of_le (by positivity)
      exact le_mul_of_one_le_right (by positivity) habs
    calc ‖fourierCoeffOn h01 f i‖ ^ 2 ≤ ((1 / (2 * π)) * ‖fourierCoeffOn h01 f' i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = (1 / (4 * π ^ 2)) * ‖fourierCoeffOn h01 f' i‖ ^ 2 := by
          rw [mul_pow, div_pow, one_pow, mul_pow]; norm_num

section InnerSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Wirtinger's inequality** for a `C¹` map `y : ℝ → V` into a finite-dimensional
real inner product space, with `y 1 = y 0` and mean zero:
`∫₀¹ ‖y‖² ≤ (1 / 4π²) ∫₀¹ ‖y'‖²`.  Proved coordinatewise along an orthonormal
basis from the complex-valued case. -/
theorem inner_space {y y' : ℝ → V} (hy : ∀ t, HasDerivAt y (y' t) t) (hy'c : Continuous y')
    (hper : y 1 = y 0) (hmean : ∫ t in (0:ℝ)..1, y t = 0) :
    ∫ t in (0:ℝ)..1, ‖y t‖ ^ 2 ≤ (1 / (4 * π ^ 2)) * ∫ t in (0:ℝ)..1, ‖y' t‖ ^ 2 := by
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  let b := stdOrthonormalBasis ℝ V
  have hcoord : ∀ i : Fin (Module.finrank ℝ V), ∫ t in (0:ℝ)..1, ‖((⟪b i, y t⟫ : ℝ) : ℂ)‖ ^ 2 ≤
      (1 / (4 * π ^ 2)) * ∫ t in (0:ℝ)..1, ‖((⟪b i, y' t⟫ : ℝ) : ℂ)‖ ^ 2 := by
    intro i
    refine complex (f' := fun t => ((⟪b i, y' t⟫ : ℝ) : ℂ)) (fun t => ?_) ?_ ?_ ?_
    · have h := (hasDerivAt_const t (b i)).inner ℝ (hy t)
      simp only [inner_zero_left, add_zero] at h
      exact h.ofReal_comp
    · exact Complex.continuous_ofReal.comp (continuous_const.inner hy'c)
    · simp only [hper]
    · have hyi : IntervalIntegrable y volume 0 1 := hyc.intervalIntegrable 0 1
      have h := (innerSL ℝ (b i)).intervalIntegral_comp_comm hyi
      simp only [innerSL_apply_apply] at h
      rw [intervalIntegral.integral_ofReal, h, hmean, inner_zero_right, Complex.ofReal_zero]
  have hnormsq : ∀ v : V, ‖v‖ ^ 2 = ∑ i, ‖((⟪b i, v⟫ : ℝ) : ℂ)‖ ^ 2 := by
    intro v
    rw [← b.sum_sq_norm_inner_right v]
    simp only [Complex.norm_real]
  have hint : ∀ (z : ℝ → V), Continuous z → ∀ i : Fin (Module.finrank ℝ V),
      IntervalIntegrable (fun t => ‖((⟪b i, z t⟫ : ℝ) : ℂ)‖ ^ 2) volume 0 1 := by
    intro z hz i
    exact ((Complex.continuous_ofReal.comp (continuous_const.inner hz)).norm.pow 2
      |>.intervalIntegrable 0 1)
  calc ∫ t in (0:ℝ)..1, ‖y t‖ ^ 2
      = ∫ t in (0:ℝ)..1, ∑ i, ‖((⟪b i, y t⟫ : ℝ) : ℂ)‖ ^ 2 := by
        rw [show (fun t => ‖y t‖ ^ 2) = fun t => ∑ i, ‖((⟪b i, y t⟫ : ℝ) : ℂ)‖ ^ 2 from
          funext fun t => hnormsq (y t)]
    _ = ∑ i, ∫ t in (0:ℝ)..1, ‖((⟪b i, y t⟫ : ℝ) : ℂ)‖ ^ 2 :=
        intervalIntegral.integral_finsetSum fun i _ => hint y hyc i
    _ ≤ ∑ i, (1 / (4 * π ^ 2)) * ∫ t in (0:ℝ)..1, ‖((⟪b i, y' t⟫ : ℝ) : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = (1 / (4 * π ^ 2)) * ∑ i, ∫ t in (0:ℝ)..1, ‖((⟪b i, y' t⟫ : ℝ) : ℂ)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1 / (4 * π ^ 2)) * ∫ t in (0:ℝ)..1, ∑ i, ‖((⟪b i, y' t⟫ : ℝ) : ℂ)‖ ^ 2 := by
        rw [intervalIntegral.integral_finsetSum fun i _ => hint y' hy'c i]
    _ = (1 / (4 * π ^ 2)) * ∫ t in (0:ℝ)..1, ‖y' t‖ ^ 2 := by
        rw [show (fun t => ‖y' t‖ ^ 2) = fun t => ∑ i, ‖((⟪b i, y' t⟫ : ℝ) : ℂ)‖ ^ 2 from
          funext fun t => hnormsq (y' t)]

/-- **Yorke's theorem.**  If `X` is `K`-Lipschitz on a finite-dimensional real
inner product space with `K < 2π`, then every `1`-periodic solution of
`ẋ = X(x)` is constant. -/
theorem yorke {X : V → V} {K : ℝ≥0} (hX : LipschitzWith K X) (hK : (K : ℝ) < 2 * π)
    {x : ℝ → V} (hx : ∀ t, HasDerivAt x (X (x t)) t) (hper : Periodic x 1) (t : ℝ) :
    x t = x 0 := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hx s).continuousAt
  have hyd : ∀ s, HasDerivAt (fun s => x (s + t) - x s) (X (x (s + t)) - X (x s)) s :=
    fun s => ((hx (s + t)).comp_add_const s t).sub (hx s)
  have hy'c : Continuous fun s => X (x (s + t)) - X (x s) :=
    (hX.continuous.comp (hxc.comp (continuous_add_const t))).sub (hX.continuous.comp hxc)
  have hyc : Continuous fun s => x (s + t) - x s :=
    continuous_iff_continuousAt.2 fun s => (hyd s).continuousAt
  have hper' : x (1 + t) - x 1 = x (0 + t) - x 0 := by
    have h1 : x 1 = x 0 := by simpa using hper 0
    rw [add_comm 1 t, hper t, h1, zero_add]
  have hmean : ∫ s in (0:ℝ)..1, (x (s + t) - x s) = 0 := by
    have hi1 : IntervalIntegrable (fun s => x (s + t)) volume 0 1 :=
      (hxc.comp (continuous_add_const t)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub hi1 (hxc.intervalIntegrable 0 1),
      intervalIntegral.integral_comp_add_right (f := x) t, zero_add,
      add_comm 1 t, hper.intervalIntegral_add_eq t 0, zero_add, sub_self]
  have hbound : ∀ s, ‖X (x (s + t)) - X (x s)‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖x (s + t) - x s‖ ^ 2 := by
    intro s
    have h := hX.dist_le_mul (x (s + t)) (x s)
    rw [dist_eq_norm, dist_eq_norm] at h
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hW := inner_space hyd hy'c hper' hmean
  have hint1 : IntervalIntegrable (fun s => ‖X (x (s + t)) - X (x s)‖ ^ 2) volume 0 1 :=
    (hy'c.norm.pow 2).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun s => (K : ℝ) ^ 2 * ‖x (s + t) - x s‖ ^ 2) volume 0 1 :=
    ((hyc.norm.pow 2).const_mul _).intervalIntegrable 0 1
  have h2 : ∫ s in (0:ℝ)..1, ‖X (x (s + t)) - X (x s)‖ ^ 2
      ≤ (K : ℝ) ^ 2 * ∫ s in (0:ℝ)..1, ‖x (s + t) - x s‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one hint1 hint2 fun s _ => hbound s
  set W := ∫ s in (0:ℝ)..1, ‖x (s + t) - x s‖ ^ 2 with hWdef
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hc : (1 / (4 * π ^ 2)) * (K : ℝ) ^ 2 < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    have h4 : (K : ℝ) ^ 2 < (2 * π) ^ 2 := pow_lt_pow_left₀ hK (NNReal.coe_nonneg K) two_ne_zero
    have h5 : (2 * π) ^ 2 = 4 * π ^ 2 := by ring
    linarith
  have hWle : W ≤ (1 / (4 * π ^ 2)) * (K : ℝ) ^ 2 * W := by
    calc W ≤ (1 / (4 * π ^ 2)) * ∫ s in (0:ℝ)..1, ‖X (x (s + t)) - X (x s)‖ ^ 2 := hW
      _ ≤ (1 / (4 * π ^ 2)) * ((K : ℝ) ^ 2 * W) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 / (4 * π ^ 2)) * (K : ℝ) ^ 2 * W := by ring
  have hWzero : W = 0 := by
    have : W ≤ 0 := by nlinarith
    exact le_antisymm this hW0
  have hy0 : ‖x (0 + t) - x 0‖ ^ 2 = 0 :=
    eq_zero_of_integral_eq_zero (hyc.norm.pow 2) (fun s => sq_nonneg _) hWzero
      ⟨le_rfl, zero_le_one⟩
  have h0 : x (0 + t) - x 0 = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hy0)
  rwa [zero_add, sub_eq_zero] at h0

end InnerSpace

end Wirtinger
end MorseFloer
