import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Brouwer's fixed point theorem in every dimension

This file proves, with no `sorry`, that a continuous self-map of the closed unit
ball of a finite-dimensional real inner product space has a fixed point
(`MorseFloer.brouwer_fixed_point` for `EuclideanSpace ℝ (Fin n)`,
`MorseFloer.Brouwer.brouwer_fixed_point_of_innerProductSpace` in general), and
the equivalent no-retraction theorem (`MorseFloer.no_retraction`). It supplies
Theorem 2.3.3 of the book (reproved in §4.8.b), which `Chapter2.brouwer` and
`Chapter4.brouwer_fixedPoint` state.

This Mathlib has no homology of spheres and no degree theory, so the proof does
not follow the book. It is analytic, in the style of Milnor and Rogers, and uses
only the change of variables formula, the Banach fixed point theorem, Lagrange
interpolation and smooth partitions of unity. Throughout, `D` is the closed unit
ball and `S` the unit sphere.

**(A) There is no `C¹` retraction `D → S`** (`Brouwer.no_C1_retraction`).
Suppose `r` is `C¹` near `D`, maps `D` into `S` and fixes `S`. Let `A x = Dr(x) - 1`
and let `L` bound `‖A‖` on `D`.

* For `0 ≤ t < 1/(L+1)` the homotopy `fₜ = id + t (r - id)` maps `D` injectively
  onto `D`. Injectivity holds because `r - id` is `L`-Lipschitz on `D`.
  Surjectivity comes from extending `r - id` by zero outside `D`, which stays
  `L`-Lipschitz because `r - id` vanishes on `S` (`norm_indicator_sub_le`), so
  that `id + t (r - id)` becomes a global bijection (Banach fixed point theorem)
  equal to the identity off `D`.
* `det (1 + t A x) > 0` because `‖t A x‖ < 1` (`det_id_add_pos`). The change of
  variables formula then gives `∫_D det (1 + t A) = vol D`
  (`integral_det_homotopy_eq`).
* For each `x`, `t ↦ det (1 + t A x)` is a polynomial of degree at most `dim E`
  (`exists_poly_det`). Lagrange interpolation at `dim E + 1` small nodes
  therefore carries the identity to `t = 1`, giving `∫_D det Dr = vol D > 0`
  (`integral_det_eq_of_forall_small`).
* But `‖r‖ = 1` near every interior point, so `Dr(x)` takes values in `r(x)ᗮ`
  and `det Dr(x) = 0` on the open ball (`det_eq_zero_of_eventually_norm_eq_one`).
  The sphere is null, so `∫_D det Dr = 0`, a contradiction.

**(B) From continuous to smooth.** If `ϕ : D → D` is continuous with no fixed
point, then `‖ϕ x - x‖ ≥ δ > 0` on `D`. A smooth partition of unity gives a `C¹`
map `q` that is uniformly `δ/3`-close to `(1 - δ/3) ϕ` (`exists_contDiff_approx`).
It maps `D` into `D` and still has no fixed point there. The point where the ray
from `q x` through `x` leaves the ball is given by an explicit formula whose
discriminant stays positive near `D`, so it defines a `C¹` retraction `D → S`
(`exists_C1_retraction`). This contradicts (A).

The no-retraction theorem for merely continuous maps follows from the fixed
point theorem applied to `-r`.
-/

open Set Metric MeasureTheory Polynomial
open scoped NNReal ENNReal Manifold

namespace MorseFloer
namespace Brouwer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Linear algebra: the determinant along a ray of operators -/

/-- For an operator `A` on a finite-dimensional space, `t ↦ det (1 + t A)` is a
polynomial in `t` of degree at most `dim E`. It is read off the matrix of `A` in
a basis, as `det (X • M + 1)` over `ℝ[X]`. -/
theorem exists_poly_det (A : E →L[ℝ] E) :
    ∃ p : ℝ[X], p.natDegree ≤ Module.finrank ℝ E ∧
      ∀ t : ℝ, p.eval t = (ContinuousLinearMap.id ℝ E + t • A).det := by
  classical
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin (Module.finrank ℝ E))
    (Fin (Module.finrank ℝ E)) ℝ).map C), ?_, ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · intro t
    have h1 : ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        LinearMap.id + t • (A : E →ₗ[ℝ] E) := LinearMap.ext fun x => by simp
    rw [ContinuousLinearMap.det, h1, ← LinearMap.det_toMatrix b, map_add, map_smul,
      LinearMap.toMatrix_id, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply, M]
    split_ifs <;> simp only [eval_one, eval_zero] <;> ring

/-- An operator within distance `1` of the identity has positive determinant.
It is injective, so `s ↦ det (1 + s A)` has no zero on `[0, 1]`, and the
intermediate value theorem gives the sign, since the value at `s = 0` is `1`. -/
theorem det_id_add_pos {A : E →L[ℝ] E} (hA : ‖A‖ < 1) :
    0 < (ContinuousLinearMap.id ℝ E + A).det := by
  set g : ℝ → ℝ := fun s => (ContinuousLinearMap.id ℝ E + s • A).det
  have hgc : Continuous g := ContinuousLinearMap.continuous_det.comp
    (continuous_const.add (continuous_id.smul continuous_const))
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, g s ≠ 0 := by
    intro s hs h0
    obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.mp
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0)
    have hy' : y + s • A y = 0 := by simpa using LinearMap.mem_ker.mp hy
    have h1 : y = -(s • A y) := eq_neg_of_add_eq_zero_left hy'
    have h2 : ‖y‖ ≤ s * ‖A‖ * ‖y‖ := by
      calc ‖y‖ = ‖s • A y‖ := by rw [← norm_neg (s • A y), ← h1]
        _ = s * ‖A y‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1]
        _ ≤ s * (‖A‖ * ‖y‖) := mul_le_mul_of_nonneg_left (A.le_opNorm y) hs.1
        _ = s * ‖A‖ * ‖y‖ := by ring
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have : s * ‖A‖ < 1 := by nlinarith [norm_nonneg A, hs.2]
    nlinarith
  have hg0 : g 0 = 1 := by simp [g, ContinuousLinearMap.det, LinearMap.det_id]
  have hg1 : g 1 = (ContinuousLinearMap.id ℝ E + A).det := by simp [g]
  rw [← hg1]
  by_contra hle
  push Not at hle
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hgc.continuousOn
    ⟨hle, by rw [hg0]; exact zero_le_one⟩
  exact hne s hs hs0

/-- **Polynomial extrapolation of Jacobian integrals.** Suppose that, for every
`t` in some interval `[0, ε)`, `∫_s det (1 + t A x)` equals the same constant
`c`. Then it also equals `c` at `t = 1`. Pointwise, `t ↦ det (1 + t A x)` is a
polynomial of degree `≤ dim E`, so Lagrange interpolation at `dim E + 1` nodes
in `[0, ε)` expresses its value at `1` as a fixed combination of its values at
the nodes, with weights summing to `1`. Integrating that identity gives the
result. -/
theorem integral_det_eq_of_forall_small [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {s : Set E} (hs : IsCompact s)
    {A : E → E →L[ℝ] E} (hA : ContinuousOn A s) {c ε : ℝ} (hε : 0 < ε)
    (h : ∀ t, 0 ≤ t → t < ε →
      ∫ x in s, (ContinuousLinearMap.id ℝ E + t • A x).det ∂μ = c) :
    ∫ x in s, (ContinuousLinearMap.id ℝ E + A x).det ∂μ = c := by
  classical
  set N := Module.finrank ℝ E
  let S : Finset ℕ := Finset.range (N + 1)
  let v : ℕ → ℝ := fun i => i * (ε / (N + 1))
  have hstep : 0 < ε / (N + 1) := by positivity
  have hv : Set.InjOn v S := by
    intro i _ j _ hij
    exact_mod_cast mul_right_cancel₀ hstep.ne' hij
  have hvs : ∀ i ∈ S, 0 ≤ v i ∧ v i < ε := by
    intro i hi
    have hi' : (i : ℝ) < N + 1 := by
      have := Finset.mem_range.mp hi
      exact_mod_cast this
    refine ⟨by positivity, ?_⟩
    calc v i = i * (ε / (N + 1)) := rfl
      _ < (N + 1) * (ε / (N + 1)) := mul_lt_mul_of_pos_right hi' hstep
      _ = ε := by field_simp
  let w : ℕ → ℝ := fun i => (Lagrange.basis S v i).eval 1
  have hw : ∑ i ∈ S, w i = 1 := by
    simp only [w]
    rw [← Polynomial.eval_finsetSum, Lagrange.sum_basis hv ⟨0, by simp [S]⟩, eval_one]
  have hpt : ∀ x, (ContinuousLinearMap.id ℝ E + A x).det =
      ∑ i ∈ S, (ContinuousLinearMap.id ℝ E + v i • A x).det * w i := by
    intro x
    obtain ⟨p, hpdeg, hpeval⟩ := exists_poly_det (A x)
    have hdeg : p.degree < S.card := by
      rw [Finset.card_range]
      exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hpdeg)
    have key := congrArg (Polynomial.eval 1) (Lagrange.eq_interpolate hv hdeg)
    rw [Lagrange.interpolate_apply, eval_finsetSum] at key
    simp only [eval_mul, eval_C] at key
    have h1 : (ContinuousLinearMap.id ℝ E + A x).det = p.eval 1 := by rw [hpeval, one_smul]
    rw [h1, key]
    exact Finset.sum_congr rfl fun i _ => by rw [hpeval]
  have hint : ∀ t : ℝ, IntegrableOn
      (fun x => (ContinuousLinearMap.id ℝ E + t • A x).det) s μ := fun t =>
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add (hA.const_smul t))).integrableOn_compact hs
  calc ∫ x in s, (ContinuousLinearMap.id ℝ E + A x).det ∂μ
      = ∫ x in s, ∑ i ∈ S, (ContinuousLinearMap.id ℝ E + v i • A x).det * w i ∂μ := by
        congr 1
        exact funext hpt
    _ = ∑ i ∈ S, ∫ x in s, (ContinuousLinearMap.id ℝ E + v i • A x).det * w i ∂μ :=
        integral_finsetSum _ fun i _ => (hint (v i)).mul_const _
    _ = ∑ i ∈ S, c * w i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_mul_const, h _ (hvs i hi).1 (hvs i hi).2]
    _ = c := by rw [← Finset.mul_sum, hw, mul_one]

/-! ### A Lipschitz extension by zero -/

omit [FiniteDimensional ℝ E] in
/-- Radial projection onto the unit sphere moves a point outside the ball
closer to every point of the ball. -/
theorem norm_sub_normalize_le {x y : E} (hx : ‖x‖ ≤ 1) (hy : 1 < ‖y‖) :
    ‖x - ‖y‖⁻¹ • y‖ ≤ ‖x - y‖ := by
  have hρ : 0 < ‖y‖ := by linarith
  have hP : inner ℝ x y ≤ ‖y‖ :=
    (real_inner_le_norm x y).trans (by nlinarith [norm_nonneg y, norm_nonneg x])
  have hw : ‖‖y‖⁻¹ • y‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hρ.ne']
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, norm_sub_sq_real,
    real_inner_smul_right, hw]
  have hinv : ‖y‖ * ‖y‖⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
  have hinv1 : ‖y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy.le
  nlinarith [mul_le_mul_of_nonneg_right hP (sub_nonneg.mpr hinv1), sq_nonneg (‖y‖ - 1)]

omit [FiniteDimensional ℝ E] in
/-- A map that is `L`-Lipschitz on the closed unit ball and vanishes on the unit
sphere stays `L`-Lipschitz on the whole space once extended by zero outside the
ball. -/
theorem norm_indicator_sub_le {v : E → E} {L : ℝ} (hL : 0 ≤ L)
    (hv : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1, ‖v x - v y‖ ≤ L * ‖x - y‖)
    (h0 : ∀ x ∈ sphere (0 : E) 1, v x = 0) (x y : E) :
    ‖(closedBall (0 : E) 1).indicator v x - (closedBall (0 : E) 1).indicator v y‖ ≤
      L * ‖x - y‖ := by
  have mixed : ∀ x y : E, x ∈ closedBall (0 : E) 1 → y ∉ closedBall (0 : E) 1 →
      ‖v x‖ ≤ L * ‖x - y‖ := by
    intro x y hx hy
    rw [mem_closedBall_zero_iff] at hx
    rw [mem_closedBall_zero_iff, not_le] at hy
    have hρ : 0 < ‖y‖ := by linarith
    have hwS : ‖y‖⁻¹ • y ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hρ.ne']
    have hwD : ‖y‖⁻¹ • y ∈ closedBall (0 : E) 1 := sphere_subset_closedBall hwS
    calc ‖v x‖ = ‖v x - v (‖y‖⁻¹ • y)‖ := by rw [h0 _ hwS, sub_zero]
      _ ≤ L * ‖x - ‖y‖⁻¹ • y‖ := hv x (mem_closedBall_zero_iff.mpr hx) _ hwD
      _ ≤ L * ‖x - y‖ := mul_le_mul_of_nonneg_left (norm_sub_normalize_le hx hy) hL
  by_cases hx : x ∈ closedBall (0 : E) 1 <;> by_cases hy : y ∈ closedBall (0 : E) 1
  · rw [indicator_of_mem hx, indicator_of_mem hy]
    exact hv x hx y hy
  · rw [indicator_of_mem hx, indicator_of_notMem hy, sub_zero]
    exact mixed x y hx hy
  · rw [indicator_of_notMem hx, indicator_of_mem hy, zero_sub, norm_neg, norm_sub_rev]
    exact mixed y x hy hx
  · rw [indicator_of_notMem hx, indicator_of_notMem hy, sub_zero, norm_zero]
    positivity


/-! ### (A) There is no `C¹` retraction of the ball onto the sphere -/

/-- **The small-time Jacobian identity.** Let `r` be differentiable on the closed
unit ball `D`, with derivative `r'` continuous on `D` and `‖r' x - 1‖ ≤ L` there,
and suppose that `r` maps `D` into the sphere and fixes the sphere. Then for
`0 ≤ t < 1/(L+1)`, `∫_D det (1 + t (r' x - 1)) dμ = μ D`.

The homotopy `fₜ = id + t (r - id)` is a bijection of `D` onto itself. It agrees
on `D` with a global bijection that is the identity off `D`, obtained from the
zero extension of `r - id` and the Banach fixed point theorem. Its Jacobian is
positive, so the change of variables formula gives the identity. -/
theorem integral_det_homotopy_eq [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {r : E → E} {r' : E → E →L[ℝ] E}
    (hr : ∀ x ∈ closedBall (0 : E) 1, HasFDerivAt r (r' x) x)
    (hr'c : ContinuousOn r' (closedBall (0 : E) 1)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ closedBall (0 : E) 1, ‖r' x - ContinuousLinearMap.id ℝ E‖ ≤ L)
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1)) (hfix : ∀ x ∈ sphere (0 : E) 1, r x = x)
    {t : ℝ} (ht0 : 0 ≤ t) (htε : t < (L + 1)⁻¹) :
    ∫ x in closedBall (0 : E) 1,
        (ContinuousLinearMap.id ℝ E + t • (r' x - ContinuousLinearMap.id ℝ E)).det ∂μ =
      (μ (closedBall (0 : E) 1)).toReal := by
  set D := closedBall (0 : E) 1
  set I := ContinuousLinearMap.id ℝ E
  have hL1 : 0 < L + 1 := by linarith
  have htL1 : t * (L + 1) < 1 := by
    have := mul_lt_mul_of_pos_right htε hL1
    rwa [inv_mul_cancel₀ hL1.ne'] at this
  have htL : t * L < 1 := by nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  -- `v = r - id` is `L`-Lipschitz on the ball and vanishes on the sphere
  let v : E → E := fun x => r x - x
  have hvd : ∀ x ∈ D, HasFDerivAt v (r' x - I) x := fun x hx => (hr x hx).sub (hasFDerivAt_id x)
  have hvlip : ∀ x ∈ D, ∀ y ∈ D, ‖v x - v y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := v)
      (fun z hz => (hvd z hz).differentiableAt)
      (fun z hz => by rw [(hvd z hz).fderiv]; exact hL z hz) (convex_closedBall 0 1) hy hx
  have hv0 : ∀ x ∈ sphere (0 : E) 1, v x = 0 := fun x hx => by simp [v, hfix x hx]
  -- its extension by zero is globally `L`-Lipschitz
  let w : E → E := D.indicator v
  have hwlip : ∀ x y, ‖w x - w y‖ ≤ L * ‖x - y‖ := norm_indicator_sub_le hL0 hvlip hv0
  let g : E → E := fun x => x + t • w x
  have hginj : Function.Injective g := by
    intro x y hxy
    have h1 : x - y = t • (w y - w x) := by
      have h := hxy
      simp only [g] at h
      rw [smul_sub]
      linear_combination (norm := module) h
    have h2 : ‖x - y‖ ≤ t * L * ‖x - y‖ := by
      calc ‖x - y‖ = t * ‖w y - w x‖ := by rw [h1, norm_smul, Real.norm_of_nonneg ht0]
        _ ≤ t * (L * ‖y - x‖) := mul_le_mul_of_nonneg_left (hwlip y x) ht0
        _ = t * L * ‖x - y‖ := by rw [norm_sub_rev]; ring
    have h3 : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hgsurj : Function.Surjective g := by
    intro y
    let K : ℝ≥0 := ⟨t * L, mul_nonneg ht0 hL0⟩
    have hK : ContractingWith K (fun z => y - t • w z) := by
      refine ⟨by rw [← NNReal.coe_lt_coe]; exact htL, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_left, ← smul_sub, norm_smul,
        Real.norm_of_nonneg ht0]
      calc t * ‖w b - w a‖ ≤ t * (L * ‖b - a‖) := mul_le_mul_of_nonneg_left (hwlip b a) ht0
        _ = (K : ℝ) * ‖a - b‖ := by
            rw [norm_sub_rev]
            show t * (L * ‖a - b‖) = t * L * ‖a - b‖
            ring
    obtain ⟨z, hz⟩ : ∃ z, y - t • w z = z := ⟨_, hK.fixedPoint_isFixedPt⟩
    exact ⟨z, (sub_eq_iff_eq_add.mp hz).symm⟩
  have hgD : ∀ x ∈ D, g x = x + t • (r x - x) := fun x hx => by
    simp [g, w, indicator_of_mem hx, v]
  have hgDc : ∀ x ∉ D, g x = x := fun x hx => by simp [g, w, indicator_of_notMem hx]
  -- the homotopy `f = id + t (r - id)` maps the ball injectively onto itself
  have hmapsD : ∀ x ∈ D, x + t • (r x - x) ∈ D := by
    intro x hx
    have hrx : ‖r x‖ = 1 := mem_sphere_zero_iff_norm.mp (hmaps hx)
    have hxn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    rw [mem_closedBall_zero_iff]
    have : x + t • (r x - x) = (1 - t) • x + t • r x := by module
    rw [this]
    calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
      _ = (1 - t) * ‖x‖ + t * ‖r x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
      _ ≤ 1 := by rw [hrx]; nlinarith
  have himg : (fun x => x + t • (r x - x)) '' D = D := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hmapsD x hx
    · intro y hy
      obtain ⟨x, rfl⟩ := hgsurj y
      by_cases hx : x ∈ D
      · exact ⟨x, hx, (hgD x hx).symm⟩
      · rw [hgDc x hx] at hy
        exact absurd hy hx
  have hinj : InjOn (fun x => x + t • (r x - x)) D := fun x hx y hy hxy =>
    hginj (by rw [hgD x hx, hgD y hy]; exact hxy)
  have hderiv : ∀ x ∈ D,
      HasFDerivWithinAt (fun x => x + t • (r x - x)) (I + t • (r' x - I)) D x :=
    fun x hx => ((hasFDerivAt_id x).add ((hvd x hx).const_smul t)).hasFDerivWithinAt
  -- change of variables
  have hcov := lintegral_abs_det_fderiv_eq_addHaar_image μ measurableSet_closedBall hderiv hinj
  rw [himg] at hcov
  have hpos : ∀ x ∈ D, 0 < (I + t • (r' x - I)).det := by
    intro x hx
    apply det_id_add_pos
    calc ‖t • (r' x - I)‖ = t * ‖r' x - I‖ := by rw [norm_smul, Real.norm_of_nonneg ht0]
      _ ≤ t * L := mul_le_mul_of_nonneg_left (hL x hx) ht0
      _ < 1 := htL
  have hcont : ContinuousOn (fun x => (I + t • (r' x - I)).det) D :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add ((hr'c.sub continuousOn_const).const_smul t))
  rw [integral_eq_lintegral_of_nonneg_ae _ (hcont.aestronglyMeasurable measurableSet_closedBall)]
  · congr 1
    rw [← hcov]
    refine setLIntegral_congr_fun measurableSet_closedBall (fun x hx => ?_)
    simp only [abs_of_pos (hpos x hx)]
  · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx using (hpos x hx).le

/-- If `‖r‖ = 1` near `x`, then the derivative of `r` at `x` is singular. The
derivative of `‖r‖²` is `2 ⟪r x, r' ·⟫`, which vanishes, so `r x ≠ 0` is not in
the range of `r'`. -/
theorem det_eq_zero_of_eventually_norm_eq_one {r : E → E} {x : E} {r' : E →L[ℝ] E}
    (hr : HasFDerivAt r r' x) (hloc : ∀ᶠ y in nhds x, ‖r y‖ = 1) :
    r'.det = 0 := by
  have hx : ‖r x‖ = 1 := hloc.self_of_nhds
  have h1 : HasFDerivAt (fun y => ‖r y‖ ^ 2) (2 • (innerSL ℝ (r x)).comp r') x := hr.norm_sq
  have h2 : HasFDerivAt (fun y => ‖r y‖ ^ 2) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq (hloc.mono fun y hy => by simp [hy])
  have h3 := h1.unique h2
  by_contra hdet
  have hker : LinearMap.ker (r' : E →ₗ[ℝ] E) = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hsurj : Function.Surjective (r' : E →ₗ[ℝ] E) :=
    LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)
  obtain ⟨h, hh⟩ := hsurj (r x)
  have hh' : r' h = r x := hh
  have h4 := congrArg (fun T : E →L[ℝ] ℝ => T h) h3
  simp [hh', hx] at h4

/-- **No `C¹` retraction.** No map that is `C¹` on a neighbourhood of the closed
unit ball can send the ball into the unit sphere while fixing the sphere.

The integral of the Jacobian determinant of `r` over the ball would equal the
volume of the ball (`integral_det_homotopy_eq`, extended to `t = 1` by
`integral_det_eq_of_forall_small`), yet it vanishes because the Jacobian is
singular at every interior point (`det_eq_zero_of_eventually_norm_eq_one`) and
the sphere is null. -/
theorem no_C1_retraction {U : Set E} (hU : IsOpen U) (hDU : closedBall (0 : E) 1 ⊆ U)
    {r : E → E} (hr : ContDiffOn ℝ 1 r U) (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1))
    (hfix : ∀ x ∈ sphere (0 : E) 1, r x = x) : False := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h := hmaps (mem_closedBall_self zero_le_one : (0 : E) ∈ closedBall 0 1)
    rw [mem_sphere_zero_iff_norm, Subsingleton.elim (r 0) 0, norm_zero] at h
    exact zero_ne_one h
  borelize E
  let μ : Measure E := Measure.addHaar
  set D := closedBall (0 : E) 1
  set I := ContinuousLinearMap.id ℝ E
  have hr' : ∀ x ∈ U, HasFDerivAt r (fderiv ℝ r x) x := fun x hx =>
    ((hr.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hrc : ContinuousOn (fderiv ℝ r) U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  have hAc : ContinuousOn (fun x => fderiv ℝ r x - I) D := (hrc.mono hDU).sub continuousOn_const
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hAc
  have hsmall : ∀ t, 0 ≤ t → t < (max C 0 + 1)⁻¹ →
      ∫ x in D, (I + t • (fderiv ℝ r x - I)).det ∂μ = (μ D).toReal := fun t ht0 ht =>
    integral_det_homotopy_eq μ (fun x hx => hr' x (hDU hx)) (hrc.mono hDU) (le_max_right _ _)
      (fun x hx => (hC x hx).trans (le_max_left _ _)) hmaps hfix ht0 ht
  have h1 := integral_det_eq_of_forall_small (μ := μ) (isCompact_closedBall 0 1) hAc
    (by positivity) hsmall
  have h2 : ∫ x in D, (I + (fderiv ℝ r x - I)).det ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_closedBall, ae_iff]
    refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_sphere μ 0 1)
    obtain ⟨hxD, hx0⟩ := Classical.not_imp.mp hx
    by_contra hxS
    have hxB : x ∈ ball (0 : E) 1 := by
      rw [mem_ball_zero_iff]
      rw [mem_closedBall_zero_iff] at hxD
      rw [mem_sphere_zero_iff_norm] at hxS
      exact lt_of_le_of_ne hxD hxS
    apply hx0
    have heq : I + (fderiv ℝ r x - I) = fderiv ℝ r x := by abel
    simp only [Pi.zero_apply, heq]
    refine det_eq_zero_of_eventually_norm_eq_one (hr' x (hDU hxD)) ?_
    filter_upwards [isOpen_ball.mem_nhds hxB] with y hy
    exact mem_sphere_zero_iff_norm.mp (hmaps (ball_subset_closedBall hy))
  have hpos : 0 < (μ D).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos μ 0 one_pos).ne' measure_closedBall_lt_top.ne
  linarith

/-! ### (B) From continuous maps to `C¹` retractions -/

/-- A map continuous on a closed set `K` of a finite-dimensional space is
uniformly approximated on `K`, to any precision `ε > 0`, by a `C¹` map on the
whole space. A smooth partition of unity glues the locally constant choices
`ϕ x`, and membership in the convex sets `ball (ϕ y) ε` survives the gluing. -/
theorem exists_contDiff_approx {K : Set E} (hK : IsClosed K) {ϕ : E → E}
    (hϕ : ContinuousOn ϕ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → E, ContDiff ℝ 1 g ∧ ∀ x ∈ K, ‖g x - ϕ x‖ < ε := by
  classical
  let T : E → Set E := fun x => if x ∈ K then ball (ϕ x) ε else univ
  have hT : ∀ x, Convex ℝ (T x) := fun x => by
    by_cases hx : x ∈ K
    · simp only [T, if_pos hx]; exact convex_ball _ _
    · simp only [T, if_neg hx]; exact convex_univ
  have hloc : ∀ x : E, ∃ c : E, ∀ᶠ y in nhds x, c ∈ T y := by
    intro x
    by_cases hx : x ∈ K
    · refine ⟨ϕ x, ?_⟩
      have h1 : ∀ᶠ y in nhdsWithin x K, ϕ y ∈ ball (ϕ x) ε :=
        Filter.Tendsto.eventually_mem (hϕ x hx) (ball_mem_nhds _ hε)
      rw [eventually_nhdsWithin_iff] at h1
      filter_upwards [h1] with y hy
      by_cases hyK : y ∈ K
      · simp only [T, if_pos hyK]; exact mem_ball_comm.mp (hy hyK)
      · simp only [T, if_neg hyK]; exact mem_univ _
    · refine ⟨0, ?_⟩
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simp only [T, if_neg hy]; exact mem_univ _
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, E) (n := 1) hT hloc
  refine ⟨g, contMDiff_iff_contDiff.mp g.contMDiff, fun x hx => ?_⟩
  have := hg x
  simp only [T, if_pos hx] at this
  rwa [mem_ball, dist_eq_norm] at this

/-- The algebra behind the ray construction. If `τ` is the larger root of
`a τ² + 2 b τ + (X - 1) = 0`, written through `s² = b² + a (1 - X)`, then
`X + 2 τ b + τ² a = 1`. -/
theorem ray_algebra {a b X s τ : ℝ} (ha : a ≠ 0) (hs : s ^ 2 = b ^ 2 + a * (1 - X))
    (hτ : a * τ = -b + s) : X + 2 * τ * b + τ ^ 2 * a = 1 := by
  have h2 : a * (X + 2 * τ * b + τ ^ 2 * a - 1) = 0 := by
    linear_combination (a * τ + s + b) * hτ + hs
  have := (mul_eq_zero.mp h2).resolve_left ha
  linarith

omit [FiniteDimensional ℝ E] in
/-- **The ray construction.** A `C¹` self-map `q` of the closed unit ball with no
fixed point yields a `C¹` retraction of a neighbourhood of the ball onto the
sphere. Let `u = x - q x`. Then `r x = x + τ(x) u` with
`τ = (-⟪x,u⟫ + √(⟪x,u⟫² + ‖u‖² (1 - ‖x‖²))) / ‖u‖²` is the point where the ray
from `q x` through `x` meets the sphere. On the ball the discriminant is positive
(on the sphere it is `⟪x,u⟫² > 0`, since `⟪x, q x⟫ = 1` would force `q x = x`)
and `u ≠ 0`, so both conditions hold on an open neighbourhood, where `r` is `C¹`.
On the sphere the larger root is `0`, so `r` fixes the sphere. -/
theorem exists_C1_retraction {q : E → E} (hq : ContDiff ℝ 1 q)
    (hqD : MapsTo q (closedBall 0 1) (closedBall 0 1))
    (hne : ∀ x ∈ closedBall (0 : E) 1, q x ≠ x) :
    ∃ U : Set E, IsOpen U ∧ closedBall (0 : E) 1 ⊆ U ∧ ∃ r : E → E, ContDiffOn ℝ 1 r U ∧
      MapsTo r (closedBall 0 1) (sphere 0 1) ∧ ∀ x ∈ sphere (0 : E) 1, r x = x := by
  let u : E → E := fun x => x - q x
  let a : E → ℝ := fun x => inner ℝ (u x) (u x)
  let b : E → ℝ := fun x => inner ℝ x (u x)
  let d : E → ℝ := fun x => b x ^ 2 + a x * (1 - inner ℝ x x)
  let τ : E → ℝ := fun x => (-b x + √(d x)) / a x
  let r : E → E := fun x => x + τ x • u x
  have hu : ContDiff ℝ 1 u := contDiff_id.sub hq
  have ha : ContDiff ℝ 1 a := hu.inner ℝ hu
  have hb : ContDiff ℝ 1 b := contDiff_id.inner ℝ hu
  have hd : ContDiff ℝ 1 d :=
    (hb.pow 2).add (ha.mul (contDiff_const.sub (contDiff_id.inner ℝ contDiff_id)))
  let U := {x | 0 < d x} ∩ {x | 0 < a x}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hd.continuous).inter (isOpen_lt continuous_const ha.continuous)
  have key : ∀ x ∈ closedBall (0 : E) 1, 0 < a x ∧ 0 < d x ∧ (‖x‖ = 1 → 0 < b x) := by
    intro x hx
    have hxn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hqn : ‖q x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hqD hx)
    have hX : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
    have hQ : inner ℝ (q x) (q x) = ‖q x‖ ^ 2 := real_inner_self_eq_norm_sq _
    have haeq : a x = inner ℝ x x - 2 * inner ℝ x (q x) + inner ℝ (q x) (q x) := by
      simp only [a, u, inner_sub_left, inner_sub_right, real_inner_comm x (q x)]
      ring
    have hbeq : b x = inner ℝ x x - inner ℝ x (q x) := by simp only [b, u, inner_sub_right]
    have hapos : 0 < a x := real_inner_self_pos.mpr (sub_ne_zero.mpr (hne x hx).symm)
    have hb1 : ‖x‖ = 1 → 0 < b x := by
      intro h1
      have hQ1 : ‖q x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hqn
      have hapos' := hapos
      rw [haeq, hX, hQ, h1] at hapos'
      rw [hbeq, hX, h1]
      nlinarith
    refine ⟨hapos, ?_, hb1⟩
    rcases hxn.lt_or_eq with hlt | heq
    · have : 0 < 1 - inner ℝ x x := by rw [hX]; nlinarith [norm_nonneg x]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hapos this)
    · have : 1 - inner ℝ x x = 0 := by rw [hX, heq]; norm_num
      simp only [d, this, mul_zero, add_zero]
      exact pow_pos (hb1 heq) 2
  have hDU : closedBall (0 : E) 1 ⊆ U := fun x hx => ⟨(key x hx).2.1, (key x hx).1⟩
  refine ⟨U, hUo, hDU, r, ?_, ?_, ?_⟩
  · intro x hx
    have hdx : d x ≠ 0 := hx.1.ne'
    have hax : a x ≠ 0 := hx.2.ne'
    have hτ : ContDiffAt ℝ 1 τ x :=
      ((hb.contDiffAt.neg).add (hd.contDiffAt.sqrt hdx)).div ha.contDiffAt hax
    exact (contDiffAt_id.add (hτ.smul hu.contDiffAt)).contDiffWithinAt
  · intro x hx
    obtain ⟨hapos, hdpos, -⟩ := key x hx
    have hax : a x ≠ 0 := hapos.ne'
    rw [mem_sphere_zero_iff_norm]
    have hs : √(d x) ^ 2 = b x ^ 2 + a x * (1 - inner ℝ x x) := Real.sq_sqrt hdpos.le
    have hτ : a x * τ x = -b x + √(d x) := by simp only [τ]; field_simp
    have hsq : inner ℝ (r x) (r x) = 1 := by
      have : inner ℝ (r x) (r x) = inner ℝ x x + 2 * τ x * b x + τ x ^ 2 * a x := by
        simp only [r, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, b, a, real_inner_comm x (u x)]
        ring
      rw [this]
      exact ray_algebra hax hs hτ
    rw [real_inner_self_eq_norm_sq] at hsq
    have := norm_nonneg (r x)
    nlinarith
  · intro x hx
    have hxD : x ∈ closedBall (0 : E) 1 := sphere_subset_closedBall hx
    obtain ⟨-, -, hb1⟩ := key x hxD
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hbpos := hb1 hn
    have hX : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    have hdx : d x = b x ^ 2 := by simp only [d, hX, sub_self, mul_zero, add_zero]
    have hτ0 : τ x = 0 := by
      simp only [τ, hdx, Real.sqrt_sq hbpos.le, neg_add_cancel, zero_div]
    simp only [r, hτ0, zero_smul, add_zero]

/-- **Brouwer's fixed point theorem** on the closed unit ball of any
finite-dimensional real inner product space. If `ϕ` had no fixed point, a `C¹`
map close to `(1 - δ/3) ϕ` would also have none (`δ` being the minimal
displacement of `ϕ`). The ray construction would turn it into a `C¹` retraction
of the ball onto the sphere, which `no_C1_retraction` forbids. -/
theorem brouwer_fixed_point_of_innerProductSpace {ϕ : E → E}
    (hcont : ContinuousOn ϕ (closedBall (0 : E) 1))
    (hmaps : MapsTo ϕ (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : E) 1, ϕ x = x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    (nonempty_closedBall.mpr zero_le_one) (hcont.sub continuousOn_id).norm
  set δ := ‖ϕ x₀ - x₀‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (hcon x₀ hx₀))
  have hδle : ∀ x ∈ closedBall (0 : E) 1, δ ≤ ‖ϕ x - x‖ := fun x hx => hmin hx
  have hδ2 : δ ≤ 2 := by
    calc δ ≤ ‖ϕ x₀‖ + ‖x₀‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (mem_closedBall_zero_iff.mp (hmaps hx₀))
          (mem_closedBall_zero_iff.mp hx₀)
      _ = 2 := by norm_num
  set η := δ / 3 with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨q, hq, hqa⟩ := exists_contDiff_approx isClosed_closedBall
    (hcont.const_smul (1 - η)) hη
  have hqD : MapsTo q (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    have hϕx := mem_closedBall_zero_iff.mp (hmaps hx)
    calc ‖q x‖ = ‖(q x - (1 - η) • ϕ x) + (1 - η) • ϕ x‖ := by rw [sub_add_cancel]
      _ ≤ ‖q x - (1 - η) • ϕ x‖ + ‖(1 - η) • ϕ x‖ := norm_add_le _ _
      _ ≤ η + (1 - η) * 1 := by
          rw [norm_smul, Real.norm_of_nonneg (by linarith)]
          exact add_le_add (hqa x hx).le (mul_le_mul_of_nonneg_left hϕx (by linarith))
      _ = 1 := by ring
  have hqne : ∀ x ∈ closedBall (0 : E) 1, q x ≠ x := by
    intro x hx hqx
    have hϕx := mem_closedBall_zero_iff.mp (hmaps hx)
    have h1 : ‖ϕ x - q x‖ < 2 * η := by
      have hsplit : ϕ x - q x = η • ϕ x - (q x - (1 - η) • ϕ x) := by module
      calc ‖ϕ x - q x‖ ≤ ‖η • ϕ x‖ + ‖q x - (1 - η) • ϕ x‖ := by
            rw [hsplit]; exact norm_sub_le _ _
        _ < η + η := by
            rw [norm_smul, Real.norm_of_nonneg hη.le]
            exact add_lt_add_of_le_of_lt (by nlinarith [norm_nonneg (ϕ x)]) (hqa x hx)
        _ = 2 * η := by ring
    rw [hqx] at h1
    have h2 := hδle x hx
    linarith
  obtain ⟨U, hU, hDU, r, hr, hrmaps, hrfix⟩ := exists_C1_retraction hq hqD hqne
  exact no_C1_retraction hU hDU hr hrmaps hrfix

/-- **No retraction of the ball onto the sphere**, for continuous maps on any
finite-dimensional real inner product space. A continuous map of the closed
ball into the sphere moves some point of the sphere. Otherwise `-r` would be a
fixed-point-free self-map of the ball: a fixed point `x = -r x` lies on the
sphere, where `r x = x` forces `x = 0`. -/
theorem no_retraction_of_innerProductSpace {r : E → E}
    (hr : ContinuousOn r (closedBall (0 : E) 1))
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1)) :
    ∃ x ∈ sphere (0 : E) 1, r x ≠ x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hfix⟩ := brouwer_fixed_point_of_innerProductSpace (ϕ := fun x => -r x) hr.neg
    (fun y hy => by
      simpa [mem_closedBall_zero_iff, norm_neg] using
        (mem_sphere_zero_iff_norm.mp (hmaps hy)).le)
  have hn : ‖x‖ = 1 := by
    rw [← hfix, norm_neg]
    exact mem_sphere_zero_iff_norm.mp (hmaps hx)
  have hrx : r x = x := hcon x (mem_sphere_zero_iff_norm.mpr hn)
  have hx0 : x = 0 := by
    have h : -x = x := by simpa [hrx] using hfix
    have : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel x
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  rw [hx0, norm_zero] at hn
  exact zero_ne_one hn

end Brouwer

/-- **Brouwer's fixed point theorem** (Theorem 2.3.3 of the book, reproved in
§4.8.b). Every continuous self-map of the closed unit ball of `ℝⁿ` has a fixed
point, in every dimension `n`. The proof is the analytic one sketched in the
module docstring and does not go through homology. -/
theorem brouwer_fixed_point {n : ℕ} (ϕ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn ϕ (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo ϕ (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ϕ x = x :=
  Brouwer.brouwer_fixed_point_of_innerProductSpace hcont hmaps

/-- **No retraction of the ball onto its boundary** (§4.8.b). In every dimension,
a continuous map of the closed unit ball of `ℝⁿ` into the unit sphere moves some
point of the sphere. -/
theorem no_retraction {n : ℕ} (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : ContinuousOn r (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo r (Metric.closedBall 0 1) (Metric.sphere 0 1)) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, r x ≠ x :=
  Brouwer.no_retraction_of_innerProductSpace hr hmaps

end MorseFloer
